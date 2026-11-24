import random
import unittest
from itertools import product

from anonymous_blocks import _local_literals, _switching, contract
from matching_balance import BLOCK, PORTS, balanced_substitution
from forgetting import cnf_value
from solve_cnf import solve


def scramble(matchings, n, rng):
    rename = list(range(n))
    rng.shuffle(rename)
    edges = []
    for group in matchings:
        for e in group:
            edge = [rename[v] for v in e]
            rng.shuffle(edge)
            edges.append(tuple(edge))
    rng.shuffle(edges)
    return tuple(edges)


def valid(bits, edges):
    return all(bits[a] != bits[b] or bits[b] != bits[c] for a,b,c in edges)


class AnonymousBlockTests(unittest.TestCase):
    def test_unlabeled_models_in_both_directions(self):
        rng = random.Random(940061948)
        image = balanced_substitution(BLOCK)
        for _ in range(3):
            edges = scramble(image.matchings, 48, rng)
            core = contract(48, edges)
            self.assertEqual(core.vertices,12)
            good = 0
            for x in product((False,True), repeat=12):
                lifted = core.lift(x)
                feasible = valid(x, core.triples)
                self.assertEqual(feasible, valid(lifted, edges))
                self.assertEqual(core.project(lifted),x)
                good += feasible
            self.assertEqual(good,6)

    def test_multiple_levels_with_no_names(self):
        rng = random.Random(940061949)
        groups, n = BLOCK, 12
        for _ in range(3):
            groups = balanced_substitution(groups).matchings
            n *= 4
        edges = scramble(groups, n, rng)
        original = edges
        levels = []
        while (core := contract(n, edges)) is not None:
            levels.append(core)
            n, edges = core.vertices, core.triples
        self.assertEqual([c.vertices for c in levels], [192,48,12])
        x = next(bits for bits in product((False, True),repeat=n) if valid(bits,edges))
        for level in reversed(levels):
            x = level.lift(x)
        self.assertEqual(len(x),768)
        self.assertEqual(sum(x),384)
        self.assertTrue(valid(x,original))

    def test_default_solver_on_five_scrambled_levels(self):
        plane = tuple(tuple(tuple(3*i+j for j in range(3)) for i in range(3)) if d == 3
                      else tuple(tuple(3*r+(i+d*r)%3 for r in range(3)) for i in range(3))
                      for d in range(4))
        for n, groups, expected in [(9,plane,"UNSAT"), (12,BLOCK,"SAT")]:
            for _ in range(5):
                groups = balanced_substitution(groups).matchings
                n *= 4
            edges = scramble(groups, n, random.Random(940061953))
            formula = [tuple(sign*(i+1) for i in edge) for edge in edges for sign in (1,-1)]
            result = solve(n,formula)
            self.assertEqual(result.status,expected)
            self.assertTrue(result.method.startswith("NAE block contraction / "))
            if result.assignment is not None:
                self.assertTrue(cnf_value(formula,result.assignment))
            else:
                self.assertEqual(result.assignments_tested,0)

    def test_rejection_and_inverted_lanes(self):
        physical = [e for j,group in enumerate(BLOCK) for e in group
                    if j==3 or set(e)!=set(PORTS[j])]
        self.assertIsNotNone(_local_literals(physical))
        self.assertIsNone(_local_literals(physical[:3]))
        self.assertIsNone(_switching(3, [(1,2,3), (1,-2,3)]))
        self.assertIsNone(contract(12, [e for group in BLOCK for e in group]))
        self.assertIsNone(contract(12, [(0,1,15)]*16))
