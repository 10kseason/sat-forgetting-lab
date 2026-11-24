import random
import unittest
from itertools import combinations, product

from binary_probing import learned_binary_clauses
from forgetting import cnf_value
from nae_cut import cut_obstruction
from solve_cnf import solve


def steiner_clauses(dimension, flip=()):
    n = (1 << dimension) - 1
    triples = ((a,b,a^b) for a,b in combinations(range(1,n+1),2) if b < a^b)
    clauses = []
    for triple in triples:
        row = tuple(-v if v in flip else v for v in triple)
        clauses.extend((row, tuple(-lit for lit in row)))
    return n, clauses


class NAECutTests(unittest.TestCase):
    def test_steiner_solver_entry(self):
        n, formula = steiner_clauses(4)
        self.assertEqual(learned_binary_clauses(n, formula), ())
        cert = cut_obstruction(formula)
        self.assertEqual((cert.triples, cert.required_score, cert.score_upper_bound),
                         (35, 70, 56))
        before = solve(n, formula, use_cut=False)
        after = solve(n, formula, max_patterns=1)
        self.assertEqual((before.status, before.assignments_tested), ("UNSAT", 8192))
        self.assertEqual((after.status, after.method, after.assignments_tested),
                         ("UNSAT", "NAE cut bound", 0))

    def test_embedded_component_and_signed_clauses(self):
        n, signed = steiner_clauses(5, flip=(7,))
        paired = signed + [signed[0], (n+1, n+2, n+3)]
        cert = cut_obstruction(paired)
        self.assertLess(cert.score_upper_bound, cert.required_score)
        self.assertEqual(set(cert.vertices), set(range(1, n+1)))

    def test_arbitrary_signed_systems_against_truth_tables(self):
        rng = random.Random(99173)
        rows = list(product((False,True), repeat=6))
        for _ in range(400):
            formula = []
            for _ in range(rng.randrange(30)):
                nodes = sorted(rng.sample(range(1,7), 3))
                triple = tuple(v*rng.choice((-1,1)) for v in nodes)
                formula.append(triple)
                if rng.randrange(4):
                    formula.append(tuple(-lit for lit in triple))
            if cut_obstruction(formula) is not None:
                self.assertFalse(any(cnf_value(formula, x) for x in rows))
            # A planted solution must suppress every false UNSAT certificate.
            witness = rng.choice(rows)
            self.assertIsNone(cut_obstruction(c for c in formula if cnf_value([c],witness)))

    def test_strict_subsets_at_every_possible_size(self):
        fano = [(a,b,a^b) for a,b in combinations(range(1,8),2) if b<a^b]
        nine = [tuple(3*i+j+1 for j in range(3)) for i in range(3)]
        nine.extend(tuple(3*r+(line+d*r)%3+1 for r in range(3))
                    for d in range(3) for line in range(3))
        nine = nine[1:]
        ten = [(0,1,2),(0,3,8),(0,4,6),(0,5,7),(1,3,9),(1,4,7),(1,6,8),
               (2,3,4),(2,5,9),(2,6,7),(3,5,6),(4,5,8),(7,8,9)]
        for size, core in [(7,fano),(9,nine),(10,[tuple(i+1 for i in e) for e in ten])]:
            loose = next(i for i in range(1,size+1) if sum(i in e for e in core)<4)
            edges = core + [(loose,size+1,size+2)]
            formula = [tuple(sign*i for i in sorted(e)) for e in edges for sign in (1,-1)]
            result = cut_obstruction(formula)
            self.assertEqual(set(result.vertices),set(range(1,size+1)))
            self.assertLess(result.score_upper_bound,result.required_score)
