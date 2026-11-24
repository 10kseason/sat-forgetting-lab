import random
import unittest
from itertools import combinations, product

from matching_balance import BLOCK
from near_cut import solve_near_cut
from solve_cnf import solve


def valid(bits, triples):
    return all(bits[a] != bits[b] or bits[a] != bits[c] for a,b,c in triples)


class NearCutTests(unittest.TestCase):
    def test_independent_truth_tables(self):
        rng = random.Random(1234886835)
        for n in range(10):
            candidates = list(combinations(range(n),3))
            rows = list(product((False,True),repeat=n))
            for _ in range(30):
                rng.shuffle(candidates)
                edges, pairs = [], set()
                for triple in candidates:
                    inside = set(combinations(triple,2))
                    if not pairs & inside and rng.randrange(3):
                        edges.append(triple)
                        pairs.update(inside)
                result = solve_near_cut(n,edges)
                expected = any(valid(x,edges) for x in rows)
                self.assertEqual(result.status,"SAT" if expected else "UNSAT")
                if result.assignment is not None:
                    self.assertTrue(valid(result.assignment,edges))
                self.assertLessEqual(result.patterns,result.bound)

    def test_normal_entry_and_budget(self):
        edges = [e for group in BLOCK for e in group]
        f = [tuple(s*(v+1) for v in e) for e in edges for s in (1,-1)]
        result = solve(12,f)
        self.assertEqual((result.status,result.method),("SAT","NAE complement forest"))
        self.assertTrue(valid(result.assignment,edges))
        bounded = solve_near_cut(12,edges,1,skip_over_budget=True)
        self.assertEqual((bounded.status,bounded.patterns),("UNKNOWN",0))
        self.assertGreater(bounded.bound,1)
        self.assertEqual(solve_near_cut(0,[]).assignment,())
        for n, edges in [(3, [(0,1,2),(0,1,2)]), (2, [(0,1,2)]), (2, [(0,0,1)])]:
            with self.assertRaises(ValueError):
                solve_near_cut(n,edges)
