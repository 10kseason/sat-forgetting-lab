import random
import runpy
import unittest
from itertools import combinations, product
from pathlib import Path

from linear_autarky import peel


def valid(bits, edges):
    return all(bits[a]!=bits[b] or bits[b]!=bits[c] for a,b,c in edges)


class AutarkyTests(unittest.TestCase):
    def test_all_extensions_satisfy_touched_triples(self):
        rng = random.Random(2766427327)
        pool = list(combinations(range(6),3))
        for _ in range(100):
            edges = rng.sample(pool,rng.randrange(len(pool)+1))
            doubled = rng.choices(range(3),k=len(edges))
            result = peel(6,edges,doubled)
            self.assertEqual(set(result.remaining),
                             {e for e in edges if all(result.fixed[v] is None for v in e)})
            for x in product((False,True),repeat=6):
                self.assertEqual(valid(result.extend(x),edges),valid(x,result.remaining))
            self.assertEqual(any(valid(x,edges) for x in product((False,True),repeat=6)),
                             any(valid(x,result.remaining) for x in product((False,True),repeat=6)))

    def test_double_the_minority_only(self):
        data = runpy.run_path(str(Path(__file__).parent/"routes"/"matching-balance"/"dual.py"))
        rng = random.Random(2766427327)
        for k in (1,2):
            edges = [e for group in data["cycle"](k) for e in group]
            n = 15*k
            bits = tuple(bool(0x3263>>(i%15)&1) for i in range(n))
            actual = [edge.index(data["minority"](bits,edge)) for edge in edges]
            result = peel(n,edges,actual)
            self.assertFalse(result.remaining)
            self.assertIn(result.extend([False]*n),(bits,tuple(not v for v in bits)))
            self.assertEqual(peel(n,edges).rounds,0)
            for j in range(len(edges)):
                wrong = actual.copy()
                wrong[j] = (wrong[j]+rng.choice((1,2)))%3
                self.assertEqual(peel(n,edges,wrong).rounds,0)

    def test_local_peel_can_leave_an_unsat_core(self):
        data = runpy.run_path(str(Path(__file__).parent/"routes"/"matching-balance"/"independent.py"))
        core = [e for group in data["affine_plane"]() for e in group]
        result = peel(11,[*core,(0,9,10)])
        self.assertEqual(set(result.remaining),set(core))
        self.assertNotEqual(result.fixed[9],result.fixed[10])
