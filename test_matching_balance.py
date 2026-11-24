import unittest
from itertools import combinations

from gf2 import reduce_system
from matching_balance import BLOCK, PORT, PORTS, balanced_cycle, balanced_substitution, proper


class MatchingBalanceTests(unittest.TestCase):
    def test_exact_block_models_and_rank(self):
        triples = [edge for group in BLOCK for edge in group]
        rows = [(sum(1 << i for i in edge),0) for edge in triples]
        self.assertEqual(len(reduce_system(12, rows)), 12)
        wanted = {0x43b, 0x5b2, 0x64b, 0x9b4, 0xa4d, 0xbc4}
        for edges in (triples, [e for e in triples if e != PORT]):
            self.assertEqual({x for x in range(4096) if proper(x,edges)}, wanted)
        self.assertTrue(all(bits.bit_count() == 6 for bits in wanted))

    def test_lift_incidence_and_coloring(self):
        for count in (1, 2, 3, 9):
            matchings = balanced_cycle(count)
            vertices = set(range(12*count))
            for group in matchings:
                self.assertEqual(sorted(i for edge in group for i in edge), sorted(vertices))
            triples = [edge for group in matchings for edge in group]
            pairs = [tuple(sorted(pair)) for edge in triples for pair in combinations(edge,2)]
            self.assertEqual(len(pairs), len(set(pairs)))
            reached = {0}
            while True:
                more = reached.union(*(e for e in triples if reached.intersection(e)))
                if more == reached:
                    break
                reached = more
            self.assertEqual(reached, vertices)
            witness = sum(0x43b << (12*i) for i in range(count))
            self.assertTrue(proper(witness,triples))
            for group in matchings:
                doubled = sum(sum(witness>>i&1 for i in e) == 2 for e in group)
                self.assertEqual(doubled, 2*count)

    def test_parsimonious_replacement(self):
        plane = tuple(tuple(tuple(3*r+c for c in range(3)) for r in range(3))
                      if direction == 3 else
                      tuple(tuple(3*r + (line+direction*r)%3 for r in range(3))
                            for line in range(3))
                      for direction in range(4))
        for source, expected in [(BLOCK,6), (plane,0)]:
            image = balanced_substitution(source)
            triples = [e for group in image.matchings for e in group]
            inputs = [e for group in source for e in group]
            n = 3*len(source[0])
            for group in image.matchings:
                self.assertEqual(sorted(i for edge in group for i in edge), list(range(4*n)))
            pairs = [tuple(sorted(p)) for e in triples for p in combinations(e,2)]
            self.assertEqual(len(pairs),len(set(pairs)))
            total = 0
            for bits in range(1<<n):
                if proper(bits,source[0]):
                    lifted = image.lift(bits)
                    self.assertEqual(proper(lifted,triples),proper(bits,inputs))
                    self.assertEqual(image.project(lifted),bits)
                    total += proper(lifted,triples)
            self.assertEqual(total,expected)
        with self.assertRaises(ValueError):
            balanced_substitution([BLOCK[0]]*4)

    def test_open_port_rows(self):
        inside = [e for j,g in enumerate(BLOCK) for e in g
                  if j == 3 or set(e) != set(PORTS[j])]
        states = [x for x in range(4096) if proper(x,inside)]
        self.assertEqual(len(states),6)
        for x in states:
            signals = tuple(x>>i&1 for i in PORTS[0])
            self.assertEqual(tuple(x>>i&1 for i in PORTS[1]),tuple(1-y for y in signals))
            self.assertEqual(tuple(x>>i&1 for i in PORTS[2]),signals)
            self.assertEqual(x.bit_count(),6)
