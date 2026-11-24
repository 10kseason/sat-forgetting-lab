import random
import unittest
from itertools import combinations, permutations, product

from binary_promotion import check_clause, promote
from forgetting import clause_value, cnf_value


def majority(a, b, c):
    return tuple(x + y + z >= 2 for x, y, z in zip(a, b, c))


def models(rows, formula):
    return {x for x in rows if cnf_value(formula, x)}


class BinaryPromotionTests(unittest.TestCase):
    def check_relation(self, n, rows, base, clause):
        result = check_clause(n, (iter(c) for c in base), iter(clause))
        exact = models(rows, [*base, clause])
        reduced = list(base) if result.reduced is None else [*base, result.reduced]
        self.assertEqual(models(rows, reduced), exact)
        closed = all(majority(*triple) in exact for triple in combinations(exact, 3))
        self.assertEqual(result.binary, closed)
        if not closed:
            self.assertEqual(len(result.obstruction), 3)
            self.assertTrue(all(x in exact for x in result.obstruction))
            median = majority(*result.obstruction)
            self.assertTrue(cnf_value(base, median))
            self.assertFalse(clause_value(clause, median))

    def test_all_three_bit_background_relations(self):
        n = 3
        rows = list(product((False, True), repeat=n))
        short = [()] + [(i*s,) for i in range(1,n+1) for s in (-1, 1)]
        short.extend((i*s, j*t) for i,j in combinations(range(1,n+1), 2)
                     for s,t in product((-1,1), repeat=2))
        for mask in range(1 << len(rows)):
            relation = {row for i,row in enumerate(rows) if mask & (1 << i)}
            base = [c for c in short if all(clause_value(c, x) for x in relation)]
            if models(rows, base) != relation:
                continue
            for signs in product((-1,1), repeat=3):
                clause = tuple(i*s for i,s in enumerate(signs, 1))
                self.check_relation(n, rows, base, clause)

    def test_long_signed_clauses(self):
        rng = random.Random(549904478)
        rows = list(product((False, True), repeat=5))
        alphabet = tuple(i*s for i in range(1,6) for s in (-1,1))
        for _ in range(125):
            base = [rng.choices(alphabet, k=2) for _ in range(rng.randrange(7))]
            clause = rng.choices(alphabet, k=rng.randrange(10))
            self.check_relation(5, rows, base, clause)

    def test_fixed_point_and_limits(self):
        base = [(-1,)]
        wide = [(1, 2, 3), (-2, 3, 4), (-3, 4, 5)]
        rows = list(product((False, True), repeat=5))
        for order in permutations(wide):
            result = promote(5, base + list(order))
            self.assertEqual(result.remaining, ())
            self.assertEqual(set(result.promoted_ids), {1, 2, 3})
            self.assertEqual(models(rows, result.binary), models(rows, base + wide))
        stuck = [(1, 2, 3), (1, 2, -3)]
        result = promote(3, stuck)
        self.assertEqual(result.remaining, tuple(enumerate(stuck)))
        self.assertEqual(models(rows, stuck), models(rows, [(1,2)]))

    def test_zero_variables_and_validation(self):
        self.assertEqual(check_clause(2, [(1, 1, 1)], (2,)).reduced, (2,))
        self.assertEqual(check_clause(0, [()], ()).reduced, ())
        self.assertEqual(promote(0, []).remaining, ())
        for n, base, clause in [(-1, [], []), (3, [(1,2,3)], []),
                                 (3, [()], (4,)), (1, [(0,)], ())]:
            with self.assertRaises(ValueError):
                check_clause(n, base, clause)
