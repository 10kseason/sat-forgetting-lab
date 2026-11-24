"""Truth-table oracle independent of the elimination and occurrence-path code."""

import random
import unittest
from itertools import combinations, product

from guarded_affine import (matching_path_witness, occurrence_path,
                            single_row_frontier, split_occurrences)
from two_sat import solve_2cnf


def truth_table_masks(n, bundles, background=()):
    """Intersect sets of truth assignments, then check every selector support."""
    def solutions(rows):
        return sum(1 << x for x in range(1 << n)
                   if all((normal & x).bit_count() % 2 == bit for normal, bit in rows))

    systems = [solutions(background)]
    for bundle in bundles:
        allowed = solutions(bundle)
        systems.extend([prior & allowed for prior in systems])
    forbidden = [mask for mask, allowed in enumerate(systems)
                 if mask.bit_count() <= 2 and not allowed]
    admissible = {mask for mask in range(len(systems))
                  if all(mask & bad != bad for bad in forbidden)}
    maximal = {mask for mask in admissible
               if all(mask & (1 << i) or mask | (1 << i) not in admissible
                      for i in range(len(bundles)))}
    return systems, admissible, maximal


class GuardedAffineTests(unittest.TestCase):
    def check_rank(self, n, guarded, background=()):
        systems, admissible, maximal = truth_table_masks(n, [(row,) for row in guarded],
                                                        background)
        result = single_row_frontier(n, iter(guarded), iter(background))
        self.assertEqual(result.maximal_pairwise, len(maximal))
        self.assertEqual(result.feasible_among_maximal, sum(bool(systems[m]) for m in maximal))
        self.assertEqual(result.exact, all(systems[m] for m in admissible))
        if result.exact:
            self.assertIsNone(result.obstruction)
        else:
            mask = sum(1 << i for i in result.obstruction)
            self.assertIn(mask, admissible)
            self.assertFalse(systems[mask])
            self.assertGreater(mask.bit_count(), 2)
            self.assertTrue(all(systems[mask ^ (1 << i)] for i in result.obstruction))

    def test_all_two_bit_families(self):
        rows = list(product(range(4), (0, 1)))
        for size in range(len(rows) + 1):
            for guarded in combinations(rows, size):
                for background in [(), *((row,) for row in rows)]:
                    self.check_rank(2, guarded, background)

    def test_duplicates_and_affine_quotients(self):
        rng = random.Random(209782414)
        for _ in range(350):
            n = rng.randrange(5)
            rows = list(product(range(1 << n), (0, 1)))
            self.check_rank(n, rng.choices(rows, k=rng.randrange(9)),
                            rng.choices(rows, k=rng.randrange(5)))
        self.check_rank(3, [(4, 0), (5, 0), (4, 1), (6, 1)], [(1, 1)])
        self.check_rank(0, [], [(0, 1)])
        self.check_rank(0, [], [])
        self.check_rank(2, [(1, 0), (2, 0), (3, 1)])

    def check_path(self, n, clauses):
        path = occurrence_path(n, clauses)
        self.assertTrue(all(a.bit_count() == 1 and 1 <= b.bit_count() <= 2
                            for ((a, _), (b, _)) in path.bundles))
        systems, admissible, _ = truth_table_masks(path.hidden_bits, path.bundles)
        sat = any(all(any(bool(bits & (1 << (abs(lit)-1))) == (lit > 0) for lit in c)
                      for c in clauses) for bits in range(1 << n))
        self.assertEqual(any(not systems[m] for m in admissible), sat)
        # An all-disabled support has a witness for both SAT and UNSAT inputs.
        self.assertTrue(systems[0])

    def test_occurrence_path_reduction(self):
        pool = [(), (1,), (-1,), (2,), (-2,), (1, -2), (-1, 2)]
        for size in range(4):
            for formula in product(pool, repeat=size):
                self.check_path(2, formula)
        for formula in [[(1, -1), (1, 1), (-1, -1)], [(), (), ()],
                        [(1, 2), (-1, 2), (1, -2), (-1, -2)],
                        [(1, 2), (1, 2), (1, 2)], [(-1,)], []]:
            self.check_path(2, formula)

    def test_invalid_input(self):
        for rows in [[(4, 0)], [(1, 2)], [(-1, 1)]]:
            with self.assertRaises(ValueError):
                single_row_frontier(2, rows, [(0, 1)])
        for formula in [[(0,)], [(-3,)]]:
            with self.assertRaises(ValueError):
                occurrence_path(2, formula)

    def test_cycle_and_matching(self):
        def models(n, clauses):
            return [bits for bits in product((False, True), repeat=n)
                    if all(any(bits[abs(lit)-1] == (lit > 0) for lit in c) for c in clauses)]

        pool = [(), (1,), (-1,), (2,), (1, -2), (-1, 2), (1, 1), (-1, 1)]
        for length in range(4):
            for clauses in product(pool, repeat=length):
                original = models(2, clauses)
                n, copied = split_occurrences(2, clauses)
                self.assertEqual(bool(models(n, copied)), bool(original))
                output = [lit for c in copied for lit in c]
                self.assertTrue(all(output.count(i) <= 2 and output.count(-i) <= 1
                                    for i in range(1, n+1)))
                literals = [lit for c in clauses for lit in c]
                if any(literals.count(-lit) > 1 for lit in literals):
                    with self.assertRaises(ValueError):
                        matching_path_witness(2, clauses)
                else:
                    witness = matching_path_witness(2, clauses)
                    self.assertEqual(witness is not None, bool(original))
                    if witness is not None:
                        self.assertIn(witness, original)
        self.assertIsNotNone(matching_path_witness(3, [(1, 2), (-1,), (3,)]))
        self.assertIsNone(matching_path_witness(3, [(1,), (-1,), (2, 3)]))

    def test_half_integral_cover_obstruction(self):
        for length in (1, 2, 8, 31):
            first, last = 1, length + 1
            b, c = last + 1, last + 2
            clauses = [(first, b), (first, -b)]
            clauses.extend((-i, i + 1) for i in range(first, last))
            clauses.extend([(-last, c), (-last, -c)])
            self.assertTrue(all(len(clause) == 2 for clause in clauses))
            self.assertIsNone(solve_2cnf(c, clauses))
            for j in range(len(clauses)):
                self.assertIsNotNone(solve_2cnf(c, clauses[:j] + clauses[j+1:]))
