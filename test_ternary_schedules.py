import random
import unittest
from itertools import combinations, product

from forgetting import cnf_value
from ternary_schedules import block_cover, solve_ternary


class TernaryScheduleTests(unittest.TestCase):
    def test_cover_every_pattern(self):
        for width in range(7):
            cover = block_cover(width)
            rows = list(product(range(3), repeat=width))
            for target in rows:
                self.assertTrue(any(all(a != b for a,b in zip(row,target)) for row in cover))
        for width, expected in enumerate((1,2,3,5)):
            self.assertEqual(len(block_cover(width)), expected)

    def test_all_three_variable_truth_tables(self):
        bits = list(product((False,True), repeat=3))
        pool = [tuple(-i if x else i for i,x in enumerate(row,1)) for row in bits]
        for k in range(len(pool)+1):
            for clauses in combinations(pool, k):
                result = solve_ternary(3, clauses)
                self.assertEqual(result.status, "UNSAT" if k == 8 else "SAT")
                if result.assignment is not None:
                    self.assertTrue(cnf_value(clauses, result.assignment))
                if result.status == "UNSAT":
                    self.assertEqual(result.calls, result.schedule_count)

    def test_mixed_clauses_and_budget(self):
        rng = random.Random(3495360995)
        rows = list(product((False,True), repeat=5))
        for _ in range(150):
            clauses = [tuple(lit * rng.choice((-1,1)) for lit in
                             rng.sample(range(1,6), rng.randrange(1,4)))
                       for _ in range(rng.randrange(14))]
            result = solve_ternary(5, clauses)
            sat = any(cnf_value(clauses, row) for row in rows)
            self.assertEqual(result.status, "SAT" if sat else "UNSAT")
            if sat:
                self.assertTrue(cnf_value(clauses, result.assignment))
        self.assertEqual(solve_ternary(0, []).assignment, ())
        self.assertEqual(solve_ternary(0, [()]).status, "UNSAT")
        pool = list(product((1,-1),(2,-2),(3,-3)))
        result = solve_ternary(3, pool, max_calls=3)
        self.assertEqual((result.status, result.calls, result.schedule_count), ("UNKNOWN",3,75))
        with self.assertRaises(ValueError):
            solve_ternary(4, [(1,2,3,4)])
