"""Independent finite checks. The reference evaluates the original, unprojected clauses."""

import random
import unittest
from itertools import combinations, product

from binary_envelope import binary_envelope, decide_with_envelope, projected_value, recognition_instance
from examples import dense_guarded, matching_instance
from forgetting import HiddenCNF, cnf_value
from two_sat import solve_2cnf


def assignments(n):
    return product((False, True), repeat=n)


class ResearchTests(unittest.TestCase):
    def test_two_sat_all_two_variable_formulas(self):
        pool = [(1,), (-1,), (2,), (-2,), (1, 2), (-1, 2), (1, -2), (-1, -2)]
        for selection in assignments(len(pool)):
            clauses = [c for c, use in zip(pool, selection) if use]
            result = solve_2cnf(2, clauses)
            self.assertEqual(result is not None, any(cnf_value(clauses, x) for x in assignments(2)))
            if result is not None:
                self.assertTrue(cnf_value(clauses, result))
        self.assertIsNone(solve_2cnf(0, [()]))
        self.assertEqual(solve_2cnf(0, []), ())

    def compare_projection(self, retained, hidden, clauses, background):
        system = HiddenCNF(retained, hidden, clauses, background)
        projection = system.project()
        self.assertEqual(projection.policy_bound, projection.policies_examined)
        for x in assignments(retained):
            possible = [y for y in assignments(hidden) if cnf_value(clauses + background, x + y)]
            result = system.extend(x)
            self.assertEqual(result is not None, bool(possible))
            self.assertEqual(cnf_value(projection.clauses, x), bool(possible))
            if possible:
                self.assertEqual(result, x + tuple(any(y[i] for y in possible) for i in range(hidden)))

    def test_complete_small_pool(self):
        pool = [(-2,), (-2, 1), (-2, 3), (-3, 2), (-3, -1), (2, 3), (2,), (1, 3)]
        for selection in assignments(len(pool)):
            self.compare_projection(1, 2, [c for c, use in zip(pool, selection) if use], [])

    def test_seeded_cyclic_signed_backgrounds(self):
        rng = random.Random(20261125)
        for _ in range(250):
            n, h = rng.randrange(1, 4), rng.randrange(1, 5)
            terminals = [sign*i for i in range(1, n+1) for sign in (1, -1)]
            heads = list(range(n+1, n+h+1))
            clauses = []
            for v in heads:
                for _ in range(rng.randrange(4)):
                    tail = rng.choices(terminals + heads, k=rng.randrange(4))
                    clauses.append((-v, *tail))
            clauses += [tuple(rng.choices(terminals + heads, k=rng.randrange(4)))
                        for _ in range(rng.randrange(1, 5))]
            background = [tuple(rng.choices(terminals, k=rng.randrange(1, 3)))
                          for _ in range(rng.randrange(4))]
            self.compare_projection(n, h, clauses, background)

    def test_policy_range_and_tight_bound(self):
        self.assertEqual(HiddenCNF(0, 1, [(1,)]).project().clauses, ())
        self.assertEqual(HiddenCNF(0, 1, [(1,),(-1,)]).project().clauses, ((),))
        self.assertEqual(HiddenCNF(1, 0, [], [()]).project().clauses, ((),))
        for k in range(1, 7):
            p = matching_instance(k).project()
            self.assertEqual(p.clauses, tuple(product(*[(2*i+1, 2*i+2) for i in range(k)])))
            with self.assertRaises(ValueError):
                matching_instance(k).project(max_policies=2**k - 1)
        for n in (3, 5):
            p = dense_guarded(n).project()
            self.assertEqual(p.rules_after, n)
            for x in assignments(2*n):
                expected = all(not x[j] or x[j+1] for j in range(n,2*n-1)) and (
                    x[n] or sum(not v for v in x[:n]) <= 1)
                self.assertEqual(cnf_value(p.clauses,x), expected)

    def test_envelope_signed_orientation_and_decisions(self):
        for mask in range(8):
            clause = tuple(-v if mask >> (v-1) & 1 else v for v in (1,2,3))
            off = [(-v,) for v in clause]
            s = HiddenCNF(3, 0, [clause], off)
            self.assertEqual(binary_envelope(s), ())
            result = decide_with_envelope(s)
            self.assertEqual((result.status, result.wide_prime), ("UNRESOLVED", clause))
        self.assertEqual(decide_with_envelope(HiddenCNF(0,0,[()])).status, "UNSAT")
        self.assertEqual(decide_with_envelope(HiddenCNF(0,0,[])).status, "SAT")
        with self.assertRaises(ValueError):
            binary_envelope(HiddenCNF(2,0,[(1,2),(-1,)]))

    def test_binary_exactness_reduction(self):
        pool = [(), (1,), (-1,), (2,), (-2,), (1,-2), (1,-1), (1,2,-2)]
        for count in range(4):
            for src in combinations(pool, count):
                sat = any(cnf_value(src, a) for a in assignments(2))
                s = recognition_instance(2, src)
                env = binary_envelope(s)
                self.assertEqual(env, ((1,2),(3,4)))
                for x in assignments(s.retained):
                    hit = lambda l: x[2*(abs(l)-1) + (l < 0)]
                    closed = cnf_value(env, x) and (
                        any(x[4:]) or any(all(hit(l) for l in c) for c in src))
                    self.assertEqual(closed, projected_value(s, x))
                mismatch = any(cnf_value(env,x) and not projected_value(s,x)
                               for x in assignments(s.retained))
                self.assertEqual(mismatch,sat)


if __name__ == "__main__":
    unittest.main()
