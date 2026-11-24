"""Truth-table checks for the affine maximal-support solver."""

import random
import unittest
from itertools import product
from math import comb

from affine_frontier import solve_affine_frontier
from forgetting import HiddenCNF
from frontier_sat import solve_frontier


def satisfies(clauses, rows, values):
    for clause in clauses:
        if not any(values[abs(literal) - 1] == (literal > 0) for literal in clause):
            return False
    value_mask = sum(1 << i for i, value in enumerate(values) if value)
    return all((value_mask & mask).bit_count() % 2 == rhs for mask, rhs in rows)


class AffineFrontierTests(unittest.TestCase):
    def verify(self, n, h, clauses, background, rows, oriented=None):
        solver = HiddenCNF(n, h, clauses, background)
        answer = solve_affine_frontier(solver, rows, oriented=oriented)
        all_clauses = (*clauses, *background)
        expected = any(
            satisfies(all_clauses, rows, values)
            for values in product((False, True), repeat=n + h)
        )
        self.assertEqual(answer.satisfiable, expected, (clauses, background, rows, oriented))
        if answer.satisfiable:
            self.assertTrue(satisfies(all_clauses, rows, answer.assignment))

        row_span = {0}
        for mask, _ in rows:
            row_span |= {previous ^ mask for previous in row_span}
        self.assertEqual(answer.rank, len(row_span).bit_length() - 1)
        bound = (1 << len(answer.cover)) * sum(comb(n, j) for j in range(answer.rank + 1))
        self.assertLessEqual(answer.seed_sets, bound)
        self.assertLessEqual(answer.membership_queries, answer.seed_sets)
        return answer

    def test_exhaustive_two_variable_backgrounds(self):
        pool = [(1,), (-1,), (2,), (-2,), (1, 2), (-1, 2), (1, -2), (-1, -2)]
        affine = [(), ((1, 0), (2, 1)), ((1, 0), (1, 1)), ((1, 1), (2, 0), (3, 1))]
        affine += [((mask, rhs),) for mask in range(4) for rhs in (0, 1)]
        for selected in product((False, True), repeat=len(pool)):
            background = [c for c, use in zip(pool, selected) if use]
            for oriented in product((1, -1), (2, -2)):
                for rows in affine:
                    self.verify(2, 0, [oriented], background, rows)

    def test_mixed_hidden_systems(self):
        rng = random.Random(504216)
        for case in range(600):
            n, h = rng.randrange(1, 6), rng.randrange(4)
            oriented = [i * rng.choice((1, -1)) for i in range(1, n + 1)]
            heads = list(range(n + 1, n + h + 1))
            available = oriented + heads
            clauses = [
                (-head, *rng.choices(available, k=rng.randrange(4)))
                for head in heads for _ in range(rng.randrange(3))
            ]
            clauses += [
                tuple(rng.choices(available, k=rng.randrange(4)))
                for _ in range(rng.randrange(4))
            ]
            background = [
                tuple(v * rng.choice((1, -1)) for v in rng.choices(oriented, k=rng.randrange(1, 3)))
                for _ in range(rng.randrange(8))
            ]
            rows = [(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(5))]
            self.verify(n, h, clauses, background, rows, oriented if case % 2 else None)

    def test_rank_zero_reuses_frontier(self):
        for background in ((), ((-1, 2), (-2, 3)), ((-1, -2), (-2, -3)), ((),)):
            for clauses in ((), ((1,),), ((-3,), (-1,)), ((),)):
                system = HiddenCNF(3, 0, clauses, background)
                plain = solve_frontier(system)
                affine = solve_affine_frontier(system, ((0, 0), (0, 0)))
                self.assertEqual(affine.rank, 0)
                self.assertEqual(affine.assignment, plain.assignment)
                self.assertEqual(affine.cover, plain.cover)
                self.assertEqual(affine.cover_patterns, plain.patterns_checked)
                self.assertEqual(affine.membership_queries, plain.maxima_evaluated)
        inconsistent = solve_affine_frontier(HiddenCNF(0, 0, ()), ((0, 1),))
        self.assertFalse(inconsistent.satisfiable)
        self.assertEqual(inconsistent.rank, 0)

    def test_chain_and_component_allow_many_drops_at_rank_one(self):
        for n in (9, 17):
            chain = [(-i, i + 1) for i in range(1, n)] + [(n - 1,)]
            parity = sum(1 << i for i in range(n - 3, n))
            system = HiddenCNF(n, 0, [(n,)], chain)
            answer = solve_affine_frontier(system, [(parity, 0)])
            self.assertEqual(answer.rank, 1)
            self.assertEqual(answer.assignment, (False,) * (n - 2) + (True, True))

        cycle = [(-i, i + 1) for i in range(1, 5)] + [(-5, 1)]
        answer = solve_affine_frontier(HiddenCNF(5, 0, (), cycle), [(31, 0)])
        self.assertEqual((answer.rank, answer.seed_sets), (1, 2))
        self.assertEqual(answer.assignment, (False,) * 5)

        oriented = (-1, 2, -3, 4, 5)
        signed_chain = [(-left, right) for left, right in zip(oriented, oriented[1:])]
        signed_chain.append((oriented[-2],))
        answer = self.verify(5, 0, [(5,)], signed_chain, [(0b11100, 1)], oriented)
        self.assertEqual(answer.assignment, (True, False, True, True, True))

    def test_local_block_span_rejects_target(self):
        # Tied columns cancel in the only SCC although the global rank is one.
        answer = self.verify(2, 0, (), [(-1, 2), (-2, 1)], [(3, 1)])
        self.assertEqual((answer.rank, answer.maxima_examined, answer.seed_sets), (1, 1, 0))

    def test_supplied_semantic_orientation(self):
        # This syntactically mixed formula is semantically just x1.
        clauses = [(1, 2), (1, -2)]
        system = HiddenCNF(2, 0, clauses)
        with self.assertRaises(ValueError):
            solve_affine_frontier(system, ((2, 1),))
        answer = self.verify(2, 0, clauses, (), ((2, 1),), (1, -2))
        self.assertEqual(answer.assignment, (True, True))

    def test_partitioned_parity_punctures(self):
        for k, r, m in ((2, 0, 2), (0, 2, 3), (2, 2, 3)):
            n = 2 * k + r * m
            pairs = [(2 * i, 2 * i + 1) for i in range(k)]
            blocks = [tuple(range(2 * k + i * m, 2 * k + (i + 1) * m)) for i in range(r)]
            targets = [(sum(1 << i for i in block), (m - 1) % 2) for block in blocks]
            models = set()
            base = set()
            for values in product((False, True), repeat=n):
                value = sum(1 << i for i, bit in enumerate(values) if bit)
                if any(values[u] and values[v] for u, v in pairs) or any(
                    all(values[i] for i in block) for block in blocks
                ):
                    base.add(value)
                if not any(values[u] and values[v] for u, v in pairs) and satisfies(
                    (), targets, values
                ):
                    models.add(value)
            self.assertFalse(models & base)
            maximal_rows = {a for a in models if all(a == b or a & b != a for b in models)}
            self.assertEqual(len(maximal_rows), 2 ** k * m ** r)
            for row in maximal_rows:
                larger = {a for a in range(1 << n) if a & row == row}
                self.assertEqual(larger - base, {row})


if __name__ == "__main__":
    unittest.main()
