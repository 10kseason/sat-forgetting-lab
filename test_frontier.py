"""Cross-check maximal-model SAT against complete retained and hidden enumeration."""

import random
import unittest
from itertools import combinations, product

from examples import matching_instance
from forgetting import HiddenCNF, cnf_value
from frontier_sat import conflict_graph, matching_cover, solve_frontier


class FrontierTests(unittest.TestCase):
    def test_single_pass_background(self):
        clauses = (iter(clause) for clause in [(-1, -2)])
        self.assertEqual(conflict_graph(2, clauses, (1, 2)), {1: {2}, 2: {1}})

    def test_every_two_variable_background_and_orientation(self):
        rows = list(product((False, True), repeat=2))
        pool = [(1,), (-1,), (2,), (-2,), (1, 2), (-1, 2), (1, -2), (-1, -2)]
        for selection in product((False, True), repeat=len(pool)):
            background = [c for c, use in zip(pool,selection) if use]
            models = [x for x in rows if cnf_value(background,x)]
            for a,b in product((1,-1),(2,-2)):
                oriented = (a,b)
                graph = conflict_graph(2, background, oriented)
                if not models:
                    self.assertIsNone(graph)
                    continue
                supports = [{v for v,xv in zip(oriented, x) if (v > 0) == xv} for x in models]
                for mask in product((False,True), repeat=2):
                    subset = {v for v,used in zip(oriented, mask) if used}
                    independent = subset <= graph.keys() and all(
                        w not in graph[v] for v,w in combinations(subset,2))
                    self.assertEqual(independent, any(subset <= m for m in supports))
                cover = set(matching_cover(graph))
                self.assertTrue(all(v in cover or w in cover for v in graph for w in graph[v]))
                s = HiddenCNF(2,0,[(a,b)],background)
                self.assertEqual(solve_frontier(s).satisfiable, any(cnf_value([(a,b)],x) for x in models))

    def test_retained_witnesses_against_raw_cnf(self):
        rng = random.Random(41325)
        for _ in range(300):
            n,h = 4,3
            oriented = [(i if rng.choice((False,True)) else -i) for i in range(1,n+1)]
            heads = list(range(n+1,n+h+1))
            rules = [(-v, *rng.choices(oriented + heads, k=rng.randrange(4))) for v in heads
                     for _ in range(rng.randrange(3))]
            goals = [tuple(rng.choices(oriented+heads,k=rng.randrange(4))) for _ in range(rng.randrange(4))]
            background = [tuple(v if rng.randrange(2) else -v for v in rng.choices(oriented,k=2))
                          for _ in range(rng.randrange(9))]
            all_clauses = rules+goals+background
            expected = any(cnf_value(all_clauses,x) for x in product((False,True),repeat=n+h))
            result = solve_frontier(HiddenCNF(n,h,rules+goals,background))
            self.assertEqual(result.satisfiable, expected)
            if result.assignment is not None:
                self.assertTrue(cnf_value(all_clauses,result.assignment))

    def test_tight_query_counts_and_star(self):
        for k in range(1,8):
            bg = [(-(2*i+1), -(2*i+2)) for i in range(k)]
            s = matching_instance(k, background=bg)
            answer = solve_frontier(s)
            self.assertFalse(answer.satisfiable)
            self.assertEqual((len(answer.cover),answer.maxima_evaluated), (k,2**k))
            with self.assertRaises(ValueError):
                solve_frontier(s, cover=())
            with self.assertRaises(ValueError):
                solve_frontier(s, max_patterns=2**k-1)
        k=24
        s = matching_instance(k, switch=True, background=[(-2*k-1,-(2*i+1)) for i in range(k)])
        answer = solve_frontier(s, max_patterns=2)
        self.assertFalse(answer.satisfiable)
        self.assertEqual((len(answer.cover),answer.maxima_evaluated), (1,2))
        self.assertTrue(solve_frontier(HiddenCNF(0,0,[])).satisfiable)
        self.assertFalse(solve_frontier(HiddenCNF(0,0,[], [()])).satisfiable)


if __name__ == "__main__":
    unittest.main()
