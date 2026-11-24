import random
import unittest
from itertools import combinations, islice, product

from binary_probing import learned_binary_clauses
from binary_promotion import promote
from forgetting import cnf_value
from solver_experiment import prism
from two_sat import solve_2cnf


def pinned_triples(pattern):
    """Fixed unsigned incidence. Each target has just its designated true literal."""
    t = 3
    while t*(t-1)*(t-2)//6 < len(pattern):
        t += 1
    clauses = []
    for i in range(1, t+1):
        a, b = t + 2*i - 1, t + 2*i
        clauses.extend((i, a*s, b*r) for s,r in product((-1,1), repeat=2))
    triples = islice(combinations(range(1,t+1), 3), len(pattern))
    for target, position in zip(triples, pattern):
        clauses.append(tuple(v if index == position else -v for index,v in enumerate(target)))
    return 3*t, t, clauses


class BinaryProbingTests(unittest.TestCase):
    def test_read_pins_that_survive_individual_promotion(self):
        for pattern in product(range(3), repeat=3):
            n, t, clauses = pinned_triples(pattern)
            self.assertEqual(len(promote(n, clauses).remaining), len(clauses))
            learned = learned_binary_clauses(n, clauses)
            self.assertTrue(all((i,) in learned for i in range(1,t+1)))
            result = promote(n, [*clauses, *learned])
            self.assertFalse(result.remaining)
            self.assertTrue(cnf_value(clauses, solve_2cnf(n, result.binary)))

    def test_same_local_answer_for_both_parities(self):
        for odd in (False,True):
            n, clauses = prism(3, odd=odd)
            self.assertEqual(learned_binary_clauses(n, clauses), ())
            self.assertEqual(len(promote(n, clauses).remaining), len(clauses))
            self.assertEqual(any(cnf_value(clauses, row)
                                 for row in product((False,True), repeat=n)), not odd)

    def test_no_false_consequences(self):
        rng = random.Random(3170088966)
        n = 4
        rows = list(product((False,True), repeat=n))
        for _ in range(200):
            formula = [tuple(v*rng.choice((-1,1)) for v in rng.sample(range(1,n+1),
                                                                      rng.randint(1,n)))
                       for _ in range(rng.randrange(14))]
            learned = learned_binary_clauses(n, formula)
            self.assertTrue(all(cnf_value(learned, row) for row in rows if cnf_value(formula,row)))
        self.assertEqual(learned_binary_clauses(1, [(1,), (-1,)]), ((),))
