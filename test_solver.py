import random
import unittest
from itertools import product

from forgetting import cnf_value
from solve_cnf import hidden_orientation, read_dimacs, solve
from gf2 import equations_in_cnf, reduce_system, one_solution
from pivot_elimination import candidate, minimal, recover
from solver_experiment import guarded_pair, prism


class SolverTests(unittest.TestCase):
    def test_noncanonical_subsumption(self):
        self.assertEqual(minimal([(2, 1), (1, 2), (2, -2)]), {(1, 2)})
        self.assertEqual(minimal([(1, 1, 1), (1, 2)]), {(1,)})

    def test_all_three_variable_truth_tables(self):
        rows = list(product((False, True), repeat=3))
        for table in range(256):
            clauses = {tuple(-i if b else i for i,b in enumerate(row,1))
                       for r,row in enumerate(rows) if not (table >> r) & 1}
            result = solve(3, clauses)
            self.assertEqual(result.status, "SAT" if table else "UNSAT")
            if result.assignment is not None:
                self.assertTrue(cnf_value(clauses,result.assignment))
            for v in (1,2,3):
                residual,tails = candidate(clauses,v)
                for fixed in rows:
                    possible = any(cnf_value(clauses, fixed[:v-1] + (b,) + fixed[v:])
                                   for b in (False,True))
                    self.assertEqual(cnf_value(residual,fixed), possible)
                    if possible:
                        self.assertTrue(cnf_value(clauses,recover([(v,tails)],fixed)))

    def test_dimacs(self):
        n, c = read_dimacs(["c comment", "p cnf 3 2", "1 -2", "3 0 -3 0"])
        self.assertEqual((n, c), (3, [(1, -2, 3), (-3,)]))
        for lines in (["p cnf 1 1","2 0"], ["0"], ["p cnf 1 0","0"],
                      ["p cnf 2 1","1"], ["p cnf -2 0"]):
            with self.assertRaises(ValueError):
                read_dimacs(lines)
        self.assertEqual(solve(0,[()]).status, "UNSAT")
        self.assertEqual(solve(0,[]).assignment, ())

    def test_arbitrary_cnfs_against_truth_tables(self):
        rng = random.Random(624)
        for _ in range(500):
            n = rng.randrange(1,7)
            literals = [i*sign for i in range(1,n+1) for sign in (-1,1)]
            clauses = [tuple(rng.choices(literals,k=rng.randrange(1,6)))
                       for _ in range(rng.randrange(1,23))]
            if rng.randrange(15) == 0:
                clauses.append(())
            expected = any(cnf_value(clauses,x) for x in product((False,True),repeat=n))
            result = solve(n, clauses)
            self.assertEqual(result.status,"SAT" if expected else "UNSAT")
            if result.status == "SAT":
                self.assertTrue(cnf_value(clauses,result.assignment))

    def test_known_backdoors(self):
        # Renaming all four variables makes every clause entirely positive.
        clauses = [(1,-2,3),(-2,3,-4),(1,3,-4)]
        result = solve(4, clauses, use_elimination=False)
        self.assertEqual((result.status, result.retained, result.assignments_tested), ("SAT", (), 1))
        for m in (3,4):
            n, clauses = prism(m)
            hidden, _ = hidden_orientation(n, clauses)
            self.assertEqual(hidden, set(range(1, m+1)))
            result = solve(n, clauses, use_affine=False, use_elimination=False)
            self.assertEqual((result.status, result.assignments_tested), ("UNSAT",4**m))
            self.assertEqual(solve(n, clauses, max_patterns=1, use_affine=False,
                                   use_elimination=False).status,"UNKNOWN")
            self.assertEqual(solve(n, clauses).method,"affine contradiction")
            masked = solve(*prism(m, masked=True), use_elimination=False)
            self.assertEqual(masked.method,"backdoor")
            self.assertGreaterEqual(masked.assignments_tested,2**(2*m-1))
            n, clauses = prism(m, odd=False)
            sat = solve(n, clauses)
            self.assertEqual(sat.status,"SAT")
            self.assertTrue(cnf_value(clauses,sat.assignment))

    def test_non_growing_solver_and_stuck_family(self):
        clauses = [(1, 2, 3), (-1, 2, 3), (-2,), (-3,4)]
        result = solve(4, clauses)
        self.assertEqual(result.status, "SAT")
        self.assertTrue(cnf_value(clauses,result.assignment))
        from forgetting import canonical
        n, clauses = guarded_pair(5)
        clauses = {canonical(c) for c in clauses}
        self.assertEqual(equations_in_cnf(clauses), [])
        for v in range(1,n):
            reduced, _ = candidate(clauses,v)
            self.assertEqual(len(reduced),len(clauses) + 16)
        reduced, _ = candidate(clauses,n)
        self.assertEqual(len(reduced), (8*5)**2)
        row = solve(n,clauses,max_patterns=4)
        self.assertEqual((row.status, row.assignments_tested, row.eliminated), ("UNKNOWN",4,()))

    def test_affine_basis(self):
        rng = random.Random(53)
        for _ in range(250):
            n = rng.randrange(6)
            rows = [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(10))]
            solutions = [x for x in range(1<<n) if all((x&m).bit_count()%2 == r for m,r in rows)]
            basis = reduce_system(n,rows)
            self.assertEqual(basis is not None, bool(solutions))
            if basis is not None:
                assignment = one_solution(n,basis)
                bits = sum(1<<i for i,v in enumerate(assignment) if v)
                self.assertIn(bits, solutions)
                self.assertEqual(len(solutions), 1 << (n-len(basis)))


if __name__ == "__main__":
    unittest.main()
