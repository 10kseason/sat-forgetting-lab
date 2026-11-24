# Reproducing the checks

Use Python 3.10 or later and the Lean version in `lean-toolchain`. Run from the repository root. The package manifest contains no external Lean packages.

```sh
python -B -m unittest discover -v
python -B examples.py
python -B solver_experiment.py
python -B routes/construction/guarded_dp.py
python -B routes/obstructions/check.py
python -B routes/obstructions/check_affine_frontier.py
python -B routes/query-limit/check.py
lake build
lean routes/query-limit/QueryTrace.lean
```

| Check | Coverage |
|---|---|
| Projection and 2-SAT | Every selection from an eight-clause pool, cyclic signed cases, and every two-variable background from a signed eight-clause catalogue. Retained truth tables and returned witnesses are compared with brute force. |
| Binary versus unary | Exact unary models, signed orientations, binary relaxations, the 3-SAT reduction, and a transient wide prime that disappears before the final fixed point. |
| General solver | 500 seeded arbitrary CNFs, every three-variable truth table and all three pivots, GF(2) basis checks, DIMACS parsing, and search limits. A SAT model is checked against the input. |
| Guard-chain construction | 1,024 formulas and 6,144 projected-prefix comparisons. A separate two-chain instance at size 32 has 1,024 final clauses. |
| Projection obstructions | 1,748 parity elimination orders, 254 prefix checkpoint sets and 746 implication-background orders. The general arbitrary-helper bound is a counting proof in the route note. |
| Query bounds | 120 function/envelope checks, 56 explicit hidden-CNF projections, and exact finite minimax checks for eight exceptional inputs. |
| Affine decision frontier | 12,288 complete two-variable combinations, 600 seeded mixed instances and an independent checker covering 42,851 affine searches. |

The Lean build checks single-pivot semantics, iteration and cumulative caps, simultaneous static policies, reachability, CNF materialization, the signed binary-recognition reduction, unary exactness and maximal-support decision. [The emission theorem](Formal/Emission.lean) takes certificates for reachability, constant goals and coverage of choices on each goal's dependency cone. It does not certify the Python program that constructs those data. The query trace theorem has a separate Lean entry point above. Runtime bounds, the coding lower bound for parity, and the rank argument for affine frontier search are written proofs. Numerical experiments are finite checks.

For the larger guarded UNSAT example, `solver_experiment.py` deliberately caps the search and reports UNKNOWN. The following reproduces the completed 131,072-pattern run for the smallest size.

```sh
python -B -c "from solver_experiment import guarded_pair; from solve_cnf import solve; print(solve(*guarded_pair(5)))"
```
