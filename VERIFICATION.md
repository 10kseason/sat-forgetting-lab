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
python -B routes/matching-balance/independent.py
python -B routes/matching-balance/order12.py
python -B routes/matching-balance/verify15.py
lake build
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
| Guarded parity equations | All 256 two-bit row families against nine backgrounds, 350 seeded cases with duplicates, minimal obstruction checks, occurrence-path reductions on small CNFs, and bounded-occurrence and matching checks. The independent oracle intersects explicit sets of hidden truth assignments. |
| Single-clause promotion | Every three-bit relation expressible by a 2-CNF, with each signed full-width clause. The oracle checks all triples of distinct models, and checks each returned obstruction against the original formula. Longer signed inputs, saturation order and a jointly binary counterexample are covered separately. |
| Probing and cuts | Two-pin probes recover the hidden pins and stall on both parities of the triangular prism. Signed clause systems are checked against truth tables. The 15-vertex Steiner instance is run to completion under both default and legacy settings. |
| Twelve-vertex substitution | The Lean kernel evaluates the six block states and verifies both model maps and inverses. Python checks finite SAT and UNSAT sources, four perfect matchings, incidence linearity, signed ports, and inversion on shuffled unlabeled triples. Five-level 9,216- and 12,288-variable inputs go through the default solver. |
| Independent four-round controls | Four sizes of generated controls and an independent complete NAE search. The 12-point enumeration reproduces all three resolved types. Gray-code truth tables verify every full and single-round-deletion coloring count of the 13,933 stored 15-point representatives. The longer catalogue generator is documented in the route. |

The default Lean build checks single-pivot semantics, iteration and cumulative caps, simultaneous static policies, reachability, CNF materialization, the signed binary-recognition reduction, unary exactness, maximal-support decision, the membership-query trace theorem and the semantic occurrence-path reduction. [The emission theorem](Formal/Emission.lean) assumes certificates for reachability, constant goals and coverage of choices on each goal's dependency cone. Python certificate generation is tested separately. Runtime bounds, the coding lower bound for parity and the affine rank arguments are written proofs. Numerical experiments are finite checks.

On each public push the CI performs a fresh default build, checks that each tracked Lean source has a corresponding compiled module, runs unittest discovery and runs the standalone research checks above. It uses a standard Ubuntu runner without artifact or cache uploads. [Workflow](.github/workflows/ci.yml) · [GitHub runner billing](https://docs.github.com/en/billing/concepts/product-billing/github-actions)

For the larger guarded UNSAT example, `solver_experiment.py` deliberately caps the search and reports UNKNOWN. The following reproduces the completed 131,072-pattern run for the smallest size.

```sh
python -B -c "from solver_experiment import guarded_pair; from solve_cnf import solve; print(solve(*guarded_pair(5)))"
```
