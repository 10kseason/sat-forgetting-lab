# Reproducing the checks

Use Python 3.10 or later and the Lean version in `lean-toolchain`. Run from the repository root with Python assertions enabled, as in the commands below. The package manifest contains no external Lean packages.

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
python -B routes/matching-balance/verify15.py --lean-unsat
python -B routes/matching-balance/dual.py
python -B routes/matching-balance/damage.py
python -B routes/matching-balance/ternary_check.py
python -B routes/matching-balance/diagrams.py
lake build
python -B audit_lean.py
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
| Independent four-round controls | Four sizes of generated controls and an independent complete NAE search. The 12-point enumeration reproduces all three resolved types. Gray-code truth tables verify every full and single-round-deletion coloring count of the 13,933 stored 15-point representatives. Lean also proves a contradiction from the 40 Boolean clauses of each of the 109 negative representatives. The longer catalogue generator is documented in the route. |
| Recoloring and algebraic witnesses | The general proper-flip path into the 7/15–8/15 band and finite 7:8 sharp block are checked by Lean. Its three-port links and the twelve-vertex damaged block have separate kernel checks. The GF(3) omitted-incidence calculation matches all stored model counts modulo three. |

The default Lean build checks single-pivot semantics, iteration and cumulative caps, simultaneous static policies, reachability, CNF materialization, the signed binary-recognition reduction, unary exactness, maximal-support decision, the membership-query trace theorem and the semantic occurrence-path reduction. [The emission theorem](Formal/Emission.lean) assumes certificates for reachability, constant goals and coverage of choices on each goal's dependency cone. Python certificate generation is tested separately. Runtime bounds, the coding lower bound for parity and the affine rank arguments are written proofs. Numerical experiments are finite checks.

On each public push the CI performs a fresh default build, checks that each tracked Lean source has a corresponding compiled module, runs unittest discovery and runs the standalone research checks above. It uses a standard Ubuntu runner without artifact or cache uploads. [Workflow](.github/workflows/ci.yml) · [GitHub runner billing](https://docs.github.com/en/billing/concepts/product-billing/github-actions)

The axiom audit uses Lean's transitive dependency report for imported project theorems. It accepts the standard axioms of propositional extensionality, classical choice and quotient soundness. A dependency on an unchecked proof or on a native computation axiom fails the check. [Audit script](audit_lean.py)

## Audit of the 09:00 KST research freeze on 25 November 2026

- A clean clone of the public snapshot passed 62 Python tests and the default Lake build (51 jobs covering all 24 project modules). The axiom audit inspected 411 project theorem declarations. As negative controls, the coverage gate rejected a tracked source outside the default build and the axiom gate rejected a theorem that used an added test axiom. [Frozen source](https://github.com/10kseason/sat-forgetting-lab/tree/237adffac3f31c2f7bf2ff7bf5d7d0263a8064cd) · [CI for that snapshot](https://github.com/10kseason/sat-forgetting-lab/actions/runs/45513143495)
- A temporary module importing all 24 project modules passed `leanchecker --fresh` and `lean4lean --fresh`. Lean4Lean counted 114,009 declarations across the project **and its imports**. The packaged Windows Lean4Lean executable rejected this toolchain's object-file header, so the successful run used Lean4Lean built from its matching source revision with Lean 4.36.0. [Lean4Lean revision](https://github.com/digama0/lean4lean/tree/23fd0341e823a332ce5df21a1897c8afcbf34471)
- Regenerating the 15-vertex catalogue produced a byte-identical gzip file. Its SHA-256 is `b9de6149ebfa3c7a0976300d8472e21ef403390eec54f041bc9f6c1b1396b05e`. The uncompressed TSV's SHA-256 is `612c97281f4766666ed263b89e2d9b888d6ef645743594c4074d19670364f456`. The Gray-code checker rejected a copy with one stored model count changed from 38 to 40. [Catalogue, generator and independent count check](routes/matching-balance/README.md#complete-finite-catalogues)
- A separate solver regression used all 65,536 Boolean functions on four variables. For each function, two CNFs encoded its truth table, one by forbidden assignments and one by prime implicates. All 131,072 decisions agreed with the truth tables, including the two encodings of the identically false function. Every SAT answer supplied a checked witness. A further 65,535 tests pinned an assignment known to be false and all returned UNSAT.
- A red-team run crossed 770 generated instances with 16 feature settings and two budget settings. It checked the witnesses on 18,902 SAT answers and compared 4,747 UNSAT answers with a truth-table oracle. The other 991 runs returned UNKNOWN under a search cap.

During integration, the optional catalogue solver sweep gained a check that every SAT result supplies a full witness. Its maximum assignment counts were 474 for SAT by branching and 1,024 for UNSAT by branching. A deliberately missing SAT witness failed the new check. The separate Lean audit proved the 109 negative rows using only propositional extensionality as a reported axiom, and rejected an attempted contradiction for a satisfiable triple. [Catalogue checks](routes/matching-balance/verify15.py)

All 13,933 rows have distinct coloring profiles under vertex and round renaming. The verifier rejected a copy of a row with its vertices and rounds permuted. A separate check recomputed the full and round-deletion counts, then compared the thirteen candidate pairs left by those counts with NetworkX 3.5's VF2++ algorithm. Its incidence graphs contained fifteen point vertices, twenty triple vertices and four round vertices, with the verified deletion count attached to each round. All thirteen pairs were nonisomorphic. A relabeled copy of row 1078 admitted an isomorphism. The repository verifier uses Python's standard library. [Coloring profiles and catalogue definition](routes/matching-balance/README.md#complete-finite-catalogues)

As an external solver check, CaDiCaL 2.1.2 read the 40-clause DIMACS encoding of every representative. All 13,824 returned colorings satisfied the original triples. On the 109 negative inputs, `--plain --lrat --no-binary` produced textual certificates. A separate unit-propagation replay checked 3,484 clause additions across those certificates and derived the empty clause in every case. CI reproduces the negative results directly from the triples with Lean. [Catalogue verifier](routes/matching-balance/verify15.py)

For the larger guarded UNSAT example, `solver_experiment.py` deliberately caps the search and reports UNKNOWN. The following reproduces the completed 131,072-pattern run for the smallest size.

```sh
python -B -c "from solver_experiment import guarded_pair; from solve_cnf import solve; print(solve(*guarded_pair(5)))"
```
