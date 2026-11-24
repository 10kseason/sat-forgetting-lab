# Review record

## Random branches at retrospectives

For each of the draws below, the index is the recorded integer modulo the listed menu length, counting from zero. These draws chose a question to investigate. The proofs and counterexamples determine the result.

| Draw | Candidate variations in draw order | Outcome |
|---|---|---|
| 209782414 | Opposite-sign duplicate, dependent fixed rows, free high column above pivots, repeated clause, all selectors disabled, inconsistent background | Switching everything off always gives a witness in the SAT encoding. The decision question must quantify over supports. The truth-table test checks the empty support explicitly. |
| 3374215100 | One exceptional bundle, short variable lifetime, few negative occurrences, triples, change coordinates, split occurrences | Tovey's variable-copy cycle gives hardness with at most one negative occurrence per copied variable. On occurrence paths, degree-one pair conflicts permit an actual matching algorithm. With degree two, the hard instances already have disjoint three-vertex paths and isolates. |
| 1587482894 | Count exceptional bundles, check triples, try fractional matching, find disjoint obstructions, combine signs, forget stage labels | The natural stage-cover relaxation admits half of every occurrence on a minimally unsatisfiable chain of arbitrary length. Its conflict graph has only two three-vertex components. The proof and finite checks are in the guarded-affine note. |
| 549904478 | Count branching components, allow one large bundle, drop a literal per clause, bounded-width consistency, change the row basis, cut stage connections | Against a binary background a single clause either has an equivalent short subclause or admits three explicit models ruling out every existential binary encoding. The two-wide-clause example shows precisely where separate tests lose completeness. [Derivation](BINARY-PROMOTION.md) |
| 3495360995 | Third field value, matching gadget, fewer existential tests, defer deletion, couple clauses sharing a variable, correlate omission schedules | Correlated block covers give a complete 3-CNF solver using 2-SAT queries. The number of residual ternary clauses controls the exponential term. The ternary cube covering problem is prior work. [Algorithm and counterexamples](BINARY-PROMOTION.md) |
| 3170088966 | Learn from a failed 2-SAT core, use mod-three choices, promote two clauses together, characterize witness families, matching gadget, rare sign first | Failed short residuals recover the preceding construction's pins. Linear NAE triple systems defeat two-pin probing. Counting cut edges then decides the dense Steiner example at the default solver entry point. [Proof and limits](PROBING-AND-CUTS.md) |
| 1097197151 | Switch sign conventions, round a fractional cut, subtract overlapping constraints, bound certificate reads, count induced subsets, condition on one perfect matching | A twelve-vertex example has six balanced models. Opening three of its triples gives a parsimonious hard family in which every model is 6–6 on each designated block. [Construction and proof](MATCHING-BALANCE.md) |
| 940061948 | Swap a port sign, hide the partition, hide the four matching names, delete an internal triple, repeat substitution, erase vertex order | Unlabeled triangle neighborhoods identify the blocks. Complete local truth tables recover three signals and parity switching restores positive NAE constraints. Five anonymous substitutions can be undone without knowing the matching names. [Inversion](anonymous_blocks.py) |

[Definitions and proofs](GUARDED-AFFINE.md) · [Reproducible checks](test_guarded_affine.py)

## Counterexamples that changed the implementation or its stated scope

| Issue | Resolution |
|---|---|
| A single-pass 2-CNF background iterator was exhausted by the first solve. Later conflict queries lost edges. | Materialize the background and its clauses once at the graph entry point. A nested-iterator regression checks the sole edge on two vertices. [Code](frontier_sat.py) · [Test](test_frontier.py) |
| Reordered or repeated literals could survive the subsumption helper as different clauses. | Normalize each input before deduplication. A regression exercises reordered, repeated and tautological input. [Code](pivot_elimination.py) · [Test](test_solver.py) |
| The round checker can reject mixed signs even when the represented function is monotone. | Document its syntactic check across the raw rules and goals, including unreachable rules. [Condition](CERTIFICATION.md) |
| The affine rank test assumes an affine mandatory background on hidden coordinates. | With the non-affine background $x_1\lor x_2$, the independent equations $x_1+x_2+x_3=0$, $x_2+x_3=0$, $x_3=0$ pass in pairs but fail jointly. A separate selector restriction can also exclude an otherwise-valid counterexample support. [Theorem scope](GUARDED-AFFINE.md) |
| Tracking a Lean file outside the default Lake module paths allowed a normal build to skip it. | The query trace now lives under Formal. A fresh CI build checks for a compiled module for every tracked Lean source. [Workflow](.github/workflows/ci.yml) |
