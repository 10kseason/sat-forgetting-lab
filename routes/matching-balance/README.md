# Independent four-matching experiments

A round partitions the vertices into triples. A pair of vertices occurs together at most once in all four rounds. A proper coloring assigns both colors to every triple.

## Controls outside the twelve-vertex substitution

With seed 1162398546, the generator builds each round by randomized backtracking against pairs already used. The distribution over isomorphism types need not be uniform. Independent NAE backtracking supplies a witness or exhausts both choices at each branch. A negative control joins a sample to the nine-point affine plane by swapping one vertex between two triples in the same round. Eleven triples remain inside the nine original vertices. They require 22 crossing pairs against a capacity of 20.

| Sample vertices | Samples | SAT | Compressed by anonymous inverse | Refuted by whole-component cut | Joined negative controls refuted by induced-subset cut |
|---|---:|---:|---:|---:|---:|
| 12 | 24 | 17 | 0 | 0 | 24/24 |
| 24 | 24 | 24 | 0 | 0 | 24/24 |
| 36 | 24 | 24 | 0 | 0 | 24/24 |
| 48 | 24 | 24 | 0 | 0 | 24/24 |

The whole-component cut missed all 96 joined controls. The induced-subset cut catches them. Neither cut refutes the seven negative samples at size twelve. The complement-forest method decides them at slack four. Those seven samples all belong to one isomorphism type. [Generator](independent.py) · [Cut proofs](../../PROBING-AND-CUTS.md)

## Complete finite catalogues

Isomorphisms may rename vertices and permute the four rounds. The partition into rounds is part of the object. The intersections of two rounds form a simple cubic bipartite graph. At twelve points this is the 4-by-4 array with its diagonal missing. At fifteen points the missing cells form a bipartite 2-regular graph on ten vertices, either a ten-cycle or a four-cycle and a six-cycle. For each skeleton the generator enumerates possible third matchings and all compatible unordered pairs of remaining matchings.

To identify types, try each ordered choice of the first two rounds, name the rows, try every compatible naming of the columns, and sort the remaining rounds. In the four-plus-six cycle skeleton two columns have identical missing row pairs; both namings count. An orbit can visit both skeletons. The disjoint orbit sizes sum to the full normalized presentation count in each skeleton. The totals reproduce Sellmann's Social Golfer catalogue. [Sellmann, Tables 4.1 and 8.9](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/2798) · [Related literature](../../RELATED-WORK.md)

| Points | Candidate matchings per skeleton | Compatible normalized presentations | Resolved types | SAT | UNSAT |
|---|---|---|---:|---:|---:|
| 12 | 56 | 41 | 3 | 2 | 1 |
| 15 | 8,230 and 8,220 | 1,160,033 and 1,133,232 | 13,933 | 13,824 | 109 |

The twelve-point types have 0, 6 and 90 proper colorings, counting both members of a complementary pair. The negative type admits 114, 114, 114 or 120 colorings when one round is dropped. Each deletion admits a coloring that misses just one triple in the restored round. At fifteen points this one-miss property holds for all 436 negative type/round pairs. Known three-round bicolorability gives existence after deletion. Here we count the colorings and check the cost of restoring the round. [Twelve-point enumeration](order12.py) · [Fifteen-point enumeration](order15.py) · [Independent Gray-code check](verify15.py)

The compressed TSV contains one representative per fifteen-point type. Its first four columns give the rounds. A triple is three hexadecimal digits for vertices 0 through 14, with a period separating triples. The remaining columns give the full model count and the four counts after dropping the indicated round. [Download 13,933 representatives](order15.tsv.gz)

An optional complete solver sweep checks the 13,933 DIMACS-equivalent formulas against these counts and validates every returned assignment. The ternary incidence witness certified one SAT type. Backdoor enumeration decided 13,823 other SAT types and all 109 UNSAT types. The maximum number of assignments tried by that route was 474 on SAT and 1,024 on UNSAT. Run `python -B routes/matching-balance/verify15.py --solver` to reproduce the method counts. [Solver sweep](verify15.py)

## A single miss does not generalize

Take $k$ copies of the nine-point affine plane. In the fourth round of each block open the same triple $(a_i,b_i,c_i)$ and replace it by $(a_i,b_i,c_{i+1})$ cyclically. The result is connected, linear and still has four perfect matchings. Among colorings satisfying the first three rounds, the minimum number of violations in the fourth is **$k+(k\bmod 2)$**.

Each block retains eleven internal triples on nine points. At most 20 pairs cross, so at least one internal triple is monochromatic. With exactly one internal miss, the ten satisfied triples already use 20 crossing pairs. The three pairs of the old open triple are therefore uncut, so its ports share a color. If the total number of misses equals $k$, all cross-block triples are satisfied; this forces the port colors to alternate and requires even $k$. For the upper bound, color alternate blocks by the reference mask 15 and its nine-bit complement. In each block this satisfies the first three rounds and misses one internal fourth-round triple. Exactly one cross-block triple is missed when $k$ is odd. [Generator and witnesses](independent.py)

## Reproduction

The dual incidence hypergraph has one vertex per triple and one hyperedge per original variable, joining the four triples containing it. A proper coloring partitions the dual edges into two edge covers: each dual vertex sees both colors. The incidence counts give a sharp color-class bound. Cycle repair and damaged-block decoding test the limits of two further ways to use that structure. [Recoloring and sharp examples](IMBALANCE.md) · [Alternating cycles and phase repair](REPAIR.md) · [Damaged-block decoding](DAMAGE.md)

The ternary coefficient expansion gives an independent modular check on every catalogue row. A later construction pairs easy witness recovery with large exact ordered diagrams. Over the rationals, partial assignments from weighted kernels provide a separate decision reduction. [Ternary tests](TERNARY.md) · [Ordered diagrams and hidden witnesses](DIAGRAMS.md) · [Rational incidence weights](WEIGHTS.md)

Run from the repository root. The final command writes a separate copy of the full catalogue.

~~~sh
python -B routes/matching-balance/independent.py
python -B routes/matching-balance/order12.py
python -B routes/matching-balance/verify15.py
python -B routes/matching-balance/dual.py
python -B routes/matching-balance/order15.py --output regenerated-order15.tsv.gz
~~~
