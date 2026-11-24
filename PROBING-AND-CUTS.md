# What does a failed 2-SAT check tell the original solver?

## Reading the pin gadget

Try each assignment to one or two variables. Under those assumptions retain the current binary background and every original clause shortened to width at most two. If this 2-SAT system is infeasible, its assumptions cannot occur in any model of the original formula. Add their complement as a unit or binary consequence. Repeat to saturation. There are at most $2n+4\binom n2$ different nonempty assumptions and at most one corresponding consequence per assumption. Each successful addition excludes a model of the previous binary background. Thus termination and polynomial running time follow. An inconsistent binary background certifies UNSAT. [Implementation](binary_probing.py)

On the pin gadgets in the [schedule lower bound](BINARY-PROMOTION.md), trying $x=0$ shortens the four clauses forcing $x$ to all four binary clauses on the same two helpers. They are jointly inconsistent, so the probe learns $x$. With all the pins added, individual clause promotion absorbs every target. Probing followed by promotion therefore decides this family in polynomial time. The DIMACS solver's default path currently uses the cut test below; probing and promotion have their own entry points. Failed-literal and failed-pair learning have earlier formulations using unit propagation, binary resolution and related inferences. Here the oracle is exactly the retained 2-SAT system above. [Prior work](RELATED-WORK.md) · [Tests](test_binary_probing.py)

## Two pins cannot read every parity contradiction

On a cubic graph put a Boolean variable on every edge. At each vertex require the parity of its three incident bits to equal its charge, encoded by four ternary clauses. Summing all equations gives zero on the left. For a connected graph, an odd total charge is impossible and an even total has a solution.

Take a simple cubic 3-edge-connected graph with more than four vertices. Under at most two edge pins, only vertices touching a pinned edge can produce clauses of width at most two. The resulting constraints give the parity equations at those vertices, with pin values substituted. Delete the pinned edges from the graph. It remains connected and the touched vertices are a proper subset. No nonempty subset of those incidence rows sums to zero: such a sum would have no edge leaving the subset in the connected residual graph. The selected rows are independent, so all their right-hand sides are consistent. No probe learns a clause, for either total charge. Each original ternary clause also fails individual promotion against an empty background. The complete four-clause parity block is directly recognizable by the repository's GF(2) routine. [Triangular prism checks](test_binary_probing.py) · [Parity extraction](gf2.py)

## A family that separates local probes from a global cut

A **linear triple system** is a collection of three-element sets in which two distinct triples share at most one vertex. On each triple require both a positive clause and its all-negative counterpart. This says the three vertex colors are not all equal (NAE).

For one pin or two pins of the same color, give all unpinned vertices the opposite color. Every triple meeting a pin is then valid. For two opposite-colored pins, the triples meeting both are already valid. After removing one pinned vertex from triples meeting only it, the remaining pairs form a matching by linearity. The analogous pairs for the other pin form a second matching. The union of two matchings is a disjoint union of paths and even cycles, hence admits a coloring making each such pair bichromatic. Again every short residual clause is feasible. No single clause promotes, and the two opposite excluded patterns on a triple do not constitute the four exclusions needed for a parity equation.

At a vertex of degree $d$, eliminate it by resolution. The positive and negative clauses from the same triple give a tautological resolvent. Each ordered pair of different incident triples yields a distinct width-four clause with two positive and two negative literals. No remaining monochromatic-sign ternary clause subsumes it. The step therefore adds $d(d-1)$ clauses and removes $2d$. If every degree is at least four, the reference non-growing elimination rule has no first step.

For a concrete family take the nonzero binary vectors of dimension $q$, with triples $\{a,b,a+b\}$ for distinct vectors $a,b$. Every pair occurs once. For $n=2^q-1$ vertices, every degree is $(n-1)/2$ and there are $n(n-1)/6$ triples. In the solver's oriented dual-Horn search, two hidden variables sharing a clause must have opposite orientations because both signs of that clause occur. Every pair shares a clause here, so at most two variables can be hidden. The greedy rule accepts its first two. For $q\ge4$, the backdoor search with the cut test disabled consequently tries $2^{n-2}$ assignments on these UNSAT formulas.

To see the contradiction directly, regard each triple as a triangle in the complete graph. A valid triple has two edges crossing the color cut. All pairs occur once, so the required crossing count is $n(n-1)/3$. A cut can contain at most $\lfloor n^2/4\rfloor$ pairs; the demand exceeds this capacity for the stated family. At $n=15$ the demand is **70** and the capacity is **56**. The earlier search actually executed **8,192** assignments. The current default solver returns UNSAT with **zero** assignment trials. The earlier configuration can be reproduced with the solver's `--no-cut` option. [Regression with both solver configurations](test_nae_cut.py)

## The certificate used by the solver

The DIMACS solver detects complementary pairs of signed ternary clauses. Each pair enforces NAE on its three signed literals. For a pair of variables in a triple, equal literal signs award a point when the variables differ; opposite literal signs award a point when the variables agree. Count repeated pair occurrences with multiplicity.

On a connected component, let $S$ count occurrences awarding a point for agreement, and let $w_{uv}$ be the number awarding a point for disagreement minus the number awarding one for agreement. An assignment's total score is exactly $S+\sum_{uv\text{ crossing}} w_{uv}$. On $v$ vertices a cut contains at most $\lfloor v^2/4\rfloor$ distinct pairs. An upper bound is therefore $S$ plus that many largest positive weights, or all positive weights if there are fewer. Satisfying all $t$ triples would score exactly $2t$. A strictly smaller upper bound proves UNSAT for that component and for any CNF containing it. Unpaired clauses need no special treatment. [Certificate](nae_cut.py) · [Normal DIMACS entry point](solve_cnf.py)

Linear positive NAE-3 remains NP-complete even on the four-regular class with a supplied decomposition into four perfect matchings. In a connected four-regular linear instance on $v$ vertices, $t=4v/3$ and all pair weights are one. Once $v\ge12$ the unrestricted pair-capacity bound is already at least $2t$. Thus this particular certificate handles a dense obstruction while leaving sparse hard instances in play. [Darmann, Döcker and Dorn, Theorem 3.6](https://arxiv.org/html/2412.03395)

## Finding the same obstruction inside a sparse formula

For a set of $s$ vertices, count only the $t$ positive NAE triples wholly inside it. If the entire extracted positive hypergraph is linear and has maximum degree four, the detector returns a certificate whenever some set satisfies $2t>\lfloor s^2/4\rfloor$. This search takes linear work at fixed degree.

Each vertex in the subset has internal triple degree at most $\min(4,\lfloor(s-1)/2\rfloor)$. These degrees sum to $3t$. For $s\le6$ or $s=8$ the bound excludes a strict violation. For $s\ge11$, $2t\le8s/3\le s^2/4$. The three remaining sizes give the algorithm.

| $s$ | Internal triples | How to find the set |
|---|---|---|
| 7 | Exactly 7 | Every pair is present. Choose a vertex and six neighbors. |
| 9 | 11 or 12 | The missing-pair graph has even degrees and at most three edges. It is empty or a triangle. A vertex of internal pair degree eight has all eight neighbors inside. |
| 10 | Exactly 13 | The internal pair degrees sum to 78. They are even and at most eight, so nine vertices have degree eight and one has degree six. Choose a degree-eight vertex, its eight neighbors, and its single missing member at graph distance two. |

In each case the chosen vertex has at least six neighbors sharing at least four common neighbors with it. The preliminary neighborhood filter therefore preserves a witness. There are at most eight neighbors in the whole positive pair graph. For four supplied perfect matchings, only size nine is possible: the seven triples at size seven intersect pairwise, and each matching contributes at most three internal triples at size ten. [Implementation](nae_cut.py) · [Independent controls](routes/matching-balance/README.md) · [Packing antecedents](RELATED-WORK.md)

## Exact decision near the complete-graph cut capacity

For a positive linear triple system on $n$ vertices, write $G$ for its graph of occurring pairs and let $t$ be the number of triples. A coloring splits all triples exactly when its cut in $G$ has size $2t$. If one side has $w$ vertices and $h$ **missing** pairs cross, this cut has size $w(n-w)-h$. Any solution must therefore have $h\le D=\lfloor n^2/4\rfloor-2t$. Negative $D$ immediately refutes the input.

Build a spanning forest of the missing-pair graph, with $c$ components. Enumerate which at most $D$ forest edges cross. Each pattern assigns colors throughout a component up to a common flip. It determines the exact number $h$ of crossing missing pairs, including nonforest edges. Test $w(n-w)=2t+h$ by solving this integer quadratic. For an integer root, use subset-sum dynamic programming on the two possible side sizes of each component. Complementing the whole coloring exchanges the two roots. A successful trace gives an actual coloring. Exhausting all patterns certifies UNSAT.

There are at most $\sum_{j=0}^{\min(D,n-c)}\binom{n-c}{j}$ patterns, with polynomial work per pattern. This is polynomial for fixed $D$. On unrelated four-regular inputs $D$ grows quadratically with the number of vertices. The default DIMACS path tries this method on pure positive linear NAE when $0\le D\le4$ and the entire search fits both 10,000 patterns and any lower caller budget. The separate API accepts other budgets. [Algorithm](near_cut.py) · [Truth tables and budget checks](test_near_cut.py)
