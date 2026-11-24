# Deciding SAT without expanding the projection

Suppose the retained background $B$ is any 2-CNF and the hidden system's projected goals $g$ are increasing in a supplied orientation. The [implementation](frontier_sat.py) obtains that orientation from syntactically unate occurrences outside $B$. Evaluating $g$ and constructing a hidden extension at any retained assignment take polynomial time by the greatest-state algorithm. The decision method here permits $g$ to have arbitrarily large prime clauses.

## From pair conflicts to complete assignments

First check $B$ by 2-SAT. If satisfiable, build a graph on individually feasible oriented-true literals. Join two vertices if adding both units to $B$ is unsatisfiable. This uses at most a quadratic number of 2-SAT calls.

An independent set in this graph can be true simultaneously. To see this, note that the bitwise majority of three models of a signed 2-CNF is another model. A violated clause would require at least two of the three assignments to falsify each of its at most two literals, so some assignment would falsify the whole clause. Now let $U$ be a list of requested literal values. If $|U|\ge3$, obtain models for the three sublists formed by omitting a different one of the first three positions. Their majority meets all of $U$. Induction proves the claim from pairwise feasibility, with the empty set handled by satisfiability of $B$. [Core Lean proof for signed requests](Reductions/PairExtension.lean)

Consequently the inclusion-maximal models of $B$ in oriented coordinates correspond exactly to the maximal independent sets. A model extending a maximal independent set has precisely its support; any additional true literal would extend the independent set. Conversely, extending the support of a maximal model to any larger independent set would produce a larger model. A satisfiable $B\land g$ has a model at one of these maxima, since increasing the oriented input preserves $g$.

If $C$ is a vertex cover with $k$ vertices, inspect each choice $S\subseteq C$. Discard choices with an internal conflict. Outside the cover, include every vertex with no neighbor in $S$. These outside vertices have no mutual conflicts. Finally check that every omitted cover vertex has a neighbor in the resulting set; this last test avoids treating a nonmaximal candidate as a full model. There are at most $2^k$ evaluations of $g$, with polynomial overhead per pattern.

A supplied cover gives this bound directly. The default greedy maximal-matching cover, followed by deletion of redundant vertices, has size at most twice the minimum $\tau$, giving $O^*(4^\tau)$ time; the star denotes suppression of polynomial factors in the explicit input size. Thus the algorithm decides SAT in polynomial time when $\tau=O(\log N)$ for input size $N$. It needs no promise of exact binary projection.

### Two checks in place of an exponential formula

Take $g=s\land\bigvee_{i=1}^{k}(a_i\land b_i)$ and background $B=\bigwedge_i(\neg s\lor\neg a_i)$. The argument in [the projection note](THEORY.md) gives $2^k$ essential matching clauses when $s=1$. For the conjunction with $s$, its maximal false assignments are the $2^k$ matching maxima at $s=1$ and the assignment with $s=0$ and all other bits true. These $2^k+1$ inputs require distinct clauses; a unit for $s$ and the matching clauses attain the bound.

The conflict graph for $B$ is a star on $s,a_1,\ldots,a_k$ and isolated $b_i$. Its two maximal models either set $s=0$, or set every $a_i=0$. Both falsify $g$. For $k=24$, the body alone requires 16,777,217 clauses to project into ordinary retained-only CNF, while SAT of the combined instance is decided by two maximal-model checks. The exponential count is **for the body alone**. The combined instance is unsatisfiable and therefore has a constant-false projection. [Executable example](examples.py)

Taking a disjoint matching instead of a star gives $2^k$ maximal models for a minimum cover of size $k$. With a membership oracle for $g$, this many deterministic queries can be necessary even when arbitrary off-background queries are allowed. The source program can disclose more information than its input-output interface. [Tight oracle bound](routes/query-limit/README.md)

## A complete decision procedure on ordinary DIMACS CNF

[solve_cnf.py](solve_cnf.py) accepts a DIMACS file or standard input. It uses ordinary 2-SAT when every surviving clause is binary. On general clauses it detects a set of variables that can be hidden after renaming their polarities. An orientation variable $s_i$ represents the original value encoded by a true hidden variable. For every pair of hidden literals $\ell_i,\ell_j$ in the same clause require

$$
(s_i=\mathop{\mathrm{sign}}\ell_i)\ \lor\
(s_j=\mathop{\mathrm{sign}}\ell_j).
$$

The constraints form a 2-CNF. Satisfying them is equivalent to having at most one negative hidden literal per original clause. Try hiding all variables, then use an incremental greedy selection if necessary. The greedy choice is inclusion-maximal and can be smaller than a maximum-cardinality choice. For each assignment to the $k$ other variables, evaluate the renamed hidden system by greatest fixed point and recover an original satisfying assignment if there is one. All variables in this counted parameter are actual variables of the original CNF. Enumerating the $2^k$ settings directly is equivalent to using the two-rail matching background on those choices, and avoids constructing that graph. A supplied search cap can return **UNKNOWN**. Only a complete search or a sound shortcut returns **UNSAT**.

### Parity detection and non-growing elimination

The default solver also looks for complete forbidden parity classes grouped by their exact set of variables. A normalized clause on a support of size $d$ forbids one assignment there. If all $2^{d-1}$ assignments of one parity are forbidden, their clauses entail the opposite XOR equation. Gaussian elimination of the extracted equations can certify UNSAT. A solution of those equations is returned as SAT only after it satisfies the entire input.

The second preprocessing pass attempts exact Davis–Putnam elimination. For each candidate pivot it resolves all opposite-polarity pairs, deletes tautologies, duplicates and subsumed clauses, and accepts the step when the residual clause count does not grow. The number of variables decreases, and the clause count never exceeds the starting budget on the accepted trace. Even trying all pivots at each step is polynomial in the explicit input. For reconstruction, set the pivot true exactly when a positive tail is false. A conflict with a false negative tail would violate their resolvent. The implementation checks recovered models against all original normalized clauses. [Pivot implementation](pivot_elimination.py) · [Parity implementation](gf2.py)

### Connected counterexamples and a repair

Let the variables be edges of the cubic prism $C_m\square K_2$, $m\ge3$. At each vertex encode a parity equation on its three incident bits using four width-three clauses. Give exactly one vertex odd charge. Adding all equations modulo two cancels every edge bit and gives $0=1$, so the formula is unsatisfiable. Removing any one vertex equation makes the rest consistent: root a spanning tree at the omitted vertex, set non-tree edges to zero, then choose each parent edge from the leaves up to satisfy the non-root equations.

Every incident pair appears in all four combinations of signs in that vertex's clauses. No orientation can make both edges hidden. The hidden variables must form a matching and any matching is allowable. The $m$ rungs are a maximum matching of this $2m$-vertex graph. Even an optimal choice therefore retains at least $3m-m=2m$ variables. Rung-first numbering attains the optimum for the implemented greedy rule. The branching method alone tests exactly $4^m$ assignments before returning UNSAT. The affine pass recognizes the contradiction immediately. Replacing one clause $(a\lor b\lor c)$ by $(a\lor b\lor s)\land(\neg s\lor c)$ with a fresh variable hides one vertex equation from exact-support recognition. Non-growing elimination can recover it. Both variants are in the [experiment](solver_experiment.py).

### A family that defeats the combined implementation

On $m\ge5$ vertices form a simple 4-regular graph with neighbors at cyclic offsets $\pm1,\pm2$. Encode an odd-charge Tseitin system using the eight width-four clauses at each vertex. Use two disjoint copies $A,B$ of this edge-variable system and one selector $s$. Prefix every clause of $A$ by $\neg s$ and every clause of $B$ by $s$. The resulting CNF is connected, has $4m+1$ variables, $16m$ clauses and width five. Each setting of the selector activates an inconsistent system. One split on $s$ followed by Gaussian elimination therefore solves this family in polynomial time.

For the implemented order of preprocessing and fixed-set branching, the following counts hold before branching:

* Each guarded vertex support has eight forbidden rows on five variables. A whole parity class would need sixteen rows. The affine pass extracts no equation.
* Eliminating an edge variable removes sixteen clauses from its two endpoints. Pairs from within one parity equation give tautologies. Across the endpoints, the two pivot signs each give $4\cdot4$ distinct resolvents. The 32 new clauses have three other edges from each endpoint and the common guard. No unchanged vertex clause subsumes one: another vertex touches at most two edges in that union, and the two endpoints would need the missing pivot. All new resolvents have the same width. Thus this step grows the clause count by sixteen.
* Eliminating $s$ produces $(8m)^2$ distinct clauses on disjoint copies and removes $16m$. Therefore no non-growing pivot exists.
* Each pair of incident edge variables still occurs in all four sign combinations. Irrespective of renaming or the selector's status, at most a matching of edges per copy can be hidden. At least $4m-2\lfloor m/2\rfloor\ge3m$ edge variables remain. With an unlimited pattern budget this UNSAT input makes the fixed-backdoor solver test every retained assignment, at least $2^{3m}$ patterns.

The smallest tested instance, $m=5$, ran to completion: 21 variables, 80 clauses, zero accepted pivots, 17 retained variables and 131,072 assignments. This rules out a polynomial worst-case bound for this particular combination of algorithms. It does not rule out different decisions about when to branch, and the selector itself gives a fast alternative.
