# Maximal supports with affine side conditions

Let $g$ be a Boolean function on $n$ retained variables, with polynomial-time evaluation and a known orientation in which it is monotone increasing. Let $B$ be a retained 2-CNF and $Ax=b$ a system of GF(2) equations on the retained variables. The goal is to find a model of $B\land (Ax=b)\land g$ or decide that none exists.

If $B$ is satisfiable, let $k$ be the size of a chosen vertex cover of its conflict graph in the given orientation. Let $r=\operatorname{rank}(A)$. The search uses at most

$$2^k\sum_{j=0}^{r}\binom{n}{j}$$

candidate seed sets, with polynomial work per set and polynomial preprocessing. It also makes at most this many evaluations of $g$. The condition on $g$ is monotonicity in the given orientation. The 2-CNF and the affine system are separate supplied constraints.

## Background maxima

Write $y_i$ for the indicator that the oriented literal of variable $i$ is true. If the orientation reverses a variable, $x_i=y_i\oplus1$. Thus $x=y\oplus s$ for a fixed mask $s$, and the affine equations in oriented coordinates have right-hand side $b'=b\oplus As$.

The conflict graph has one vertex for each oriented literal that can be true in a model of $B$. Two are adjacent if no model of $B$ makes both true. Every independent set extends to a model of $B$. Otherwise, take an inclusion-minimal nonextendible subset. It would have at least three literals. For three different literals in the subset, choose three models that satisfy all but the corresponding literal. The coordinatewise majority satisfies the full subset and still satisfies $B$. Indeed, if it falsified a 2-clause, at least two of the three models would falsify each of that clause's literals, and some model would falsify the whole clause. Units have the same property.

Consequently, the maximal independent sets are exactly the maximal oriented supports of $B$-models. For a vertex cover $C$, a maximal independent set is determined by its intersection $S$ with $C$. It contains every vertex outside $C$ that has no neighbor in $S$, since the vertices outside $C$ are independent. Trying all $2^k$ intersections, with a check for independence and maximality, enumerates all the supports. Every $B$-model's support is contained in one of them.

## At most $r$ seeds inside a maximal support

Fix one maximal support $M$, and fix the oriented variables outside $M$ to zero. The restricted $B$ is satisfied by the all-ones assignment on $M$. After simplifying the fixed variables and tautologies, each clause is a positive unit, a positive pair, or an implication $u\to v$.

Write $D\subseteq M$ for the variables dropped from the all-ones assignment. Implications hold exactly when $D$ is closed under predecessors, since dropping $v$ forces the drop of every $u$ with $u\to v$. Thus $D$ is a union of strongly connected components of the implication graph and is a downset in their reachability order. Positive clauses and $g$ stay true if a feasible drop set is made smaller.

Let $A_i$ be the column for variable $i$. Affine feasibility requires the drop syndrome to be

$$\bigoplus_{i\in D} A_i=b'\oplus\bigoplus_{i\in M}A_i.$$

If a solution lies inside $M$, choose one whose drop set $D$ is inclusion-minimal among solutions inside $M$. For each strongly connected component $Q$ define its syndrome $\lambda_Q=\bigoplus_{i\in Q}A_i$. The syndromes of the maximal components in $D$ are linearly independent. A dependence would give a nonempty collection of those components whose syndromes XOR to zero. Removing that collection from $D$ leaves a predecessor-closed set because none of the removed components precedes a retained component in $D$. This keeps the affine syndrome, and the smaller drops preserve all positive clauses and $g$. It contradicts minimality.

Let $c_M$ be the number of components and $\rho_M$ the rank of all their syndromes. Then $\rho_M\le r$, and every minimal feasible drop set is the union of predecessor closures of at most $\rho_M$ components. Enumerate up to that many component seeds and verify the resulting assignments. The target syndrome must be in the span of the component syndromes, so the search can skip $M$ entirely if this fails. Even without that rejection, the number of seed sets is bounded by

$$\sum_{M}\sum_{j=0}^{\rho_M}\binom{c_M}{j}
\ \le\ 2^k\sum_{j=0}^{r}\binom{n}{j}.$$

For a consistent rank-zero affine system, the only seed set examined in each $M$ is empty. This gives the ordinary maximal-support search. An inconsistent affine system can be rejected before constructing the conflict graph.

## Rank bounds seeds, while a seed can drop many variables

For $n\ge4$, take the implication chain $x_1\to x_2\to\cdots\to x_n$, add the unit $x_{n-1}$ to $B$, and let $g=x_n$. The single affine equation is $x_{n-2}\oplus x_{n-1}\oplus x_n=0$. It forces $x_{n-2}=0$ and therefore drops all $n-2$ variables through the start of the chain. There is one maximal dropped component, the singleton $\{x_{n-2}\}$. A directed cycle gives a second kind of example. If all its variables have to agree and their number is odd, even parity forces an all-zero support. A single component seed accounts for every drop.

## Oracle lower bound with both parameters

Take $k$ disjoint at-most-one rail pairs in $B$ and $r$ disjoint groups of $m$ other variables, with $m\ge1$. The affine equations require each group to have an odd number of zeros, using one independent equation per group. The conflict graph is a matching on the rails plus isolated vertices for the group variables. The constrained maximal supports choose exactly one rail per pair and leave exactly one zero per group, for $N=2^k m^r$ distinct supports.

Let $g_{\mathrm{base}}$ be the OR of the events that some rail pair is all true or some affine group is all true. It has no satisfying assignment under the constraints. For each constrained maximal support $T$, use $g_T=g_{\mathrm{base}}\lor\bigwedge_{i\in T}x_i$. This changes the base function on precisely the row $T$, even for membership queries anywhere in the cube. Every strict superset of $T$ fills a rail pair or an affine group and was already accepted. The functions are monotone and have linear-size monotone circuits.

The [single-row argument](../query-limit/README.md) gives a deterministic worst-case lower bound of $2^k m^r$, along with the same sharp bounded-error formulas in terms of $N$. In particular, $k=0$ gives $(n/r)^r$ for $r\ge1$. The exponent dependence on affine rank is therefore necessary for arbitrary membership access, up to constants in $n$ for fixed $r$. The argument uses hidden representations and gives an oracle bound.

## Implementation and verification

`affine_frontier.py` reuses the repository's 2-CNF conflict graph and maximal-support enumeration. It computes reverse reachability once per vertex. Vertices with the same predecessor closure are precisely an SCC, so those closures serve as component identifiers for the block syndromes. Gaussian elimination uses packed syndrome columns. The solver checks each candidate syndrome and calls `HiddenCNF.extend` to check the background and construct a hidden witness.

`solve_affine_frontier(system, rows, cover=None, oriented=None)` accepts rows as pairs of a coefficient bit mask and a right-hand side in `{0, 1}`. Bit zero corresponds to retained variable 1. A supplied cover uses signed oriented literals. By default the solver obtains a valid orientation from the signs in the hidden system. A caller with a known semantic orientation can supply it as one signed literal per retained variable in order. Monotonicity in this supplied orientation is a precondition. The return value includes a complete assignment on success and counts for the cover patterns, maximal supports, seed sets and membership evaluations.

Run from the repository root with Python 3.10 or newer.

```sh
python -B -m unittest -v test_affine_frontier
```

The suite compares against direct assignment enumeration for 12,288 two-variable instances across 256 backgrounds, all four orientations and 12 affine systems. It checks another 600 seeded mixed instances with hidden rules and verifies the returned full assignments. The remaining tests cover rank zero, rank-one chains dropping seven or fifteen variables, cancellation within an SCC, a supplied semantic orientation, and the combined rail-and-parity lower-bound family.
