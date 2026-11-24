# Affine constraints on the retained 2-CNF frontier

Let $B$ be a signed 2-CNF on $n$ retained bits, $g$ an upward-monotone Boolean function of the oriented retained bits, and $Ax=b$ an affine constraint over $\mathbb F_2$. Write $r=\operatorname{rank}A$. The problem is to find $x$ with $B(x)=g(x)=1$ and $Ax=b$. If the orientation complements the coordinates in a vector $\epsilon$, replace the original right-hand side by $b+A\epsilon$. The transformed background still has width at most two.

## What can be removed from a minimal drop set

Every $B$-model lies below some coordinatewise maximal $B$-model $M$. Fix such an $M$ and write $D\subseteq\{i:M_i=1\}$ for the bits dropped to obtain $x=M+\mathbf1_D$. Substitute $x_i=1-d_i$ for these coordinates, with $d_i=1$ meaning a drop, and $x_i=0$ for all others. Simplify constants, tautologies and duplicate literals. The all-zero drop vector satisfies the resulting 2-CNF because it gives $M$. Thus every remaining clause is a forbidden drop $\neg d_i$, an exclusion $\neg d_i\lor\neg d_j$, or an implication $d_i\Rightarrow d_j$.

Draw arcs in the direction of the drop implications, from $i$ to its required drop $j$. Feasible $D$ is successor-closed, and each strongly connected component is entirely in or out of $D$. Contract the strongly connected components. In the induced DAG on the included components, the sources are the removable components. With the reverse order these are the maximal components of a predecessor-closed set. Deleting any collection of the sources preserves closure because no remaining component has an arc into a deleted source. Deleting drops also preserves the forbidden-unit and exclusion clauses.

Take a feasible $D$ that is inclusion-minimal among sets giving a solution to all three conditions below $M$. Label each included source component $C$ by its block syndrome $A\mathbf1_C$. If these vectors are linearly dependent, some nonempty collection of source components has syndrome sum zero. Remove that collection from $D$. The result keeps the affine syndrome $A\mathbf1_D=b+AM$, preserves $B$, and increases the oriented vector $x$, so $g$ stays true. This contradicts inclusion-minimality. The source syndromes are therefore linearly independent, giving at most $r$ source components.

Every included component is reachable from one of these sources. The minimal set $D$ can thus be recovered as the union of the closures of at most $r$ components. Enumerating such generators, taking their closure, and testing $B$, $g$ and the affine equation suffices. This takes at most $\sum_{j=0}^{r}\binom{n}{j}$ closure tests per maximal $M$, with polynomial work per test when $g$ has polynomial evaluation. The conflict-graph enumeration gives at most $2^k$ maximal $M$ for a vertex cover of size $k$. Empty drop sets and rank zero are included. The same argument permits arbitrary dependencies in the equation rows, forced retained values, signed clauses and cycles.

For $x_1\Rightarrow x_2\Rightarrow\cdots\Rightarrow x_n$ with $M=\mathbf1$ and the single equation $x_n=0$, a solution must drop all $n$ coordinates. The drop implication path has one source in that solution, showing why enumeration takes closures of generators. A hidden system with monotone retained occurrences supplies a monotone $g$ because a hidden witness can be reused when the oriented retained vector increases. The dual-Horn form on hidden variables gives polynomial evaluation by the greatest-vector procedure. Monotonicity is essential to the drop argument. With trivial $B$, rank zero, and $g$ true only at the all-zero point, the unique solution drops every bit, and every drop is a source.

## A matching oracle obstruction for fixed rank

Take $B=\top$ and $n=rq$ with $r\ge1$, $q\ge2$. Partition the retained bits into $r$ blocks of $q$. Give each block one affine equation requiring an odd number of zeros. The equations have disjoint supports and rank $r$. Their maximal models have exactly one zero in each block, so there are $q^r$ such models. If a block has at least three zeros, two can be raised without changing parity. A model with one zero per block cannot be increased while keeping all block parities.

Set $g_0=\bigvee_{j=1}^{r}\bigwedge_{i=1}^{q}x_{ji}$. Every affine model gives value zero. For each maximal affine model $\sigma$, use

$$
g_\sigma(x)=g_0(x)\lor [x\ge\sigma].
$$

The added term is a conjunction of the coordinates that are one in $\sigma$. On any point strictly above $\sigma$, at least one block is full and $g_0$ is already one. Therefore $g_\sigma$ differs from $g_0$ at exactly $\sigma$ on the whole Boolean cube. The functions are monotone and have fan-in-two AND/OR formulas of size $O(rq)$. Encoding formula gates by upper-bound rules and asserting the root also gives acyclic hidden systems of clause width at most three and size $O(rq)$.

On input $g_0$, any deterministic exact membership-query algorithm must query every $\sigma$. An unqueried $\sigma$ leaves the transcript identical for the satisfiable instance using $g_\sigma$. A randomized algorithm with worst-case error $\delta<1/2$ must query each $\sigma$ on $g_0$ with probability at least $1-2\delta$. Couple its two runs using the same random tape. Their outputs agree unless the $g_0$ run queries $\sigma$, while their probabilities of answering SAT differ by at least $1-2\delta$. Summing shows at least $(1-2\delta)q^r$ expected queries on $g_0$. This gives $\Omega(n^r)$ queries for fixed $r$ even with arbitrary cube queries and trivial $B$. The indistinguishability argument concerns oracle access to $g$. An algorithm inspecting the explicit formulas can distinguish this family directly.

## Limits of direct XOR-pattern recognition

On a connected simple cubic graph, take a Tseitin constraint on each vertex's three incident edge bits, with odd total charge. Its four wrong-parity assignments give the four ternary clauses of that vertex. The incidence equations are inconsistent together. Every proper subset is consistent because a linear dependency among the incidence rows selects a vertex subset with empty edge boundary, and connectedness permits only the empty and full subsets.

Replace one wrong-parity clause $D$ at a chosen vertex by $D\lor s$ and $D\lor\neg s$ for a fresh selector $s$. Their conjunction is equivalent to $D$ for each selector value. The vertex's original scope now has only three ternary exclusions, and its enlarged scope has only two quaternary clauses. A recognizer that requires the complete syntactic parity pattern on one scope therefore misses that vertex's equation. The other equations alone are consistent. This defeats a shortcut that handles the pure recognizable XOR case and falls back on the ordinary CNF when it encounters a residual clause.

For every pair of incident edge variables, all four sign pairs occur among the clauses at the vertex. The split keeps this property by leaving the old literals in both new clauses. Thus any fixed renaming in which each clause contains at most one negative hidden literal can hide at most one original edge variable at each vertex. The hidden original edges form a matching. With $v$ vertices, at least $3v/2-v/2=v$ original edge bits must remain retained under this syntactic condition.

If a hybrid removes the recognized equations before testing the residual CNF, a single split leaves a residual on only three edge bits and one selector. To retain the backdoor lower bound on the residual itself, split one clause per vertex, with a fresh selector for each vertex. No direct full parity pattern remains and the matching bound still applies. These transformations target exact scope recognition. Resolving the selector pair recovers $D$ immediately, and a hybrid can also solve the single-split case by enumerating the residual variables and checking affine extendibility.

For a width-three variant, replace $D=\ell_1\lor\ell_2\lor\ell_3$ at each vertex by $(\ell_1\lor\ell_2\lor s)\land(\neg s\lor\ell_3)$. Existentially eliminating the fresh selector gives $D$. The pair on the first two original coordinates still realizes all four sign pairs, so at most two original edge variables can be hidden per vertex. This keeps a linear bound of at least $v/2$ retained original edges in a formula of width three.

## Reproduction

From the repository root run `python -B routes/obstructions/check_affine_frontier.py`. The checker compares the closure search with exhaustive satisfying assignments, tests independence of the removable block syndromes, verifies the oracle differences on complete small cubes, and checks the direct syntactic XOR patterns and orientation constraints on four prism sizes.
