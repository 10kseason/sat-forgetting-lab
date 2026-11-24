# Membership queries can miss a single exceptional row

Let $n\ge3$ and let the retained variables be pairs of rails $(u_i,v_i)$ for $1\le i\le n$. Set

$$H=\bigwedge_{i=1}^n(u_i\lor v_i).$$

For a secret bit string $\sigma\in\{0,1\}^n$, let $\ell_i$ be $u_i$ if $\sigma_i=0$ and $v_i$ if $\sigma_i=1$. Define

$$g_\sigma=H\land\left(\bigvee_{i=1}^n\ell_i\right).$$

The only assignment where $g_\sigma$ and $H$ differ is the row $d_\sigma$ that sets $\ell_i=0$ and the opposite rail to 1 for every pair. Indeed, $H$ forces the opposite rail on each pair when its selected rail is off. The $N=2^n$ rows are distinct.

## The binary envelope is the same

The binary envelope is the conjunction of all entailed clauses of width at most two on the retained variables. To check a nontautological clause of that width against a monotone function, set the variables in its positive literals to zero and every other variable to one. This assignment falsifies the clause and is coordinatewise maximal among the assignments that do. The clause is entailed exactly when the function is zero on that assignment. This test applies to signed clauses as well.

Both functions are monotone and agree on every assignment with at most two zeros, since $d_\sigma$ has $n$ zeros. Thus they share all binary implicates. Their envelope is $H$ because $H$ itself is a 2-CNF.

## Small acyclic CNF encodings

Use $H$ directly for the reference. To encode $g_\sigma$, add the following clauses with hidden variables $z_1,\ldots,z_{n-2}$:

$$
(\ell_1\lor\ell_2\lor z_1),\qquad
(\neg z_{j-1}\lor\ell_{j+1}\lor z_j)\quad(2\le j\le n-2),\qquad
(\neg z_{n-2}\lor\ell_n).
$$

If all selected rails are zero, the chain forces every hidden variable to one and violates the last clause. Otherwise, setting $z_j$ to one exactly when the first $j+1$ selected rails are all zero satisfies the chain. This proves the claimed projection. The $2n-1$ clauses have width at most three and at most one negative literal each. The hidden dependencies are $z_{j-1}\to z_j$. The primal graph has a tree decomposition of width at most two, with the chain clauses as path bags and each original rail pair attached to the bag that contains its selected rail.

## Tight query bounds

An algorithm knows the family and receives one membership oracle promised to be $H$ or some $g_\sigma$. It can query any complete retained assignment at unit cost and may choose later queries from earlier answers. The output is whether the oracle is $H$. Computation apart from membership queries is free.

Every deterministic correct algorithm has to query all $N$ rows on $H$. If it skips $d_\sigma$, that same transcript occurs on $g_\sigma$, so the answer cannot be correct on both. Querying the rows until a discrepancy appears or the list is exhausted achieves $N$ in the worst case.

Let a randomized algorithm have error at most $\epsilon$ on **each** promised oracle, where $0\le\epsilon\le 1/2$. Let $A$ be the event that it answers $H$ on the reference oracle and set $p=\Pr(A)\ge1-\epsilon$. On that run, let $S$ be the set of distinct exceptional rows queried before it stops. Use the same random choices for the comparison run on a punctured oracle. If the puncture is $d$ and $d\notin S$, the two transcripts coincide and $A$ gives an error on the punctured oracle. Consequently for every row $d$,

$$
\Pr(A\land d\in S)\ge p-\epsilon,\qquad
\mathbb E[|S|\mathbf{1}_A]\ge N(p-\epsilon)
$$

where the second inequality sums the first over all rows.

**Hard query cap.** If at most $T$ queries are allowed on every run, then $Tp\ge N(p-\epsilon)$. Since $p\ge1-\epsilon$, the exact least integer cap is

$$T^*(N,\epsilon)=\left\lceil\frac{N(1-2\epsilon)}{1-\epsilon}\right\rceil.$$

With probability $\epsilon$, answer that the oracle is punctured immediately. Otherwise choose a uniformly random $T^*$-subset of the $N$ rows and check it. A discrepancy identifies a punctured function. With no discrepancy, answer $H$. The reference error is $\epsilon$ and each punctured error is $(1-\epsilon)(1-T^*/N)\le\epsilon$. Equivalently, for an integer cap $0\le T\le N$, the optimal error is $(N-T)/(2N-T)$.

**Worst-case expected queries.** The expected number of queries on $H$ is at least $N(p-\epsilon)\ge N(1-2\epsilon)$. With probability $\epsilon$ each, guess $H$ or a punctured oracle immediately. Otherwise scan all rows until a discrepancy appears. This uses at most $N(1-2\epsilon)$ queries in expectation on each oracle and exactly that on $H$, with error $\epsilon$ on each. No rounding is needed for expected cost.

At error $1/3$, the hard cap is $N/2$ and the worst-case expected cost is $N/3$. Thus a budget of 58 rows fails for exact queries already at $n=6$, and for a hard cap with error $1/3$ at $n=7$. The query bounds concern an oracle whose representation is hidden. In the displayed CNFs the rail choices are explicit, so a procedure reading the encoding can recover the missed row directly.

## A sharp bound for satisfiability with a 2-CNF restriction

Let $B_k=\bigwedge_{i=1}^k(\neg u_i\lor\neg v_i)$ for $k\ge1$. Every rail is individually feasible, and two rails conflict exactly when they belong to the same pair. Thus the conflict graph consists of $k$ disjoint edges and has minimum vertex cover size $k$. Its $2^k$ maximal models set exactly one rail per pair to one.

Given membership access to a monotone $f$, consider deciding whether $B_k\land f$ is satisfiable. Put $f_{\mathrm{base}}=\bigvee_i(u_i\land v_i)$ and $f_\sigma=f_{\mathrm{base}}\lor\bigwedge_i\ell_i$, with one selected rail $\ell_i$ per pair as above. The base function is false on all models of $B_k$. The function $f_\sigma$ agrees with the base function outside $B_k$, where the base is already true, and differs inside $B_k$ only at the model that turns on exactly the selected rails. Every maximal model is such an exceptional row for one $\sigma$.

The same transcript argument therefore applies even if queries may use any row of the full cube. The exact cost is $2^k$, attained by querying all maximal models. With error $\epsilon$ on each oracle, the matching hard cap and worst-case expected costs above hold with $N=2^k$.

## Reproduce

```sh
python -B check.py
lean QueryTrace.lean
```

The Python check uses only the standard library. It compares all retained truth assignments and every nontautological signed binary implicate for 120 punctured functions with $3\le n\le6$. It directly enumerates hidden assignments for 56 of the encodings with $3\le n\le5$.

For $N=8$, the script enumerates all subsets that a deterministic protocol can query on its reference transcript and both terminal answers. After a hit the protocol can answer immediately, so its reference subset and answer determine its pair of errors. The exact convex hull of these error pairs gives the finite randomized optimum for every cap from 0 to 8. A uniformly random permutation of candidate rows makes the average punctured error equal to each individual punctured error, with reference error and cap preserved. The computed errors are $1/2,7/15,3/7,5/13,1/3,3/11,1/5,1/9,0$. Both matching strategies also pass exact rational checks.

The Lean file formalizes reference-transcript indistinguishability and the deterministic length bound for any finite decision tree and list of distinct puncture rows. Direct checking was done with Lean 4.36.0.
