# Forgetting in guarded 2-CNF

Let $F$ be a CNF on a disjoint union of protected variables $R$ and body variables $B$. The task is to compute $\exists Y\,F$ in ordinary CNF on the remaining variables, for any $Y\subseteq B$. A clause is a disjunction of a guard on $R$ and a body of at most two literals on $B$. The guard can be long.

Suppose the input provides $w\ge 1$ inclusion chains of guards. Chain $i$ has $p_i$ signed literal sets $G_{i,0}=\varnothing\subsetneq \cdots\subsetneq G_{i,p_i-1}$. No guard in a chain contains both signs of a variable. The chains may overlap and need not use disjoint variables. Each input clause is labelled by $\alpha=(\alpha_1,\ldots,\alpha_w)$, with guard $D_\alpha=\bigcup_iG_{i,\alpha_i}$. In particular, any input clause whose guard lies in one chain can use a label with only one nonzero coordinate.

## Bound in every elimination order

Write $r=|R|$, $b=|B|$, $k=|Y|$ and

$$P=\frac{\prod_{i=1}^{w}p_i}{\max_i p_i}.$$

After the initial omission of tautologies and subsumed labels, ordinary Davis–Putnam elimination can maintain an equivalent CNF at every step. For every ordering of $Y$, the state after $j$ eliminations has at most $P(1+2(b-j)^2)$ clauses and at most $(r+2)P(1+2(b-j)^2)$ literal occurrences. Counting the initial reduced state and all $k$ results, the cumulative number of literal occurrences is at most

$$ (r+2)P \sum_{j=0}^{k}\bigl(1+2(b-j)^2\bigr). $$

This counts expanded clauses. To include the supplied unreduced input, add its actual literal size. A stream of candidate resolvents needs only the current and partially built next state, plus the guard chains and one candidate at a time. At the step starting with $d$ body variables, there are at most $P^2(2d-1)^2$ pairs of clauses containing opposite signs of the pivot. Since $p_i\le r+1$, the bounds are polynomial for every fixed $w$.

### Proof

At a pivot $y\in B$, keep clauses that omit $y$ and resolve each opposite pair. For a fixed assignment outside $y$, a false positive tail forces $y=1$ and a false negative tail forces $y=0$. Both forces occur exactly when some resolvent is false. Thus the resulting clauses characterize precisely the assignments with an extension to $y$.

The body of a resolvent is the union of two tails of size at most one. Its guard is $D_\alpha\cup D_\beta=D_{\max(\alpha,\beta)}$, where the maximum is coordinatewise. Tautologies can be dropped. For a fixed body, $\alpha\le\beta$ coordinatewise implies $D_\alpha\subseteq D_\beta$, so the clause labelled by $\alpha$ subsumes the one labelled by $\beta$. Retain only the coordinatewise-minimal labels of each body. This rule can be applied to each new resolvent as it arrives because it preserves the conjunction accumulated so far.

An antichain of labels projects injectively onto all coordinates except any one chosen coordinate. Two labels equal on the others would be comparable. Dropping a largest chain bounds the labels per body by $P$. On $d$ variables there are $1+2d+4\binom{d}{2}=1+2d^2$ distinct non-tautological bodies of length at most two, including the empty body. Each surviving guard uses at most one sign of each of $r$ variables. This proves the state and cumulative bounds. A body containing a fixed sign of the pivot has at most $1+2(d-1)$ possible tails, which gives the candidate-pair bound.

## An infinite family with large clauses and hidden primal treewidth

For each $n\ge 1$, keep $a_1,\ldots,a_n,b_1,\ldots,b_n,u_1,\ldots,u_n,v_1,\ldots,v_n$. Hide $\ell_1,\ldots,\ell_n,h_1,\ldots,h_n$. Use the two guard chains $A_i=\{a_1,\ldots,a_i\}$ and $C_j=\{b_1,\ldots,b_j\}$, each starting with the empty guard. The clauses, with a guard set denoting the disjunction of its literals, are

$$ A_i\lor\neg u_i\lor\ell_i,\qquad
   \neg\ell_i\lor h_j,\qquad
   C_j\lor\neg h_j\lor v_j $$

for every indicated index or index pair. The original maximum clause width is $n+2$. The primal graph restricted to the hidden variables is $K_{n,n}$ and has treewidth $n$. For the lower bound, a tree decomposition of width $d$ has a vertex of degree at most $d$, obtained from a leaf bag after removing leaf bags contained in their neighbors. For the upper bound on $K_{n,n}$, take bags consisting of one entire side and one vertex of the other side.

The projection is the conjunction of $A_i\lor C_j\lor\neg u_i\lor v_j$ over all $i,j$. If $u_i$ is true and both guards are false, the three implications force $v_j$. Conversely, set $\ell_i$ when $u_i$ is true and $A_i$ is false, and set all $h_j$ to the disjunction of those $\ell_i$. The projected clauses ensure this assignment satisfies the guarded clauses at the $h_j$. For the order that eliminates all $\ell_i$ then all $h_j$, the state starts with $n^2+2n$ clauses and loses exactly one per step. It performs exactly $2n^2$ opposite-pivot pair resolutions.

## The number of labels per body can be necessary

For two chains of $n+1$ positive prefixes on disjoint variables, use one hidden variable $z_i$ for each $0\le i\le n$. Give the edge $u\to z_i$ guard $A_i$ and the edge $z_i\to v$ guard $C_{n-i}$. Eliminating all $z_i$ yields $n+1=P$ different labels of the same body $\neg u\lor v$. These are the guards $A_i\cup C_{n-i}$.

At $u=1,v=0$, setting every variable outside one such guard to true and all variables of that guard to false falsifies precisely the corresponding clause. Each resulting assignment is maximal among the false assignments under coordinatewise order. Any CNF representing the restricted function needs at least one distinct clause per maximal false assignment. A clause falsified at two such assignments would also be false at their coordinatewise OR, which is strictly greater than both and is true. This argument permits signed clauses.

For fixed $w>2$, equal-length prefix chains of size $p$ on disjoint variables give the same asymptotic dependence on $p$. Choose a largest level of the label grid on which the coordinate sum is fixed. Some level has at least $p^w/(w(p-1)+1)$ labels, since those levels partition the grid. One separate hidden path per chosen label, using its $w$ prefixes as successive guards, produces exactly one final clause per label with the same body. All guards have equal cardinality, so the same maximal-false-assignment argument applies. This establishes the dependence on guard-chain dimensions for a fixed body.

## Unrestricted guard chains can give exponential CNF output

Let $x_0=u,x_m=v$ and hide $x_1,\ldots,x_{m-1}$. For each link $i$ use two clauses

$$ (a_i\lor\neg x_{i-1}\lor x_i)\quad\text{and}\quad
   (b_i\lor\neg x_{i-1}\lor x_i), $$

with all guard variables distinct. The link imposes an implication unless $a_i=b_i=1$. The endpoint implication is forced if all links impose it. If a link is disabled, a sequence that changes from true to false at that link is a witness for $u=1,v=0$. The projection is

$$ \neg u\lor v\lor\bigvee_{i=1}^m(a_i\land b_i). $$

Under $u=1,v=0$, the maximal false assignments set exactly one variable in each pair to true. There are $2^m$ of these assignments, so every ordinary CNF for the projection on the retained variables has at least $2^m$ clauses. The input has width three. Its primal graph has a width-two tree decomposition with bags $\{x_{i-1},x_i,a_i\}$ in a path and bags $\{x_{i-1},x_i,b_i\}$ attached to the corresponding path bags. Its guard family contains $2m$ incomparable singleton sets.

## Reproduce

Run from this directory with Python 3.10 or newer and without optional packages.

```sh
python -B guarded_dp.py
```

The checker compares the truth table of each projected prefix with the truth table obtained by direct existential enumeration. It covers 1,024 formulas from a fixed ten-clause catalogue, both hidden-variable orders, and 6,144 prefix checks. The catalogue includes opposite guard signs, conflicting units, and dominance. Every input also contains two tautologies. The checker validates the two-chain frontier, the exponential path, and the exact output for the wide bipartite family at five sizes. At $n=32$ that family uses 1,024 final clauses, 68,640 cumulative clauses, 1,100,704 cumulative literal occurrences, and 2,048 opposite-pivot pairs.

The proof uses ordinary Davis–Putnam resolution, two-literal resolution closure, and clause subsumption. Its hypotheses specify which variables stay protected and how the guards are presented. The lower bounds on output size concern ordinary CNF on the retained variables.
