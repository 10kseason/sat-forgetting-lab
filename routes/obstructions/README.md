# Small CNFs can have exponential CNF projections

We require the result of forgetting to be an explicit CNF on the variables retained by the projection. Clause counts below permit arbitrary clause width and both signs of every retained variable.

## Parity on a path

For data bits $x_1,\ldots,x_n$, introduce prefix bits $s_1,\ldots,s_{n-1}$. Fix $s_0=0$ and $s_n=b$, with $b\in\{0,1\}$. Impose $s_{i-1}\oplus x_i\oplus s_i=0$ at each position. A parity constraint on $w$ variables has a CNF with one clause excluding each of the $2^{w-1}$ wrong assignments. For $n\ge2$ the chain therefore uses $4n-4$ clauses of width at most three. Its primal graph has a path decomposition with bags $\{s_{i-1},x_i,s_i\}$ after omitting the fixed endpoints. The bags overlap at the prefix bits, giving treewidth at most two.

Given the data, the recurrence determines the prefix bits uniquely and admits an extension exactly when $x_1\oplus\cdots\oplus x_n=b$. Every non-tautological clause implied by this parity contains all $n$ data variables. If it omitted one, there would be an assignment falsifying the clause whose parity could be set to $b$ by changing the omitted bit. A clause containing every variable falsifies at most one assignment. Thus the minimum explicit CNF for the projection has exactly $2^{n-1}$ clauses, each of width $n$. This lower bound applies to the outputs of all exact elimination orders.

## Which prefix bits help

Suppose the retained prefix positions are $0<i_1<\cdots<i_k<n$. Define $i_0=0$, $i_{k+1}=n$ and $\ell_j=i_j-i_{j-1}$. The projection is the conjunction of one parity equation per block,

$$
s_{i_{j-1}}\oplus x_{i_{j-1}+1}\oplus\cdots\oplus x_{i_j}\oplus s_{i_j}=0.
$$

Necessity follows by adding the original equations inside that block. Sufficiency follows by solving for its omitted prefix bits from the assigned left boundary, and the block equation ensures agreement with the assigned right boundary. If $w_j$ counts the block data and the boundary bits retained as variables, the explicit clause count is between $\max_j 2^{w_j-1}$ and $\sum_j 2^{w_j-1}$.

For the lower bound, choose one block and leave its data and its unpinned boundaries free. Set all earlier checkpoints to zero and all later checkpoints to $b$. Set all outside data to zero with two possible exceptions. In an immediately preceding block, identify one data bit with the chosen block's left boundary. In an immediately following block, identify one data bit with the chosen right boundary if $b=0$, or with its negation if $b=1$. Each exception makes the corresponding outside block equation true for either boundary value. These substitutions satisfy every other block identically. Substitution of literals and constants cannot increase the number of explicit clauses, so the parity bound on the $w_j$ variables applies to the original projection.

With $L=\max_j\ell_j$, the bounds in particular lie between $2^{L-1}$ and $(k+1)2^{L+1}$. Along any family of such projections, polynomial clause count is possible exactly when the largest gap is $O(\log n)$. Spacing the checkpoints by $O(\log n)$ uses $O(n/\log n)$ retained prefix bits. With $k=o(n/\log n)$, at least one gap has length $\omega(\log n)$.

## A limit for arbitrary Boolean helpers

Let $C(x,y)$ be any CNF with $M$ clauses, $n\ge1$ data bits and $k$ other Boolean bits, such that $\exists y\ C(x,y)$ is parity. The bits $y$ may be arbitrary helpers. If $r=k+1\le n$, then

$$
M\ \ge\ \frac{r}{2}\,2^{n/r}.
$$

Balanced prefix blocks use at most $r2^{\lceil n/r\rceil+1}$ clauses, within a factor of eight of the lower bound for every such $k$. Polynomial-size explicit CNFs of this kind require $\Omega(n/\log n)$ helper bits, and linear-size explicit CNFs require $\Omega(n)$ helper bits. The proof uses the random-order satisfiability-coding method of Paturi, Pudlák and Zane. Emdin and coauthors already give the balanced prefix construction and the same exponential term in a parity lower bound. The proof here obtains the stated prefactor over the full displayed parameter range. The comparison to earlier bounds and their adjustable parameter is recorded in the literature note. [Emdin et al., Eq. (1) and Theorem 1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol241-mfcs2022/LIPIcs.MFCS.2022.47/LIPIcs.MFCS.2022.47.pdf) · [Detailed comparison](../../RELATED-WORK.md#parity-encodings-and-the-size-bound)

Remove tautologies and repeated literals. For each correct-parity assignment $x$, choose one witness $y$. Flipping a single $x_i$ makes the CNF false with that same $y$. Some clause therefore has the original literal on $x_i$ as its only true literal. Choose one such critical clause for each $x_i$ and write $t_i(x)$ for its number of data variables. A clause can be chosen for at most one data variable at a given assignment, so $M\ge n$.

For a permutation $\pi$ of the data variables, encode each correct-parity $x$ by writing its $k$ witness bits first. Substitute that witness into $C$ and visit the data bits in order $\pi$. When a clause is unit on the current bit after the preceding bits have been set, that clause determines the bit. For any other current bit, append its value to the code. The decoder uses the same order and unit-clause rule. The codes are prefix-free because the witness has fixed length and the decoder stops as soon as it recovers all $n$ data bits. If $u(x,\pi)$ bits were forced, the code length is $k+n-u(x,\pi)$.

For every $\pi$, different codewords have disjoint sets of completions to $k+n$ bits. Thus the sum of $2^{-(k+n-u(x,\pi))}$ over the $2^{n-1}$ correct-parity assignments is at most one. With $x$ uniform on those assignments, this gives $\mathbb{E}_x 2^{u(x,\pi)}\le 2^{k+1}$. Averaging over uniform $\pi$ and applying convexity of $2^u$ gives $\mathbb{E}_{x,\pi}u(x,\pi)\le k+1$. Each $x_i$ is last in its chosen critical clause with probability $1/t_i(x)$ and is forced in that case. Thus, for a uniform data index $i$ and $T=t_i(x)$,

$$
\mathbb{E}_{x,i}(1/T)\le r/n.
$$

A clause of data width $t\ge1$ can be selected only when exactly one of its data literals is true. At most $t2^{n-t}$ data assignments have that property. After restricting to the correct-parity half of the cube and choosing $i$ uniformly, the clause's selection probability is at most $2t2^{-t}/n$. Weight its selection by $2^t/t$ and sum over clauses to obtain

$$
\mathbb{E}_{x,i}(2^T/T)\le 2M/n.
$$

The function $g(v)=v2^{1/v}$ is convex on $v>0$ and decreasing for $0<v\le1/2$. Its second derivative is $2^{1/v}(\ln 2)^2/v^3$, and its first derivative is $2^{1/v}(1-\ln(2)/v)$. If $r/n\le1/2$, Jensen's inequality and the expectation bound on $1/T$ give $2M/n\ge g(\mathbb E(1/T))\ge g(r/n)$. If $1/2\le r/n\le1$, convexity and $g(1/2)=g(1)=2$ give $g(r/n)\le2$, so $M\ge n$ already gives $2M/n\ge g(r/n)$. Both cases yield the stated lower bound.

If an explicit background formula is part of the retained representation, this tradeoff applies to the combined clause count whenever the existential projection of the combined formula is parity.

## A fixed implication background with genuine tail compression

For each $i\in\{1,\ldots,m\}$, retain data $a_i,b_i$ and a tag $t_i$. Use the fixed retained background $B=\bigwedge_i(a_i\to t_i)$. The body has hidden variables $h_i,r_i$, a positive unit $r_1$, and the following clauses written as implications.

$$
\begin{aligned}
r_i&\to h_i\vee r_{i+1} & (i<m),\\
r_m&\to h_m,\\
h_i&\to a_i,\qquad h_i\to b_i,\qquad h_i\to t_i & (1\le i\le m).
\end{aligned}
$$

There are $5m+1$ input clauses including $B$, all of width at most three. A width-two primal decomposition uses path bags $\{r_i,h_i,r_{i+1}\}$ and the final bag $\{r_m,h_m\}$. Attach $\{h_i,a_i,t_i\}$ and $\{h_i,b_i\}$ to the $i$-th path bag. In particular, the background implications fit those attached bags.

Under $B$, the tail $a_i$ implies $t_i$ strictly. The two tails have different variables, so ordinary syntactic subsumption does not remove $h_i\to t_i$. Background-relative dominance does remove it, leaving at most two clauses of either sign on every hidden variable in the original formula. These counts describe both signs after initial tail compression.

The positive unit and root implications force some $h_i$ to be true. Conversely, if $a_i=b_i=1$ for some $i$, set $h_i=1$ and take the root path as far as $r_i$. That choice satisfies the body under $B$. The exact projection, relative to $B$, is therefore

$$
F=\bigvee_{i=1}^m(a_i\wedge b_i).
$$

Setting all tags to one makes $B$ true on every data assignment. Any explicit CNF for the projection relative to $B$ must still represent $F$ on this slice, using at most its original clause count. For each of the $2^m$ assignments with exactly one zero per pair, changing any zero to one makes $F$ true. A clause of the projected CNF falsified at such an assignment must contain the positive literal of every zero position, since flipping any of those positions has to satisfy that clause. The clause then cannot be false on any other witness of this kind. There must be at least $2^m$ clauses. The matching CNF takes all clauses $c_1\vee\cdots\vee c_m$ where $c_i\in\{a_i,b_i\}$.

To relate this to pivot compression, denote by $P_i,Q_j$ the tails of the clauses containing $v,\neg v$ after removing dominated tails within each sign. If $B\models P_i\to P_{i'}$, then $v\vee P_i$ implies $v\vee P_{i'}$ under $B$. The same rule works for the opposite sign. Resolving every retained pair yields the exact projection at $v$. On a fixed assignment to other variables, neither value of $v$ works precisely when some $P_i$ and some $Q_j$ are both false. This is precisely when one resolvent $P_i\vee Q_j$ is false. The background is retained throughout and contains no pivot variables.

Let $p_s,q_s$ be the surviving tail counts at elimination step $s$. For a process that adds clauses by these pivot resolutions and otherwise deletes redundant clauses, the final body has at most $4m+1+\sum_s p_sq_s$ clauses. In this family it has at least $2^m$ clauses, and there are at most $2m$ hidden pivots. Hence some step in every order satisfies

$$
p_sq_s\ge\frac{2^m-(4m+1)}{2m}.
$$

The initial low counts and strict comparisons hold in this family. A polynomial bound on cumulative generated clauses across the entire elimination would fail on this output specification.

## Policy shortcuts and scope

For a head absent from the background and its own tails, retaining one original upper rule is a local equivalence exactly when its tail implies every other tail under $B$. Those implications give all sibling bounds when the head is one. When the head is zero all bounds hold. If an implication fails, set the head to one in a countermodel to satisfy the chosen rule while violating an omitted one. Independent bounds $h\to a$ and $h\to b$ have a common model, yet neither tail implies the other. Context can supply additional reasons to simplify a rule group, so this criterion concerns the local replacement.

Independent choices of one upper rule per head can give $2^m$ policies in the implication family, even with the positive target restricted to a unit. The CNF lower bound shows that this policy product can be tight. If heads share a single policy index, the resulting conjunction can be too weak. With positive $h_1\vee h_2$ and rules $h_1\to a,b$ and $h_2\to c,d$ taken as separate clauses, tying the first/second rule choice across the two heads gives $(a\vee c)\wedge(b\vee d)$. At $(a,b,c,d)=(0,1,1,0)$ it holds while the exact projection $(a\wedge b)\vee(c\wedge d)$ fails. Likewise, a cycle in the union of all rule edges is insufficient for several rules per head. The positive unit $h$ with bounds $h\to q$, $q\to h$, and $h\to x$ projects to $x$.

These are output lower bounds for explicit projection onto a specified interface. A satisfying data assignment for the original parity chain is immediate. The projected parity has a single XOR equation and a linear-size ordered decision diagram that tracks the running parity. Keeping auxiliary variables, using such a representation, and deciding satisfiability of the original CNF are different tasks from writing its exact projected CNF.

## Reproduction

From the repository root, run the standard-library checker with Python 3.10 or later.

```text
python -B routes/obstructions/check.py
```

It compares explicit projections to exhaustive assignments for both parities and checks every full elimination order and every retained checkpoint set up to seven data bits. It also checks the prefix codes over all data orders up to five data bits and every semantically compressed elimination order through three implication blocks. The general lower bounds follow from the proofs above.
