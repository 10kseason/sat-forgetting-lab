# How close to equal size can two proper color classes be?

In a positive 3-uniform, 4-regular hypergraph with $n\ge15$ vertices, every proper coloring can reach one of weight between $7n/15$ and $8n/15$ by flipping one vertex at a time while keeping all triples proper. Both endpoints are sharp: for every $k\ge1$ there is a connected linear instance with four perfect matchings on $15k$ vertices whose **only two** proper colorings have weights $7k$ and $8k$. The global difference between the two color-class sizes is $n/15$ on this family. [Recoloring algorithm and generator](dual.py)

## The upper bound

Write $w$ for the number of ones and $t=4n/3$ for the number of triples. In a proper coloring each triple contains either one or two ones. If $a$ and $b$ are the counts of these two types, $a+b=t$ and $a+2b=4w$. Thus $a=2t-4w$ and $b=4w-t$.

A vertex can change color while preserving all triples exactly when it is never the sole representative of its color in an incident triple. The number of blocked ones is at most $a$, and the number of blocked zeros is at most $b$. Consequently the number of free ones is at least $5w-8n/3$, and the number of free zeros is at least $7n/3-5w$.

Above $8n/15$ there is a free one to turn off; below $7n/15$ there is a free zero to turn on. Each step decreases the distance to an integer in the target interval. The same argument works whenever the interval contains an integer. Starting from a supplied proper coloring, at most $n$ flips suffice. Finding an initial proper coloring remains NP-hard on the four-matching class. The incidence-count and recoloring argument has a degree-three antecedent. [Erskine, Griggs and Širáň, Theorem 2.2](https://onlinelibrary.wiley.com/doi/full/10.1002/jcd.21773)

## The connected sharp family

In zero-based data row 1062 of the [fifteen-point catalogue](order15.tsv.gz), omit triple $(1,4,14)$. The remaining nineteen triples admit only masks **3263** and **4d9c** in hexadecimal. They are complements and have weights seven and eight. On vertices $(1,4,14)$ the lighter coloring reads $(1,0,0)$; the heavier one reads $(0,1,1)$. The Lean kernel checks all 32,768 assignments. [Local theorem, port implication and path uniformity](../../Formal/MatchingImbalance.lean)

For $k$ copies use the three opened slots in each affected matching to make triples $(4_i,14_i,1_{i+1})$ cyclically. The port with index 1 has the opposite color to the other two in the same block. Hence the new triple is proper precisely when its two blocks have the same choice of local model. Along the cycle every block must choose the lighter model, or every block must choose the heavier model. Both choices work. This proves the two model counts and weights for all $k$.

Each interior is connected; the new triples join consecutive interiors. The wiring uses each opened slot once and keeps the four perfect matchings. The only pair of physical vertices that stays in the same block and is used together in a new triple formerly belonged to the deleted triple, so linearity is preserved. For $k=1$ the wiring restores the source. A cyclic exchange of one incidence is a known construction; the verified two-state interface is what determines the weights here. [Related work](../../RELATED-WORK.md)

## The limits of single flips

For any coloring, let $b$ be the number of monochromatic triples, let $b_v$ count violated triples containing $v$, and let $c_v$ count proper triples in which $v$ supplies the unique minority color. Flipping $v$ changes the number of violations by $c_v-b_v$. At a strict local minimum over all individual flips this is at least one for every vertex. Since $\sum_v c_v=t-b$ and $\sum_v b_v=3b$, one gets $4b\le t-n$. For four-regular triples this bounds violations by $n/12$. A non-strict local minimum need only satisfy $4b\le t$.

Distance inside the proper-coloring graph is a different question. In the twelve-vertex balanced substitution, each of the three logical colors occurs in exactly four physical positions, possibly complemented. Thus the Hamming distance between lifts of two source models is exactly four times their source distance. The number of vertices also quadruples. Repeating $j$ times multiplies both quantities by $4^j$, and every proper model in the image is such a lift. For any fixed $0<\epsilon<1$, choosing $j$ so that $(4^j)^\epsilon>n^{1-\epsilon}$ takes polynomial output size in the source order $n$. Distinct output solutions then differ in more than $N^{1-\epsilon}$ bits for output order $N$. The claim describes distances between satisfying assignments; it gives no bound on search paths allowed to visit violations. [Balanced substitution](../../MATCHING-BALANCE.md)
