# Can a decision diagram compress the Fourier coefficients?

For a function with exactly two complementary models $z,-z$, it can. The coefficient formula in the [ternary experiment](TERNARY.md) needs only the parity of the subset size and the product of the corresponding signs of $z$. A four-state machine reads the subset bits in any order. An exponentially large support need not make the coefficient function hard to represent.

There is also an infinite family of linear, four-round positive NAE instances where **every** variable order requires exponential size for an exact ordered decision diagram for the truth indicator or its ternary Fourier coefficients. On the *same family*, a polynomial-time algorithm finds a checked satisfying assignment even after erasing the names of the parts and rounds. The graph-CNF expander argument has direct antecedents. [Bova and Slivovsky, §4](https://link.springer.com/article/10.1007/s00224-016-9715-z) · [Related work](../../RELATED-WORK.md)

## The positive construction and the hidden witness

Use three parts $A,B,C$ of size $m$, with cyclic indices and $3\nmid m$. In the first three rounds use the triples

$$
(A_i,B_i,C_i),\qquad (A_i,B_{i+1},C_{i+2}),\qquad (A_i,B_{i+2},C_{i+1}).
$$

For $m\ge12$ these rounds are linear. For the fourth, pair $A$ and $B$ by a permutation avoiding the three previous $A$–$B$ matchings. Assign distinct guards from $C$ to these $m$ pairs. Each pair forbids at most six guards previously seen at its two endpoints. Conversely, each guard is forbidden for at most six fourth-round pairs. The bipartite availability graph has minimum degree at least $m/2$ on both sides. For any subset of at most $m/2$ pairs its neighborhood has at least $m/2$ guards; a larger subset meets the neighborhood of every guard. Hall's condition gives a perfect assignment, computable by augmenting paths. All four rounds are perfect matchings, and no vertex pair is repeated.

From the *unlabeled* incidence matrix solve the homogeneous system that the three vertex labels sum to zero modulo three in every triple. Write the labels on the three parts as $a_i,b_i,c_i$ only for this proof. Subtracting the second and third round equations shows $b_i-c_i=d$ independent of $i$. The first equation gives $a_i=c_i-d$, and the second gives $c_i+c_{i+1}+c_{i+2}=0$. Thus $c_{i+3}=c_i$ and $3\nmid m$ forces it to be constant. The kernel consists exactly of the three part constants with their sum zero, a space of dimension two. Every legal fourth round preserves it. Nonconstant solutions give three distinct part labels, so grouping two labels together gives a proper bicoloring.

The solver computes this ternary kernel for a pure positive NAE formula. With nullity two it tests a nonconstant vector, returns a witness only if every triple is rainbow, and checks the final Boolean model against the input. Failure leaves the other solver routes available. [Implementation](../../rainbow_nae.py) · [Scrambled examples](diagrams.py)

## A fourth round with large balanced cuts

The first two $A$–$B$ matchings alone form a cycle through all $2m$ data vertices. For arbitrarily large $m$ with $3\nmid m$, a fourth perfect matching can make every balanced cut of the data graph have linearly many crossing edges. Here is a direct existence argument that keeps the three rounds required by the kernel proof.

Let $\epsilon=1/1000$. There are at most $2\sum_{j\le\epsilon m}\binom{2m}{j}$ sets whose cycle boundary contains at most $\epsilon m$ edges: specify the starting side and the change locations. For a fixed balanced set with $a$ vertices on the $A$ side, the image of those $a$ indices under a random permutation is uniform among the $a$-subsets of $B$. Its symmetric difference with the set's $B$ indices is exactly the set of crossing matching endpoints in $B$. To have at most $\epsilon m$ of them needs $a\in[m/3,2m/3]$, and its probability is bounded by

$$
\frac{\sum_{j\le\epsilon m}\binom{m}{j}}{\binom m a}.
$$

The denominator is at least $2^{\lfloor m/3\rfloor}$. For example $\binom{2r}{r}\ge2^r$ and the middle binomial coefficients are at least $\binom{m}{\lfloor m/3\rfloor}$. The two numerator sums contribute at most $2^{m(2H_2(\epsilon/2)+H_2(\epsilon))+o(m)}$, where $H_2$ is binary entropy. The parenthesized exponent is below 0.025. A union bound shows that the probability of a balanced cut small in both the cycle and the random matching tends to zero.

The expected number of fourth-round pairs colliding with one of the three prescribed data matchings is three. With positive probability the balanced-cut property holds and there are at most twelve collisions. Repair one collision by swapping its permutation image with that of a currently legal index. At most six indices would introduce a forbidden data pair at one of the two positions, and at most twelve indices are currently bad. For $m>18$ there is a legal swap. At most twelve swaps reduce the crossing count of any cut by at most 24. Thus for sufficiently large $m$ each balanced cut retains at least $\epsilon m/2$ crossing edges. Adding guards as above preserves the data graph.

## The representation lower bound

In any order of the $3m$ variables, take the cut just after the $m$-th data vertex. Fix every guard to false. The restricted truth indicator on the data is the monotone graph CNF requiring at least one true endpoint per edge. The balanced cut contains an induced crossing matching of size $k=\Omega(m)$. Greedily select a crossing edge and discard all candidates incident to the closed neighborhoods of either endpoint. In maximum degree four each choice discards at most 40 candidates, and no edges remain between endpoints of different selected pairs.

Fix every other data vertex true. The communication matrix at this cut contains a submatrix for $k$ disjoint OR clauses. Up to row and column order this is the tensor power of the two-by-two matrix with rows $(0,1)$ and $(1,1)$. It has rank $2^k$ over $\mathbb F_3$. Distinct independent rows require distinct residual functions in an exact ordered diagram.

The full coefficient matrix across the same cut is obtained from the full truth matrix by an invertible character transform on the rows and another on the columns, up to nonzero scaling. Their ranks are equal. The restriction argument took place in the truth matrix before this rank transfer. Thus both exact diagrams need exponentially many states. When edges may skip variable levels, the residual pointers can land at later levels; exponential total size still forces exponential maximum level width up to the linear factor for the number of levels. The lower bound concerns materializing the entire function or coefficient table as an ordered diagram. [Finite tensor-rank and witness checks](diagrams.py)
