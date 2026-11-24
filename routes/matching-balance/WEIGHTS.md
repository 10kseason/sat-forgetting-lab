# Can weighting the incidence equations reveal a coloring?

Multiplying an entire row by a nonzero scalar leaves its kernel unchanged. Changing the relative weights of vertices *within* a row can affect its kernel. This experiment uses exact rationals. Its conclusions about rank do not transfer to characteristic three.

## Exact partial assignments

Give each incidence of a positive NAE triple a positive rational weight, and form the weighted incidence matrix $M$. Any nonzero vector $x$ with $Mx=0$ gives a partial proper coloring: assign the signs of its nonzero coordinates. Every triple touching the support contains terms of both signs, so it is already satisfied whatever happens on the unassigned vertices. Remove those triples and repeat. A model of the remaining formula extends using the fixed signs. Conversely any original model satisfies the untouched triples. This preserves the decision problem; the number of models may change. Each nonempty step eliminates a variable and rational Gaussian elimination is polynomial. Such partial assignments are known as linear autarkies. [Implementation](../../linear_autarky.py) · [Tests](../../test_linear_autarky.py) · [Kullmann and Zhao, §1.6.3](https://arxiv.org/abs/1408.0629)

For example, a triple attached to a rigid core through one vertex can be satisfied by assigning opposite signs to its other two vertices and leaving the core alone. A completely removed formula supplies a SAT witness. A nonempty residual with full column rank can still be satisfiable.

## One successful schedule among exponentially many

In each triple choose exactly one coefficient to double, leaving the other two equal to one. For any proper coloring the schedule that doubles the minority gives a null vector: encode its two colors as $+1$ and $-1$. Choosing a useful schedule is the unresolved algorithmic step in general.

On the connected [fifteen-point cyclic family](IMBALANCE.md) of size $n=15k$, exactly one of the $3^{20k}$ schedules has any nonzero rational null vector. Its kernel is one-dimensional. The proof uses two properties of that family.

1. Every nonempty partial proper coloring satisfying all touched triples independently must assign **all** vertices. Otherwise take that partial coloring or its complement, and independently take the restriction of either global coloring to the nonempty remaining set. The four combinations all satisfy the formula, contradicting its exact pair of complementary models. Thus every nonzero weighted null vector has full support and its signs are one of the two global colorings.
2. Direct an arc from the minority vertex of each triple to each majority vertex. Complementing a coloring leaves these arcs unchanged. The nineteen-triple interior of the fifteen-point block is strongly connected in this directed sense. The cross triples add arcs from vertex 1 in the next block to vertices 4 and 14 in the current block. The resulting directed cycle of strongly connected blocks is strongly connected.

Let $\mu>0$ be the smallest coordinate magnitude of a nonzero null vector, achieved at $v$. In any triple where $v$ is the minority, doubling a majority would require $|x_v|=2|x_a|+|x_b|\ge3\mu$, which is impossible. Doubling $v$ gives $2\mu=|x_a|+|x_b|$, forcing both neighbors to have magnitude $\mu$. Following the directed arcs forces every magnitude to equal $\mu$. Every row must then double its minority. Conversely that schedule accepts precisely the scalar multiples of the signed coloring. The unweighted matrix also has full column rank over the rationals: at a minimum-magnitude vertex, an outgoing minority row would require $\mu\ge2\mu$.

Uniform independent guesses therefore hit the useful matrix with probability $3^{-20k}$. The explicit input-aware phase algorithm solves this family, so this probability bounds that guessing strategy. [Phase repair](REPAIR.md) · [Finite ranks and directed reachability](dual.py)
