# What does a ternary algebraic test see?

Write a Boolean color as $x_v\in\{-1,+1\}\subset\mathbb F_3$. On a triple $e=\{a,b,c\}$ the sum $L_e=x_a+x_b+x_c$ is nonzero exactly when the triple has both colors. The product $F(x)=\prod_e L_e^2$ is therefore the indicator of a proper coloring. Equivalently one seeks a word $(x,Ax)$ of full support in a ternary linear code, with $A$ the triple incidence matrix. [Fourier, code and finite-field antecedents](../../RELATED-WORK.md)

## Counting by omitted incidences

Since $x_v^2=1$ and $3=0$,

$$L_e^2=-(x_ax_b+x_bx_c+x_ax_c).$$

In expanding $F$, choose one pair per triple. Summing over all choices of signs kills a term whenever some vertex occurs an odd number of times; otherwise the sum is $2^n$. Thus the proper-coloring count modulo three is $2^n(-1)^t$ times the number of pair selections with all vertex counts even, where $t$ is the number of triples. With degree four, this is equivalent to omitting one vertex per triple so that every vertex is omitted an even number of times.

The modular dynamic program tracks these parity masks and the number of ways to reach each, reduced modulo three. Its two bitsets represent residues one and two in a table indexed by $2^n$ masks. On all 13,933 fifteen-point types the three residue counts were **4,653**, **4,706**, and **4,574**, respectively. Residues one and two certify existence. Among the residue-zero instances, 4,544 are satisfiable and 109 are unsatisfiable. Simply finding an even omission pattern is insufficient: pair two rounds by a perfect matching of their cubic bipartite incidence graph, omit the matching variable in both matched triples, and repeat for the other two rounds. This works on every resolved instance. [Dynamic program](ternary.py) · [Catalogue cross-check](ternary_check.py)

## An exact algorithm and its representation cost

Multilinear monomials indexed by subsets are the sign characters of the Boolean cube. Over $\mathbb F_3$ their evaluation table is invertible: the two-by-two table on a single sign has nonzero determinant and the full table is its tensor power. Consequently $F$ is zero on the entire cube precisely when **every** Fourier coefficient is zero. To recover a model from a nonzero coefficient vector, restrict a variable to $+1$ or $-1$ and keep a nonzero restriction. At least one exists by the same two-by-two identity. After all variables are fixed the indicator equals one. Sparse multiplication is polynomial if every intermediate support is polynomial in the input size. The optional term cap returns UNKNOWN when exceeded. [Reference solver](ternary.py)

There is an explicit obstruction to that size guarantee. The connected $15k$-vertex [imbalance family](IMBALANCE.md) has exactly two complementary models $z,-z$. Its coefficient at $S$ is $2^{-n}\chi_S(z)(1+(-1)^{|S|})$. Exactly $2^{n-1}$ coefficients are nonzero, even though the instance has a short cyclic description.

## Two failed shortcuts

**A skew matrix.** Give each clause one matrix index. At each variable add a skew four-clique on its incident clauses, with sign chosen by the global order of the four rounds. Between any two rounds its incidence block sums to three in every row. Over $\mathbb F_3$ the indicator of each nonempty round is therefore in the kernel, so the Pfaffian vanishes on all nonempty instances, including ones with nonzero model count modulo three. Arbitrarily reordering the four ports locally can make the skew matrix full rank even on the unsatisfiable nine-point affine plane. The test checks a specific ordering. An unsigned count needs its own sign argument. [Rank control](ternary_check.py)

**Modular counts under sparse pins.** Data row 18 of the [catalogue](order15.tsv.gz) has 24 proper models even after removing (0,1,2), and vertices 0 and 2 have opposite colors in all of them. Join $k$ copies by triples $(0_i,2_i,1_{i+1})$ cyclically. The joins always hold independently of neighboring colors. The interiors are connected, all four rounds remain perfect matchings, and the global model set is exactly the product of the $k$ local sets. One coordinate pin leaves 12 models in its block. Fewer than $2k$ coordinate pins leave at least one block with zero or one pin, so the restricted global count is zero modulo three. Pinning vertices 0 and 1 to zero in every block leaves exactly one global model. This is a limit on the information provided by those restricted count residues. [Pin checks](ternary_check.py)

## Matrix evaluations with fixed commuting involutions

Replacing each sign variable by a commuting matrix $T_i$ with $T_i^2=I$ over a characteristic-three field still tests ordinary sign assignments. Each matrix splits into its two eigenspaces because $X^2-1$ has distinct roots in that field. Commutativity preserves these subspaces and inductively gives a common eigenbasis. In that basis $F(T)$ has entries given by at most the dimension's worth of ordinary sign evaluations.

Take all vertex renamings of the connected two-model family on $n=15k$ vertices. Its lighter model can be *any* size-$7k$ subset and its complement is the only other model. These give $\binom{15k}{7k}$ disjoint pairs of assignments. Any input-oblivious collection of matrix tests required to produce a nonzero evaluation on every relabeling needs at least that total dimension. This only bounds fixed probes of the full indicator. The explicit clauses can be inspected and the construction has the efficient phase decoder described in the repair note. [Linear-algebra antecedents](../../RELATED-WORK.md) · [Input-aware repair](REPAIR.md)
