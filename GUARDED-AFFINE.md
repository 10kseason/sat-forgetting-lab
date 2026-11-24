# When do pairwise checks decide a system of optional parity equations?

Each Boolean selector independently activates a bundle of equations over hidden bits in GF(2). A support is the set of enabled selectors. It is **feasible** when one hidden assignment satisfies every active equation and the unconditional affine background. It is **pairwise admissible** when all its subsets of size at most two are feasible. This includes the empty set. **Pairwise exactness** asks whether every admissible support is feasible.

For instance, activating any two of `x=0`, `y=0`, and `x+y=1` is feasible. Activating all three is impossible. In both this example and the SAT reduction below, turning every selector off is feasible. The decision problem concerns *all* supports.

| Restrictions | Recognition of pairwise exactness | Evidence |
|---|---|---|
| One equation per selector, optional unconditional affine background | Polynomial time. The algorithm counts feasible maximal admissible supports and returns a minimal obstruction when exactness fails. | [종이] below · [테스트] [truth tables](test_guarded_affine.py) |
| Two equations per selector, empty background | coNP-complete, even with one unit and one equation of width at most two per selector. | [Lean] [semantic reduction](Formal/GuardedPath.lean) · [종이] size, padding and membership below · [테스트] [encoding](test_guarded_affine.py) |

## One equation per selector

An inconsistent unconditional background excludes even the empty support. Otherwise use Gaussian elimination to express every optional equation on the free coordinates of the background. Eliminate each pivot in descending order and carry its right-hand side along. A row reducing to `0=0` is always available. A row reducing to `0=1` is individually forbidden. For nonzero rows, two selectors conflict exactly when they have identical reduced coefficient vectors and opposite right-hand sides. Two different nonzero vectors are linearly independent over GF(2).

Group the remaining selectors by reduced coefficient vector. A **fixed** group has just one observed right-hand side. A **flexible** group offers both. A maximal admissible support contains all tautologies, all selectors from every fixed group, and every selector on one chosen side of each flexible group. This description accounts for duplicate and complementary input rows. With $q$ flexible groups there are exactly $2^q$ maximal admissible supports.

Let $Fx=f$ contain one representative of each fixed group and let $V$ contain one coefficient vector per flexible group. If $Fx=f$ is inconsistent, zero maximal supports are feasible. Otherwise choose any solution $x_0$. The attainable right-hand sides on the flexible groups form $Vx_0+V(\ker F)$. Its dimension is

$$
d = \operatorname{rank}\begin{pmatrix}F\\V\end{pmatrix} - \operatorname{rank}(F).
$$

Indeed the kernel of the map from $\ker F$ to flexible syndromes is $\ker F\cap\ker V$, so rank-nullity gives the difference. Exactly $2^d$ maximal supports are feasible. Feasibility is closed under taking subsets, hence the pairwise check is exact precisely when $d=q$ and the fixed system is consistent.

When $d<q$, some coordinate vector lies outside the image of $\ker F$, since those vectors span the whole target. Flip each coordinate of $Vx_0$ in turn and check consistency to find a forbidden syndrome in polynomial time. When the fixed system is already contradictory, its fixed representatives suffice. Starting from either obstruction, try removing each selector and keep the removal if the rest remains inconsistent. Monotonicity gives an inclusion-minimal obstruction with at least three selectors. The counts use at most $q+1$ bits. [Reference implementation](guarded_affine.py)

The assumptions matter. If an arbitrary constraint on selectors excludes a bad support, exactness *relative to that constraint* may hold. A non-affine background on hidden bits can also break the rank argument.

## Two equations per selector

Start with a CNF $C_0,\dots,C_{m-1}$. While $m<3$, append a positive unit on a fresh variable. This preserves satisfiability. Make a path of $m$ edges with endpoint values fixed to 0 and 1. Its $m-1$ internal vertices are hidden bits. Stage $j$ demands equality between consecutive vertices. Substituting endpoint constants into the first and last equations leaves no mandatory background. All stages together are inconsistent. Any proper subset is feasible by changing the path from 0 to 1 at a missing edge.

For **each literal occurrence** in clause $j$, create a selector activating two equations. One fixes the truth bit of the literal's variable to the value satisfying that occurrence. The other demands equality on stage $j$. Repeated occurrences keep separate selector identities. Variables share a single truth bit across all of their occurrences.

* Any two selectors touch at most two of the $m\ge3$ stages. They conflict exactly when they demand opposite values of the same truth variable.
* In a pairwise-admissible support every selected literal can be made true simultaneously. Thus the whole support is infeasible exactly when it touches every stage.
* If such a support exists, its truth values extend to an assignment satisfying every original clause. Conversely a satisfying assignment supplies a true occurrence for every clause. Selecting these gives a pairwise-admissible but infeasible support.

This proves SAT iff pairwise exactness **fails**. An empty clause has no selector on its stage and cannot be covered. An empty input formula becomes satisfiable padding. There is one selector per occurrence and at most a constant amount of padding. The reduction is linear in declared variables, clauses and literal occurrences when each row is stored as up to two variable indices. The reference code uses dense integer bit masks and still takes polynomial space and time. Non-exactness is in NP because the proposed support, every activated singleton and pair, and the whole active system can all be checked by polynomial-time Gaussian elimination. Taking complements gives coNP-completeness. [Lean equivalence for three or more stages](Formal/GuardedPath.lean) · [Executable encoder](guarded_affine.py)

For a concrete example take the clauses $(u),(v),(\neg u\lor\neg v)$. The path has three stages. Each individual stage can be selected, but covering all three would force $u=v=1$ and one of them to be 0. Here every pairwise-admissible support has a hidden witness. Replacing the last clause with $(u\lor v)$ makes the support selecting $u,v,u$ a three-selector obstruction.

## How many pair conflicts per occurrence?

Keep the occurrence-path representation above, including its stage labels. When its pair-conflict graph has maximum degree one, create a resource for each conflict edge and each isolated occurrence. Join a stage to the resources of its occurrences. A matching covering every stage selects one occurrence from each clause without using opposite signs. Conversely any consistent cover can keep exactly one occurrence per stage, which uses distinct resources and yields a matching. An augmenting-path search therefore decides whether there is a gap in polynomial time and returns a satisfying assignment when there is one. A pure variable may occur arbitrarily often since each such occurrence has a private resource. [Implementation and witness checks](test_guarded_affine.py)

Maximum degree two already suffices for coNP-hardness in this representation. Copy each literal occurrence to a fresh variable. For each source variable with two or more occurrences, join its copies in a directed implication cycle so their truth values must coincide. Then complement the coordinates of copies whose source occurrence was negative. This leaves exactly one positive occurrence per copy in the copied source clauses. In the cycle each participating copy has one occurrence of each sign. The construction preserves satisfiability even for a two-copy cycle. A singleton needs no cycle. Substituting this CNF into the path construction yields pair-conflict components that are isolated vertices or three-vertex paths. Fresh padding units contribute isolated vertices. The cycle is Tovey's bounded-occurrence SAT construction. [Tovey, Theorem 2.1 and §3](https://cedric.cnam.fr/~bentzc/INITREC/Files/CB11.pdf) · [Sign-oriented implementation](guarded_affine.py)

Stage incidence is essential. For example, $(x\lor y),(\neg x),(z)$ is satisfiable and $(x),(\neg x),(y\lor z)$ is unsatisfiable. Both give the same unlabeled graph consisting of one edge and two isolated vertices.

### A fractional cover misses arbitrarily long contradictions

Can fractional occurrence weights replace choosing a sign at a three-vertex component? Give each occurrence a weight between zero and one, require a total of at least one in each stage, and bound the sum at the ends of each conflict edge by one. Whenever every clause contains at least two occurrences, setting every weight to one half is feasible.

For any positive $k$, take two clauses forcing $x_0$ true through opposite signs of a fresh $b$, the $k$ implications $x_i \to x_{i+1}$, and two clauses forcing $x_k$ false through opposite signs of a fresh $c$. Every clause has two literals. The conflict graph has just two three-vertex paths, one per endpoint variable, and isolated conflict edges for the other variables. All stages have a fractional cover. An integral cover would have to carry true along the chain and is impossible.

Dropping an implication lets the truth value change at its missing edge. Dropping one of the first two clauses lets all chain variables be false and the remaining first clause chooses $b$. Dropping one of the last two lets all be true and the remaining last clause chooses $c$. Therefore every proper subset of stages admits an integral cover, even for arbitrarily long chains. This refutes this particular linear relaxation and any check based solely on integral feasibility of bounded-size stage subsets. The examples themselves are decidable by 2-SAT. [Checked instances](test_guarded_affine.py)
