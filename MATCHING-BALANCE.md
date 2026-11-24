# When every solution is half-and-half in every block

Consider positive not-all-equal 3-SAT (NAE) on a linear triple system. The input supplies four perfect matchings of triples, each partitioning the same vertices. This class is NP-complete. We give a parsimonious reduction to instances of the same class in which **every proper coloring has exactly six vertices of each color in every designated block of twelve**. The block partition can be supplied. The construction uses four times the input's vertices and triples. [Hard source problem, Darmann, Döcker and Dorn, Theorem 3.6](https://arxiv.org/html/2412.03395v3) · [Related work](RELATED-WORK.md)

The quantifier over solutions matters. Merely asking for the existence of a globally balanced solution permits a simpler construction: take two disjoint copies and color the second by the complement of the first. Here even choosing a different solution cannot disturb any individual block's balance.

## The finite calculation

Number twelve physical vertices from 0 to 11. The following lists partition the vertices into four matchings before any triple is opened. In each of the first three rows, the bold triple marks the external ports.

| Matching | Triples |
|---|---|
| First | (0,7,9), (1,2,8), **(3,4,11)**, (5,6,10) |
| Second | (0,4,8), **(1,6,7)**, (2,3,10), (5,9,11) |
| Third | **(0,2,5)**, (1,4,9), (3,6,8), (7,10,11) |
| Fourth | (0,1,11), (2,4,6), (3,5,7), (8,9,10) |

Remove the three bold triples, leaving thirteen internal constraints. Let $p=x_3,\ q=x_4,\ r=x_{11}$. All $2^{12}$ assignments are covered by the finite calculation. The six satisfying cases, with vertex 0 as the least significant bit, are as follows.

| $pqr$ | Physical mask |
|---|---|
| 001 | bc4 |
| 010 | 5b2 |
| 011 | 9b4 |
| 100 | 64b |
| 101 | a4d |
| 110 | 43b |

Each nonmonochromatic input has exactly one extension, and each extension has weight six. Reading the ports in the orders **(3,4,11)**, **(7,6,1)** and **(0,5,2)** gives $(p,q,r)$, $(\neg p,\neg q,\neg r)$ and $(p,q,r)$, respectively. The finite propositions in Lean are evaluated by its kernel. [Finite model classification](Formal/MatchingBalance.lean) · [Three-port interface](Formal/BalancedSubstitution.lean)

## Wiring a general instance

Choose the first of the source's four matchings. Create one block per triple in it and use its three source vertices as $p,q,r$. For each of the three other source matchings, replace each vertex occurrence with its corresponding physical port, using one port row per matching. Keep the thirteen internal constraints of each block. A triple in the middle external matching reads all three colors complemented, which preserves NAE.

The internal triples and wired triples reproduce four perfect matchings. In the first three output classes the internal rows cover nine vertices per block, and the corresponding external matching uses each of the remaining three ports exactly once. The fourth class covers every vertex internally. Each external triple meets three distinct blocks because the source is linear. It meets any internal edge in at most one vertex. The physical port sets of different external classes are disjoint, and edges of each external class are disjoint. Internal edges are linear by inspection of the table.

Lifting a source coloring uses the six-entry table independently in each block. Projecting a target coloring reads its $p,q,r$ and recovers the source coloring. These maps preserve satisfiability and are inverse on models. With $m$ source triples in each matching the input has $3m$ vertices and $4m$ triples. The target has $12m$ vertices and $13m+3m=16m$ triples. The implementation constructs it in polynomial time. [Lean model maps and inverses](Formal/BalancedSubstitution.lean) · [Encoder and decoder](matching_balance.py)

Thus on the stated promise, deciding SAT is NP-hard and a coloring is a polynomial certificate for a YES input. Alternatively, restrict the input syntax to the displayed blocks and their well-formed port wiring; the shape is directly checkable given block coordinates, and SAT on that syntactic class is NP-complete. No recognition of a universal semantic promise is needed for the reduction. The Lean theorems verify the model correspondence and block weights. The structural restrictions, size accounting and complexity consequence follow from the argument above.

## The failed uniform-majority shortcut

On $3m$ vertices, let a proper coloring have $w$ vertices of color 1. In *each* perfect matching exactly $w-m$ triples have two vertices of color 1, since each contributes one or two. Requiring a common majority color throughout even one matching, up to global complement, therefore forces $w=m$. The minority vertices must meet every triple of all four matchings exactly once. This exact-transversal problem is itself NP-complete at four classes. [Döcker et al., Theorem 5.5, preprint](https://arxiv.org/html/2611.31145v1)

The full twelve-vertex example above has six proper colorings, all of weight six. Every matching has two triples of each majority. Its incidence matrix also has rank 12 over GF(2); the only odd-incidence vector is all ones, which cannot be a size-four transversal. Joining copies after removing just the first bold triple gives connected examples of arbitrary size: in block $i$ replace (3,4,11) by (3 in $i$, 4 in $i$, 11 in the next block), cyclically. Removing that single triple preserves the six local models and repeating any of them gives a global coloring. All proper colorings have weight six in each block. [Generator and checks](test_matching_balance.py)

## Can we undo the construction after removing every label?

Yes. The default DIMACS solver can recover the smaller positive NAE instance from paired all-positive/all-negative ternary clauses even after permuting every variable, changing the order of every clause and withholding the block partition and the four matching labels. The guarantee is for images of this construction. On other inputs the implementation contracts only when it can verify a model-preserving reduction, or falls back to the other solver routes. [Recognizer](anonymous_blocks.py) · [DIMACS entry point](solve_cnf.py)

Make a graph on variables by joining the three pairs in each triple. The 13 internal triples give 39 internal pairs. Among these, 6 have two common internal neighbors, 12 have three, 15 have four and 6 have five. These internal pairs connect the whole block. An external adjacent pair has exactly one common neighbor in the full graph: the third vertex of its external triple. Its endpoints belong to different blocks, and each is in only that one external triple. Therefore the connected components of the graph retaining edges with at least two common neighbors are exactly the original blocks. The vertex degree is eight, so neighborhoods have constant size.

Within each recovered block evaluate just its internal triples on the 4,096 bit patterns. Each vertex has a six-bit column recording its values on the six valid states. Identical or complementary columns form three classes. Choosing representatives produces six different three-bit words whose two missing words are complements. Complement the coordinates of either missing word to normalize those missing words to 000 and 111. Each physical vertex is now a signed copy of a known logical variable. By the truth table this change of variables is a bijection between that block's states and a single NAE triple.

Replace every external triple with its three signed copies and include the single positive NAE triple for **each block**. Solve the binary parity equations asking for a variable complementation that makes all three signs agree in every triple. Including the block triples ensures the three local signals are switched consistently. A true image admits the original polarity conventions. Each resulting NAE triple can drop its common sign. This yields the original unsigned hyperedges up to variable renaming. Recovering the names of the source matchings is unnecessary. The local finite tables also give an explicit map for lifting a satisfying assignment and checking it on the original CNF.

At fixed degree and block size the graph traversal, finite checks per block, and sign propagation take linear work in the number of vertices and triples with ordinary bounded-index graph operations. When the input was inflated repeatedly, each successful pass divides its vertex count by four. The total work of the contractions forms a geometric series. This removes construction overhead; the recovered core can still be an unrestricted member of the NP-hard source class.

An independently scrambled five-level instance descended from the affine plane on 9 vertices had 9,216 variables. It reduced to the 9-vertex core and the cut certificate decided UNSAT with zero assignment trials. A second five-level instance, descended from the twelve-vertex SAT example, had 12,288 variables. A core witness lifted all the way to a checked model of the original CNF. The executable supports a baseline comparison via the `--no-blocks` option. [Tests and reproducible examples](test_anonymous_blocks.py)
