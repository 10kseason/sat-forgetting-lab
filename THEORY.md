# Projecting a CNF through upper bounds

Let $x$ be the retained variables and $h$ the hidden variables. Keep a background 2-CNF $B(x)$. Outside the background, allow at most one negative hidden literal per clause. A clause containing $\neg h_i$ is an upper bound $h_i\Rightarrow D$, with tail $D$ a disjunction of signed retained literals and **positive** hidden variables. Clauses with positive hidden occurrences only are called goals. Remove tautologies first. An empty goal, an empty tail and a head without a rule are all allowed.

## One retained assignment

Fix $x$. Define $T(v)_i$ to be the conjunction of the tails for head $i$, evaluated at $(x,v)$. The empty conjunction is true. $T$ is monotone in the hidden vector. Starting at all true, iterate $T$ downwards. Each strict step loses a head, so there are at most as many strict steps as heads. Every vector satisfying the bounds has $v\le T(v)$. Induction shows it is below every iterate and hence below the fixed point $v^*$. This proves $v^*$ is the greatest feasible vector for the rules. Since every goal is monotone in the hidden variables, $x$ has a satisfying extension exactly when $B(x)$ and the goals hold at $v^*$. This constructs the extension.

Two tails on the same head can be compared before evaluating $x$. If $B\models D_1\Rightarrow D_2$, retain the stronger $D_1$. Try making each literal of $D_1$ true together with every literal of $D_2$ false. Each test is 2-SAT with units, including when the tails mention hidden variables. Keep one representative of equivalent tails and all incomparable minimal tails. Transitivity preserves all discarded bounds.

## One choice per head

A policy selects one remaining rule for each head with rules. A head with no rules stays unrestricted. Deleting the other rules can only raise the greatest vector; denote the new vector by $v^\pi$. For every **fixed** $x$, some policy satisfies $v^\pi=v^*$ on all heads simultaneously. Give each losing head the round when it first became false. Select a tail that was false in the preceding iterate. Its retained literals are false and each hidden successor lost in a strictly earlier round. Induction on that round excludes the head from every feasible vector of the selected rules. The original winners survive any selection.

The policy achieving equality may depend on $x$. Nevertheless, a monotone goal is true at $v^*$ exactly when it is true at $v^\pi$ for every policy. Only the heads reachable from the goal in the union of the dependency graphs can affect it.

For a fixed policy, draw an arc from each bounded head to each hidden successor in its selected tail. The greatest value of a head is true if and only if it can reach an unrestricted head, a directed cycle, or a true retained literal. In the first two cases one can set the heads on the path, and on the cycle, true. In their absence the reachable graph is a DAG, and backwards substitution yields the OR of its reachable retained literals. A cycle in the union of several alternative rules does not alone certify a true head.

For each goal $Q$ and a selection on its reachable heads, output the disjunction of its own retained literals and the reachable retained literals. Omit the clause when the goal is always true for that selection. Keep the background. This gives a pointwise exact CNF projection.

For a satisfiable background let $r_i$ denote the number of surviving rules at head $i$ and $C(Q)$ the heads reachable from goal $Q$ in the union graph. The algorithm examines exactly

$$K=\sum_Q\ \prod_{i\in C(Q)}\max(1,r_i)$$

selections. Besides $B$, it outputs at most $K$ clauses. After removing tautologies and duplicate literals, each has at most as many literals as retained variables. The preliminary 2-SAT tests and the work per selection are polynomial in the explicit input size. A polynomial bound on $K$ therefore gives a polynomial **construction** of the projection. SAT of the resulting retained CNF still has to be decided. Binary output together with the 2-CNF background can be decided in polynomial time.

The selections must be independent. With a goal $h_1\lor h_2$ and bounds $h_1\Rightarrow a,b$ and $h_2\Rightarrow c,d$, the projection is $(a\land b)\lor(c\land d)$. Tying the two choices omits mixed selections. The assignment $a=d=0,\ b=c=1$ passes both tied tests and fails the original.

### A tight family

Take a goal $\bigvee_i h_i$ and bounds $h_i\Rightarrow a_i,\ h_i\Rightarrow b_i$, all retained variables distinct. The exact projection is $\bigvee_i(a_i\land b_i)$. A binary OR tree of fresh bounded heads and a positive root unit encode the wide goal in linear size and width three. Those extra heads have only one rule each. There are $2^k$ selections on the $k$ original heads.

At each of the $2^k$ assignments with exactly one zero per pair the projection is false. The coordinatewise OR of any two distinct such assignments is true. If one clause were false on both assignments, all its literals would also be false on their OR, even for signed clauses. Every equivalent CNF over the retained variables alone therefore needs at least $2^k$ clauses. The algorithm produces exactly that many.

## The strongest binary relaxation

Suppose all occurrences of each retained variable in rules and goals have the same sign. Orient that variable accordingly. The projected goals now give a monotone function $g$ of the oriented retained inputs, ignoring the separately enforced background $B$. A positive clause with variable set $S$, $|S|\le 2$, is entailed exactly when $g$ is false on the largest assignment falsifying it: precisely the variables in $S$ are zero. Each evaluation uses the descending iteration. At most $1+n+\binom n2$ evaluations are needed for $n$ retained variables.

Denote the conjunction of all such entailed clauses by $E_2(g)$. If $g$ entails a nontautological signed clause it also entails the positive part: set all variables occurring negatively to true. This preserves $g$ and the positive literals, and falsifies all negatives. Thus $g$ has an equivalent signed 2-CNF exactly when $g=E_2(g)$.

Solve $B\land E_2(g)$ by 2-SAT. An unsatisfiable relaxation proves UNSAT; a model extendible by the greatest hidden vector proves SAT. If the model does not extend, greedily turn oriented zero coordinates to one as long as $g$ remains false. The remaining zeros form a prime implicate of width at least three that separates the model from $g$. The original SAT instance may still have another model. When $g$ has a binary representation the algorithm always decides. The [implementation](binary_envelope.py) reports the third outcome as **UNRESOLVED**.

## Recognizing exact binary compression

For these acyclic syntactically positive systems with empty background, recognizing $g=E_2(g)$ is **coNP-complete**. Non-exactness has an NP witness: evaluate the polynomially constructible envelope and the greatest hidden vector on a retained assignment with $E_2(g)=1,\ g=0$.

For hardness start from any 3-CNF $\varphi$. For each literal $\ell$ provide a positive retained variable $u_\ell$. Include three fresh positive guards $t_1,t_2,t_3$. Define

$$H=\bigwedge_i(u_{+i}\lor u_{-i}),\qquad
g=H\land\left(t_1\lor t_2\lor t_3\lor
       \bigvee_{C\in\varphi}\bigwedge_{\ell\in C}u_\ell\right).$$

With at most two zeros, a guard is true. Hence $g$ and $H$ have the same positive empty, unit and binary consequences, giving $E_2(g)=H$. An assignment with $H=1,\ g=0$ chooses, through its zero variables, a consistent set of literals hitting each clause of $\varphi$. Extend this set to a satisfying assignment. Conversely, make the variables for the true literals of a satisfying assignment zero, the other variables one, and all guards zero. This produces $H=1,\ g=0$.

Implement AND with two rules $h\Rightarrow a,\ h\Rightarrow b$, and OR with one rule $h\Rightarrow a\lor b$. Use binary trees and a positive root unit. Retain the matching clauses directly. This yields a linear-size acyclic width-three instance. Each hidden gate output is used once, so the hidden-only dependency graph is a forest; sharing occurs through the retained inputs. A polynomial-time recognizer for the whole class would decide arbitrary 3-SAT in polynomial time by negating its answer.

The semantic reduction is kernel-checked in [BinaryExactness.lean](Reductions/BinaryExactness.lean). Complexity class membership, encoding size and running times are paper arguments. The [tests](test_research.py) also compare the Python encoding with its closed form.
