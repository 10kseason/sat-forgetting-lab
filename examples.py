"""Repeatable examples from the policy and binary-envelope results."""

from itertools import combinations

from binary_envelope import binary_envelope, decide_with_envelope, recognition_instance
from forgetting import HiddenCNF
from frontier_sat import solve_frontier


def matching_instance(k, *, switch=False, background=()):
    """Width-three encoding of OR_i(a_i AND b_i)."""
    if k < 1:
        raise ValueError("expected a positive matching size")
    retained = 2*k + int(switch)
    heads = list(range(retained+1, retained+k+1))
    clauses = [(-h, v) for i, h in enumerate(heads) for v in (2*i+1, 2*i+2)]
    current = heads[0]
    for i, h in enumerate(heads[1:], 1):
        root = retained + k + i
        clauses.append((-root, current, h))
        current = root
    clauses.append((current,))
    if switch:
        clauses.append((retained,))
    return HiddenCNF(retained, 2*k-1, clauses, background)


def dense_guarded(n):
    """Hidden primal clique, and n alternative rules per head before compression."""
    q = range(n + 1, 2*n + 1)
    background = [(-v, v+1) for v in list(q)[:-1]]
    heads = range(2*n+1, 3*n+1)
    bounds = [(-h, i, v) for i, h in enumerate(heads, 1) for v in q]
    return HiddenCNF(2*n, n, bounds + list(combinations(heads, 2)), background)


def main():
    print("Matching family: k, policies, projected clauses")
    for k in (1, 2, 4, 8, 10):
        projection = matching_instance(k).project()
        assert len(projection.clauses) == projection.policies_examined == 2**k
        print(k, projection.policies_examined, len(projection.clauses))
    print("Guarded clique: n, rules before/after, policies, output clauses including background")
    for n in (4, 8, 16):
        result = dense_guarded(n).project()
        pairs = n*(n-1)//2
        assert (result.rules_before, result.rules_after, result.policies_examined) == (n*n, n, pairs)
        assert len(result.clauses) == pairs + n - 1
        print(n, result.rules_before, result.rules_after, result.policies_examined, len(result.clauses))
    cycle = HiddenCNF(1, 2, [(-2, 3), (-3, 2), (-2, 1), (2,)])
    assert cycle.project().clauses == ((1,),)
    print("Cycle with an independent blocking rule projects to", cycle.project().clauses)
    forced_guard_failure = HiddenCNF(3, 0, [(1, 2, 3)], [(-1,), (-2,), (-3,)])
    decision = decide_with_envelope(forced_guard_failure)
    assert decision.status == "UNRESOLVED" and decision.wide_prime == (1, 2, 3)
    print("Wide prime returned by binary relaxation:", decision.wide_prime)
    s = recognition_instance(2, [(1, 2), (-1,), (-2,)])
    print("Binary envelope of a reduction instance:", binary_envelope(s))
    k = 24
    switch = 2*k + 1
    star = [(-switch, -(2*i+1)) for i in range(k)]
    answer = solve_frontier(matching_instance(k, switch=True, background=star))
    assert not answer.satisfiable and len(answer.cover) == 1 and answer.maxima_evaluated == 2
    print(f"Switch + {k} matching terms: UNSAT after {answer.maxima_evaluated} maximal models;"
          f" the body alone needs {2**k+1:,} projected CNF clauses.")


if __name__ == "__main__":
    main()
