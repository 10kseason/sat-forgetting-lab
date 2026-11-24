"""Learn original-variable binary clauses from failed 2-SAT subproblems."""

from itertools import combinations, product

from binary_promotion import checked_clause
from two_sat import solve_2cnf


def _assumptions(n):
    for i in range(1, n + 1):
        yield (i,)
        yield (-i,)
    for i, j in combinations(range(1, n + 1), 2):
        for s, t in product((-1, 1), repeat=2):
            yield (i*s, j*t)


def learned_binary_clauses(n, clauses):
    """Return sound unit/binary consequences, or the empty clause when refuted.

    Probes keep all currently known binary clauses. A wider original clause
    participates when the assumptions shorten it to width at most two.
    Returning no new clauses means this particular inference has saturated.
    """
    if n < 0:
        raise ValueError("negative variable count")
    base, wide = [], []
    for raw in clauses:
        clause = checked_clause(n, raw)
        if clause is None:
            continue
        if len(clause) <= 2:
            base.append(clause)
        else:
            wide.append(clause)
    learned = []
    while True:
        previous = len(learned)
        if solve_2cnf(n, base) is None:
            return ((),)
        for pins in _assumptions(n):
            # The negated assumption is already a consequence of the base.
            if solve_2cnf(n, base, pins) is None:
                continue
            true_literals = set(pins)
            false_literals = {-v for v in pins}
            short = []
            for clause in wide:
                if len(clause) > len(pins) + 2 or true_literals.intersection(clause):
                    continue
                residual = tuple(v for v in clause if v not in false_literals)
                if len(residual) <= 2:
                    short.append(residual)
            if short and solve_2cnf(n, (*base, *short), pins) is None:
                consequence = tuple(-lit for lit in pins)
                base.append(consequence)
                learned.append(consequence)
        if len(learned) == previous:
            return tuple(learned)
