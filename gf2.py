"""GF(2) reference operations. Bit i denotes the coefficient of variable i+1."""


def reduce_system(n, rows):
    """Return an equivalent basis in increasing pivot order, or None for 0=1."""
    if n < 0:
        raise ValueError("negative variable count")
    pivots = {}
    for mask, rhs in rows:
        if mask < 0 or mask.bit_length() > n or rhs not in (0, 1):
            raise ValueError("invalid parity equation")
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (mask, int(rhs))
                break
            other, value = pivots[pivot]
            mask ^= other
            rhs ^= value
        else:
            if rhs:
                return None
    return tuple(pivots[i] for i in sorted(pivots))


def one_solution(n, echelon):
    """Set the free bits to zero and solve an echelon basis from low pivots up."""
    assignment = 0
    for mask, rhs in echelon:
        if rhs ^ ((mask & assignment).bit_count() & 1):
            assignment |= 1 << (mask.bit_length() - 1)
    return tuple(bool(assignment >> i & 1) for i in range(n))


def equations_in_cnf(clauses):
    """Extract every complete forbidden parity class grouped by its precise support.

    Clauses must already have distinct literals and contain no complementary pair.
    A group can yield two inconsistent equations. Other clauses remain constraints.
    """
    groups = {}
    for clause in clauses:
        if not clause:
            return [(0, 1)]
        mask = sum(1 << (abs(v)-1) for v in clause)
        false_at = sum(1 << (-v-1) for v in clause if v < 0)
        key = (mask, false_at.bit_count() % 2)
        groups.setdefault(key, set()).add(false_at)
    return [(mask, 1 - forbidden) for (mask, forbidden), rows in groups.items()
            if len(rows) == 1 << (mask.bit_count() - 1)]
