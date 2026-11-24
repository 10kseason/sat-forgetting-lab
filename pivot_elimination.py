"""Davis–Putnam elimination with a nonincreasing explicit clause budget."""

from forgetting import canonical, clause_value


def minimal(clauses):
    """Normalize clauses and remove tautologies, duplicates and subsumed clauses."""
    kept = {}
    normalized = {canonical(clause) for clause in clauses}
    normalized.discard(None)
    for c in sorted(normalized, key=lambda item: (len(item), item)):
        same = frozenset(c)
        if not any(prev <= same for prev in kept.values() if len(prev) < len(same)):
            kept[c] = same
    return set(kept)


def candidate(clauses, pivot):
    """Return the normalized exact residual and positive tails for model recovery."""
    positive, negative, unchanged = [], [], set()
    for c in clauses:
        if pivot in c:
            positive.append(tuple(v for v in c if v != pivot))
        elif -pivot in c:
            negative.append(tuple(v for v in c if v != -pivot))
        else:
            unchanged.add(c)
    for left in positive:
        for right in negative:
            resolvent = canonical((*left, *right))
            if resolvent is not None:
                unchanged.add(resolvent)
    return minimal(unchanged), positive


def first_non_growing(clauses):
    for pivot in sorted({abs(v) for c in clauses for v in c}):
        new, tails = candidate(clauses, pivot)
        if len(new) <= len(clauses):
            return new, (pivot, tails)
    return None


def recover(trace, model):
    assignment = list(model)
    for pivot, positive in reversed(trace):
        assignment[pivot-1] = any(not clause_value(tail, assignment) for tail in positive)
    return tuple(assignment)
