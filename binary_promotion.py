"""Absorb a clause into a 2-CNF when the combined relation stays bijunctive."""

from dataclasses import dataclass

from forgetting import canonical
from two_sat import solve_2cnf


@dataclass(frozen=True)
class ClauseCheck:
    # None represents the constant-true clause (a tautology).
    reduced: tuple[int, ...] | None
    # Three models of background AND original whose majority falsifies it.
    obstruction: tuple

    @property
    def binary(self):
        return self.reduced is None or len(self.reduced) <= 2


def _clause(n, literals):
    clause = tuple(literals)
    if any(not 1 <= abs(lit) <= n for lit in clause):
        raise ValueError("literal index out of range")
    return canonical(clause)


def _check(n, background, clause):
    if clause is None or len(clause) <= 2:
        return ClauseCheck(clause, ())
    remaining = list(clause)
    witnesses = []
    for lit in clause:
        units = [lit] + [-other for other in remaining if other != lit]
        witness = solve_2cnf(n, background, units)
        if witness is None:
            remaining.remove(lit)
        elif len(witnesses) < 3:
            witnesses.append(witness)
    # A kept witness stays exclusive as later literals are deleted.
    return ClauseCheck(tuple(remaining), tuple(witnesses) if len(remaining) > 2 else ())


def check_clause(n, background, clause):
    """Recognize existential 2-CNF representability of background AND one clause."""
    if n < 0:
        raise ValueError("negative variable count")
    base = []
    for raw in background:
        raw = tuple(raw)
        if len(raw) > 2:
            raise ValueError("background clause wider than two")
        clean = _clause(n, raw)
        if clean is not None:
            base.append(clean)
    return _check(n, base, _clause(n, clause))


@dataclass(frozen=True)
class Promotion:
    binary: tuple
    remaining: tuple
    promoted_ids: tuple


def promote(n, clauses):
    """Return an equivalent binary background and the indexed unabsorbed clauses.

    When remaining is empty, solve_2cnf decides the full input on its original
    variables. An unabsorbed clause has an obstruction relative to the final
    background. Other unabsorbed clauses may remove its witness models.
    """
    if n < 0:
        raise ValueError("negative variable count")
    background = []
    pending = []
    for index, raw in enumerate(clauses):
        clause = _clause(n, raw)
        if clause is None:
            continue
        if len(clause) <= 2:
            background.append(clause)
        else:
            pending.append((index, clause))
    promoted = []
    while pending:
        rejected = []
        for index, clause in pending:
            check = _check(n, background, clause)
            if check.binary:
                background.append(check.reduced)
                promoted.append(index)
            else:
                rejected.append((index, clause))
        if len(rejected) == len(pending):
            break
        pending = rejected
    return Promotion(tuple(background), tuple(pending), tuple(promoted))
