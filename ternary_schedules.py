"""Solve a promoted 3-CNF with correlated deletions and ordinary 2-SAT calls."""

from dataclasses import dataclass
from itertools import product
from math import prod

from binary_promotion import promote
from two_sat import solve_2cnf


def block_cover(width):
    """Each ternary pattern differs everywhere from at least one returned row."""
    small = {
        0: ((),),
        1: ((0,), (1,)),
        2: ((0, 0), (1, 1), (2, 2)),
        3: ((0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0), (2, 2, 2)),
    }
    if width < 0:
        raise ValueError("negative block width")
    if width in small:
        return small[width]
    rows = list(product(range(3), repeat=width))
    # Prepending a digit keeps the suffix mask in two of three target blocks.
    masks = [1]
    stride = 1
    for _ in range(width):
        previous = masks
        masks = []
        for drop in range(3):
            left, right = [digit * stride for digit in range(3) if digit != drop]
            masks.extend((mask << left) | (mask << right) for mask in previous)
        stride *= 3
    uncovered = (1 << len(rows)) - 1
    chosen = []
    while uncovered:
        j = max(range(len(rows)), key=lambda i: (masks[i] & uncovered).bit_count())
        chosen.append(rows[j])
        uncovered &= ~masks[j]
    return tuple(chosen)


@dataclass(frozen=True)
class ScheduleDecision:
    status: str
    assignment: tuple | None
    calls: int
    schedule_count: int


def solve_ternary(n, clauses, max_calls=None):
    """The call budget counts schedule solves after polynomial preprocessing."""
    if max_calls is not None and max_calls < 0:
        raise ValueError("negative 2-SAT budget")
    reduced = promote(n, clauses)
    wide = [clause for _, clause in reduced.remaining]
    if any(len(clause) != 3 for clause in wide):
        raise ValueError("each clause left after promotion must have width three")

    width = 3
    while 3 ** (2 * (width + 1)) <= len(wide):
        width += 1
    whole, tail = divmod(len(wide), width)
    blocks = [block_cover(width)] * whole if whole else []
    if tail:
        blocks.append(block_cover(tail))
    count = prod(len(block) for block in blocks)
    calls = 0
    for pieces in product(*blocks):
        if max_calls is not None and calls >= max_calls:
            return ScheduleDecision("UNKNOWN", None, calls, count)
        schedule = (pos for piece in pieces for pos in piece)
        binary = list(reduced.binary)
        for clause, pos in zip(wide, schedule):
            binary.append(clause[:pos] + clause[pos+1:])
        calls += 1
        witness = solve_2cnf(n, binary)
        if witness is not None:
            return ScheduleDecision("SAT", witness, calls, count)
    return ScheduleDecision("UNSAT", None, calls, count)
