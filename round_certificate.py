"""Check a sufficient condition for binary projection, including cyclic upper bounds."""

from dataclasses import dataclass
from itertools import product

from binary_envelope import orientation


@dataclass(frozen=True)
class RoundResult:
    clauses: tuple | None
    rounds: int
    failed_head: int | None
    wide_prime: tuple | None
    clause_products: int


def certify_binary_rounds(system, max_hidden_fanin=2):
    """Check every reachable intermediate head against exact signed-unit/binary forms.

    The background is kept separately. With fixed max_hidden_fanin this runs in
    polynomial time. A wide prime at an intermediate head does not settle the output.
    """
    if max_hidden_fanin < 0:
        raise ValueError("negative hidden fan-in limit")
    orientation(system)
    active = sorted({v for goal in system.goals for v in system._cone(goal, system.rules)})
    observed = 0
    states = {head: () for head in active}  # Top is the empty conjunction.

    def binary_form(tails):
        nonlocal observed
        candidates = set()
        for tail in tails:
            heads = [v for v in tail if v > system.retained]
            if len(heads) > max_hidden_fanin:
                raise ValueError(f"rule or goal reads {len(heads)} hidden inputs")
            fixed = frozenset(v for v in tail if v <= system.retained)
            for selected in product(*(states[v] for v in heads)):
                observed += 1
                candidates.add(fixed.union(*selected))
        # Under a common orientation, monotone CNF's prime clauses are precisely
        # its inclusion-minimal members. A superset of a unit or binary can go.
        short = [c for c in candidates if len(c) <= 2]
        small = [c for c in short if not any(d < c for d in short)]
        wide = [c for c in candidates if len(c) > 2 and not any(d <= c for d in small)]
        key = lambda c: (len(c), tuple(sorted(c)))
        if wide:
            return None, tuple(sorted(min(wide, key=key)))
        return tuple(tuple(sorted(c)) for c in sorted(small, key=key)), None

    rounds = 0
    for rounds in range(1, len(active) + 1):
        nxt = {}
        for head in active:
            form, wide = binary_form(system.rules[head])
            if wide is not None:
                return RoundResult(None, rounds, head, wide, observed)
            nxt[head] = form
        if nxt == states:
            break
        states = nxt
    form, wide = binary_form(system.goals)
    return RoundResult(form, rounds, None, wide, observed)
