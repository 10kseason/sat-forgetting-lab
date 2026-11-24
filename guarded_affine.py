"""Pairwise feasibility for optional GF(2) constraints. Selector indices start at 0."""

from collections import deque
from dataclasses import dataclass

from gf2 import one_solution, reduce_system


@dataclass(frozen=True)
class PairwiseResult:
    """Both counts refer to maximal pairwise-admissible supports."""
    maximal_pairwise: int
    feasible_among_maximal: int
    obstruction: tuple[int, ...] | None

    @property
    def exact(self):
        return self.maximal_pairwise == self.feasible_among_maximal


def _rows(n, rows):
    checked = []
    if n < 0:
        raise ValueError("negative variable count")
    for mask, rhs in rows:
        if mask < 0 or mask.bit_length() > n or rhs not in (0, 1):
            raise ValueError("invalid parity equation")
        checked.append((mask, int(rhs)))
    return tuple(checked)


def _quotient(row, unconditional):
    mask, rhs = row
    # A free high bit must not prevent cancellation of a lower pivot.
    for other, value in reversed(unconditional):
        if mask & (1 << (other.bit_length() - 1)):
            mask ^= other
            rhs ^= value
    return mask, rhs


def single_row_frontier(n, guarded, background=()):
    """Count maximal pairwise-admissible masks and return a minimal gap, if any.

    Each independent selector enables one equation. Background rows are mandatory.
    The pairwise check includes the empty set and all singletons.
    """
    guarded = _rows(n, guarded)
    unconditional = reduce_system(n, _rows(n, background))
    if unconditional is None:
        return PairwiseResult(0, 0, None)
    groups = {}
    for index, row in enumerate(guarded):
        normal, sign = _quotient(row, unconditional)
        if normal:
            groups.setdefault(normal, ([], []))[sign].append(index)

    fixed = []
    flex = []
    for normal, sides in groups.items():
        if all(sides):
            flex.append((normal, sides))
        else:
            sign = int(bool(sides[1]))
            fixed.append((normal, sign, sides[sign][0]))

    fixed_rows = [(normal, sign) for normal, sign, _ in fixed]
    basis = reduce_system(n, fixed_rows)
    total = 1 << len(flex)
    obstruction = [index for _, _, index in fixed]
    feasible = 0
    if basis is not None:
        directions = [(normal, 0) for normal, _ in fixed_rows]
        directions.extend((normal, 0) for normal, _ in flex)
        gain = len(reduce_system(n, directions)) - len(basis)
        feasible = 1 << gain
        if feasible == total:
            return PairwiseResult(total, feasible, None)

        # At least one coordinate vector lies outside a proper linear image.
        point = sum(1 << i for i, value in enumerate(one_solution(n, basis)) if value)
        syndrome = [(normal & point).bit_count() % 2 for normal, _ in flex]
        for flipped in range(len(flex)):
            signs = [bit ^ (i == flipped) for i, bit in enumerate(syndrome)]
            selected = [(normal, bit) for (normal, _), bit in zip(flex, signs)]
            if reduce_system(n, fixed_rows + selected) is None:
                obstruction.extend(sides[bit][0] for (_, sides), bit in zip(flex, signs))
                break

    # Use original equations to certify inclusion-minimality, including background.
    for index in tuple(obstruction):
        smaller = [i for i in obstruction if i != index]
        if reduce_system(n, (*unconditional, *(guarded[i] for i in smaller))) is None:
            obstruction = smaller
    return PairwiseResult(total, feasible, tuple(sorted(obstruction)))


@dataclass(frozen=True)
class OccurrencePath:
    hidden_bits: int
    # Each selector activates a literal-value row and a path row.
    bundles: tuple


def occurrence_path(n, clauses):
    """Reduce CNF SAT to a pairwise-admissible, jointly inconsistent support.

    Fresh padding units ensure any two stages of the path can be enforced.
    The internal path vertices follow the original and padding truth variables.
    """
    if n < 0:
        raise ValueError("negative variable count")
    clauses = [tuple(clause) for clause in clauses]
    if any(lit == 0 or abs(lit) > n for clause in clauses for lit in clause):
        raise ValueError("literal index out of range")
    while len(clauses) < 3:
        n += 1
        clauses.append((n,))

    stages = len(clauses)
    bundles = []
    for j, clause in enumerate(clauses):
        # Endpoint values are 0 and 1. Only internal vertices need columns.
        left = 1 << (n + j - 1) if j > 0 else 0
        right = 1 << (n + j) if j + 1 < stages else 0
        edge = (left | right, int(j + 1 == stages))
        for lit in clause:
            bundles.append(((1 << (abs(lit) - 1), int(lit > 0)), edge))
    return OccurrencePath(n + stages - 1, tuple(bundles))


def split_occurrences(n, clauses):
    """Tovey's implication cycle, with coordinates oriented toward source literals.

    Every copied source occurrence is positive. Each clone has at most two
    positive occurrences and one negative occurrence in the complete output.
    """
    by_variable = {}
    copied = []
    variable_count = 0
    if n < 0:
        raise ValueError("negative variable count")
    for clause in clauses:
        stage = []
        for literal in clause:
            if literal == 0 or abs(literal) > n:
                raise ValueError("literal index out of range")
            variable_count += 1
            stage.append(variable_count)
            # In original coordinates this signed clone represents x, not ¬x.
            clone = variable_count if literal > 0 else -variable_count
            by_variable.setdefault(abs(literal), []).append(clone)
        copied.append(tuple(stage))
    for clones in by_variable.values():
        if len(clones) >= 2:
            copied.extend((-left, right) for left, right in
                          zip(clones, clones[1:] + clones[:1]))
    return variable_count, tuple(copied)


def matching_path_witness(n, clauses):
    """Return a SAT assignment for the occurrence-path matching case or None.

    Opposite-sign occurrence pairs must be disjoint. Pure variables may be
    repeated arbitrarily. The clause positions are part of the input.
    """
    if n < 0:
        raise ValueError("negative variable count")
    clauses = [tuple(clause) for clause in clauses]
    counts = {}
    for clause in clauses:
        for lit in clause:
            if not 1 <= abs(lit) <= n:
                raise ValueError("literal index out of range")
            counts[lit] = counts.get(lit, 0) + 1
    if any(count > 1 and -lit in counts for lit, count in counts.items()):
        raise ValueError("opposite-sign occurrence pairs do not form a matching")

    # A mixed variable has one resource shared by its two opposite occurrences.
    # Each pure occurrence has a private resource so several clauses may use it.
    choices = []
    selected = [None] * len(clauses)
    owner = {}
    for stage, clause in enumerate(clauses):
        choices.append([(abs(lit) if -lit in counts else (stage, slot), lit)
                        for slot, lit in enumerate(clause)])
        # Augment the previous matching to cover this stage.
        queue = deque([stage])
        parent = {}
        seen_stages = {stage}
        end = None
        while queue and end is None:
            current = queue.popleft()
            for resource, lit in choices[current]:
                if resource in parent:
                    continue
                parent[resource] = (current, lit)
                if resource not in owner:
                    end = resource
                    break
                neighbor = owner[resource]
                if neighbor not in seen_stages:
                    seen_stages.add(neighbor)
                    queue.append(neighbor)
        if end is None:
            return None
        while end is not None:
            current, lit = parent[end]
            previous = selected[current]
            selected[current] = (end, lit)
            owner[end] = current
            end = previous[0] if previous is not None else None

    assignment = [False] * n
    for _, lit in selected:
        assignment[abs(lit) - 1] = lit > 0
    return tuple(assignment)
