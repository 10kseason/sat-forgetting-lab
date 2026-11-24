"""Labelled 2-CNF elimination and reproducible finite checks. Run with Python 3.10+."""

from itertools import permutations, product


Literals = frozenset[int]
Label = tuple[int, ...]
Chains = tuple[tuple[Literals, ...], ...]
State = dict[Literals, set[Label]]


def tautological(literals: Literals) -> bool:
    return any(-literal in literals for literal in literals)


def expand_guard(chains: Chains, label: Label) -> Literals:
    return frozenset().union(*(chain[index] for chain, index in zip(chains, label)))


def dominates(smaller: Label, larger: Label) -> bool:
    return all(left <= right for left, right in zip(smaller, larger))


def insert(state: State, body: Literals, label: Label) -> None:
    frontier = state.setdefault(body, set())
    if any(dominates(previous, label) for previous in frontier):
        return
    obsolete = {previous for previous in frontier if dominates(label, previous)}
    frontier.difference_update(obsolete)
    frontier.add(label)


def initial_state(chains: Chains, clauses: list[tuple[Label, Literals]]) -> State:
    if not chains:
        raise ValueError("Provide at least the trivial chain containing the empty guard.")
    for chain in chains:
        if not chain or chain[0] or any(not a < b for a, b in zip(chain, chain[1:])):
            raise ValueError("Each guard chain must start empty and grow by strict inclusion.")
        if 0 in chain[-1] or tautological(chain[-1]):
            raise ValueError("Each chain must contain only nonzero literals without opposites.")
    protected = {abs(literal) for chain in chains for literal in chain[-1]}

    state: State = {}
    for label, body in clauses:
        if len(label) != len(chains) or any(
            not 0 <= index < len(chain) for chain, index in zip(chains, label)
        ):
            raise ValueError("Label indices must agree with the guard chains.")
        if len(body) > 2 or any(not literal or abs(literal) in protected for literal in body):
            raise ValueError("A body must have at most two nonzero, unprotected literals.")
        if not tautological(body) and not tautological(expand_guard(chains, label)):
            insert(state, body, label)
    return state


def forget(chains: Chains, state: State, pivot: int) -> tuple[State, int]:
    """Return a new equivalent projection and the number of pivot-opposed pairs."""
    if pivot <= 0 or any(pivot in chain[-1] or -pivot in chain[-1] for chain in chains):
        raise ValueError("A pivot must be a positive variable number outside all guards.")

    positive = []
    negative = []
    result: State = {}
    for body, labels in state.items():
        if pivot in body:
            positive.append((body - {pivot}, labels))
        elif -pivot in body:
            negative.append((body - {-pivot}, labels))
        else:
            result[body] = labels.copy()

    pairs = 0
    for left_body, left_labels in positive:
        for right_body, right_labels in negative:
            pairs += len(left_labels) * len(right_labels)
            body = left_body | right_body
            if tautological(body):
                continue
            for left in left_labels:
                for right in right_labels:
                    label = tuple(max(a, b) for a, b in zip(left, right))
                    if not tautological(expand_guard(chains, label)):
                        insert(result, body, label)
    return result, pairs


def expand(chains: Chains, state: State) -> list[Literals]:
    return [
        body | expand_guard(chains, label)
        for body, labels in state.items()
        for label in labels
    ]


def satisfies(formula: list[Literals], assignment: int) -> bool:
    return all(
        any(bool(assignment & (1 << (abs(literal) - 1))) == (literal > 0) for literal in clause)
        for clause in formula
    )


def body_count(variables: int) -> int:
    return 1 + 2 * variables * variables


def profile_limit(chains: Chains) -> int:
    sizes = [len(chain) for chain in chains]
    sizes.remove(max(sizes))
    result = 1
    for size in sizes:
        result *= size
    return result


def check_state_bounds(chains: Chains, state: State, body_variables: int) -> tuple[int, int]:
    profile = profile_limit(chains)
    for labels in state.values():
        assert len(labels) <= profile
        assert not any(a != b and dominates(a, b) for a in labels for b in labels)
    expanded = expand(chains, state)
    protected = {abs(literal) for chain in chains for literal in chain[-1]}
    count = len(expanded)
    occurrences = sum(map(len, expanded))
    assert count <= profile * body_count(body_variables)
    assert occurrences <= (len(protected) + 2) * count
    return count, occurrences


def exhaustive_small() -> tuple[int, int]:
    chains = (
        (frozenset(), frozenset({1}), frozenset({1, 2})),
        (frozenset(), frozenset({-1}), frozenset({-1, 2})),
    )
    catalog = [
        ((1, 0), frozenset({-3, 5})),
        ((2, 0), frozenset({-3, 5})),
        ((0, 1), frozenset({-5, 4})),
        ((0, 2), frozenset({-5, 6})),
        ((0, 0), frozenset({-5, 6})),
        ((0, 0), frozenset({-6, 4})),
        ((0, 0), frozenset({5})),
        ((0, 0), frozenset({-5})),
        ((1, 0), frozenset({6})),
        ((0, 1), frozenset({-6})),
    ]
    tautologies = [
        ((1, 1), frozenset({-3, 4})),
        ((0, 0), frozenset({3, -3})),
    ]
    universe = range(1 << 6)
    state_checks = 0
    for flags in product((False, True), repeat=len(catalog)):
        selected = [clause for include, clause in zip(flags, catalog) if include]
        selected.extend(tautologies)
        original = [body | expand_guard(chains, label) for label, body in selected]
        models = [assignment for assignment in universe if satisfies(original, assignment)]
        start = initial_state(chains, selected)
        for order in permutations((5, 6)):
            state = start
            eliminated = 0
            for index in range(len(order) + 1):
                expected = {assignment & ~eliminated for assignment in models}
                projected = expand(chains, state)
                actual = {
                    assignment for assignment in universe
                    if not assignment & eliminated and satisfies(projected, assignment)
                }
                assert actual == expected
                check_state_bounds(chains, state, 4 - index)
                state_checks += 1
                if index < len(order):
                    pivot = order[index]
                    state, pairs = forget(chains, state, pivot)
                    assert pairs <= (profile_limit(chains) * (2 * (4 - index) - 1)) ** 2
                    eliminated |= 1 << (pivot - 1)
    return 1 << len(catalog), state_checks


def prefix_chain(start: int, length: int) -> tuple[Literals, ...]:
    return tuple(frozenset(range(start, start + size)) for size in range(length + 1))


def wide_bipartite(n: int) -> tuple[int, int, int, int]:
    chains = (prefix_chain(1, n), prefix_chain(n + 1, n))
    u, v, left, right = [tuple(range(j * n + 1, (j + 1) * n + 1)) for j in range(2, 6)]
    clauses = [((i + 1, 0), frozenset({-u[i], left[i]})) for i in range(n)]
    clauses += [((0, 0), frozenset({-a, b})) for a in left for b in right]
    clauses += [((0, j + 1), frozenset({-right[j], v[j]})) for j in range(n)]
    state = initial_state(chains, clauses)
    cumulative_clauses = 0
    cumulative_occurrences = 0
    candidate_pairs = 0
    for step, pivot in enumerate((*left, *right, None)):
        count, occurrences = check_state_bounds(chains, state, 4 * n - step)
        cumulative_clauses += count
        cumulative_occurrences += occurrences
        assert count == n * n + 2 * n - step
        if pivot is not None:
            state, pairs = forget(chains, state, pivot)
            candidate_pairs += pairs

    expected = {
        frozenset({-u[i], v[j]}): {(i + 1, j + 1)}
        for i in range(n) for j in range(n)
    }
    assert state == expected
    assert candidate_pairs == 2 * n * n
    return len(state), cumulative_clauses, cumulative_occurrences, candidate_pairs


def sharp_frontier(n: int) -> int:
    chains = (prefix_chain(1, n), prefix_chain(n + 1, n))
    u, v = 2 * n + 1, 2 * n + 2
    hidden = range(v + 1, v + n + 2)
    clauses = []
    for i, pivot in enumerate(hidden):
        clauses.extend((
            ((i, 0), frozenset({-u, pivot})),
            ((0, n - i), frozenset({-pivot, v})),
        ))
    state = initial_state(chains, clauses)
    for pivot in hidden:
        state, _ = forget(chains, state, pivot)
    body = frozenset({-u, v})
    assert state == {body: {(i, n - i) for i in range(n + 1)}}
    formula = expand(chains, state)
    for clause in formula:
        outside = set(range(1, 2 * n + 1)) - clause
        assignment = (1 << (u - 1)) | sum(1 << (bit - 1) for bit in outside)
        assert {c for c in formula if not satisfies([c], assignment)} == {clause}
    return len(formula)


def exponential_path(layers: int) -> int:
    chains = tuple(prefix_chain(j + 1, 1) for j in range(2 * layers))
    path = range(2 * layers + 1, 3 * layers + 2)
    clauses = []
    for i, (left, right) in enumerate(zip(path, path[1:])):
        body = frozenset({-left, right})
        for literal_index in (2 * i, 2 * i + 1):
            label = tuple(int(j == literal_index) for j in range(2 * layers))
            clauses.append((label, body))
    state = initial_state(chains, clauses)
    for pivot in path[1:-1]:
        state, _ = forget(chains, state, pivot)
    fixed_body = frozenset({-path[0], path[-1]})
    expected = {fixed_body | frozenset(chosen) for chosen in product(*(
        (2 * i + 1, 2 * i + 2) for i in range(layers)
    ))}
    assert set(expand(chains, state)) == expected
    return len(expected)


def main() -> None:
    formulas, states = exhaustive_small()
    print(f"small_scope formulas={formulas} checked_prefix_states={states}")
    for n in (2, 4, 8, 16, 32):
        final, cumulative, occurrences, pairs = wide_bipartite(n)
        print(
            f"wide_bipartite n={n} final_clauses={final} cumulative_clauses={cumulative} "
            f"cumulative_literals={occurrences} pivot_opposed_pairs={pairs}"
        )
    print(f"sharp_two_chain_frontier n=12 final_clauses={sharp_frontier(12)}")
    print(f"unbounded_chain_count_path layers=8 final_clauses={exponential_path(8)}")


if __name__ == "__main__":
    main()
