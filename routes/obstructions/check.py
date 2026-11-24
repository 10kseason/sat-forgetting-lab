"""Exhaustive small checks for the explicit CNF projection obstructions."""

from fractions import Fraction
from functools import cache
from itertools import combinations, pairwise, permutations, product


def assignments(variables):
    for signs in product((-1, 1), repeat=len(variables)):
        yield frozenset(sign * variable for sign, variable in zip(signs, variables))


def cnf(clauses):
    return frozenset(frozenset(clause) for clause in clauses)


def accepts(formula, assignment):
    return all(clause & assignment for clause in formula)


def clause_order(clause):
    return len(clause), tuple(sorted(clause))


def subsume(clauses):
    kept = []
    for clause in sorted(set(clauses), key=clause_order):
        if any(-literal in clause for literal in clause):
            continue
        if not any(previous <= clause for previous in kept):
            kept.append(clause)
    return frozenset(kept)


def restrict(formula, assignment):
    assignment = frozenset(assignment)
    false_literals = {-literal for literal in assignment}
    return subsume(clause - false_literals for clause in formula if not clause & assignment)


def identify(formula, aliases):
    return subsume(
        frozenset((1 if literal > 0 else -1) * aliases.get(abs(literal), abs(literal)) for literal in clause)
        for clause in formula
    )


def compact_tails(tails, meaning):
    # Keep one representative for each behavior, then keep the strongest behaviors.
    representatives = {}
    for tail in sorted(tails, key=clause_order):
        representatives.setdefault(meaning(tail), tail)
    return tuple(
        tail for mask, tail in representatives.items()
        if not any(other != mask and other & mask == other for other in representatives)
    )


def pivot_tails(formula, pivot, meaning=None):
    positive = tuple(clause - {pivot} for clause in formula if pivot in clause)
    negative = tuple(clause - {-pivot} for clause in formula if -pivot in clause)
    if meaning is not None:
        return compact_tails(positive, meaning), compact_tails(negative, meaning)
    return positive, negative


def forget(formula, order, meaning=None):
    products = []
    for pivot in order:
        positive, negative = pivot_tails(formula, pivot, meaning)
        unaffected = [clause for clause in formula if pivot not in clause and -pivot not in clause]
        resolvents = [left | right for left in positive for right in negative]
        formula = subsume(unaffected + resolvents)
        products.append(len(positive) * len(negative))
    return formula, products


def parity(variables, rhs):
    return cnf(
        {-literal for literal in assignment}
        for assignment in assignments(variables)
        if sum(literal > 0 for literal in assignment) % 2 != rhs
    )


def blocks(size, rhs, checkpoints):
    formula = set()
    for start, stop in pairwise((0, *checkpoints, size)):
        variables = list(range(start + 1, stop + 1))
        if start:
            variables.append(size + start)
        if stop < size:
            variables.append(size + stop)
        formula.update(parity(variables, rhs if stop == size else 0))
    return frozenset(formula)


def projected_models(solutions, visible):
    visible_literals = frozenset(sign * variable for variable in visible for sign in (-1, 1))
    return {assignment & visible_literals for assignment in solutions}


def coding_word(formula, assignment, helpers, order):
    code = [int(variable in assignment) for variable in helpers]
    known_false = {(-variable if variable in assignment else variable) for variable in helpers}
    for variable in order:
        value = variable in assignment
        literal = variable if value else -variable
        if not any(literal in clause and clause - {literal} <= known_false for clause in formula):
            code.append(int(value))
        known_false.add(-literal)
    return tuple(code)


def check_coding_bound(formula, data, helpers, models):
    data_set = set(data)
    width = {clause: sum(abs(literal) in data_set for literal in clause) for clause in formula}
    critical_widths = []
    for assignment in models:
        for variable in data:
            literal = variable if variable in assignment else -variable
            critical_widths.append(min(width[clause] for clause in formula if clause & assignment == {literal}))
    inverse_sum = sum(Fraction(1, size) for size in critical_widths)
    weighted_sum = sum(Fraction(2 ** size, size) for size in critical_widths)
    assert inverse_sum <= (len(helpers) + 1) * len(models)
    assert weighted_sum <= 2 * len(formula) * len(models)
    for order in permutations(data):
        codes = sorted(coding_word(formula, assignment, helpers, order) for assignment in models)
        assert all(left != right[:len(left)] for left, right in pairwise(codes))


def check_parity():
    orders_checked = 0
    checkpoint_sets_checked = 0
    for size in range(1, 8):
        data = tuple(range(1, size + 1))
        positions = tuple(range(1, size))
        hidden = tuple(size + position for position in positions)
        for rhs in (0, 1):
            original = blocks(size, rhs, positions)
            expected = parity(data, rhs)
            assert len(original) == (1 if size == 1 else 4 * size - 4)
            assert max(map(len, original)) <= 3
            assert len(expected) == 2 ** (size - 1)
            assert all(len(clause) == size for clause in expected)
            solutions = [a for a in assignments(data + hidden) if accepts(original, a)]
            assert len(solutions) == 2 ** (size - 1)
            assert projected_models(solutions, data) == {a for a in assignments(data) if accepts(expected, a)}
            for order in permutations(hidden):
                result, _ = forget(original, order)
                assert result == expected, (size, rhs, order)
                orders_checked += 1

            for count in range(len(positions) + 1):
                for retained in combinations(positions, count):
                    visible = data + tuple(size + position for position in retained)
                    candidate = blocks(size, rhs, retained)
                    actual = projected_models(solutions, visible)
                    assert actual == {a for a in assignments(visible) if accepts(candidate, a)}
                    if size <= 5:
                        check_coding_bound(candidate, data, visible[len(data):], actual)
                    start, stop = max(pairwise((0, *retained, size)), key=lambda interval: interval[1] - interval[0])
                    gap = tuple(range(start + 1, stop + 1))
                    pins = {-v for v in data if v not in gap}
                    pins.update((size + p) if p >= stop and rhs else -(size + p) for p in retained)
                    assert restrict(candidate, pins) == parity(gap, rhs), (size, rhs, retained)

                    for left, right in pairwise((0, *retained, size)):
                        aliases = {}
                        if left:
                            aliases[left] = size + left
                        if right < size:
                            aliases[right + 1] = (size + right) * (-1 if rhs else 1)
                        block_data = tuple(range(left + 1, right + 1))
                        free = block_data + tuple(abs(value) for value in aliases.values())
                        pins = {-v for v in data if v not in block_data and v not in aliases}
                        pins.update(-(size + p) for p in retained if p < left or (p > right and not rhs))
                        pins.update(size + p for p in retained if p > right and rhs)
                        restricted = identify(restrict(candidate, pins), aliases)
                        assert restricted == parity(free, rhs if right == size else 0), (size, rhs, retained, left, right)
                    checkpoint_sets_checked += 1
    print(f"Parity: {orders_checked} elimination orders and {checkpoint_sets_checked} checkpoint sets passed.")


def implication_family(size):
    pairs = tuple((i, size + i) for i in range(1, size + 1))
    tags = tuple(range(2 * size + 1, 3 * size + 1))
    heads = tuple(range(3 * size + 1, 4 * size + 1))
    roots = tuple(range(4 * size + 1, 5 * size + 1))
    background = cnf((-a, tag) for (a, _), tag in zip(pairs, tags))
    body = {frozenset({roots[0]})}
    for i, ((a, b), tag, head, root) in enumerate(zip(pairs, tags, heads, roots)):
        body.update(cnf([(-head, a), (-head, b), (-head, tag)]))
        body.add(frozenset((-root, head, roots[i + 1])) if i + 1 < size else frozenset((-root, head)))
    return background, frozenset(body), pairs, tags, heads + roots


def clause_meaning(background, variables):
    literal_masks = {sign * variable: 0 for variable in variables for sign in (-1, 1)}
    models = (assignment for assignment in assignments(variables) if accepts(background, assignment))
    for index, assignment in enumerate(models):
        for literal in assignment:
            literal_masks[literal] |= 1 << index

    @cache
    def meaning(clause):
        mask = 0
        for literal in clause:
            mask |= literal_masks[literal]
        return mask

    return meaning


def check_background():
    orders_checked = 0
    for size in range(1, 4):
        background, body, pairs, tags, hidden = implication_family(size)
        retained = tuple(range(1, 3 * size + 1))
        whole = retained + hidden
        meaning = clause_meaning(background, whole)
        assert len(background) == size and len(body) == 4 * size + 1
        assert max(map(len, body)) <= 3
        for pivot in hidden:
            assert all(len(tails) <= 2 for tails in pivot_tails(body, pivot, meaning))
        for (a, _), tag in zip(pairs, tags):
            strong = meaning(frozenset({a}))
            weak = meaning(frozenset({tag}))
            assert strong != weak and strong & weak == strong

        models = (assignment for assignment in assignments(whole) if accepts(background | body, assignment))
        expected_models = projected_models(models, retained)
        admissible = tuple(a for a in assignments(retained) if accepts(background, a))
        assert expected_models == {a for a in admissible if any(set(pair) <= a for pair in pairs)}
        minimum_cnf = cnf(product(*pairs))
        assert len(minimum_cnf) == 2 ** size
        for order in permutations(hidden):
            projected, products = forget(body, order, meaning)
            assert {a for a in admissible if accepts(projected, a)} == expected_models, (size, order)
            assert restrict(projected, tags) == minimum_cnf, (size, order)
            assert len(projected) <= len(body) + sum(products), (size, order)
            orders_checked += 1
    print(f"Implication background: all {orders_checked} semantically compressed elimination orders passed.")


def check_policy_counterexamples():
    witness = (False, True, True, False)
    a, b, c, d = witness
    assert (a or c) and (b or d)
    assert not ((a and b) or (c and d))

    for retained in (False, True):
        exists = any(
            h and (not h or q) and (not q or h) and (not h or retained)
            for h, q in product((False, True), repeat=2)
        )
        assert exists == retained
    print("Policy counterexamples: tied-index conjunction and union-cycle shortcut fail as claimed.")


if __name__ == "__main__":
    check_parity()
    check_background()
    check_policy_counterexamples()
