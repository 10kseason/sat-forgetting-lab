"""Finite checks for affine frontier search and its two obstructions."""

from functools import reduce
from itertools import combinations, product
from operator import or_
from random import Random


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def bit_of(literal):
    return 1 << (abs(literal) - 1)


def satisfies(clauses, row):
    return all(any(bool(row & bit_of(lit)) == (lit > 0) for lit in clause) for clause in clauses)


def rank(rows):
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length()
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return len(basis)


def syndrome(equations, row):
    return sum(((mask & row).bit_count() % 2) << i for i, (mask, _) in enumerate(equations))


def drop_constraints(n, background, maximum):
    arcs = [0] * n
    forbidden = 0
    excludes = set()
    for clause in background:
        if any(lit < 0 and not maximum & bit_of(lit) for lit in clause):
            continue
        remaining = {-lit for lit in clause if maximum & bit_of(lit)}
        if any(-lit in remaining for lit in remaining):
            continue
        assert remaining and any(lit < 0 for lit in remaining)
        if len(remaining) == 1:
            forbidden |= bit_of(next(iter(remaining)))
        else:
            left, right = sorted(remaining)
            if right < 0:
                excludes.add(bit_of(left) | bit_of(right))
            else:
                arcs[-left - 1] |= bit_of(right)
    return arcs, forbidden, excludes


def closure(arcs, seeds):
    while True:
        expanded = seeds | reduce(or_, (arcs[i] for i in bits(seeds)), 0)
        if expanded == seeds:
            return seeds
        seeds = expanded


def components(maximum, arcs):
    reachable = {i: closure(arcs, 1 << i) for i in bits(maximum)}
    unseen = maximum
    blocks = []
    for i in bits(maximum):
        if unseen & (1 << i):
            block = sum(1 << j for j in bits(reachable[i]) if reachable[j] & (1 << i))
            unseen ^= block
            blocks.append((block, reachable[i]))
    return blocks


def feasible_below(n, background, equations, function, maximum):
    arcs, forbidden, excludes = drop_constraints(n, background, maximum)
    blocks = components(maximum, arcs)
    bound = rank(mask for mask, _ in equations)
    rhs = sum(value << i for i, (_, value) in enumerate(equations))
    successful = set()
    for drops in range(1 << n):
        if drops & ~maximum:
            continue
        row = maximum ^ drops
        structurally_feasible = (not (drops & forbidden) and closure(arcs, drops) == drops
                                 and not any(drops & pair == pair for pair in excludes))
        assert structurally_feasible == satisfies(background, row)
        if structurally_feasible and function >> row & 1 and syndrome(equations, row) == rhs:
            successful.add(drops)
    for drops in successful:
        if any(other != drops and other & drops == other for other in successful):
            continue
        included = [(members, reach) for members, reach in blocks if members & drops]
        sources = [(members, reach) for members, reach in included
                   if not any(members != other and members & descendants for other, descendants in included)]
        assert reduce(or_, (reach for _, reach in sources), 0) == drops
        assert rank(syndrome(equations, members) for members, _ in sources) == len(sources) <= bound
    generated = {reduce(or_, (reach for _, reach in chosen), 0)
                 for k in range(min(bound, len(blocks)) + 1) for chosen in combinations(blocks, k)}
    assert bool(generated & successful) == bool(successful)
    return bool(successful)


def check_instance(n, background, equations, function, orientation=0):
    rows = range(1 << n)
    b_models = [row for row in rows if satisfies(background, row)]
    maxima = [row for row in b_models if not any(other != row and row & other == row for other in b_models)]
    physical = [tuple(-lit if orientation & bit_of(lit) else lit for lit in clause) for clause in background]
    physical_eq = [(mask, rhs ^ ((mask & orientation).bit_count() % 2)) for mask, rhs in equations]
    rhs = sum(value << i for i, (_, value) in enumerate(physical_eq))
    expected = any(satisfies(physical, x) and syndrome(physical_eq, x) == rhs
                   and function >> (x ^ orientation) & 1 for x in rows)
    actual = [feasible_below(n, background, equations, function, m) for m in maxima]
    assert any(actual) == expected


def monotone_functions(n):
    rows = range(1 << n)
    edges = [(v, v | (1 << i)) for v in rows for i in range(n) if not v >> i & 1]
    return [g for g in range(1 << len(rows)) if all(not (g >> v & 1) or g >> w & 1 for v, w in edges)]


def binary_clauses(n):
    return [tuple(v * sign for v, sign in zip(names, signs))
            for arity in range(3) for names in combinations(range(1, n + 1), arity)
            for signs in product((-1, 1), repeat=arity)]


def check_search():
    checked = 0
    eq_pool = list(product(range(4), (0, 1)))
    functions = monotone_functions(2)
    for clause_count, row_count in product(range(3), repeat=2):
        for background in combinations(binary_clauses(2), clause_count):
            for equations in combinations(eq_pool, row_count):
                for function, orientation in product(functions, range(4)):
                    check_instance(2, background, equations, function, orientation)
                    checked += 1
    rng = Random(20261125)
    pool, functions = binary_clauses(3), monotone_functions(3)
    for _ in range(2000):
        background = rng.sample(pool, rng.randrange(len(pool) + 1))
        equations = [(rng.randrange(8), rng.randrange(2)) for _ in range(rng.randrange(5))]
        check_instance(3, background, equations, rng.choice(functions), rng.randrange(8))
        checked += 1
    check_instance(0, [], [(0, 0)], 1)
    check_instance(0, [], [(0, 1)], 1)
    check_instance(3, [(-1, 2), (-2, 1), (-2, 3), (1, -1), (2, 2)], [(4, 0)], 255, 5)
    print(f"Affine frontier: {checked + 3} searches match exhaustive satisfiability.")


def check_oracles():
    compared = 0
    for r, q in product(range(1, 4), range(2, 5)):
        n = r * q
        full = (1 << n) - 1
        blocks = [((1 << q) - 1) << (q * i) for i in range(r)]
        affine = [x for x in range(1 << n) if all((block & ~x).bit_count() % 2 for block in blocks)]
        maxima = {x for x in affine if not any(x != y and x & y == x for y in affine)}
        assert len(maxima) == q ** r
        for target in maxima:
            assert all((block & ~target).bit_count() == 1 for block in blocks)
            changed = {x for x in range(full + 1) if x & target == target and not any(x & b == b for b in blocks)}
            assert changed == {target}
            compared += 1
    print(f"Oracle obstruction: {compared} single-point differences verified on complete cubes.")


def prism(side):
    edges = [(i, i + side) for i in range(side)]
    for layer in (0, side):
        edges.extend((layer + i, layer + (i + 1) % side) for i in range(side))
    ports = [tuple(i for i, e in enumerate(edges, 1) if v in e) for v in range(2 * side)]
    groups = [[tuple(-v if bit else v for v, bit in zip(group, x))
               for x in product((0, 1), repeat=3) if sum(x) % 2 != int(v == 0)]
              for v, group in enumerate(ports)]
    return len(edges), ports, groups


def scoped_xors(clauses):
    by_scope = {}
    for clause in clauses:
        ordered = tuple(sorted(clause, key=abs))
        by_scope.setdefault(tuple(map(abs, ordered)), set()).add(ordered)
    rows = []
    for scope, clauses_at_scope in by_scope.items():
        wrong = {sum(literal < 0 for literal in clause) % 2 for clause in clauses_at_scope}
        if len(clauses_at_scope) == 1 << (len(scope) - 1) and len(wrong) == 1:
            rows.append((sum(bit_of(v) for v in scope), 1 - next(iter(wrong))))
    return rows


def pair_signs(group, a, b):
    return {(a in clause, b in clause) for clause in group
            if (a in clause or -a in clause) and (b in clause or -b in clause)}


def check_recognition():
    all_signs = set(product((False, True), repeat=2))
    for a, b, c in product((False, True), repeat=3):
        assert all(((a or b or c or s) and (a or b or c or not s)) == (a or b or c) for s in (False, True))
        assert any((a or b or s) and (not s or c) for s in (False, True)) == (a or b or c)
    for side in range(3, 7):
        n, ports, groups = prism(side)
        original = [clause for group in groups for clause in group]
        full = scoped_xors(original)
        root_rank = rank(mask for mask, _ in full)
        assert len(full) == len(ports) and root_rank == len(ports) - 1
        assert rank(mask | rhs << n for mask, rhs in full) == root_rank + 1
        for hide_all in (False, True):
            changed = []
            for v, (scope, group) in enumerate(zip(ports, groups)):
                d, *others = group
                selector = n + v + 1
                if hide_all or v == 0:
                    clauses = [*others, (*d, selector), (*d, -selector)]
                    third = [*others, (d[0], d[1], selector), (-selector, d[2])]
                    assert pair_signs(third, *scope[:2]) == all_signs
                    assert not scoped_xors(third)
                else:
                    clauses = group
                assert all(pair_signs(clauses, a, b) == all_signs for a, b in combinations(scope, 2))
                changed.extend(clauses)
            found = scoped_xors(changed)
            assert len(found) == (0 if hide_all else len(ports) - 1)
            assert rank(mask for mask, _ in found) == rank(mask | rhs << n for mask, rhs in found)
    print("XOR recognition: all four prism sizes passed scope, consistency and sign-pair checks.")


if __name__ == "__main__":
    check_search()
    check_oracles()
    check_recognition()
