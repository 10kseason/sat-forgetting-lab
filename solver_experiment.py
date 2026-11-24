"""Odd-charge Tseitin formulas on connected cubic prisms. No external data."""

from itertools import product

from solve_cnf import solve


def prism(side, odd=True, masked=False):
    if side < 3:
        raise ValueError("a simple prism needs side length at least three")
    edges = [(i, i+side) for i in range(side)]
    for layer in (0, side):
        edges += [(layer+i, layer+(i+1) % side) for i in range(side)]
    ports = [[] for _ in range(2*side)]
    for v, (u,w) in enumerate(edges, 1):
        ports[u].append(v)
        ports[w].append(v)
    clauses = []
    for i, incident in enumerate(ports):
        assert len(incident) == 3
        for row in product((False, True), repeat=3):
            if sum(row) % 2 != int(odd and i == 0):
                clauses.append(tuple(-v if value else v for v, value in zip(incident, row)))
    n = len(edges)
    if masked:
        # Existentially splitting one clause disrupts one syntactic parity block.
        a, b, c = clauses.pop(0)
        n += 1
        clauses.extend(((a, b, n), (-n, c)))
    return n, clauses


def guarded_pair(order):
    """One selector between two odd-charge simple 4-regular cycle-square graphs."""
    if order < 5:
        raise ValueError("distinct neighbors at offsets ±1, ±2 require at least five vertices")
    edges = [(i,(i+distance) % order) for i in range(order) for distance in (1,2)]
    assert len({tuple(sorted(edge)) for edge in edges}) == 2*order
    ports = [[] for _ in range(order)]
    for j,(u,v) in enumerate(edges,1):
        ports[u].append(j)
        ports[v].append(j)
    selector = 4*order + 1
    clauses = []
    for branch in (0,1):
        guard = selector if branch else -selector
        for vertex,incident in enumerate(ports):
            assert len(incident) == 4
            for row in product((False, True), repeat=4):
                if sum(row) % 2 != int(vertex == 0):
                    clause = (guard, *( (v + 2*order*branch) * (-1 if value else 1)
                                        for v,value in zip(incident,row)))
                    clauses.append(clause)
    return selector, clauses


if __name__ == "__main__":
    print("prism, bare assignments, direct affine shortcut, masked bare assignments, repaired shortcut")
    for m in (3, 4, 5, 6):
        n, clauses = prism(m)
        result = solve(n, clauses, use_affine=False, use_elimination=False)
        assert (result.status, len(result.retained), result.assignments_tested) == ("UNSAT", 2*m, 4**m)
        quick = solve(n, clauses)
        assert (quick.status, quick.method) == ("UNSAT", "affine contradiction")
        masked = solve(*prism(m, masked=True), use_elimination=False)
        assert masked.status == "UNSAT" and masked.assignments_tested >= 2**(2*m-1)
        repaired = solve(*prism(m, masked=True))
        assert repaired.status == "UNSAT"
        print(m, result.assignments_tested, quick.method, masked.assignments_tested, repaired.method)
    print("Guarded 4-regular pair: order, clauses, non-growing pivots, retained, bounded-run result")
    for order in (5, 6, 8):
        n, clauses = guarded_pair(order)
        row = solve(n, clauses, max_patterns=8)
        assert row.status == "UNKNOWN" and not row.eliminated and len(row.retained) >= 3*order
        for choice in (False,True):
            residual = [tuple(v for v in c if abs(v) != n) for c in clauses
                        if (n if choice else -n) not in c]
            assert solve(n-1,residual).method == "affine contradiction"
        print(order, len(clauses), len(row.eliminated), len(row.retained), row.status)
