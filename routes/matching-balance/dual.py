"""Proper single flips and a sharp four-round color-class imbalance family."""

from collections import Counter
from itertools import combinations


BASE = (
    ((0,1,2),(3,4,5),(6,7,8),(9,10,11),(12,13,14)),
    ((3,6,9),(7,10,12),(0,11,13),(1,4,14),(2,5,8)),
    ((0,4,6),(1,3,7),(2,11,12),(5,10,13),(8,9,14)),
    ((0,3,10),(1,8,12),(2,4,13),(5,7,9),(6,11,14)),
)
OPEN = (1,4,14)


def minority(values, edge):
    a,b,c = edge
    if values[a] == values[b] == values[c]:
        raise ValueError("coloring must be proper")
    return c if values[a] == values[b] else b if values[a] == values[c] else a


def rebalance(n, triples, coloring):
    """Move a supplied model into the proven interval by proper flips."""
    values = list(coloring)
    triples = tuple(tuple(e) for e in triples)
    if len(values) != n or any(len(e)!=3 or len(set(e))!=3 for e in triples):
        raise ValueError("expected a coloring and triples on distinct vertices")
    if Counter(v for e in triples for v in e) != {v:4 for v in range(n)}:
        raise ValueError("expected a four-regular incidence system")
    if (7*n+14)//15 > 8*n//15:
        raise ValueError("the target interval contains no integer")
    history = []
    while True:
        blocked = {minority(values,e) for e in triples}
        ones = sum(values)
        if 7*n <= 15*ones <= 8*n:
            return tuple(values), tuple(history)
        flip_from = 15*ones > 8*n
        v = next(i for i,bit in enumerate(values) if bit == flip_from and i not in blocked)
        values[v] = not values[v]
        history.append(v)


def cycle(copies):
    if copies < 1:
        raise ValueError("positive copy count required")
    groups = [[],[],[],[]]
    for i in range(copies):
        for j,group in enumerate(BASE):
            for e in group:
                if e == OPEN:
                    groups[j].append((15*i+4,15*i+14,15*((i+1)%copies)+1))
                else:
                    groups[j].append(tuple(15*i+v for v in e))
    return tuple(tuple(g) for g in groups)


def check():
    interior = [e for g in BASE for e in g if e != OPEN]
    states = [x for x in range(1<<15) if all(len({x>>v&1 for v in e})==2 for e in interior)]
    assert states == [0x3263,0x4d9c]
    bits = [bool(states[0]>>v&1) for v in range(15)]
    arcs = [set() for _ in bits]
    for edge in interior:
        source = minority(bits,edge)
        arcs[source].update(set(edge)-{source})
    for root in range(15):
        reached = {root}
        queue = [root]
        for v in queue:
            fresh = arcs[v]-reached
            reached.update(fresh)
            queue.extend(fresh)
        assert len(reached)==15
    for k in range(1,9):
        groups = cycle(k)
        all_pairs = [tuple(sorted(p)) for g in groups for e in g for p in combinations(e,2)]
        assert len(all_pairs)==len(set(all_pairs))
        for g in groups:
            assert sorted(v for e in g for v in e) == list(range(15*k))
        # The verified local relation has two states, so every phase choice is covered.
        sizes = []
        for phase in range(1<<k):
            row = sum(states[phase>>i&1] << (15*i) for i in range(k))
            if all(len({row>>v&1 for v in e})==2 for g in groups for e in g):
                sizes.append(row.bit_count())
        assert sorted(sizes)==[7*k,8*k]
    print("two interior states, sharp 7:8 cycles verified through eight copies")


if __name__=="__main__":
    check()
