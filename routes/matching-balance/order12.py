"""All order-12 linear systems with four *given* perfect matchings.

Isomorphisms may permute vertices and matching classes. A different resolution
of the same uncolored hypergraph can be a different object in this count.
"""

from collections import Counter
from itertools import combinations, permutations


CELLS = tuple((i,j) for i in range(4) for j in range(4) if i != j)
INDEX = {cell: v for v,cell in enumerate(CELLS)}
ROWS = tuple(tuple(v for v,(i,j) in enumerate(CELLS) if i == k) for k in range(4))
COLS = tuple(tuple(v for v,(i,j) in enumerate(CELLS) if j == k) for k in range(4))
PAIRS = {p: i for i,p in enumerate(combinations(range(12),2))}
ALL = (1 << 4096) - 1
COLUMNS = tuple(sum(1 << x for x in range(4096) if x & (1 << v)) for v in range(12))


def candidates():
    choices = []
    for e in combinations(range(12),3):
        ij = [CELLS[v] for v in e]
        if len({i for i,j in ij}) == 3 and len({j for i,j in ij}) == 3:
            choices.append((sum(1 << v for v in e), e))

    def grow(remaining):
        if not remaining:
            yield ()
            return
        first = remaining & -remaining
        for mask, edge in choices:
            if mask & first and mask & remaining == mask:
                for tail in grow(remaining ^ mask):
                    yield (edge, *tail)

    return tuple(grow(4095))


def pair_mask(group):
    return sum(1 << PAIRS[p] for e in group for p in combinations(e,2))


def model_mask(group):
    result = ALL
    for a,b,c in group:
        x,y,z = COLUMNS[a], COLUMNS[b], COLUMNS[c]
        result &= (x | y | z) & ~(x & y & z)
    return result


def presentations(groups):
    """Enumerate every normalized presentation of this resolved design."""
    for a,b in permutations(range(4),2):
        other = tuple(i for i in range(4) if i != a and i != b)
        rows, cols = groups[a], groups[b]
        row_of = {v: i for i,g in enumerate(rows) for v in g}
        # Every column misses exactly one row; use its name to name the column.
        col_of = {}
        for col in cols:
            miss, = set(range(4)) - {row_of[v] for v in col}
            col_of.update((v,miss) for v in col)
        for names in permutations(range(4)):
            rename = [INDEX[names[row_of[v]],names[col_of[v]]] for v in range(12)]
            last = [tuple(sorted(tuple(sorted(rename[v] for v in e)) for e in groups[k]))
                    for k in other]
            yield tuple(sorted(last))


def classify():
    possible = candidates()
    pair_sets = list(map(pair_mask, possible))
    known = set()
    rows = []
    normalized = 0
    for i, first in enumerate(possible):
        for j in range(i):
            if pair_sets[i] & pair_sets[j]:
                continue
            normalized += 1
            key = tuple(sorted((first,possible[j])))
            if key in known:
                continue
            system = (ROWS,COLS,*key)
            orbit = set(presentations(system))
            assert key in orbit and not known.intersection(orbit)
            known.update(orbit)
            masks = list(map(model_mask,system))
            full = masks[0] & masks[1] & masks[2] & masks[3]
            weights = tuple(sorted({x.bit_count() for x in range(4096) if full & (1 << x)}))
            after_drop = []
            for k in range(4):
                partial = ALL
                for j,mask in enumerate(masks):
                    if j != k:
                        partial &= mask
                after_drop.append(partial.bit_count())
            rows.append((len(orbit),full.bit_count(),weights,tuple(sorted(after_drop))))
    assert len(known) == normalized == sum(row[0] for row in rows)
    return len(possible), normalized, tuple(sorted(rows))


if __name__ == "__main__":
    choices, normalized, rows = classify()
    print("candidate matchings",choices,"normalized presentations",normalized,"orbits",len(rows))
    print("models per orbit",sorted(Counter(row[1] for row in rows).items()))
    for size, count, weights, drops in rows:
        print("orbit",size,"models",count,"weights",weights,"models after dropping one matching",drops)
