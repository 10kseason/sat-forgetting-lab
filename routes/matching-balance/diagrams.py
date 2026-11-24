"""Guard completion and independent small rank checks for the diagram argument."""

from itertools import combinations, product
from pathlib import Path
import random
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from rainbow_nae import rainbow_witness


def completed_rounds(permutation):
    m = len(permutation)
    if m<12 or sorted(permutation)!=list(range(m)):
        raise ValueError("expected a permutation of at least twelve indices")
    if any((b-a)%m in (0,1,2) for a,b in enumerate(permutation)):
        raise ValueError("fourth matching repeats a data pair")
    groups = [tuple((a,m+(a+s)%m,2*m+(a+t)%m) for a in range(m))
              for s,t in ((0,0),(1,2),(2,1))]
    forbid_a = [set() for _ in range(m)]
    forbid_b = [set() for _ in range(m)]
    for group in groups:
        for a,b,c in group:
            forbid_a[a].add(c-2*m)
            forbid_b[b-m].add(c-2*m)
    guards = [None]*m
    owner = {}
    for start in range(m):
        # Augment a matching between fourth-round graph edges and guards.
        parents = {}
        queue = [start]
        free = None
        for a in queue:
            for c in range(m):
                if c in parents or c in forbid_a[a] or c in forbid_b[permutation[a]]:
                    continue
                parents[c] = a
                if c not in owner:
                    free = c
                    break
                queue.append(owner[c])
            if free is not None:
                break
        if free is None:
            raise AssertionError("guard matching is incomplete")
        while free is not None:
            a = parents[free]
            old = guards[a]
            guards[a] = free
            owner[free] = a
            free = old
    groups.append(tuple((a,m+b,2*m+guards[a]) for a,b in enumerate(permutation)))
    return tuple(groups)


def rank3(matrix):
    rows = [list(row) for row in matrix]
    rank = 0
    for j in range(len(rows[0])):
        k = next((i for i in range(rank,len(rows)) if rows[i][j]%3),None)
        if k is None:
            continue
        rows[rank],rows[k] = rows[k],rows[rank]
        pivot = rows[rank]
        for i in range(rank+1,len(rows)):
            factor = rows[i][j]*pivot[j]%3
            if factor:
                rows[i] = [(a-factor*b)%3 for a,b in zip(rows[i],pivot)]
        rank += 1
    return rank


def walsh(row):
    values = list(row)
    width = 1
    while width < len(values):
        for offset in range(0,len(values),2*width):
            for i in range(offset,offset+width):
                a,b = values[i],values[i+width]
                values[i],values[i+width] = (a+b)%3,(a-b)%3
        width *= 2
    return values


def check():
    rng = random.Random(3400570366)
    for m in (13,16,49,128):
        permutation = list(range(m))
        while True:
            rng.shuffle(permutation)
            if all((b-a)%m not in (0,1,2) for a,b in enumerate(permutation)):
                break
        groups = completed_rounds(permutation)
        edges = [e for group in groups for e in group]
        assert all(sorted(v for e in group for v in e)==list(range(3*m)) for group in groups)
        assert len({tuple(sorted(p)) for e in edges for p in combinations(e,2)})==3*len(edges)
        rename = list(range(3*m))
        rng.shuffle(rename)
        scrambled = [tuple(rename[i] for i in e) for e in edges]
        rng.shuffle(scrambled)
        model = rainbow_witness(3*m,scrambled)
        assert model is not None and all(len({model[v] for v in e})==2 for e in scrambled)
    for k in range(1,7):
        size = 1 << k
        matrix = [[int(x|y == size-1) for y in range(size)] for x in range(size)]
        assert rank3(matrix)==size
        transformed = list(zip(*(walsh(row) for row in matrix)))
        assert rank3([walsh(row) for row in transformed])==size
    print("four hidden-part witnesses and six induced-matching ranks verified")


if __name__=="__main__":
    check()
