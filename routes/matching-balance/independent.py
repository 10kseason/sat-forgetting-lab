"""Reproducible four-matching controls generated independently of the substitution."""

from itertools import combinations
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from anonymous_blocks import contract
from nae_cut import cut_obstruction


def draw_matching(n, forbidden, rng):
    """Randomized backtracking. The resulting designs need not be uniform."""
    def complete(vertices):
        if not vertices:
            return ()
        head, *others = vertices
        pairs = [(a,b) for a,b in combinations(others,2)
                 if (head,a) not in forbidden and (head,b) not in forbidden
                 and (a,b) not in forbidden]
        rng.shuffle(pairs)
        for a,b in pairs:
            rest = complete(tuple(v for v in others if v != a and v != b))
            if rest is not None:
                return ((head,a,b), *rest)
        return None
    return complete(tuple(range(n)))


def draw_design(n, rng):
    while True:
        groups, forbidden = [], set()
        for _ in range(4):
            matching = draw_matching(n, forbidden, rng)
            if matching is None:
                break
            groups.append(matching)
            for edge in matching:
                forbidden.update(combinations(edge,2))
        if len(groups) == 4:
            return tuple(groups)


def independent_model(n, edges):
    """Complete NAE search using only the rule that two equal colors force a third."""
    def visit(values):
        while True:
            assigned = False
            for edge in edges:
                known = [values[i] for i in edge if values[i] is not None]
                if len(known) == 3 and len(set(known)) == 1:
                    return None
                if len(known) == 2 and known[0] == known[1]:
                    vertex = next(i for i in edge if values[i] is None)
                    values[vertex] = not known[0]
                    assigned = True
            if not assigned:
                break
        if None not in values:
            return tuple(values)
        i = values.index(None)
        for bit in (False,True):
            trial = values.copy()
            trial[i] = bit
            model = visit(trial)
            if model is not None:
                return model
        return None
    return visit([False] + [None]*(n-1))


def affine_plane():
    return tuple(tuple(tuple(3*r+c for c in range(3)) for r in range(3))
                 if d == 3 else tuple(tuple(3*r+(line+d*r)%3 for r in range(3))
                                       for line in range(3))
                 for d in range(4))


def joined_negative(groups):
    """Leave 11 affine-plane triples intact and connect to a separate design."""
    plane = affine_plane()
    joined = []
    for i, (core, body) in enumerate(zip(plane,groups)):
        rows = list(core) + [tuple(v+9 for v in e) for e in body]
        if i == 0:
            a,b,c = rows[0]
            x,y,z = rows[len(core)]
            rows[0], rows[len(core)] = (a,b,z), (x,y,c)
        joined.append(tuple(rows))
    return tuple(joined)


def cycle_of_planes(copies):
    """Keep eleven triples per affine plane and join missing fourth-round ports."""
    if copies < 1:
        raise ValueError("at least one plane")
    groups = [[],[],[],[]]
    for i in range(copies):
        for j, group in enumerate(affine_plane()):
            for a,b,c in group:
                target = (i+1)%copies if j == 3 and (a,b,c)==(0,1,2) else i
                groups[j].append((9*i+a,9*i+b,9*target+c))
    return tuple(tuple(g) for g in groups)


def check_cycle():
    def misses(bits, group):
        return sum(len({(bits >> v) & 1 for v in e}) == 1 for e in group)

    for copies in range(1,8):
        groups = cycle_of_planes(copies)
        pattern = sum((15 if i%2==0 else 511^15) << (9*i) for i in range(copies))
        assert all(misses(pattern,g)==0 for g in groups[:3])
        assert misses(pattern,groups[3]) == copies + copies%2
    print("restoration witnesses checked at cycle lengths 1 through 7")


def run(count=24):
    rng = random.Random(1162398546)
    for n in (12,24,36,48):
        sat = contracted = certified = joined_refuted = 0
        for _ in range(count):
            groups = draw_design(n, rng)
            edges = tuple(e for g in groups for e in g)
            witness = independent_model(n, edges)
            if witness is not None:
                assert all(len({witness[i] for i in e}) == 2 for e in edges)
                sat += 1
            contracted += contract(n, edges) is not None
            formula = [tuple(s*(i+1) for i in e) for e in edges for s in (1,-1)]
            formula = [tuple(sorted(c,key=abs)) for c in formula]
            certificate = cut_obstruction(formula)
            assert certificate is None or witness is None
            certified += certificate is not None
            joined = joined_negative(groups)
            edges = tuple(e for g in joined for e in g)
            assert independent_model(n+9,edges) is None
            formula = [tuple(s*(i+1) for i in sorted(e)) for e in edges for s in (1,-1)]
            joined_refuted += cut_obstruction(formula) is not None
        print(f"n={n} samples={count} SAT={sat} contracted={contracted}"
              f" cut_refuted={certified} joined_negatives_refuted={joined_refuted}")
        assert joined_refuted == count


if __name__ == "__main__":
    run()
    check_cycle()
