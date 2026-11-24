"""Exact positive linear NAE decision when few missing pairs can cross a cut."""

from dataclasses import dataclass
from itertools import combinations
from math import comb, isqrt


@dataclass(frozen=True)
class NearCutDecision:
    status: str
    assignment: tuple | None
    patterns: int
    bound: int


def _orient(parts, weights, target):
    """Pick orientations giving exactly the requested total number of one bits."""
    reachable = [1]
    for part, w in zip(parts, weights):
        last = reachable[-1]
        reachable.append((last << w) | (last << (len(part)-w)))
    if not (reachable[-1] >> target) & 1:
        return None
    flips = [False]*len(parts)
    for j in reversed(range(len(parts))):
        w = weights[j]
        if target >= w and (reachable[j] >> (target-w)) & 1:
            target -= w
        else:
            flips[j] = True
            target -= len(parts[j])-w
    return flips


def solve_near_cut(n, triples, max_patterns=None, *, skip_over_budget=False):
    """Decide unsigned NAE on distinct, linear triples over 0..n-1.

    The forest pattern count is available before enumeration. A caller asking
    to skip an over-budget run gets UNKNOWN with zero patterns consumed.
    """
    if n < 0 or (max_patterns is not None and max_patterns < 0):
        raise ValueError("negative count")
    triples = tuple(tuple(e) for e in triples)
    present = [set() for _ in range(n)]
    for e in triples:
        if len(e) != 3 or len(set(e)) != 3 or any(v < 0 or v >= n for v in e):
            raise ValueError("expected three distinct in-range vertices")
        for a,b in combinations(e,2):
            if b in present[a]:
                raise ValueError("repeated variable pair")
            present[a].add(b)
            present[b].add(a)
    demand = 2*len(triples)
    slack = n*n//4 - demand
    if slack < 0:
        return NearCutDecision("UNSAT",None,0,0)

    # Traverse missing pairs through the complement of each adjacency list.
    unseen = set(range(n))
    parent = [-1]*n
    part_id = [-1]*n
    parts, children = [], []
    for root in range(n):
        if root not in unseen:
            continue
        unseen.remove(root)
        part = [root]
        part_id[root] = len(parts)
        for u in part:
            fresh = unseen - present[u]
            unseen.difference_update(fresh)
            for v in fresh:
                parent[v] = u
                part_id[v] = len(parts)
                part.append(v)
                children.append(v)
        parts.append(part)
    within = [(a,b) for a,neighbors in enumerate(present) for b in neighbors
              if a < b and part_id[a] == part_id[b]]
    limit = min(slack,len(children))
    bound = sum(comb(len(children), k) for k in range(limit+1))
    if skip_over_budget and max_patterns is not None and max_patterns < bound:
        return NearCutDecision("UNKNOWN",None,0,bound)

    tested = 0
    for k in range(limit+1):
        for crossing_children in combinations(children,k):
            if max_patterns is not None and tested >= max_patterns:
                return NearCutDecision("UNKNOWN",None,tested,bound)
            tested += 1
            cut = set(crossing_children)
            color = [False]*n
            for child in children:
                color[child] = color[parent[child]] ^ (child in cut)
            weights = [sum(color[v] for v in part) for part in parts]
            missing_cross = sum(w*(len(part)-w) for w,part in zip(weights,parts))
            missing_cross -= sum(color[a] != color[b] for a,b in within)
            disc = n*n - 4*(demand+missing_cross)
            if disc < 0:
                continue
            root = isqrt(disc)
            if root*root != disc or (n-root)%2:
                continue
            flips = _orient(parts,weights,(n-root)//2)
            if flips is not None:
                assignment = tuple(value ^ flips[part_id[v]] for v,value in enumerate(color))
                return NearCutDecision("SAT",assignment,tested,bound)
    return NearCutDecision("UNSAT",None,tested,bound)
