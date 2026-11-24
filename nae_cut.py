"""An integer upper bound on the cut score of paired signed ternary clauses."""

from collections import Counter
from dataclasses import dataclass
from itertools import combinations


@dataclass(frozen=True)
class CutObstruction:
    vertices: tuple[int, ...]
    triples: int
    required_score: int
    score_upper_bound: int


def _sparse_positive_obstruction(triples):
    """Complete the induced-subset cut test on linear, max-degree-four positive input."""
    adj = {}
    incident = {}
    for edge in triples:
        for v in edge:
            incident.setdefault(v, []).append(edge)
        for u,v in combinations(edge,2):
            if v in adj.setdefault(u, set()):
                return None
            adj[u].add(v)
            adj.setdefault(v, set()).add(u)
    if any(len(edges) > 4 for edges in incident.values()):
        return None

    def check(vertices):
        # A triple contributes only when all three vertices belong to this set.
        triples_inside = sum(a in vertices and b in vertices and c in vertices
                             for v in vertices for a,b,c in incident[v] if a == v)
        capacity = len(vertices)**2//4
        if 2*triples_inside > capacity:
            return CutObstruction(tuple(sorted(vertices)), triples_inside,
                                  2*triples_inside, capacity)
        return None

    for v, neighbors in adj.items():
        strong = [w for w in neighbors if len(neighbors & adj[w]) >= 4]
        if len(strong) < 6:
            continue
        # Seven vertices need a K7. Its six other vertices are strong neighbors.
        for six in combinations(strong,6):
            if found := check({v, *six}):
                return found
        if len(neighbors) == 8:
            closed = {v, *neighbors}
            if found := check(closed):
                return found
            # At size ten a saturated vertex misses exactly one member of the
            # certificate, and that member is at distance two.
            distance_two = set().union(*(adj[w] for w in neighbors)) - closed
            for extra in distance_two:
                if found := check(closed | {extra}):
                    return found
    return None


def cut_obstruction(clauses):
    """Find signed-component or sparse positive-subset cut obstructions.

    Inputs are normalized clauses (distinct literals in variable order).
    Either polarity can be chosen to represent a complementary clause pair.
    """
    clauses = set(clauses)
    adjacent = {}
    pair_weights = Counter()
    same_total = Counter()
    triple_count = Counter()
    positive_triples = []
    for clause in clauses:
        if len(clause) != 3 or clause[0] < 0:
            continue
        if tuple(-lit for lit in clause) not in clauses:
            continue
        if all(lit > 0 for lit in clause):
            positive_triples.append(clause)
        first = abs(clause[0])
        triple_count[first] += 1
        for a,b in combinations(clause, 2):
            u,v = abs(a), abs(b)
            adjacent.setdefault(u, set()).add(v)
            adjacent.setdefault(v, set()).add(u)
            if (a > 0) == (b > 0):
                pair_weights[u, v] += 1
            else:
                same_total[first] += 1
                pair_weights[u, v] -= 1

    unseen = set(adjacent)
    while unseen:
        root = min(unseen)
        component = {root}
        stack = [root]
        unseen.remove(root)
        while stack:
            current = stack.pop()
            fresh = adjacent[current] & unseen
            unseen.difference_update(fresh)
            component.update(fresh)
            stack.extend(fresh)
        size = len(component)
        triples = sum(triple_count[i] for i in component)
        baseline = sum(same_total[i] for i in component)
        positive = sorted((pair_weights[u, v] for u in component for v in adjacent[u]
                           if u < v and pair_weights[u, v] > 0), reverse=True)
        upper = baseline + sum(positive[:size*size//4])
        if upper < 2*triples:
            return CutObstruction(tuple(sorted(component)), triples, 2*triples, upper)
    return _sparse_positive_obstruction(positive_triples)


def positive_nae_triples(clauses):
    """Return zero-based NAE triples if these normalized CNF clauses are precisely pairs."""
    triples = []
    for clause in clauses:
        if len(clause) != 3 or any((lit > 0) != (clause[0] > 0) for lit in clause):
            return None
        if clause[0] > 0:
            if tuple(-lit for lit in clause) not in clauses:
                return None
            triples.append(tuple(lit-1 for lit in clause))
    return tuple(triples) if 2*len(triples) == len(clauses) else None
