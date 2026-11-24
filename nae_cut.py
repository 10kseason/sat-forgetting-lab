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


def cut_obstruction(clauses):
    """Find a component whose signed NAE triples demand too many disagreements.

    Inputs are normalized clauses (distinct literals in variable order).
    Either polarity can be chosen to represent a complementary clause pair.
    """
    clauses = set(clauses)
    adjacent = {}
    pair_weights = Counter()
    same_total = Counter()
    triple_count = Counter()
    for clause in clauses:
        if len(clause) != 3 or clause[0] < 0:
            continue
        if tuple(-lit for lit in clause) not in clauses:
            continue
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
    return None
