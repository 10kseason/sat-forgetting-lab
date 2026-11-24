"""Direct SAT via the maximal models of the retained 2-CNF background."""

from dataclasses import dataclass
from itertools import combinations

from binary_envelope import orientation
from two_sat import solve_2cnf


@dataclass(frozen=True)
class FrontierDecision:
    satisfiable: bool
    assignment: tuple | None
    cover: tuple
    patterns_checked: int
    maxima_evaluated: int


def conflict_graph(n, background, oriented):
    """The vertices are oriented literals individually feasible in the background."""
    if solve_2cnf(n, background) is None:
        return None
    graph = {v: set() for v in oriented if solve_2cnf(n, background, (v,)) is not None}
    for a, b in combinations(graph, 2):
        if solve_2cnf(n, background, (a, b)) is None:
            graph[a].add(b)
            graph[b].add(a)
    return graph


def matching_cover(graph):
    """Endpoints of a maximal matching form a 2-approximate cover. Trim it."""
    cover = set()
    for v, neighbors in graph.items():
        if v not in cover:
            available = neighbors - cover
            if available:
                cover.update((v, min(available)))
    for v in sorted(cover):
        if graph[v] <= cover:
            cover.remove(v)
    return tuple(sorted(cover))


def checked_cover(graph, cover=None):
    chosen_cover = matching_cover(graph) if cover is None else tuple(dict.fromkeys(cover))
    cset = set(chosen_cover)
    outside = set(graph) - cset
    if not cset <= graph.keys() or any(graph[v] & outside for v in outside):
        raise ValueError("supplied literals do not cover the conflict graph")
    return chosen_cover


def maximal_supports(graph, chosen_cover):
    """Yield (number of cover patterns visited so far, inclusion-maximal support)."""
    cset = set(chosen_cover)
    outside = set(graph) - cset
    for bits in range(1 << len(chosen_cover)):
        selected = {v for i, v in enumerate(chosen_cover) if bits >> i & 1}
        if any(graph[v] & selected for v in selected):
            continue
        maximum_candidate = selected | {v for v in outside if not graph[v] & selected}
        if any(not graph[v] & maximum_candidate for v in cset - selected):
            continue
        yield bits + 1, maximum_candidate


def solve_frontier(system, cover=None, max_patterns=None):
    """Return an exact decision or raise before enumeration if the budget is exceeded."""
    oriented = orientation(system)
    graph = conflict_graph(system.retained, system.background, oriented)
    if graph is None:
        return FrontierDecision(False, None, (), 0, 0)
    chosen_cover = checked_cover(graph, cover)
    count = 1 << len(chosen_cover)
    if max_patterns is not None and count > max_patterns:
        raise ValueError(f"requires up to {count} cover patterns, budget is {max_patterns}")
    examined = 0
    for patterns, maximum_candidate in maximal_supports(graph, chosen_cover):
        examined += 1
        fixed = tuple((v > 0) == (v in maximum_candidate) for v in oriented)
        solution = system.extend(fixed)
        if solution is not None:
            return FrontierDecision(True, solution, chosen_cover, patterns, examined)
    return FrontierDecision(False, None, chosen_cover, count, examined)
