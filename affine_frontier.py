"""Decide a unate HiddenCNF with retained 2-CNF and affine restrictions."""

from dataclasses import dataclass
from itertools import combinations

from binary_envelope import orientation
from frontier_sat import checked_cover, conflict_graph, maximal_supports


@dataclass(frozen=True)
class AffineFrontierDecision:
    assignment: tuple[bool, ...] | None
    cover: tuple[int, ...]
    rank: int
    cover_patterns: int
    maxima_examined: int
    seed_sets: int
    membership_queries: int

    @property
    def satisfiable(self) -> bool:
        return self.assignment is not None


def parity_columns(variables, rows):
    """Turn row masks over retained variables into packed syndrome columns."""
    columns = [0] * variables
    rhs = 0
    for row, (mask, value) in enumerate(rows):
        if not isinstance(mask, int) or mask < 0 or mask.bit_length() > variables:
            raise ValueError("an equation mask must only reference retained variables")
        if value not in (0, 1):
            raise ValueError("an equation right-hand side must be 0 or 1")
        equation = 1 << row
        if value:
            rhs |= equation
        while mask:
            bit = mask & -mask
            columns[bit.bit_length() - 1] |= equation
            mask ^= bit
    return columns, rhs


def reduce_syndrome(value, basis):
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            break
        value ^= basis[pivot]
    return value


def syndrome_basis(vectors):
    basis = {}
    for value in vectors:
        remainder = reduce_syndrome(value, basis)
        if remainder:
            basis[remainder.bit_length() - 1] = remainder
    return basis


def syndrome(columns, support):
    result = 0
    for literal in support:
        result ^= columns[abs(literal) - 1]
    return result


def block_closures(maximum, background, columns):
    """Map each SCC's predecessor closure to the syndrome of that SCC alone."""
    predecessors = {literal: set() for literal in maximum}
    for clause in background:
        if len(clause) != 2:
            continue
        left, right = clause
        for start, end in ((-left, right), (-right, left)):
            if start in predecessors and end in predecessors:
                predecessors[end].add(start)

    blocks = {}
    for literal in sorted(maximum):
        visited = {literal}
        stack = [literal]
        while stack:
            unseen = predecessors[stack.pop()] - visited
            visited.update(unseen)
            stack.extend(unseen)
        closure = frozenset(visited)
        # Two vertices have the same predecessor closure exactly when in one SCC.
        blocks[closure] = blocks.get(closure, 0) ^ columns[abs(literal) - 1]
    return blocks


def solve_affine_frontier(system, rows, cover=None, oriented=None):
    """Solve exactly. A supplied orientation must be monotone for the projection."""
    n = system.retained
    if oriented is None:
        oriented = orientation(system)
    else:
        oriented = tuple(oriented)
        if len(oriented) != n or any(
            not isinstance(literal, int) or abs(literal) != i
            for i, literal in enumerate(oriented, 1)
        ):
            raise ValueError("give one signed orientation literal per variable, in order")

    columns, rhs = parity_columns(n, rows)
    basis = syndrome_basis(columns)
    rank = len(basis)
    if reduce_syndrome(rhs, basis):
        return AffineFrontierDecision(None, (), rank, 0, 0, 0, 0)

    graph = conflict_graph(n, system.background, oriented)
    if graph is None:
        return AffineFrontierDecision(None, (), rank, 0, 0, 0, 0)
    cover = checked_cover(graph, cover)
    target = rhs ^ syndrome(columns, (literal for literal in oriented if literal < 0))
    maxima = seed_sets = membership_queries = 0
    for patterns, maximum in maximal_supports(graph, cover):
        maxima += 1
        drop_target = target ^ syndrome(columns, maximum)
        blocks = block_closures(maximum, system.background, columns)
        local_basis = syndrome_basis(blocks.values())
        if reduce_syndrome(drop_target, local_basis):
            continue

        for count in range(len(local_basis) + 1):
            for seeds in combinations(blocks, count):
                seed_sets += 1
                dropped = set().union(*seeds)
                if syndrome(columns, dropped) != drop_target:
                    continue
                support = maximum - dropped
                fixed = tuple((literal > 0) == (literal in support) for literal in oriented)
                membership_queries += 1
                assignment = system.extend(fixed)
                if assignment is not None:
                    return AffineFrontierDecision(
                        assignment, cover, rank, patterns, maxima, seed_sets, membership_queries
                    )
    return AffineFrontierDecision(
        None, cover, rank, 1 << len(cover), maxima, seed_sets, membership_queries
    )
