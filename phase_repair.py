"""Solve four-round positive NAE through bounded components with two boundary states."""

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations


@lru_cache(maxsize=20)
def _columns(width):
    total = (1 << (1 << width)) - 1
    columns = []
    for i in range(width):
        run = 1 << i
        period = (1 << (2*run))-1
        columns.append((total//period) * (((1 << run)-1) << run))
    return total, tuple(columns)


@dataclass(frozen=True)
class PhaseDecision:
    status: str
    assignment: tuple | None
    component_sizes: tuple


def solve_resolved_phases(matchings, omitted, max_block=16):
    """Find components in three rounds, then enforce all four via their interfaces.

    UNKNOWN means the selected decomposition or interface exceeded this method.
    max_block limits the number of vertices in any truth-table computation.
    Vertex IDs are dense and zero-based. Each input round partitions the vertices.
    """
    groups = tuple(tuple(tuple(e) for e in group) for group in matchings)
    if len(groups)!=4 or omitted not in range(4) or max_block < 0:
        raise ValueError("expected four matchings, a round index, and a nonnegative block limit")
    n = 3*len(groups[0])
    adj = [set() for _ in range(n)]
    all_edges = []
    for j,group in enumerate(groups):
        if any(len(e)!=3 for e in group) or sorted(v for e in group for v in e)!=list(range(n)):
            raise ValueError("each round must partition the vertices into triples")
        all_edges.extend(group)
        if j != omitted:
            for edge in group:
                for a,b in combinations(edge,2):
                    adj[a].add(b)
                    adj[b].add(a)
    block_of = [-1]*n
    blocks = []
    for root in range(n):
        if block_of[root] != -1:
            continue
        block = [root]
        block_of[root] = len(blocks)
        for u in block:
            for v in adj[u]:
                if block_of[v] == -1:
                    block_of[v] = len(blocks)
                    block.append(v)
        blocks.append(block)
    sizes = tuple(map(len,blocks))
    if any(s > max_block for s in sizes):
        return PhaseDecision("UNKNOWN",None,sizes)

    inside = [[] for _ in blocks]
    boundary = [set() for _ in blocks]
    cross = []
    for a,b,c in all_edges:
        if block_of[a] == block_of[b] == block_of[c]:
            inside[block_of[a]].append((a,b,c))
        else:
            cross.append((a,b,c))
            for v in (a,b,c):
                boundary[block_of[v]].add(v)

    base = [False]*n
    for group,block in enumerate(blocks):
        local = {v:i for i,v in enumerate(block)}
        allowed, cols = _columns(len(block))
        for edge in inside[group]:
            a,b,c = (cols[local[v]] for v in edge)
            allowed &= (a^b) | (b^c)
        if not allowed:
            return PhaseDecision("UNSAT",None,sizes)
        model = (allowed & -allowed).bit_length()-1
        for i,v in enumerate(block):
            base[v] = bool((model >> i)&1)
        ports = boundary[group]
        if ports:
            anchor = next(iter(ports))
            for v in ports:
                differing = cols[local[anchor]] ^ cols[local[v]]
                wrong = ~differing if base[anchor] != base[v] else differing
                if allowed & wrong:
                    return PhaseDecision("UNKNOWN",None,sizes)

    parity = [[] for _ in blocks]
    for edge in cross:
        a,b,c = edge
        if block_of[a]!=block_of[b]:
            if block_of[a]==block_of[c]:
                b,c = c,b
            elif block_of[b]==block_of[c]:
                a,b,c = b,c,a
            else:
                return PhaseDecision("UNKNOWN",None,sizes)
        if base[a] == base[b]:
            u,v = block_of[a], block_of[c]
            delta = True ^ base[a] ^ base[c]
            parity[u].append((v,delta))
            parity[v].append((u,delta))
    phase = [None]*len(blocks)
    for root in range(len(blocks)):
        if phase[root] is not None:
            continue
        phase[root] = False
        queue = [root]
        for u in queue:
            for v,delta in parity[u]:
                expected = phase[u] ^ delta
                if phase[v] is None:
                    phase[v] = expected
                    queue.append(v)
                elif phase[v] != expected:
                    return PhaseDecision("UNSAT",None,sizes)
    model = tuple(base[v] ^ phase[block_of[v]] for v in range(n))
    if not all(model[a]!=model[b] or model[b]!=model[c] for a,b,c in all_edges):
        raise AssertionError("phase witness violates an original triple")
    return PhaseDecision("SAT",model,sizes)
