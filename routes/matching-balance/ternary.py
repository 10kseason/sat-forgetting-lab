"""Count proper four-round colorings modulo three by even omitted incidences."""

from functools import lru_cache
from itertools import combinations
from dataclasses import dataclass


@lru_cache(maxsize=6)
def columns(n):
    domain = (1 << (1 << n)) - 1
    masks = []
    for v in range(n):
        step = 1 << v
        masks.append((domain//((1 << (2*step))-1)) * (((1 << step)-1) << step))
    return domain, tuple(masks)


def parity_residue(n, triples):
    """Exponential in n bits of state; intended for a finite modular cross-check."""
    triples = tuple(tuple(e) for e in triples)
    occurrences = [0]*n
    for e in triples:
        if len(e)!=3 or len(set(e))!=3 or any(v<0 or v>=n for v in e):
            raise ValueError("expected three distinct in-range vertices")
        for v in e:
            occurrences[v] += 1
    domain, cols = columns(n)

    def shift(mask, v):
        step = 1 << v
        return ((mask & ~cols[v]) << step) | ((mask & cols[v]) >> step)

    def add(a1,a2,b1,b2):
        a0 = domain ^ (a1|a2)
        b0 = domain ^ (b1|b2)
        return ((a1&b0)|(a0&b1)|(a2&b2), (a2&b0)|(a0&b2)|(a1&b1))

    one,two = 1,0
    for a,b,c in triples:
        s1,s2 = add(shift(one,a),shift(two,a),shift(one,b),shift(two,b))
        one,two = add(s1,s2,shift(one,c),shift(two,c))
    # Selected-pair incidences are even precisely when the omitted incidences
    # have the same parity at each vertex as its total number of occurrences.
    wanted = sum((deg%2) << v for v,deg in enumerate(occurrences))
    factors = ((one>>wanted)&1) + 2*((two>>wanted)&1)
    return factors, (factors * pow(2,n,3) * (-1 if len(triples)%2 else 1))%3


def oriented_rank(groups, orders=None):
    """Rank mod three of the proposed skew clause matrix under local port orders."""
    n = 3*len(groups[0])
    incidence = [[] for _ in range(n)]
    rows = [edge for group in groups for edge in group]
    for i,edge in enumerate(rows):
        for v in edge:
            incidence[v].append(i)
    matrix = [[0]*len(rows) for _ in rows]
    for v,ports in enumerate(incidence):
        ordered = ports if orders is None else [ports[i] for i in orders[v]]
        for i,j in combinations(ordered,2):
            matrix[i][j] = (matrix[i][j]+1)%3
            matrix[j][i] = (matrix[j][i]-1)%3
    rank = 0
    for col in range(len(rows)):
        pivot = next((i for i in range(rank,len(rows)) if matrix[i][col]),None)
        if pivot is None:
            continue
        matrix[rank],matrix[pivot] = matrix[pivot],matrix[rank]
        p = matrix[rank]
        for i in range(rank+1,len(rows)):
            row = matrix[i]
            factor = row[col]*p[col]%3  # 1 and 2 each equal their inverse.
            if factor:
                matrix[i] = [(a-factor*b)%3 for a,b in zip(row,p)]
        rank += 1
    return rank


@dataclass(frozen=True)
class FourierDecision:
    status: str
    coloring: tuple | None
    peak_terms: int


def _add(terms, exponent, amount):
    new = (terms.get(exponent,0) + amount)%3
    if new:
        terms[exponent] = new
    else:
        terms.pop(exponent,None)


def sparse_model(n, triples, term_limit=None):
    """Compile the full GF(3) indicator, then recover a satisfying sign input."""
    if n < 0 or (term_limit is not None and term_limit < 1):
        raise ValueError("invalid dimension or term limit")
    terms = {0:1}
    peak = 1
    for e in triples:
        e = tuple(e)
        if len(e)!=3 or len(set(e))!=3 or any(v<0 or v>=n for v in e):
            raise ValueError("expected distinct in-range vertices")
        pairs = [(1 << a) | (1 << b) for a,b in combinations(e,2)]
        after = {}
        for exponent, value in terms.items():
            for pair in pairs:
                _add(after,exponent ^ pair,-value)
        terms = after
        peak = max(peak,len(terms))
        if not terms:
            return FourierDecision("UNSAT",None,peak)
        if term_limit is not None and len(terms)>term_limit:
            return FourierDecision("UNKNOWN",None,peak)
    assignment = []
    for vertex in range(n):
        bit = 1 << vertex
        plus,minus = {},{}
        for exponent,value in terms.items():
            target = exponent & ~bit
            _add(plus,target,value)
            _add(minus,target,-value if exponent & bit else value)
        assignment.append(bool(plus))
        terms = plus if plus else minus
    return FourierDecision("SAT",tuple(assignment),peak)
