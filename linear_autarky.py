"""Exact rational null vectors give partial proper colorings of positive NAE."""

from dataclasses import dataclass
from fractions import Fraction


def kernel_vector(vertices, weighted_rows):
    """Return a nonzero null vector, or None if the columns have full rank."""
    basis = {}
    for entries in weighted_rows:
        row = {v:Fraction(w) for v,w in entries}
        while row:
            pivot = max(row)
            factor = row[pivot]
            if pivot not in basis:
                basis[pivot] = {v:value/factor for v,value in row.items()}
                break
            for v,value in basis[pivot].items():
                reduced = row.get(v,0)-factor*value
                if reduced:
                    row[v] = reduced
                else:
                    row.pop(v,None)
    free = next((v for v in vertices if v not in basis),None)
    if free is None:
        return None
    values = {free:Fraction(1)}
    for p in sorted(basis):
        value = -sum(coeff*values.get(v,0) for v,coeff in basis[p].items() if v!=p)
        if value:
            values[p] = value
    return values


@dataclass(frozen=True)
class Peeling:
    fixed: tuple
    remaining: tuple
    rounds: int

    def extend(self, other):
        """Combine the retained solver model with the partial witness (same coordinates)."""
        if len(other)!=len(self.fixed):
            raise ValueError("wrong assignment length")
        return tuple(f if f is not None else bool(x) for f,x in zip(self.fixed,other))


def peel(n, triples, doubled=None):
    """Remove triples satisfied independently by signs of a rational null vector.

    doubled[j], when given, is the local position 0, 1 or 2 whose coefficient
    is two in row j. Support of a null vector satisfies every row it touches.
    """
    triples = tuple(tuple(e) for e in triples)
    if n<0 or any(len(e)!=3 or len(set(e))!=3 or any(v<0 or v>=n for v in e) for e in triples):
        raise ValueError("expected positive triples on distinct in-range vertex IDs")
    if doubled is not None:
        doubled = tuple(doubled)
        if len(doubled)!=len(triples) or any(j not in (0,1,2) for j in doubled):
            raise ValueError("expected one doubled position per triple")
    indexed = list(enumerate(triples))
    fixed = [None]*n
    rounds = 0
    while indexed:
        vertices = sorted({v for _,e in indexed for v in e})
        matrix = [tuple((v,2 if doubled is not None and doubled[j]==k else 1)
                        for k,v in enumerate(edge)) for j,edge in indexed]
        vector = kernel_vector(vertices,matrix)
        if vector is None:
            break
        for v,value in vector.items():
            fixed[v] = value>0
        indexed = [(j,e) for j,e in indexed if all(v not in vector for v in e)]
        rounds += 1
    return Peeling(tuple(fixed),tuple(e for _,e in indexed),rounds)
