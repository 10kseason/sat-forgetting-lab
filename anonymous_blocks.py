"""Recover a smaller positive NAE system from unordered, unlabeled triples."""

from dataclasses import dataclass
from itertools import combinations


# Bit k is set precisely when physical assignment k has the indicated bit set.
_ALL = (1 << 4096) - 1
_COLUMN = tuple(sum(1 << k for k in range(4096) if (k >> i) & 1) for i in range(12))


def _local_literals(triples):
    """Certify the complete relation on a 12-block, then find its signed copies.

    The local table itself determines the three logical bits. A positive
    return entry j means copy logical bit j, a negative entry means negate it.
    """
    allowed = _ALL
    for a,b,c in triples:
        x,y,z = _COLUMN[a], _COLUMN[b], _COLUMN[c]
        allowed &= (x | y | z) & ~(x & y & z)
    if allowed.bit_count() != 6:
        return None
    models = []
    while allowed:
        first = allowed & -allowed
        models.append(first.bit_length()-1)
        allowed ^= first
    columns = [sum(((x >> i) & 1) << j for j,x in enumerate(models)) for i in range(12)]
    classes = []
    references = []
    for signature in columns:
        key = min(signature, 63 ^ signature)
        if key not in classes:
            classes.append(key)
        references.append((classes.index(key), signature != key))
    if len(classes) != 3:
        return None

    words = {sum(((col >> j) & 1) << i for i,col in enumerate(classes)) for j in range(6)}
    missing = sorted(set(range(8)) - words)
    if len(missing) != 2 or missing[0] ^ missing[1] != 7:
        return None
    # Translate the two absent words to 000 and 111, leaving exactly NAE.
    return tuple(-(i+1) if neg ^ bool(missing[0] & (1 << i)) else i+1 for i,neg in references)


def _switching(n, signed_edges):
    """Find vertex complements making all literals of each signed triple agree in sign."""
    edges = [[] for _ in range(n)]
    for a,b,c in signed_edges:
        for x,y in ((a,b), (b,c)):
            u,v = abs(x)-1, abs(y)-1
            parity = (x < 0) != (y < 0)
            edges[u].append((v,parity))
            edges[v].append((u,parity))
    flips = [None]*n
    for start in range(n):
        if flips[start] is not None:
            continue
        flips[start] = False
        queue = [start]
        while queue:
            u = queue.pop()
            for v,parity in edges[u]:
                required = flips[u] ^ parity
                if flips[v] is None:
                    flips[v] = required
                    queue.append(v)
                elif flips[v] != required:
                    return None
    return flips


@dataclass(frozen=True)
class Contraction:
    triples: tuple
    # One signed, one-based logical literal for each zero-based physical vertex.
    references: tuple

    @property
    def vertices(self):
        return len(self.references)//4

    def lift(self, logical):
        if len(logical) != self.vertices:
            raise ValueError("wrong logical assignment length")
        return tuple(bool(logical[abs(ref)-1]) ^ (ref < 0) for ref in self.references)

    def project(self, physical):
        if len(physical) != len(self.references):
            raise ValueError("wrong physical assignment length")
        values = [None]*self.vertices
        for ref,bit in zip(self.references, physical):
            j = abs(ref)-1
            logical = bool(bit) ^ (ref < 0)
            if values[j] is not None and values[j] != logical:
                raise ValueError("inconsistent signed copies")
            values[j] = logical
        return tuple(values)

    def representatives(self):
        """Physical vertex IDs representing each logical bit, up to a known sign."""
        vertices = [None]*self.vertices
        for i,ref in enumerate(self.references):
            if vertices[abs(ref)-1] is None:
                vertices[abs(ref)-1] = i
        return tuple(vertices)


def contract(n, triples):
    """Return a certified reduction when the structural and semantic checks pass.

    Vertex IDs are 0..n-1. Each triple is a positive NAE constraint. A failed
    recognition returns None. It gives no information about satisfiability.
    """
    if n < 12 or n % 12:
        return None
    triples = tuple(tuple(edge) for edge in triples)
    if 3*len(triples) != 4*n:
        return None
    adj = [set() for _ in range(n)]
    for edge in triples:
        if len(edge) != 3 or len(set(edge)) != 3 or any(v < 0 or v >= n for v in edge):
            return None
        for u,v in combinations(edge,2):
            if v in adj[u]:
                return None
            adj[u].add(v)
            adj[v].add(u)
    if any(len(neighbors) != 8 for neighbors in adj):
        return None

    group = [-1]*n
    blocks = []
    for start in range(n):
        if group[start] != -1:
            continue
        block = [start]
        group[start] = len(blocks)
        for u in block:
            for v in adj[u]:
                if group[v] == -1 and len(adj[u] & adj[v]) >= 2:
                    group[v] = len(blocks)
                    block.append(v)
        if len(block) != 12:
            return None
        blocks.append(sorted(block))
    interiors = [[] for _ in blocks]
    external = []
    for a,b,c in triples:
        if group[a] == group[b] == group[c]:
            interiors[group[a]].append((a,b,c))
        elif len({group[a],group[b],group[c]}) == 3:
            external.append((a,b,c))
        else:
            return None
    refs = [0]*n
    signed_edges = []
    for j, block in enumerate(blocks):
        if len(interiors[j]) != 13:
            return None
        local = {v: i for i,v in enumerate(block)}
        indexed = [(local[a],local[b],local[c]) for a,b,c in interiors[j]]
        coordinates = _local_literals(indexed)
        if coordinates is None:
            return None
        for v,lit in zip(block,coordinates):
            refs[v] = lit + 3*j if lit > 0 else lit - 3*j
        signed_edges.append((3*j+1, 3*j+2, 3*j+3))
    signed_edges.extend((refs[a],refs[b],refs[c]) for a,b,c in external)
    flips = _switching(3*len(blocks), signed_edges)
    if flips is None:
        return None
    refs = tuple(-lit if flips[abs(lit)-1] else lit for lit in refs)
    positive = tuple(tuple(abs(lit)-1 for lit in edge) for edge in signed_edges)
    return Contraction(positive, refs)


def from_cnf(n, clauses):
    """Recognize complete positive NAE pairs in normalized DIMACS clauses."""
    if n < 12 or n % 12 or 3*len(clauses) != 8*n:
        return None
    triples = []
    for clause in clauses:
        if len(clause) != 3 or any((lit > 0) != (clause[0] > 0) for lit in clause):
            return None
        if clause[0] > 0:
            if tuple(-lit for lit in clause) not in clauses:
                return None
            triples.append(tuple(lit-1 for lit in clause))
    if 2*len(triples) != len(clauses):
        return None
    return contract(n, triples)
