"""Four-matching NAE constructions with exactly balanced twelve-vertex blocks.

Vertex IDs are zero-based within this construction. The first matching has
one port triple per block. Its third vertex moves to the next block.
"""

from dataclasses import dataclass
from itertools import combinations


BLOCK = (
    ((0,7,9), (1,2,8), (3,4,11), (5,6,10)),
    ((0,4,8), (1,6,7), (2,3,10), (5,9,11)),
    ((0,2,5), (1,4,9), (3,6,8), (7,10,11)),
    ((0,1,11), (2,4,6), (3,5,7), (8,9,10)),
)
PORT = (3,4,11)
PORTS = ((3,4,11), (7,6,1), (0,5,2))
# Indexed by p + 2q + 4r. A monochromatic input has no extension.
ENCODING = (None, 0x64b, 0x5b2, 0x43b, 0xbc4, 0xa4d, 0x9b4, None)


@dataclass(frozen=True)
class BalancedSubstitution:
    source_blocks: tuple
    matchings: tuple

    def lift(self, bits):
        """Lift a coloring satisfying the first matching to its unique block states."""
        result = 0
        for block, triple in enumerate(self.source_blocks):
            key = sum(((bits >> v) & 1) << j for j, v in enumerate(triple))
            local = ENCODING[key]
            if local is None:
                raise ValueError("source block is monochromatic")
            result |= local << (12*block)
        return result

    def project(self, bits):
        """Read the logical p,q,r values from their first set of physical ports."""
        result = 0
        for block, triple in enumerate(self.source_blocks):
            for v, slot in zip(triple, PORTS[0]):
                result |= ((bits >> (12*block + slot)) & 1) << v
        return result


def balanced_substitution(matchings):
    """Replace a linear positive NAE instance with four given perfect matchings.

    Vertex IDs must form the dense range starting at zero. The returned four
    matchings use four times as many vertices. Models correspond bijectively.
    """
    matchings = tuple(tuple(tuple(edge) for edge in group) for group in matchings)
    if len(matchings) != 4:
        raise ValueError("expected four perfect matchings")
    blocks = matchings[0]
    vertex_count = 3 * len(blocks)
    seen_pairs = set()
    for group in matchings:
        seen = set()
        for edge in group:
            if len(edge) != 3 or len(set(edge)) != 3 or seen.intersection(edge):
                raise ValueError("expected disjoint triples in each matching")
            seen.update(edge)
            pairs = set(combinations(sorted(edge), 2))
            if seen_pairs & pairs:
                raise ValueError("triples must share at most one vertex")
            seen_pairs.update(pairs)
        if seen != set(range(vertex_count)):
            raise ValueError("each class must partition the same vertex set")

    positions = {v: (i, j) for i, block in enumerate(blocks) for j,v in enumerate(block)}
    output = [[], [], [], []]
    for i in range(len(blocks)):
        for color, rows in enumerate(BLOCK):
            for edge in rows:
                if color < 3 and set(edge) == set(PORTS[color]):
                    continue
                output[color].append(tuple(12*i + v for v in edge))
    for color, group in enumerate(matchings[1:]):
        for edge in group:
            external = []
            for v in edge:
                block, slot = positions[v]
                external.append(12*block + PORTS[color][slot])
            output[color].append(tuple(external))
    return BalancedSubstitution(blocks, tuple(tuple(group) for group in output))


def balanced_cycle(copies):
    if copies < 1:
        raise ValueError("at least one block is required")
    matchings = [[] for _ in BLOCK]
    for block in range(copies):
        for color, triples in enumerate(BLOCK):
            for a,b,c in triples:
                target = (block + 1) % copies if (a,b,c) == PORT else block
                matchings[color].append((12*block+a, 12*block+b, 12*target+c))
    return tuple(tuple(group) for group in matchings)


def proper(bits, triples):
    return all(0 < sum((bits >> i) & 1 for i in triple) < 3 for triple in triples)
