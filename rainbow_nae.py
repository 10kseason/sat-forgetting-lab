"""A rank-two ternary kernel can reveal a hidden three-part coloring."""


def rainbow_witness(n, triples):
    """Return a proper bicoloring if a two-dimensional kernel reveals three parts.

    Each ternary row sums the colors of a triple. All constant vectors lie
    in its kernel. In dimension two all nonconstant vectors are equivalent up
    to a translation and a sign. Failure is inconclusive for bicolorability.
    """
    if n < 0:
        raise ValueError("negative vertex count")
    triples = tuple(tuple(e) for e in triples)
    basis = {}
    for edge in triples:
        if len(edge) != 3 or len(set(edge)) != 3 or any(v < 0 or v >= n for v in edge):
            raise ValueError("expected distinct in-range vertices")
        one = sum(1 << i for i in edge)
        two = 0
        while one | two:
            pivot = (one | two).bit_length()-1
            bit = 1 << pivot
            if pivot not in basis:
                basis[pivot] = (one,two) if one & bit else (two,one)
                break
            # Add the existing row or its negative to clear the pivot.
            p,q = basis[pivot]
            if one & bit:
                p,q = q,p
            empty_a, empty_b = ~(one|two), ~(p|q)
            one,two = ((one&empty_b)|(empty_a&p)|(two&q),
                       (two&empty_b)|(empty_a&q)|(one&p))
    free = [v for v in range(n) if v not in basis]
    if len(free) != 2:
        return None
    one, two = 1 << free[0], 0
    for v in sorted(basis):
        p,q = basis[v]
        value = -((p&one).bit_count() + 2*(p&two).bit_count() +
                  2*(q&one).bit_count() + (q&two).bit_count()) % 3
        if value == 1:
            one |= 1 << v
        elif value == 2:
            two |= 1 << v
    colors = tuple(((one>>v)&1) + 2*((two>>v)&1) for v in range(n))
    if any(len({colors[v] for v in edge})!=3 for edge in triples):
        return None
    return tuple(c==1 for c in colors)
