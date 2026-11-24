"""Quadratic tests for the binary consequences of a syntactically unate projection."""

from dataclasses import dataclass
from itertools import combinations

from forgetting import HiddenCNF, cnf_value
from two_sat import solve_2cnf


def orientation(system):
    """Return one signed literal per retained variable; the background is separate."""
    signs = [0] * system.retained
    clauses = [*system.goals, *(c for tails in system.rules.values() for c in tails)]
    for c in clauses:
        for v in c:
            if abs(v) <= system.retained:
                if signs[abs(v) - 1] not in (0, v):
                    raise ValueError("retained literals in the hidden system must be unate")
                signs[abs(v) - 1] = v
    return tuple(v or i for i, v in enumerate(signs, 1))


def projected_value(system, fixed):
    return cnf_value(system.goals, tuple(fixed) + system.greatest(fixed))


@dataclass(frozen=True)
class UnaryExactness:
    exact: bool
    clauses: tuple
    counterexample: tuple | None


def unary_exactness(system):
    """Recognize exact unary CNF in at most n+2 evaluations of the monotone projection."""
    literals = orientation(system)
    top = tuple(v > 0 for v in literals)
    if not projected_value(system, top):
        return UnaryExactness(True, ((),), None)
    units = set()
    for i, v in enumerate(literals):
        missing = list(top)
        missing[i] = not top[i]
        if not projected_value(system, missing):
            units.add(v)
    least = tuple((v > 0) == (v in units) for v in literals)
    exact = projected_value(system, least)
    return UnaryExactness(exact, tuple((v,) for v in literals if v in units),
                          None if exact else least)


def binary_envelope(system):
    """Compute the strongest width-at-most-two consequences of the monotone part."""
    oriented = orientation(system)
    clauses = []
    forced = set()
    for width in range(3):
        for zeros in combinations(oriented, width):
            if forced.intersection(zeros):
                continue
            largest = tuple((v > 0) != (v in zeros) for v in oriented)
            if not projected_value(system, largest):
                if width == 0:
                    return ((),)
                if width == 1:
                    forced.add(zeros[0])
                clauses.append(zeros)
    return tuple(clauses)


@dataclass(frozen=True)
class Decision:
    status: str
    assignment: tuple | None
    wide_prime: tuple | None = None


def decide_with_envelope(system):
    envelope = binary_envelope(system)
    fixed = solve_2cnf(system.retained, (*system.background, *envelope))
    if fixed is None:
        return Decision("UNSAT", None)
    extension = system.extend(fixed)
    if extension is not None:
        return Decision("SAT", extension)
    # Grow a rejected retained input to a maximal false input of the monotone
    # part. Growth need not preserve the separate background.
    oriented = orientation(system)
    maximal = list(fixed)
    for i, literal in enumerate(oriented):
        top = literal > 0
        if maximal[i] != top:
            maximal[i] = top
            if projected_value(system, maximal):
                maximal[i] = not top
    prime = tuple(v for i, v in enumerate(oriented) if maximal[i] != (v > 0))
    return Decision("UNRESOLVED", fixed, prime)


def recognition_instance(variables, formula):
    """Map a 3-CNF to an acyclic hidden system whose binary exactness means UNSAT."""
    if variables < 0:
        raise ValueError("negative variable count")
    retained = 2 * variables + 3
    next_var = retained
    clauses = [(2*i + 1, 2*i + 2) for i in range(variables)]

    def gate(inputs, conjunction):
        nonlocal next_var
        if not inputs and conjunction:
            next_var += 1
            return next_var  # Free head. Its greatest feasible value is true.
        while len(inputs) > 1:
            level = []
            for i in range(0, len(inputs), 2):
                pair = inputs[i:i + 2]
                if len(pair) == 1:
                    level.extend(pair)
                else:
                    next_var += 1
                    if conjunction:
                        clauses.extend((-next_var, v) for v in pair)
                    else:
                        clauses.append((-next_var, *pair))
                    level.append(next_var)
            inputs = level
        return inputs[0]

    terms = [retained-2, retained-1, retained]
    for clause in formula:
        if len(clause) > 3 or any(v == 0 or abs(v) > variables for v in clause):
            raise ValueError("expected a 3-CNF on the supplied variables")
        rails = [2*(abs(v)-1) + (1 if v > 0 else 2) for v in clause]
        terms.append(gate(rails, True))
    clauses.append((gate(terms, False),))
    return HiddenCNF(retained, next_var - retained, clauses)
