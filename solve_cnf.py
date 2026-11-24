"""Complete SAT search parameterized by a detected renamable dual-Horn backdoor."""

import argparse
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
import sys

from forgetting import HiddenCNF, canonical, cnf_value
from gf2 import equations_in_cnf, one_solution, reduce_system
from nae_cut import cut_obstruction
from anonymous_blocks import contract, from_cnf
from pivot_elimination import first_non_growing, minimal, recover
from two_sat import solve_2cnf


@dataclass(frozen=True)
class SearchResult:
    status: str
    assignment: tuple | None
    retained: tuple
    assignments_tested: int
    method: str
    eliminated: tuple = ()


def hidden_orientation(n, clauses):
    """Each pair in a clause requires at least one hidden literal to be positive."""
    pairs = sorted({pair for c in clauses for pair in combinations(c, 2)})
    all_vars = set(range(1, n + 1))
    preferred = solve_2cnf(n, pairs)
    if preferred is not None:
        return all_vars, preferred
    incident = {i: [] for i in all_vars}
    for left, right in pairs:
        incident[abs(left)].append((left, right))
        incident[abs(right)].append((right, left))
    hidden, required = set(), []
    for v in range(1, n + 1):
        new = [(a, b) for a, b in incident[v] if abs(b) in hidden]
        candidate = solve_2cnf(n, required + new)
        if candidate is not None:
            hidden.add(v)
            required.extend(new)
            preferred = candidate
    return hidden, preferred


def shortcut(n, clauses, use_affine, use_cut=True):
    if () in clauses:
        return SearchResult("UNSAT", None, (), 0, "empty clause")
    if all(len(c) <= 2 for c in clauses):
        result = solve_2cnf(n, sorted(clauses))
        return SearchResult("UNSAT" if result is None else "SAT", result, (), 0, "2-SAT")
    if use_affine:
        rows = equations_in_cnf(clauses)
        if rows:
            basis = reduce_system(n, rows)
            if basis is None:
                return SearchResult("UNSAT", None, (), 0, "affine contradiction")
            witness = one_solution(n, basis)
            if cnf_value(clauses, witness):
                return SearchResult("SAT", witness, (), 0, "affine witness")
    if use_cut and cut_obstruction(clauses) is not None:
        return SearchResult("UNSAT", None, (), 0, "NAE cut bound")
    return None


def branch(n, clauses, max_patterns):
    hidden, preferred = hidden_orientation(n, clauses)
    rest = tuple(i for i in range(1, n + 1) if i not in hidden)
    order = (*rest, *sorted(hidden))
    number = {v: i for i, v in enumerate(order, 1)}
    sign = {v: (-1 if v in hidden and not preferred[v-1] else 1) for v in order}
    shifted = [tuple(number[abs(v)] * sign[abs(v)] * (1 if v > 0 else -1) for v in c)
               for c in sorted(clauses)]
    system = HiddenCNF(len(rest), len(hidden), shifted)
    tested = 0
    for fixed in product((False, True), repeat=len(rest)):
        if max_patterns is not None and tested >= max_patterns:
            return SearchResult("UNKNOWN", None, rest, tested, "backdoor")
        tested += 1
        result = system.extend(fixed)
        if result is not None:
            model = tuple(result[number[v]-1] == (sign[v] > 0) for v in range(1, n+1))
            return SearchResult("SAT", model, rest, tested, "backdoor")
    return SearchResult("UNSAT", None, rest, tested, "backdoor")


def solve(n, raw, max_patterns=None, *, use_affine=True, use_elimination=True, use_cut=True,
          use_blocks=True):
    if n < 0 or (max_patterns is not None and max_patterns < 1):
        raise ValueError("invalid variable count or search budget")
    original = set()
    for item in raw:
        item = tuple(item)
        if any(not v or abs(v) > n for v in item):
            raise ValueError("literal out of range")
        c = canonical(item)
        if c is not None:
            original.add(c)
    level = from_cnf(n, original) if use_blocks else None
    if level is not None:
        levels = [level]
        while (next_level := contract(level.vertices, level.triples)) is not None:
            levels.append(next_level)
            level = next_level
        core = []
        for edge in level.triples:
            clause = tuple(i+1 for i in edge)
            core.extend((clause, tuple(-lit for lit in clause)))
        answer = solve(level.vertices, core, max_patterns, use_affine=use_affine,
                       use_elimination=use_elimination, use_cut=use_cut, use_blocks=False)
        assignment = answer.assignment
        retained = tuple(i-1 for i in answer.retained)
        for layer in reversed(levels):
            if assignment is not None:
                assignment = layer.lift(assignment)
            representatives = layer.representatives()
            retained = tuple(representatives[i] for i in retained)
        if assignment is not None and not cnf_value(original, assignment):
            raise AssertionError("expanded assignment does not satisfy the input")
        return SearchResult(answer.status, assignment, tuple(i+1 for i in retained),
                            answer.assignments_tested, f"NAE block contraction / {answer.method}")
    clauses = minimal(original) if use_elimination else original
    trace = []
    while True:
        answer = shortcut(n, clauses, use_affine, use_cut)
        if answer is not None:
            break
        step = first_non_growing(clauses) if use_elimination else None
        if step is None:
            answer = branch(n, clauses, max_patterns)
            break
        clauses, witness_step = step
        trace.append(witness_step)
    model = None
    if answer.assignment is not None:
        model = recover(trace, answer.assignment)
        if not cnf_value(original, model):
            raise AssertionError("reconstructed assignment does not satisfy the input")
    return SearchResult(answer.status, model, answer.retained, answer.assignments_tested,
                        answer.method, tuple(v for v, _ in trace))


def read_dimacs(lines):
    header, current, clauses = None, [], []
    for number, raw in enumerate(lines, 1):
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            fields = line.split()
            if header is not None or len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise ValueError(f"bad problem header at line {number}")
            header = tuple(map(int, fields[2:]))
            if min(header) < 0:
                raise ValueError("negative DIMACS count")
            continue
        if header is None:
            raise ValueError("missing DIMACS problem header")
        for token in line.split():
            v = int(token)
            if abs(v) > header[0]:
                raise ValueError(f"out-of-range literal at line {number}")
            if v:
                current.append(v)
            else:
                clauses.append(tuple(current))
                current.clear()
    if header is None or current or len(clauses) != header[1]:
        raise ValueError("missing header, unterminated clause or incorrect clause count")
    return header[0], clauses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", nargs="?", type=Path, help="DIMACS file (defaults to stdin)")
    parser.add_argument("--max-patterns", type=int, help="stop search after this many assignments")
    parser.add_argument("--no-affine", action="store_true", help="skip parity-block recognition")
    parser.add_argument("--no-elimination", action="store_true", help="skip non-growing resolution")
    parser.add_argument("--no-cut", action="store_true", help="skip the signed NAE cut bound")
    parser.add_argument("--no-blocks", action="store_true", help="skip anonymous NAE block contraction")
    args = parser.parse_args()
    try:
        if args.file is None:
            n, clauses = read_dimacs(sys.stdin)
        else:
            with args.file.open(encoding="utf-8") as source:
                n, clauses = read_dimacs(source)
        result = solve(n, clauses, args.max_patterns, use_affine=not args.no_affine,
                       use_elimination=not args.no_elimination, use_cut=not args.no_cut,
                       use_blocks=not args.no_blocks)
    except (ValueError, OSError) as error:
        parser.error(str(error))
    print(f"c method {result.method} pivots {len(result.eliminated)} retained {len(result.retained)}"
          f" assignments_tested {result.assignments_tested}")
    if result.status == "SAT":
        print("s SATISFIABLE")
        print("v", *(i if bit else -i for i, bit in enumerate(result.assignment, 1)), 0)
        return 10
    if result.status == "UNSAT":
        print("s UNSATISFIABLE")
        return 20
    print("s UNKNOWN")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
