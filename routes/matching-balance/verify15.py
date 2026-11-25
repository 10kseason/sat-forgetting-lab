"""Validate every catalogue row in reflected Gray-code assignment order."""

from collections import Counter
from csv import DictReader
from gzip import open as gzopen
from itertools import chain, combinations
from pathlib import Path
import argparse
import subprocess
import sys


def gray_columns():
    width = 1 << 15
    table = [bytearray(width//8) for _ in range(15)]
    for k in range(width):
        gray = k ^ (k >> 1)
        for v in range(15):
            if gray & (1 << v):
                table[v][k//8] |= 1 << (k%8)
    return [int.from_bytes(row,"little") for row in table]


def check_negative_formulas(negative_rows):
    """Give Lean the two Boolean clauses of each triple and prove a contradiction."""
    source = ["import Std", "set_option maxHeartbeats 4000000"]
    variables = " ".join(f"p{i}" for i in range(15))
    for index, groups in negative_rows:
        premises = []
        for triple in chain.from_iterable(groups):
            for sign in ("", "¬"):
                literals = (f"{sign}p{v}" for v in triple)
                premises.append("(" + " ∨ ".join(literals) + ")")
        source.append(f"theorem row{index} ({variables} : Prop) :")
        source.append(" →\n".join([*premises, "False := by grind (splits := 32) only"]))
    # The generated propositions are checks on this data file, so pass them through stdin.
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--stdin"],
        input="\n".join(source).encode("utf-8"),
        cwd=Path(__file__).resolve().parents[2],
        check=True,
    )
    print(f"Lean proved unsatisfiability of {len(negative_rows)} catalogue formulas")


def verify(path, check_solver=False, check_lean_unsat=False):
    if not __debug__:
        raise RuntimeError("Catalogue checks require Python assertions. Run without -O.")
    if check_solver:
        sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
        from forgetting import cnf_value
        from solve_cnf import solve
    cols = gray_columns()
    all_bits = (1 << (1<<15))-1
    allowed = {(a,b,c): (cols[a]^cols[b]) | (cols[b]^cols[c])
               for a,b,c in combinations(range(15),3)}
    seen = set()
    histogram = Counter()
    misses = Counter()
    methods = Counter()
    max_trials = {}
    negative_rows = []
    with gzopen(path,"rt",encoding="ascii",newline="") as stream:
        for index, row in enumerate(DictReader(stream, delimiter="\t")):
            key = tuple(row[f"class{i}"] for i in range(4))
            assert key not in seen
            seen.add(key)
            masks, groups, pairs = [], [], set()
            for group in key:
                triples = [tuple(int(ch,16) for ch in e) for e in group.split(".")]
                assert sorted(v for edge in triples for v in edge) == list(range(15))
                mask = all_bits
                for e in triples:
                    assert e == tuple(sorted(e)) and len(e) == 3
                    for pair in combinations(e,2):
                        assert pair not in pairs
                        pairs.add(pair)
                    mask &= allowed[e]
                groups.append(triples)
                masks.append(mask)
            full = masks[0]&masks[1]&masks[2]&masks[3]
            count = full.bit_count()
            assert count == int(row["colorings"])
            histogram[count] += 1
            if check_lean_unsat and count == 0:
                negative_rows.append((index, groups))
            if check_solver:
                formula = [tuple(sign*(v+1) for v in e) for g in groups for e in g
                           for sign in (1,-1)]
                result = solve(15,formula)
                assert result.status == ("SAT" if count else "UNSAT")
                if count:
                    assert result.assignment is not None and len(result.assignment) == 15
                    assert cnf_value(formula,result.assignment)
                else:
                    assert result.assignment is None
                route = (result.status, result.method)
                methods[route] += 1
                max_trials[route] = max(max_trials.get(route, 0), result.assignments_tested)
            for omit in range(4):
                partial = all_bits
                for j,mask in enumerate(masks):
                    if j!=omit:
                        partial &= mask
                assert partial.bit_count() == int(row[f"drop{omit}"])
                if not full:
                    # How many restored triples must be left out to regain a model?
                    for removed in range(1,6):
                        possible = False
                        for keep in combinations(groups[omit],5-removed):
                            trial = partial
                            for e in keep:
                                trial &= allowed[e]
                            if trial:
                                possible = True
                                break
                        if possible:
                            misses[removed] += 1
                            break
    assert len(seen) == 13933 and histogram[0] == 109
    print("verified designs",len(seen),"SAT",len(seen)-histogram[0],"UNSAT",histogram[0])
    print("minimum missed restored triples on UNSAT design/round pairs",sorted(misses.items()))
    if check_solver:
        print("default solver routes",sorted(methods.items()))
        print("maximum assignment trials by route", sorted(max_trials.items()))
    if check_lean_unsat:
        check_negative_formulas(negative_rows)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver",action="store_true",help="also solve and check every original CNF")
    parser.add_argument("--lean-unsat", action="store_true",
                        help="also prove each negative row inconsistent in Lean")
    args = parser.parse_args()
    verify(Path(__file__).with_name("order15.tsv.gz"), args.solver, args.lean_unsat)
