"""Cross-check the GF(3) parity expansion and counts on pinned connected blocks."""

import csv
import gzip
from itertools import combinations, product
from pathlib import Path
import random

from independent import affine_plane
from ternary import oriented_rank, parity_residue, sparse_model


def parse(row):
    return tuple(tuple(tuple(int(v,16) for v in e) for e in row[f"class{i}"].split("."))
                 for i in range(4))


def good(bits, edges):
    return all(len({(bits>>v)&1 for v in e})==2 for e in edges)


def check():
    counts = [0,0,0]
    with gzip.open(Path(__file__).with_name("order15.tsv.gz"),"rt",encoding="ascii") as f:
        for idx,row in enumerate(csv.DictReader(f,delimiter="\t")):
            groups = parse(row)
            edges = [e for g in groups for e in g]
            residue = parity_residue(15,edges)[1]
            assert residue == int(row["colorings"])%3
            counts[residue] += 1
            if idx == 18:
                open_edges = [e for e in edges if e!=(0,1,2)]
                states = [x for x in range(1<<15) if good(x,open_edges)]
                assert len(states)==24 and all(good(x,edges) for x in states)
                assert all(((x>>0)^(x>>2)) & 1 for x in states)
                assert all(sum(x>>v&1 for x in states)==12 for v in range(15))
                assert sum((x & 3)==0 for x in states)==1
    assert counts == [4653,4706,4574]

    plane = affine_plane()
    assert oriented_rank(plane)==4
    orders = ((0,2,3,1),(2,1,3,0),(1,2,0,3),(1,3,2,0),(0,2,3,1),
              (2,0,1,3),(3,2,0,1),(0,3,2,1),(1,2,3,0))
    assert oriented_rank(plane,orders)==12
    assert sparse_model(9,[e for g in plane for e in g]).status == "UNSAT"
    rng = random.Random(367172011)
    for n in range(3,9):
        pool = list(combinations(range(n),3))
        for _ in range(24):
            edges = rng.sample(pool,rng.randrange(len(pool)+1))
            models = [x for x in range(1<<n) if good(x,edges)]
            decision = sparse_model(n,edges)
            assert decision.status == ("SAT" if models else "UNSAT")
            if decision.coloring is not None:
                mask = sum(1<<i for i,bit in enumerate(decision.coloring) if bit)
                assert mask in models
            assert parity_residue(n,edges)[1]==len(models)%3
    print("mod-three residues 0/1/2:",*counts,"; pin product and Pfaffian controls passed")


if __name__ == "__main__":
    check()
