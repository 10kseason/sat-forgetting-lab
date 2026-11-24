"""Validate every catalogue row in reflected Gray-code assignment order."""

from collections import Counter
from csv import DictReader
from gzip import open as gzopen
from itertools import combinations
from pathlib import Path


def gray_columns():
    width = 1 << 15
    table = [bytearray(width//8) for _ in range(15)]
    for k in range(width):
        gray = k ^ (k >> 1)
        for v in range(15):
            if gray & (1 << v):
                table[v][k//8] |= 1 << (k%8)
    return [int.from_bytes(row,"little") for row in table]


def verify(path):
    cols = gray_columns()
    all_bits = (1 << (1<<15))-1
    allowed = {(a,b,c): (cols[a]^cols[b]) | (cols[b]^cols[c])
               for a,b,c in combinations(range(15),3)}
    seen = set()
    histogram = Counter()
    misses = Counter()
    with gzopen(path,"rt",encoding="ascii",newline="") as stream:
        for row in DictReader(stream,delimiter="\t"):
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


if __name__ == "__main__":
    verify(Path(__file__).with_name("order15.tsv.gz"))
