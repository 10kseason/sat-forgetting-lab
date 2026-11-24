"""Enumerate resolved 15-point linear four-matching designs and their colorings.

The two possible missing-cell graphs for a pair of classes are C10 and C4+C6.
The optional full catalogue takes longer than the ordinary CI tests.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
import argparse
import gzip


MISSING = (
    tuple(frozenset((i, (i+1)%5)) for i in range(5)),
    tuple(map(frozenset, ((0,1),(0,1),(2,3),(3,4),(2,4)))),
)
PAIR_INDEX = {pair: i for i,pair in enumerate(combinations(range(15),2))}
ALL_MODELS = (1 << (1 << 15)) - 1


def truth_columns():
    # Repeating runs of 2^i zeros and 2^i ones across the assignment table.
    result = []
    for i in range(15):
        run = 1 << i
        period = (1 << (2*run)) - 1
        result.append((ALL_MODELS // period) * (((1 << run)-1) << run))
    return result


COLUMNS = truth_columns()


def model_mask(group):
    result = ALL_MODELS
    for a,b,c in group:
        x,y,z = COLUMNS[a], COLUMNS[b], COLUMNS[c]
        result &= (x | y | z) & ~(x & y & z)
    return result


class Skeleton:
    def __init__(self, missing):
        cells = [(i,j) for i in range(5) for j in range(5) if j not in missing[i]]
        self.index = {cell: v for v,cell in enumerate(cells)}
        self.rows = tuple(tuple(v for v,(i,j) in enumerate(cells) if i==k) for k in range(5))
        self.cols = tuple(tuple(v for v,(i,j) in enumerate(cells) if j==k) for k in range(5))
        self.missing_rows = tuple(tuple(i for i in range(5) if j in missing[i]) for j in range(5))
        options = [[] for _ in cells]
        for e in combinations(range(15),3):
            ij = [cells[v] for v in e]
            if len({i for i,j in ij}) == 3 and len({j for i,j in ij}) == 3:
                options[e[0]].append((sum(1 << v for v in e), e))

        def candidates(rest):
            if not rest:
                yield ()
                return
            for mask,edge in options[(rest & -rest).bit_length()-1]:
                if mask & rest == mask:
                    for tail in candidates(rest ^ mask):
                        yield (edge, *tail)

        self.groups = tuple(candidates((1 << 15)-1))
        self.ids = {g:i for i,g in enumerate(self.groups)}
        self.pairs = tuple(sum(1 << PAIR_INDEX[p] for e in group for p in combinations(e,2))
                           for group in self.groups)
        length = len(self.groups)
        self.seen = bytearray((length*(length-1)//2 + 7)//8)

    def visited(self, i, j):
        k = i*(i-1)//2+j
        return self.seen[k//8] & (1 << (k%8))

    def mark(self, i, j):
        k = i*(i-1)//2+j
        self.seen[k//8] |= 1 << (k%8)


def classify(output_path=None):
    skeletons = [Skeleton(shape) for shape in MISSING]

    @lru_cache(maxsize=None)
    def renamings(missing_rows):
        # In the four-cycle the two columns missing the same two rows remain
        # interchangeable even after the names of all five rows have been set.
        kind = int(len(set(missing_rows)) < 5)
        target = skeletons[kind]
        output = []
        for rows in permutations(range(5)):
            choices = []
            for source in missing_rows:
                label = tuple(sorted(rows[i] for i in source))
                choices.append([j for j,t in enumerate(target.missing_rows) if t == label])
            if not all(choices):
                continue
            for cols in product(*choices):
                if len(set(cols))==5:
                    output.append((rows,cols))
        assert len(output) == (10,24)[kind]
        return kind, output

    def orbit(groups):
        found = set()
        for a,b in permutations(range(4),2):
            other = [groups[i] for i in range(4) if i not in (a,b)]
            row_of = [0]*15
            col_of = [0]*15
            for j, (row,col) in enumerate(zip(groups[a],groups[b])):
                for v in row:
                    row_of[v] = j
                for v in col:
                    col_of[v] = j
            missing = tuple(tuple(sorted(set(range(5)) - {row_of[v] for v in col}))
                            for col in groups[b])
            kind, naming = renamings(missing)
            target = skeletons[kind]
            for rows,cols in naming:
                rename = [target.index[rows[row_of[v]],cols[col_of[v]]] for v in range(15)]
                indices = []
                for group in other:
                    transformed = tuple(sorted(tuple(sorted(rename[v] for v in e)) for e in group))
                    indices.append(target.ids[transformed])
                i,j = sorted(indices,reverse=True)
                found.add((kind,i,j))
        return found

    counts = [0,0]
    orbit_totals = [0,0]
    model_counts = Counter()
    drop_minimums = Counter()
    orbits = 0
    records = []
    for k,sk in enumerate(skeletons):
        for i,pi in enumerate(sk.pairs):
            for j in range(i):
                if pi & sk.pairs[j]:
                    continue
                counts[k] += 1
                if sk.visited(i,j):
                    continue
                groups = (sk.rows,sk.cols,sk.groups[i],sk.groups[j])
                covered = orbit(groups)
                assert (k,i,j) in covered
                for kind,left,right in covered:
                    target = skeletons[kind]
                    assert not target.visited(left,right) and not (target.pairs[left]&target.pairs[right])
                    target.mark(left,right)
                    orbit_totals[kind] += 1
                masks = list(map(model_mask,groups))
                full = masks[0]&masks[1]&masks[2]&masks[3]
                model_counts[full.bit_count()] += 1
                dropped = [(masks[a]&masks[b]&masks[c]).bit_count()
                           for a,b,c in ((1,2,3),(0,2,3),(0,1,3),(0,1,2))]
                if not full:
                    drop_minimums[min(dropped)] += 1
                if output_path is not None:
                    encoded = [".".join("".join(format(v,"x") for v in e) for e in group)
                               for group in groups]
                    records.append("\t".join([*encoded, str(full.bit_count()), *map(str,dropped)]))
                orbits += 1
        print("checked skeleton",k,"presentations",counts[k],"orbits so far",orbits,flush=True)
    assert counts == orbit_totals
    if output_path is not None:
        header = "class0\tclass1\tclass2\tclass3\tcolorings\tdrop0\tdrop1\tdrop2\tdrop3\n"
        with open(output_path,"wb") as raw:
            with gzip.GzipFile(filename="",mode="wb",fileobj=raw,mtime=0) as out:
                out.write((header + "\n".join(records) + "\n").encode("ascii"))
    print("candidate classes",[len(sk.groups) for sk in skeletons])
    print("normalized presentations",counts,"resolved isomorphism types",orbits)
    print("model histogram",sorted(model_counts.items()))
    print("minimum models after dropping a class on UNSAT types",sorted(drop_minimums.items()))
    return counts, model_counts, drop_minimums


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",help="write the deterministic gzipped catalogue as TSV")
    classify(parser.parse_args().output)
