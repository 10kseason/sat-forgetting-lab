"""Check the soft-cost endpoint and local one-miss obstruction independently."""

from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from matching_balance import BLOCK, ENCODING, PORTS, balanced_substitution
from independent import affine_plane


def cost(bits, edges):
    return sum(len({(bits>>v)&1 for v in e}) == 1 for e in edges)


def check():
    interior = [e for j,g in enumerate(BLOCK) for e in g if j==3 or set(e)!=set(PORTS[j])]
    total = (0x7c2,*ENCODING[1:7],0x83d)
    assert [cost(x,interior) for x in total] == [1,0,0,0,0,0,0,1]
    ports = sum(1 << v for lane in PORTS for v in lane)
    one_miss = 0
    for bits in range(4096):
        bad = cost(bits,interior)
        one_miss += bad==1
        round_cost = min(((bits^x)&ports).bit_count()+int(j in (0,7))
                         for j,x in enumerate(total))
        assert round_cost <= 4*bad
        if bits == 0xf18:
            assert bad == 1 and round_cost == 4
            assert all((bits^x).bit_count()==6 for x in total[1:7])
    assert one_miss == 336
    source = affine_plane()
    source_edges = [e for group in source for e in group]
    assert min(cost(x,source_edges) for x in range(512))==2
    image = balanced_substitution(source)
    target_edges = [e for group in image.matchings for e in group]
    assert cost(0xa4da4d1e2,target_edges)==1
    print("4096 local states, 336 one-miss states, affine-plane optimum 2 to 1")


if __name__ == "__main__":
    check()
