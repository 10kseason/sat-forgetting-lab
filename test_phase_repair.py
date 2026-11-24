import runpy
import unittest
from pathlib import Path

from matching_balance import BLOCK
from phase_repair import solve_resolved_phases


def valid(bits, edge):
    a,b,c = edge
    return bits[a]!=bits[b] or bits[b]!=bits[c]


class PhaseRepairTests(unittest.TestCase):
    def test_connected_two_miss_starts(self):
        family = runpy.run_path(str(Path(__file__).parent/"routes"/"matching-balance"/"dual.py"))
        for k in (2,3,8,64):
            groups = family["cycle"](k)
            local = [0x1676,0x2989]+[0x3263]*(k-2)
            start = tuple(bool(x>>i&1) for x in local for i in range(15))
            self.assertEqual(sum(start),7*k)
            misses = [sum(not valid(start,e) for e in g) for g in groups]
            self.assertEqual(misses,[0,2,0,0])
            result = solve_resolved_phases(groups,1)
            self.assertEqual(result.status,"SAT")
            self.assertEqual(result.component_sizes,(15,)*k)
            self.assertIn(sum(result.assignment),(7*k,8*k))
            self.assertTrue(all(valid(result.assignment,e) for g in groups for e in g))
        too_big = solve_resolved_phases(groups,1,max_block=14)
        self.assertEqual(too_big.status,"UNKNOWN")

    def test_controls_and_incomplete_route(self):
        inputs = runpy.run_path(str(Path(__file__).parent/"routes"/"matching-balance"/"independent.py"))
        plane = inputs["affine_plane"]()
        for j in range(4):
            self.assertEqual(solve_resolved_phases(plane,j).status,"UNSAT")
            self.assertEqual(solve_resolved_phases(BLOCK,j).status,"SAT")
        self.assertEqual(solve_resolved_phases(inputs["cycle_of_planes"](4),3).status,"UNSAT")
        self.assertEqual(solve_resolved_phases([(),(),(),()],0).assignment,())
        with self.assertRaises(ValueError):
            solve_resolved_phases([[(0,0,1)]]*4,1)
