import Formal.MatchingBalance

namespace SatForgetting.MatchingImbalance
open MatchingBalance (Triple nae)

abbrev State := BitVec 15
def light : State := 0x3263
def heavy : State := 0x4d9c

/-- The deleted triple has vertices 1, 4 and 14. -/
def inside : List Triple := [
  (0,1,2),(3,4,5),(6,7,8),(9,10,11),(12,13,14),
  (3,6,9),(7,10,12),(0,11,13),(2,5,8),
  (0,4,6),(1,3,7),(2,11,12),(5,10,13),(8,9,14),
  (0,3,10),(1,8,12),(2,4,13),(5,7,9),(6,11,14)]

def valid (x : State) := inside.all fun t =>
  nae (x.getLsbD t.1) (x.getLsbD t.2.1) (x.getLsbD t.2.2)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 60000000 in
theorem only_two (x : State) : valid x = true ↔ x = light ∨ x = heavy := by
  decide +revert +kernel

def link (x y : State) := nae (x.getLsbD 4) (x.getLsbD 14) (y.getLsbD 1)

theorem link_iff_eq {x y : State} (hx : valid x = true) (hy : valid y = true) :
    link x y = true ↔ x = y := by
  rcases (only_two x).mp hx with a | a <;> rcases (only_two y).mp hy with b | b <;>
    subst x <;> subst y <;> decide

def weight (x : State) := ((List.range 15).filter fun i => x.getLsbD i).length
theorem weights : weight light = 7 ∧ weight heavy = 8 := by decide

theorem uniform_path (k : Nat) (states : Nat → State)
    (hv : ∀ i, i < k → valid (states i) = true)
    (hl : ∀ i, i+1 < k → link (states i) (states (i+1)) = true)
    (j : Nat) (bound : j < k) : states j = states 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have prev : j < k := by omega
    exact ((link_iff_eq (hv j prev) (hv (j+1) bound)).mp (hl j bound)).symm.trans (ih prev)

end SatForgetting.MatchingImbalance
