import Std.Tactic.BVDecide

namespace SatForgetting.MatchingBalance

abbrev Block := BitVec 12
abbrev Triple := Nat × Nat × Nat

def nae (a b c : Bool) : Bool := (a != b) || (b != c)

def edge (x : Block) (t : Triple) : Bool :=
  nae (x.getLsbD t.1) (x.getLsbD t.2.1) (x.getLsbD t.2.2)

/-- The edge (3,4,11) is left open for joining adjacent blocks. -/
def interior : List Triple := [
  (0,7,9), (1,2,8), (5,6,10),
  (0,4,8), (1,6,7), (2,3,10), (5,9,11),
  (0,2,5), (1,4,9), (3,6,8), (7,10,11),
  (0,1,11), (2,4,6), (3,5,7), (8,9,10)]

def allowed (x : Block) : Bool := interior.all (edge x)

set_option maxRecDepth 25000 in
set_option maxHeartbeats 8000000 in
theorem six_models (x : Block) : allowed x = true ↔
    x = 0x43b ∨ x = 0x5b2 ∨ x = 0x64b ∨ x = 0x9b4 ∨ x = 0xa4d ∨ x = 0xbc4 := by
  decide +revert +kernel

def weight (x : Block) : Nat := ((List.range 12).filter (fun i => x.getLsbD i)).length

theorem interior_balanced (x : Block) (h : allowed x = true) : weight x = 6 := by
  rcases (six_models x).mp h with h | h | h | h | h | h <;> subst x <;> decide

def joined {I : Type} (next : I → I) (color : I → Block) : Prop := ∀ i,
  allowed (color i) = true ∧
  nae ((color i).getLsbD 3) ((color i).getLsbD 4) ((color (next i)).getLsbD 11) = true

theorem joined_balanced {I : Type} (next : I → I) (color : I → Block)
    (h : joined next color) (i : I) : weight (color i) = 6 :=
  interior_balanced (color i) (h i).1

theorem joined_witness {I : Type} (next : I → I) : joined next (fun _ => 0x43b) := by
  intro i
  dsimp only
  decide

end SatForgetting.MatchingBalance
