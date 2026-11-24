import Formal.MatchingBalance

namespace SatForgetting.MatchingBalance.Substitution

inductive Slot | p | q | r
inductive Lane | first | second | third

def port : Lane → Slot → Nat
  | .first, .p => 3 | .first, .q => 4 | .first, .r => 11
  | .second, .p => 7 | .second, .q => 6 | .second, .r => 1
  | .third, .p => 0 | .third, .q => 5 | .third, .r => 2

def signal (v : Block) (s : Slot) := v.getLsbD (port .first s)

def encode (p q r : Bool) : Block :=
  match p, q, r with
  | false, false, true => 0xbc4
  | false, true, false => 0x5b2
  | false, true, true => 0x9b4
  | true, false, false => 0x64b
  | true, false, true => 0xa4d
  | true, true, false => 0x43b
  | _, _, _ => 0

/-- The three open triples occupy distinct lanes, with the entire second lane
complemented. The fourth matching keeps all its local edges. -/
def inside : List Triple := [
  (0,7,9), (1,2,8), (5,6,10),
  (0,4,8), (2,3,10), (5,9,11),
  (1,4,9), (3,6,8), (7,10,11),
  (0,1,11), (2,4,6), (3,5,7), (8,9,10)]

def valid (v : Block) := inside.all (edge v)

set_option maxRecDepth 25000 in
set_option maxHeartbeats 8000000 in
theorem same_six (v : Block) : valid v = true ↔ allowed v = true := by
  decide +revert +kernel

private theorem local_decode (v : Block) (h : valid v = true) :
    nae (signal v .p) (signal v .q) (signal v .r) = true ∧
    encode (signal v .p) (signal v .q) (signal v .r) = v := by
  rcases (six_models v).mp ((same_six v).mp h) with h | h | h | h | h | h <;> subst v <;> decide

private theorem local_encode (p q r : Bool) (h : nae p q r = true) :
    valid (encode p q r) = true ∧ signal (encode p q r) .p = p ∧
    signal (encode p q r) .q = q ∧ signal (encode p q r) .r = r := by
  cases p <;> cases q <;> cases r <;> (first | contradiction | decide)

private def polarity : Lane → Bool → Bool
  | .second, b => !b
  | _, b => b

private theorem port_correct (v : Block) (h : valid v = true) (lane : Lane) (s : Slot) :
    v.getLsbD (port lane s) = polarity lane (signal v s) := by
  rcases (six_models v).mp ((same_six v).mp h) with h | h | h | h | h | h <;>
    subst v <;> cases lane <;> cases s <;> decide

private theorem uniform_polarity (lane : Lane) (a b c : Bool) :
    nae (polarity lane a) (polarity lane b) (polarity lane c) = nae a b c := by
  cases lane <;> cases a <;> cases b <;> cases c <;> decide

variable {I : Type}
abbrev Node (I : Type) := I × Slot
abbrev Outside (I : Type) := Lane → Node I → Node I → Node I → Prop

def project (y : I → Block) (v : Node I) := signal (y v.1) v.2
def lift (x : Node I → Bool) (i : I) :=
  encode (x (i,.p)) (x (i,.q)) (x (i,.r))

def Source (edges : Outside I) (x : Node I → Bool) : Prop :=
  (∀ i, nae (x (i,.p)) (x (i,.q)) (x (i,.r)) = true) ∧
  (∀ l a b c, edges l a b c → nae (x a) (x b) (x c) = true)

def Target (edges : Outside I) (y : I → Block) : Prop :=
  (∀ i, valid (y i) = true) ∧
  (∀ l a b c, edges l a b c →
    nae ((y a.1).getLsbD (port l a.2)) ((y b.1).getLsbD (port l b.2))
      ((y c.1).getLsbD (port l c.2)) = true)

private theorem read_edge {y : I → Block} (h : ∀ i, valid (y i) = true)
    (l : Lane) (a b c : Node I) :
    nae ((y a.1).getLsbD (port l a.2)) ((y b.1).getLsbD (port l b.2))
      ((y c.1).getLsbD (port l c.2)) = nae (project y a) (project y b) (project y c) := by
  rw [port_correct _ (h _) l _, port_correct _ (h _) l _, port_correct _ (h _) l _]
  exact uniform_polarity _ _ _ _

theorem project_lift {edges : Outside I} {x : Node I → Bool} (h : Source edges x) :
    project (lift x) = x := by
  funext v
  obtain ⟨i,s⟩ := v
  obtain ⟨_, hp, hq, hr⟩ := local_encode _ _ _ (h.1 i)
  cases s with
  | p => exact hp
  | q => exact hq
  | r => exact hr

theorem lift_project {edges : Outside I} {y : I → Block} (h : Target edges y) :
    lift (project y) = y := by
  funext i
  exact (local_decode _ (h.1 i)).2

theorem lift_model {edges : Outside I} {x : Node I → Bool} (h : Source edges x) :
    Target edges (lift x) := by
  have ok : ∀ i, valid (lift x i) = true := fun i => (local_encode _ _ _ (h.1 i)).1
  refine ⟨ok, ?_⟩
  intro l a b c ext
  rw [read_edge ok l a b c, project_lift h]
  exact h.2 l a b c ext

theorem project_model {edges : Outside I} {y : I → Block} (h : Target edges y) :
    Source edges (project y) := by
  refine ⟨fun i => (local_decode _ (h.1 i)).1, ?_⟩
  intro l a b c ext
  rw [← read_edge h.1 l a b c]
  exact h.2 l a b c ext

theorem every_block_balanced {edges : Outside I} {y : I → Block} (h : Target edges y)
    (i : I) : weight (y i) = 6 := interior_balanced (y i) ((same_six _).mp (h.1 i))

end SatForgetting.MatchingBalance.Substitution
