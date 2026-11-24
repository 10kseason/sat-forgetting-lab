import Formal.BalancedSubstitution

namespace SatForgetting.MatchingBalance.Damage
open Substitution (inside valid port Slot Lane)

def complete (p q r : Bool) : Block :=
  if nae p q r then Substitution.encode p q r else if p then 0x83d else 0x7c2

def misses (x : Block) : Nat := (inside.filter fun t => !(edge x t)).length

theorem exact_local_cost (p q r : Bool) :
    misses (complete p q r) = (if nae p q r then 0 else 1) := by
  cases p <;> cases q <;> cases r <;> decide

def readSource (s : Slot) (p q r : Bool) : Bool :=
  match s with | .p => p | .q => q | .r => r

theorem port_on_all_inputs (p q r : Bool) (l : Lane) (s : Slot) :
    (complete p q r).getLsbD (port l s) =
      (match l with | .second => !(readSource s p q r) | _ => readSource s p q r) := by
  cases p <;> cases q <;> cases r <;> cases l <;> cases s <;> decide

theorem hamming (p q r p' q' r' : Bool) :
    weight ((complete p q r) ^^^ (complete p' q' r')) =
    4 * ((if p == p' then 0 else 1) + (if q == q' then 0 else 1) +
      (if r == r' then 0 else 1)) := by
  cases p <;> cases q <;> cases r <;> cases p' <;> cases q' <;> cases r' <;> decide

theorem one_miss : misses 0xf18 = 1 := by decide

theorem all_states_six_away (x : Block) (h : valid x = true) : weight (x ^^^ 0xf18) = 6 := by
  rcases (six_models x).mp ((Substitution.same_six x).mp h) with h | h | h | h | h | h <;>
    subst x <;> decide

end SatForgetting.MatchingBalance.Damage
