import Formal.Split
import Init.Data.List.Nat.Sum

namespace SatForgetting

universe u

variable {Var : Type u}

/-- The outer `none` is the next pivot. After a step, one more layer is exposed. -/
abbrev WithPivots (Var : Type u) : Nat → Type u
  | 0 => Var
  | depth + 1 => Option (WithPivots Var depth)

def Extends (valuation : Var → Bool) : (depth : Nat) → (WithPivots Var depth → Bool) → Prop
  | 0, full => full = valuation
  | depth + 1, full => Extends valuation depth (fun var => full (some var))

/-- The output clause list of each step is the input of the following step. -/
inductive Schedule (Var : Type u) : (depth : Nat) → CNF (WithPivots Var depth) → CNF Var → Type u where
  | done (formula : CNF Var) : Schedule Var 0 formula formula
  | next {depth : Nat} {before : CNF (WithPivots Var (depth + 1))} {after : CNF Var}
      (step : CertifiedStep (Var := WithPivots Var depth) before)
      (rest : Schedule Var depth step.output after) : Schedule Var (depth + 1) before after

namespace Schedule

variable {depth : Nat} {before : CNF (WithPivots Var depth)} {after : CNF Var}

theorem projection_iff (schedule : Schedule Var depth before after) (valuation : Var → Bool) :
    after.eval valuation = true ↔
      ∃ full, Extends valuation depth full ∧ before.eval full = true := by
  induction schedule with
  | done formula =>
    constructor
    · exact fun supported => ⟨valuation, rfl, supported⟩
    · rintro ⟨full, extension, supported⟩
      change full = valuation at extension
      subst full
      exact supported
  | next step rest ih =>
    rw [ih]
    constructor
    · rintro ⟨inner, extension, supported⟩
      obtain ⟨pivot, fullSupported⟩ := (step.projection_iff inner).mp supported
      exact ⟨extend inner pivot, extension, fullSupported⟩
    · rintro ⟨full, extension, supported⟩
      refine ⟨fun var => full (some var), extension, ?_⟩
      apply (step.projection_iff _).mpr
      refine ⟨full none, ?_⟩
      rw [extend_restrict full]
      exact supported

abbrev Measure := {Variables : Type u} → CNF Variables → Nat

def costs (measure : Measure.{u}) :
    {depth : Nat} → {before : CNF (WithPivots Var depth)} → {after : CNF Var} →
    Schedule Var depth before after → List Nat
  | _, _, _, .done formula => [measure formula]
  | _, _, _, .next (before := current) _ rest => measure current :: rest.costs measure

def Nonincreasing (measure : Measure.{u}) :
    {depth : Nat} → {before : CNF (WithPivots Var depth)} → {after : CNF Var} →
    Schedule Var depth before after → Prop
  | _, _, _, .done _ => True
  | _, _, _, .next (before := current) step rest =>
    measure step.output ≤ measure current ∧ rest.Nonincreasing measure

theorem costs_length (schedule : Schedule Var depth before after) (measure : Measure.{u}) :
    (schedule.costs measure).length = depth + 1 := by
  induction schedule with
  | done formula => rfl
  | next step rest ih => simp [costs, ih]

theorem costs_le_initial (schedule : Schedule Var depth before after) (measure : Measure.{u})
    (monotone : schedule.Nonincreasing measure) :
    ∀ cost ∈ schedule.costs measure, cost ≤ measure before := by
  induction schedule with
  | done formula => simp [costs]
  | next step rest ih =>
    obtain ⟨stepLe, restMonotone⟩ := monotone
    intro cost member
    rcases List.mem_cons.mp member with equal | later
    · exact equal ▸ Nat.le_refl _
    · exact Nat.le_trans (ih restMonotone cost later) stepLe

private theorem sum_le_of_member_le (costs : List Nat) (cap : Nat)
    (bounded : ∀ cost ∈ costs, cost ≤ cap) : costs.sum ≤ costs.length * cap := by
  induction costs with
  | nil => simp
  | cons first rest ih =>
    have firstLe := bounded first List.mem_cons_self
    have restLe := ih (fun cost member => bounded cost (List.mem_cons_of_mem _ member))
    rw [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm (rest.length * cap)]
    exact Nat.add_le_add firstLe restLe

theorem sum_costs_le (schedule : Schedule Var depth before after) (measure : Measure.{u})
    (cap : Nat) (bounded : ∀ cost ∈ schedule.costs measure, cost ≤ cap) :
    (schedule.costs measure).sum ≤ (depth + 1) * cap := by
  simpa only [schedule.costs_length measure] using sum_le_of_member_le (schedule.costs measure) cap bounded

/-- A nonincreasing per-step count bounds every intermediate cost, including the
    input and output, and the sum of those costs along the supplied schedule. -/
theorem sum_costs_le_of_nonincreasing (schedule : Schedule Var depth before after) (measure : Measure.{u})
    (monotone : schedule.Nonincreasing measure) :
    (schedule.costs measure).sum ≤ (depth + 1) * measure before :=
  schedule.sum_costs_le measure _ (schedule.costs_le_initial measure monotone)

end Schedule

end SatForgetting
