import Formal.Forgetting
import Init.Omega

namespace SatForgetting

universe u

variable {Var : Type u}

private structure ClauseParts (Var : Type u) where
  retained : Clause Var
  hasPositive : Bool
  hasNegative : Bool

private def Clause.parts : Clause (Option Var) → ClauseParts Var
  | [] => ⟨[], false, false⟩
  | ⟨none, true⟩ :: tail => { Clause.parts tail with hasPositive := true }
  | ⟨none, false⟩ :: tail => { Clause.parts tail with hasNegative := true }
  | ⟨some var, positive⟩ :: tail =>
    let parts := Clause.parts tail
    { parts with retained := ⟨var, positive⟩ :: parts.retained }

private def ClauseParts.eval (parts : ClauseParts Var) (valuation : Var → Bool) (pivot : Bool) : Bool :=
  (parts.hasPositive && pivot) || (parts.hasNegative && !pivot) || parts.retained.eval valuation

private theorem Clause.eval_parts (clause : Clause (Option Var)) (valuation : Var → Bool) (pivot : Bool) :
    clause.eval (extend valuation pivot) = (Clause.parts clause).eval valuation pivot := by
  induction clause with
  | nil => rfl
  | cons literal tail ih =>
    obtain ⟨var, polarity⟩ := literal
    rw [Clause.eval_cons, ih]
    cases var with
    | none => cases polarity <;> cases pivot <;> simp [Clause.parts, ClauseParts.eval, Literal.eval]
    | some var =>
      simp only [Clause.parts, ClauseParts.eval, Clause.eval_cons, Literal.eval, extend_some]
      ac_rfl

private def PivotCNF.place (input : PivotCNF Var) (parts : ClauseParts Var) : PivotCNF Var :=
  match parts.hasPositive, parts.hasNegative with
  | false, false => { input with background := parts.retained :: input.background }
  | true, false => { input with positive := parts.retained :: input.positive }
  | false, true => { input with negative := parts.retained :: input.negative }
  | true, true => input

/-- Split an arbitrary clause list around `none`. Repeated pivot literals collapse
    to one occurrence, and clauses with both signs of the pivot are tautologies. -/
def PivotCNF.split : CNF (Option Var) → PivotCNF Var
  | [] => ⟨[], [], []⟩
  | clause :: rest => (PivotCNF.split rest).place (Clause.parts clause)

private theorem PivotCNF.eval_place (input : PivotCNF Var) (parts : ClauseParts Var)
    (valuation : Var → Bool) (pivot : Bool) :
    (input.place parts).materialize.eval (extend valuation pivot) =
      (parts.eval valuation pivot && input.materialize.eval (extend valuation pivot)) := by
  obtain ⟨retained, positive, negative⟩ := parts
  cases positive <;> cases negative <;> cases pivot <;>
    simp [place, ClauseParts.eval, Bool.and_assoc, Bool.and_left_comm]

theorem PivotCNF.eval_split (formula : CNF (Option Var)) (valuation : Var → Bool) (pivot : Bool) :
    (PivotCNF.split formula).materialize.eval (extend valuation pivot) =
      formula.eval (extend valuation pivot) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
    rw [PivotCNF.split, PivotCNF.eval_place, ih, ← Clause.eval_parts, CNF.eval_cons]

private theorem PivotCNF.length_place_le (input : PivotCNF Var) (parts : ClauseParts Var) :
    (input.place parts).materialize.length ≤ input.materialize.length + 1 := by
  obtain ⟨retained, positive, negative⟩ := parts
  cases positive <;> cases negative <;> simp [place] <;> omega

theorem PivotCNF.length_split_le (formula : CNF (Option Var)) :
    (PivotCNF.split formula).materialize.length ≤ formula.length := by
  induction formula with
  | nil => exact Nat.le_refl 0
  | cons clause rest ih =>
    exact Nat.le_trans ((PivotCNF.split rest).length_place_le (Clause.parts clause)) (Nat.succ_le_succ ih)

def Clause.hasPivot (clause : Clause (Option Var)) : Bool :=
  clause.any (fun literal => literal.var.isNone)

def Clause.stripPivot (clause : Clause (Option Var)) : Clause Var :=
  (Clause.parts clause).retained

theorem Clause.rename_stripPivot (clause : Clause (Option Var)) (absent : clause.hasPivot = false) :
    clause.stripPivot.rename some = clause := by
  induction clause with
  | nil => rfl
  | cons literal tail ih =>
    obtain ⟨var, polarity⟩ := literal
    cases var with
    | none => simp [hasPivot] at absent
    | some var =>
      have tailAbsent : Clause.hasPivot tail = false := by simpa [hasPivot] using absent
      change ⟨some var, polarity⟩ :: (Clause.stripPivot tail).rename some = ⟨some var, polarity⟩ :: tail
      rw [ih tailAbsent]

private theorem Clause.hasPivot_of_parts (clause : Clause (Option Var)) :
    clause.hasPivot = ((Clause.parts clause).hasPositive || (Clause.parts clause).hasNegative) := by
  induction clause with
  | nil => rfl
  | cons literal tail ih =>
    obtain ⟨var, polarity⟩ := literal
    cases var with
    | none => cases polarity <;> simp [hasPivot, Clause.parts]
    | some var => simpa [hasPivot, Clause.parts] using ih

/-- The background preserves exactly the input clauses with no pivot, in order. -/
theorem PivotCNF.split_background (formula : CNF (Option Var)) :
    (PivotCNF.split formula).background =
      (formula.filter (fun clause => !clause.hasPivot)).map Clause.stripPivot := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
    cases parts : Clause.parts clause with
    | mk retained positive negative =>
      have hasPivot := Clause.hasPivot_of_parts clause
      rw [parts] at hasPivot
      rw [PivotCNF.split, parts]
      cases positive <;> cases negative <;> simp [place, hasPivot, Clause.stripPivot, parts, ih]

theorem PivotCNF.rename_split_background (formula : CNF (Option Var)) :
    (PivotCNF.split formula).background.rename some = formula.filter (fun clause => !clause.hasPivot) := by
  rw [split_background, CNF.rename, List.map_map]
  calc
    _ = List.map id (formula.filter (fun clause => !clause.hasPivot)) := by
      apply List.map_congr_left
      intro clause member
      apply clause.rename_stripPivot
      simpa using (List.mem_filter.mp member).2
    _ = _ := List.map_id _

/-- A step certifies both representative families against the same input split. -/
structure CertifiedStep (before : CNF (Option Var)) where
  positive : CNF Var
  negative : CNF Var
  positiveCert : SideCertificate (PivotCNF.split before).background (PivotCNF.split before).positive positive
  negativeCert : SideCertificate (PivotCNF.split before).background (PivotCNF.split before).negative negative

def CertifiedStep.output {before : CNF (Option Var)} (step : CertifiedStep before) : CNF Var :=
  (PivotCNF.split before).eliminate step.positive step.negative

theorem CertifiedStep.projection_iff {before : CNF (Option Var)} (step : CertifiedStep before)
    (valuation : Var → Bool) :
    step.output.eval valuation = true ↔ ∃ pivot, before.eval (extend valuation pivot) = true := by
  simp only [output, (PivotCNF.split before).projection_iff step.positiveCert step.negativeCert,
    PivotCNF.eval_split]

theorem CertifiedStep.length_output_le {before : CNF (Option Var)} (step : CertifiedStep before)
    (budget : step.positive.length * step.negative.length ≤
      (PivotCNF.split before).positive.length + (PivotCNF.split before).negative.length) :
    step.output.length ≤ before.length :=
  Nat.le_trans ((PivotCNF.split before).length_eliminate_le step.positive step.negative budget)
    (PivotCNF.length_split_le before)

end SatForgetting
