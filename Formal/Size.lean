import Formal.Schedule

namespace SatForgetting

universe u

variable {Var : Type u}

def CNF.literalCount (formula : CNF Var) : Nat := (formula.map List.length).sum

@[simp] theorem CNF.literalCount_nil : (CNF.literalCount ([] : CNF Var)) = 0 := rfl

@[simp] theorem CNF.literalCount_cons (clause : Clause Var) (rest : CNF Var) :
    CNF.literalCount (clause :: rest) = clause.length + rest.literalCount := rfl

@[simp] theorem CNF.literalCount_append (first second : CNF Var) :
    (first ++ second).literalCount = first.literalCount + second.literalCount := by
  simp [CNF.literalCount]

private theorem literalCount_append_each (first : Clause Var) (others : CNF Var) :
    CNF.literalCount (others.map (fun second => first ++ second)) =
      others.length * first.length + others.literalCount := by
  induction others with
  | nil => simp
  | cons clause rest ih =>
    simp only [List.map_cons, CNF.literalCount_cons, List.length_append, List.length_cons, ih,
      Nat.add_mul, Nat.one_mul]
    ac_rfl

theorem literalCount_resolvents (positive negative : CNF Var) :
    (resolvents positive negative).literalCount =
      negative.length * positive.literalCount + positive.length * negative.literalCount := by
  induction positive with
  | nil => simp [resolvents]
  | cons clause rest ih =>
    change CNF.literalCount ((negative.map (fun second => clause ++ second)) ++ resolvents rest negative) = _
    simp only [CNF.literalCount_append, literalCount_append_each, ih, CNF.literalCount_cons,
      List.length_cons, Nat.add_mul, Nat.mul_add, Nat.one_mul]
    ac_rfl

/-- This counts literal occurrences in the raw output lists, including duplicates. -/
theorem PivotCNF.literalCount_eliminate (input : PivotCNF Var) (positive negative : CNF Var) :
    (input.eliminate positive negative).literalCount = input.background.literalCount +
      (negative.length * positive.literalCount + positive.length * negative.literalCount) := by
  simp [eliminate, literalCount_resolvents]

namespace Schedule

variable {depth : Nat} {before : CNF (WithPivots Var depth)} {after : CNF Var}

def ClauseBudget : {depth : Nat} → {before : CNF (WithPivots Var depth)} → {after : CNF Var} →
    Schedule Var depth before after → Prop
  | _, _, _, .done _ => True
  | _, _, _, .next (before := current) step rest =>
    step.positive.length * step.negative.length ≤
      (PivotCNF.split current).positive.length + (PivotCNF.split current).negative.length ∧ rest.ClauseBudget

theorem nonincreasing_of_clauseBudget (schedule : Schedule Var depth before after)
    (budget : schedule.ClauseBudget) : schedule.Nonincreasing (fun formula => formula.length) := by
  induction schedule with
  | done formula => trivial
  | next step rest ih =>
    obtain ⟨stepBudget, restBudget⟩ := budget
    exact ⟨step.length_output_le stepBudget, ih restBudget⟩

theorem sum_clauseCounts_le (schedule : Schedule Var depth before after) (budget : schedule.ClauseBudget) :
    (schedule.costs (fun formula => formula.length)).sum ≤ (depth + 1) * before.length :=
  schedule.sum_costs_le_of_nonincreasing _ (schedule.nonincreasing_of_clauseBudget budget)

theorem sum_literalCounts_le (schedule : Schedule Var depth before after) (cap : Nat)
    (bounded : ∀ cost ∈ schedule.costs (fun formula => formula.literalCount), cost ≤ cap) :
    (schedule.costs (fun formula => formula.literalCount)).sum ≤ (depth + 1) * cap :=
  schedule.sum_costs_le _ cap bounded

end Schedule

end SatForgetting
