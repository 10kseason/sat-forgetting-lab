import Formal.PolicyClauses
import Formal.RuleCNF

namespace SatForgetting

universe u v w

variable {Head : Type u} {Retained : Type v}

private theorem any_congr_mem {α : Type w} {xs : List α} {left right : α → Bool}
    (agree : ∀ x ∈ xs, left x = right x) : xs.any left = xs.any right := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, member, satisfied⟩
    exact ⟨x, member, agree x member ▸ satisfied⟩
  · rintro ⟨x, member, satisfied⟩
    exact ⟨x, member, (agree x member).symm ▸ satisfied⟩

variable {system : RuleSystem Head (Literal Retained)} {goal : Rule Head (Literal Retained)}

private theorem RulePolicy.evalGoal_eq_of_agreement (left right : RulePolicy system)
    (goal : Rule Head (Literal Retained)) (cone : List Head)
    (contains : ∀ head ∈ goal.successors, head ∈ cone)
    (closed : ∀ head ∈ cone, ∀ rule ∈ system head, ∀ successor ∈ rule.successors, successor ∈ cone)
    (agree : ∀ head ∈ cone, left.selected head = right.selected head)
    (retained : Literal Retained → Bool) (round : Nat) :
    goal.eval retained (State.descend (left.asSystem.step retained) round) =
      goal.eval retained (State.descend (right.asSystem.step retained) round) := by
  have stateEq : ∀ fuel head, head ∈ cone →
      State.descend (left.asSystem.step retained) fuel head =
        State.descend (right.asSystem.step retained) fuel head := by
    intro fuel
    induction fuel with
    | zero => intro head _; rfl
    | succ fuel ih =>
      intro head inCone
      have same := agree head inCone
      cases picked : left.selected head with
      | none =>
        have pickedRight := same.symm.trans picked
        simp [State.descend, RuleSystem.step, asSystem, picked, pickedRight]
      | some rule =>
        have pickedRight := same.symm.trans picked
        have ruleMem := left.valid head
        rw [picked] at ruleMem
        have equalSuccessors := any_congr_mem (xs := rule.successors)
          (fun successor member => ih successor (closed head inCone rule ruleMem successor member))
        simp [State.descend, RuleSystem.step, asSystem, picked, pickedRight, Rule.eval, equalSuccessors]
  simp only [Rule.eval, any_congr_mem (fun head member => stateEq round head (contains head member))]

/-- A goal's supplied policy entries must cover all choices on a closed dependency
    cone. Their choices outside the cone may be arbitrary. -/
structure GoalEmission (system : RuleSystem Head (Literal Retained)) (goal : Rule Head (Literal Retained)) where
  cone : List Head
  contains : ∀ head ∈ goal.successors, head ∈ cone
  closed : ∀ head ∈ cone, ∀ rule ∈ system head, ∀ successor ∈ rule.successors, successor ∈ cone
  entries : List (PolicyClause system goal)
  covers : ∀ policy : RulePolicy system,
    ∃ entry ∈ entries, ∀ head ∈ cone, entry.policy.selected head = policy.selected head

namespace GoalEmission

def emit (plan : GoalEmission system goal) : CNF Retained :=
  plan.entries.filterMap PolicyClause.emit

theorem length_emit_le (plan : GoalEmission system goal) : plan.emit.length ≤ plan.entries.length :=
  List.length_filterMap_le _ _

theorem eval_iff [DecidableEq Head] (plan : GoalEmission system goal)
    (heads : List Head) (coveredHeads : ∀ head, head ∈ heads) (valuation : Retained → Bool) :
    plan.emit.eval valuation = true ↔ ∀ policy : RulePolicy system,
      goal.eval (fun literal => literal.eval valuation)
        (State.descend (policy.asSystem.step (fun literal => literal.eval valuation)) heads.length) = true := by
  rw [CNF.eval_eq_true]
  constructor
  · intro allClauses policy
    obtain ⟨entry, member, agree⟩ := plan.covers policy
    rw [← entry.policy.evalGoal_eq_of_agreement policy goal plan.cone plan.contains plan.closed agree]
    apply (entry.eval_iff heads coveredHeads valuation).mp
    cases emitted : entry.emit with
    | none => simp
    | some clause =>
      have clauseMem : clause ∈ plan.emit := List.mem_filterMap.mpr ⟨entry, member, emitted⟩
      simpa [emitted] using allClauses clause clauseMem
  · intro allPolicies clause member
    obtain ⟨entry, _, emitted⟩ := List.mem_filterMap.mp member
    simpa [emitted] using (entry.eval_iff heads coveredHeads valuation).mpr (allPolicies entry.policy)

end GoalEmission

structure RuleCNF.EmissionPlan (formula : RuleCNF Head Retained) where
  goal : (demand : Rule Head (Literal Retained)) → demand ∈ formula.demands →
    GoalEmission formula.upperBounds demand

namespace RuleCNF.EmissionPlan

variable {formula : RuleCNF Head Retained}

private def demandClauses (plan : formula.EmissionPlan) : CNF Retained :=
  formula.demands.attach.flatMap (fun demand => (plan.goal demand.val demand.property).emit)

def emit (plan : formula.EmissionPlan) (background : CNF Retained) : CNF Retained :=
  background ++ plan.demandClauses

def policyCount (plan : formula.EmissionPlan) : Nat :=
  (formula.demands.attach.map (fun demand => (plan.goal demand.val demand.property).entries.length)).sum

private theorem sum_map_le {α : Type w} (xs : List α) {left right : α → Nat}
    (each : ∀ x ∈ xs, left x ≤ right x) : (xs.map left).sum ≤ (xs.map right).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x rest ih =>
    exact Nat.add_le_add (each x List.mem_cons_self) (ih (fun y member => each y (List.mem_cons_of_mem _ member)))

theorem length_emit_le (plan : formula.EmissionPlan) (background : CNF Retained) :
    (plan.emit background).length ≤ background.length + plan.policyCount := by
  simp only [emit, demandClauses, List.length_append, List.length_flatMap, policyCount]
  apply Nat.add_le_add_left
  exact sum_map_le _ (fun demand _ => (plan.goal demand.val demand.property).length_emit_le)

private theorem eval_demandClauses_iff [DecidableEq Head] (plan : formula.EmissionPlan)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (valuation : Retained → Bool) :
    plan.demandClauses.eval valuation = true ↔
      ∀ policy : RulePolicy formula.upperBounds, (formula.withPolicy policy).project heads valuation = true := by
  simp only [demandClauses, CNF.eval, List.all_flatMap, List.all_eq_true]
  constructor
  · intro allGoals policy
    apply List.all_eq_true.mpr
    intro demand member
    exact ((plan.goal demand member).eval_iff heads covers valuation).mp
      ((CNF.eval_eq_true _ valuation).mpr (allGoals ⟨demand, member⟩ (List.mem_attach _ _))) policy
  · intro allPolicies demand _
    apply (CNF.eval_eq_true _ valuation).mp
    apply ((plan.goal demand.val demand.property).eval_iff heads covers valuation).mpr
    intro policy
    exact List.all_eq_true.mp (allPolicies policy) demand.val demand.property

/-- A certified policy enumeration emits an exact retained CNF. The background
    is copied verbatim, and each listed goal/policy pair emits at most one clause. -/
theorem projection_iff [DecidableEq Head] (plan : formula.EmissionPlan) (background : CNF Retained)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (valuation : Retained → Bool) :
    (plan.emit background).eval valuation = true ↔ background.eval valuation = true ∧
      ∃ state, (formula.materialize heads).eval (RuleCNF.combine state valuation) = true := by
  rw [emit, CNF.eval_append, Bool.and_eq_true, plan.eval_demandClauses_iff heads covers valuation,
    ← formula.project_iff_forall_policies heads covers valuation, formula.projection_iff heads covers valuation]

end RuleCNF.EmissionPlan

end SatForgetting
