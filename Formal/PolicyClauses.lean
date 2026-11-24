import Formal.Reachability
import Formal.Forgetting

namespace SatForgetting

universe u v

variable {Head : Type u} {Retained : Type v}
variable {system : RuleSystem Head (Literal Retained)}

private theorem OrGraph.Path.transfer {left right : OrGraph Head} {source target : Head}
    (same : left.successors = right.successors) (path : left.Path source target) : right.Path source target := by
  induction path with
  | refl head => exact .refl head
  | cons edge rest ih => exact .cons (by simpa [OrGraph.Edge, same] using edge) ih

private theorem OrGraph.Cycle.transfer {left right : OrGraph Head} {head : Head}
    (same : left.successors = right.successors) (cycle : left.Cycle head) : right.Cycle head := by
  obtain ⟨next, edge, path⟩ := cycle
  exact ⟨next, by simpa [OrGraph.Edge, same] using edge, path.transfer same⟩

private def RulePolicy.retainedLiterals (policy : RulePolicy system) (head : Head) : Clause Retained :=
  ((policy.selected head).map Rule.terminals).getD []

private theorem RulePolicy.enabled_iff (policy : RulePolicy system) (valuation : Retained → Bool) (head : Head) :
    (policy.graph (fun literal => literal.eval valuation)).enabled head = true ↔
      policy.selected head = none ∨ (policy.retainedLiterals head).eval valuation = true := by
  cases choice : policy.selected head <;>
    simp [graph, retainedLiterals, choice, Clause.eval]

private theorem RulePolicy.support_iff [DecidableEq Head] (policy : RulePolicy system)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (valuation : Retained → Bool) (source : Head) :
    State.descend (policy.asSystem.step (fun literal => literal.eval valuation)) heads.length source = true ↔
      ∃ target, (policy.graph (fun _ => false)).Path source target ∧
        ((policy.selected target = none ∨ (policy.graph (fun _ => false)).Cycle target) ∨
          (policy.retainedLiterals target).eval valuation = true) := by
  rw [policy.descend_true_iff_reachesSupport _ heads covers source]
  have same : (policy.graph (fun literal => literal.eval valuation)).successors =
      (policy.graph (fun _ => false)).successors := rfl
  constructor
  · rintro ⟨target, path, enabled | cycle⟩
    · rcases (policy.enabled_iff valuation target).mp enabled with unbounded | literalTrue
      · exact ⟨target, path.transfer same, Or.inl (Or.inl unbounded)⟩
      · exact ⟨target, path.transfer same, Or.inr literalTrue⟩
    · exact ⟨target, path.transfer same, Or.inl (Or.inr (cycle.transfer same))⟩
  · rintro ⟨target, path, (unbounded | cycle) | literalTrue⟩
    · exact ⟨target, path.transfer same.symm, Or.inl ((policy.enabled_iff valuation target).mpr (Or.inl unbounded))⟩
    · exact ⟨target, path.transfer same.symm, Or.inr (cycle.transfer same.symm)⟩
    · exact ⟨target, path.transfer same.symm, Or.inl ((policy.enabled_iff valuation target).mpr (Or.inr literalTrue))⟩

/-- The reachable heads and structural supports are supplied as certificates.
    Reachability uses only edges, so recording it with all terminals false
    makes it independent of the retained valuation. -/
structure PolicyClause (system : RuleSystem Head (Literal Retained)) (goal : Rule Head (Literal Retained)) where
  policy : RulePolicy system
  reachable : List Head
  reachable_exact : ∀ target, target ∈ reachable ↔
    ∃ source ∈ goal.successors, (policy.graph (fun _ => false)).Path source target
  structural : Bool
  structural_exact : structural = true ↔ ∃ target ∈ reachable,
    policy.selected target = none ∨ (policy.graph (fun _ => false)).Cycle target

namespace PolicyClause

variable {goal : Rule Head (Literal Retained)}

def literals (plan : PolicyClause system goal) : Clause Retained :=
  goal.terminals ++ plan.reachable.flatMap plan.policy.retainedLiterals

def emit (plan : PolicyClause system goal) : Option (Clause Retained) :=
  if plan.structural then none else some plan.literals

private theorem successorSupport_iff [DecidableEq Head] (plan : PolicyClause system goal)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (valuation : Retained → Bool) :
    goal.successors.any (State.descend (plan.policy.asSystem.step (fun literal => literal.eval valuation))
      heads.length) = true ↔
        ∃ target ∈ plan.reachable,
          (plan.policy.selected target = none ∨ (plan.policy.graph (fun _ => false)).Cycle target) ∨
            (plan.policy.retainedLiterals target).eval valuation = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨source, member, supported⟩
    obtain ⟨target, path, supports⟩ := (plan.policy.support_iff heads covers valuation source).mp supported
    exact ⟨target, (plan.reachable_exact target).mpr ⟨source, member, path⟩, supports⟩
  · rintro ⟨target, member, supported⟩
    obtain ⟨source, sourceMem, path⟩ := (plan.reachable_exact target).mp member
    exact ⟨source, sourceMem, (plan.policy.support_iff heads covers valuation source).mpr ⟨target, path, supported⟩⟩

theorem eval_iff [DecidableEq Head] (plan : PolicyClause system goal)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (valuation : Retained → Bool) :
    (plan.emit.map (fun clause => clause.eval valuation)).getD true = true ↔
      goal.eval (fun literal => literal.eval valuation)
        (State.descend (plan.policy.asSystem.step (fun literal => literal.eval valuation)) heads.length) = true := by
  have structuralOrLiterals : goal.eval (fun literal => literal.eval valuation)
      (State.descend (plan.policy.asSystem.step (fun literal => literal.eval valuation)) heads.length) = true ↔
        plan.structural = true ∨ plan.literals.eval valuation = true := by
    rw [Rule.eval, Bool.or_eq_true, plan.successorSupport_iff heads covers valuation, plan.structural_exact]
    simp only [literals, Clause.eval, List.any_append, Bool.or_eq_true, List.any_flatMap, List.any_eq_true (l := plan.reachable)]
    constructor
    · rintro (ownLiteral | ⟨target, member, structural | reachableLiteral⟩)
      · exact Or.inr (Or.inl ownLiteral)
      · exact Or.inl ⟨target, member, structural⟩
      · exact Or.inr (Or.inr ⟨target, member, reachableLiteral⟩)
    · rintro (⟨target, member, structural⟩ | ownLiteral | ⟨target, member, reachableLiteral⟩)
      · exact Or.inr ⟨target, member, Or.inl structural⟩
      · exact Or.inl ownLiteral
      · exact Or.inr ⟨target, member, Or.inr reachableLiteral⟩
  rw [structuralOrLiterals]
  cases choice : plan.structural <;> simp [emit, choice]

end PolicyClause

end SatForgetting
