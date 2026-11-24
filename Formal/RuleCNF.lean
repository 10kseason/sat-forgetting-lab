import Formal.Forgetting
import Formal.Policies

namespace SatForgetting

universe u v

variable {Head : Type u} {Retained : Type v}

/-- Upper bounds have the form `¬head ∨ terminals ∨ successors`. Each demand
    contains arbitrary retained literals and only positive hidden variables. -/
structure RuleCNF (Head : Type u) (Retained : Type v) where
  upperBounds : RuleSystem Head (Literal Retained)
  demands : List (Rule Head (Literal Retained))

namespace RuleCNF

def combine (state : State Head) (valuation : Retained → Bool) : Sum Head Retained → Bool
  | .inl head => state head
  | .inr var => valuation var

private def demandClause (rule : Rule Head (Literal Retained)) : Clause (Sum Head Retained) :=
  Clause.rename rule.terminals Sum.inr ++ rule.successors.map (fun head => ⟨.inl head, true⟩)

private def boundClause (head : Head) (rule : Rule Head (Literal Retained)) : Clause (Sum Head Retained) :=
  ⟨.inl head, false⟩ :: demandClause rule

private def bounds (formula : RuleCNF Head Retained) (heads : List Head) : CNF (Sum Head Retained) :=
  heads.flatMap (fun head => (formula.upperBounds head).map (boundClause head))

def materialize (formula : RuleCNF Head Retained) (heads : List Head) : CNF (Sum Head Retained) :=
  formula.bounds heads ++ formula.demands.map demandClause

def evalDemands (formula : RuleCNF Head Retained) (valuation : Retained → Bool) (state : State Head) : Bool :=
  formula.demands.all (fun rule => rule.eval (fun literal => literal.eval valuation) state)

theorem evalDemands_mono (formula : RuleCNF Head Retained) (valuation : Retained → Bool)
    {left right : State Head} (included : State.Included left right) :
    formula.evalDemands valuation left = true → formula.evalDemands valuation right = true := by
  intro supported
  refine List.all_eq_true.mpr (fun rule member => rule.eval_mono _ included ?_)
  exact List.all_eq_true.mp supported rule member

private theorem eval_demandClause (rule : Rule Head (Literal Retained)) (state : State Head)
    (valuation : Retained → Bool) :
    (demandClause rule).eval (combine state valuation) = rule.eval (fun literal => literal.eval valuation) state := by
  simp only [demandClause, Clause.eval_append, Clause.eval_rename, Rule.eval]
  change (Clause.eval rule.terminals valuation ||
    (rule.successors.map (fun head => (⟨.inl head, true⟩ : Literal (Sum Head Retained)))).any
      (fun literal => Literal.eval literal (combine state valuation))) = _
  rw [List.any_map]
  rfl

private theorem eval_boundClause (head : Head) (rule : Rule Head (Literal Retained)) (state : State Head)
    (valuation : Retained → Bool) :
    (boundClause head rule).eval (combine state valuation) =
      (!(state head) || rule.eval (fun literal => literal.eval valuation) state) := by
  simp [boundClause, eval_demandClause, Literal.eval, combine]

private theorem eval_bounds_iff (formula : RuleCNF Head Retained) (heads : List Head)
    (covers : ∀ head, head ∈ heads) (state : State Head) (valuation : Retained → Bool) :
    (formula.bounds heads).eval (combine state valuation) = true ↔
      State.Included state (formula.upperBounds.step (fun literal => literal.eval valuation) state) := by
  rw [CNF.eval_eq_true]
  simp only [bounds, List.mem_flatMap, List.mem_map]
  constructor
  · intro satisfied head alive
    apply (formula.upperBounds.step_true_iff _ state head).mpr
    intro rule member
    have satisfiesBound := satisfied (boundClause head rule) ⟨head, covers head, rule, member, rfl⟩
    simpa [eval_boundClause, alive] using satisfiesBound
  · rintro postfixed clause ⟨head, _, rule, member, rfl⟩
    cases alive : state head with
    | false => simp [eval_boundClause, alive]
    | true =>
      have supported := (formula.upperBounds.step_true_iff _ state head).mp (postfixed head alive) rule member
      simpa [eval_boundClause, alive] using supported

theorem eval_materialize_iff (formula : RuleCNF Head Retained) (heads : List Head)
    (covers : ∀ head, head ∈ heads) (state : State Head) (valuation : Retained → Bool) :
    (formula.materialize heads).eval (combine state valuation) = true ↔
      State.Included state (formula.upperBounds.step (fun literal => literal.eval valuation) state) ∧
        formula.evalDemands valuation state = true := by
  rw [materialize, CNF.eval_append, Bool.and_eq_true, formula.eval_bounds_iff heads covers state valuation]
  simp [CNF.eval, List.all_map, Function.comp_def, eval_demandClause, evalDemands]

def project (formula : RuleCNF Head Retained) (heads : List Head) (valuation : Retained → Bool) : Bool :=
  formula.evalDemands valuation
    (State.descend (formula.upperBounds.step (fun literal => literal.eval valuation)) heads.length)

theorem projection_iff (formula : RuleCNF Head Retained) (heads : List Head)
    (covers : ∀ head, head ∈ heads) (valuation : Retained → Bool) :
    formula.project heads valuation = true ↔
      ∃ state, (formula.materialize heads).eval (combine state valuation) = true := by
  simp only [project, formula.eval_materialize_iff heads covers]
  exact (State.descend_greatest (formula.upperBounds.step_mono _) heads covers).projection_iff
    (formula.evalDemands valuation) (formula.evalDemands_mono valuation)

def withPolicy (formula : RuleCNF Head Retained) (policy : RulePolicy formula.upperBounds) : RuleCNF Head Retained :=
  { formula with upperBounds := policy.asSystem }

theorem project_iff_forall_policies (formula : RuleCNF Head Retained) (heads : List Head)
    (covers : ∀ head, head ∈ heads) (valuation : Retained → Bool) :
    formula.project heads valuation = true ↔
      ∀ policy : RulePolicy formula.upperBounds, (formula.withPolicy policy).project heads valuation = true :=
  formula.upperBounds.output_iff_forall_policies (fun literal => literal.eval valuation) heads covers
    (formula.evalDemands valuation) (formula.evalDemands_mono valuation)

end RuleCNF

end SatForgetting
