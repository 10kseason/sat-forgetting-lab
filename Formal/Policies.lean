import Formal.RuleSystems

namespace SatForgetting

universe u v

variable {Head : Type u} {Terminal : Type v}

/-- A static policy keeps one existing rule at every head with rules. Heads without
    rules remain unconstrained. -/
structure RulePolicy (system : RuleSystem Head Terminal) where
  selected : Head → Option (Rule Head Terminal)
  valid : ∀ head, match selected head with
    | none => system head = []
    | some rule => rule ∈ system head

def RulePolicy.asSystem {system : RuleSystem Head Terminal}
    (policy : RulePolicy system) : RuleSystem Head Terminal :=
  fun head => (policy.selected head).toList

theorem RulePolicy.postfixed_of_original {system : RuleSystem Head Terminal}
    (policy : RulePolicy system) (retained : Terminal → Bool) {state : State Head}
    (postfixed : State.Included state (system.step retained state)) :
    State.Included state (policy.asSystem.step retained state) := by
  intro head alive
  cases choice : policy.selected head with
  | none => simp [asSystem, RuleSystem.step, choice]
  | some rule =>
    have member := policy.valid head
    rw [choice] at member
    have supports := (system.step_true_iff retained state head).mp (postfixed head alive) rule member
    simp [asSystem, RuleSystem.step, choice, supports]

private def isBlocking (retained : Terminal → Bool) (winning : State Head)
    (rank : Head → Nat) (head : Head) (rule : Rule Head Terminal) : Bool :=
  !(rule.terminals.any retained) &&
    rule.successors.all (fun successor => !(winning successor) && decide (rank successor < rank head))

private theorem isBlocking_iff (retained : Terminal → Bool) (winning : State Head)
    (rank : Head → Nat) (head : Head) (rule : Rule Head Terminal) :
    isBlocking retained winning rank head rule = true ↔
      rule.terminals.any retained = false ∧ ∀ successor ∈ rule.successors,
        winning successor = false ∧ rank successor < rank head := by
  simp [isBlocking, Bool.and_eq_true]

/-- A single policy reproduces the whole winning state. For a losing head it keeps
    a blocking rule witnessed by the strictly decreasing rank. For a winning head
    every original rule is available. -/
theorem RuleSystem.exists_tightPolicy_of_rankedLosses (system : RuleSystem Head Terminal)
    (retained : Terminal → Bool) {winning : State Head} {rank : Head → Nat}
    (postfixed : State.Included winning (system.step retained winning))
    (ranked : system.RankedLosses retained winning rank) :
    ∃ policy : RulePolicy system, State.Greatest (policy.asSystem.step retained) winning := by
  let selected : Head → Option (Rule Head Terminal) := fun head =>
    (system head).find? (fun rule => winning head || isBlocking retained winning rank head rule)
  have valid : ∀ head, match selected head with
      | none => system head = []
      | some rule => rule ∈ system head := by
    intro head
    cases found : selected head with
    | some rule => exact List.mem_of_find?_eq_some found
    | none =>
      have rejected := List.find?_eq_none.mp found
      cases rules : system head with
      | nil => rfl
      | cons first rest =>
        exfalso
        cases winner : winning head with
        | true =>
          exact rejected first (by simp [rules]) (by simp [winner])
        | false =>
          obtain ⟨rule, member, blocks⟩ := ranked head winner
          exact rejected rule member (by simpa [winner] using (isBlocking_iff retained winning rank head rule).mpr blocks)
  let policy : RulePolicy system := ⟨selected, valid⟩
  refine ⟨policy, policy.postfixed_of_original retained postfixed, ?_⟩
  intro candidate candidatePostfixed
  have noLosingHead : ∀ round head, rank head = round → winning head = false → candidate head = false := by
    intro round
    induction round using Nat.strongRecOn with
    | ind round ih =>
      intro head rankHead lost
      apply Bool.eq_false_iff.mpr
      intro candidateAlive
      cases choice : selected head with
      | none =>
        obtain ⟨rule, member, _⟩ := ranked head lost
        have noRules := valid head
        rw [choice] at noRules
        simp [noRules] at member
      | some rule =>
        have chosen := List.find?_some choice
        have blocks : isBlocking retained winning rank head rule = true := by
          simpa [lost] using chosen
        obtain ⟨terminalsFalse, smallerLosses⟩ := (isBlocking_iff retained winning rank head rule).mp blocks
        have successorsFalse : rule.successors.any candidate = false := by
          apply List.any_eq_false.mpr
          intro successor member
          obtain ⟨successorLost, smaller⟩ := smallerLosses successor member
          exact Bool.eq_false_iff.mp (ih (rank successor) (rankHead ▸ smaller) successor rfl successorLost)
        have ruleFalse : rule.eval retained candidate = false := by
          simp [Rule.eval, terminalsFalse, successorsFalse]
        have ruleTrue := candidatePostfixed head candidateAlive
        change ((selected head).toList.all (fun current => current.eval retained candidate)) = true at ruleTrue
        simp [choice, ruleFalse] at ruleTrue
  intro head candidateAlive
  cases winner : winning head with
  | true => rfl
  | false =>
    exact False.elim (Bool.eq_false_iff.mp (noLosingHead (rank head) head rfl winner) candidateAlive)

theorem RuleSystem.exists_tightPolicy (system : RuleSystem Head Terminal)
    (retained : Terminal → Bool) (heads : List Head) (covers : ∀ head, head ∈ heads) :
    ∃ policy : RulePolicy system,
      State.descend (policy.asSystem.step retained) heads.length =
        State.descend (system.step retained) heads.length := by
  have greatest := State.descend_greatest (system.step_mono retained) heads covers
  obtain ⟨policy, tight⟩ := system.exists_tightPolicy_of_rankedLosses retained greatest.postfixed
    (system.descend_rankedLosses retained heads.length)
  exact ⟨policy, (State.descend_greatest (policy.asSystem.step_mono retained) heads covers).unique tight⟩

/-- For each fixed retained valuation, evaluation at the original greatest state
    agrees with the conjunction of evaluations at every static policy's greatest state. -/
theorem RuleSystem.output_iff_forall_policies (system : RuleSystem Head Terminal)
    (retained : Terminal → Bool) (heads : List Head) (covers : ∀ head, head ∈ heads)
    (output : State Head → Bool)
    (monotone : ∀ {left right}, State.Included left right → output left = true → output right = true) :
    output (State.descend (system.step retained) heads.length) = true ↔
      ∀ policy : RulePolicy system, output (State.descend (policy.asSystem.step retained) heads.length) = true := by
  constructor
  · intro original policy
    have greatest := State.descend_greatest (system.step_mono retained) heads covers
    have policyPostfixed := policy.postfixed_of_original retained greatest.postfixed
    exact monotone (State.included_descend (policy.asSystem.step_mono retained) policyPostfixed heads.length) original
  · intro everyPolicy
    obtain ⟨policy, tight⟩ := system.exists_tightPolicy retained heads covers
    simpa [tight] using everyPolicy policy

theorem RuleSystem.projection_iff_forall_policies (system : RuleSystem Head Terminal)
    (retained : Terminal → Bool) (heads : List Head) (covers : ∀ head, head ∈ heads)
    (output : State Head → Bool)
    (monotone : ∀ {left right}, State.Included left right → output left = true → output right = true) :
    (∃ state, State.Included state (system.step retained state) ∧ output state = true) ↔
      ∀ policy : RulePolicy system,
        ∃ state, State.Included state (policy.asSystem.step retained state) ∧ output state = true := by
  constructor
  · rintro ⟨state, original, goal⟩ policy
    exact ⟨state, policy.postfixed_of_original retained original, goal⟩
  · intro allPolicies
    have greatest := State.descend_greatest (system.step_mono retained) heads covers
    apply (greatest.projection_iff output monotone).mp
    apply (system.output_iff_forall_policies retained heads covers output monotone).mpr
    intro policy
    exact ((State.descend_greatest (policy.asSystem.step_mono retained) heads covers).projection_iff
      output monotone).mpr (allPolicies policy)

end SatForgetting
