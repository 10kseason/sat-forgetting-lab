import Formal.Policies
import Init.Data.List.Perm

namespace SatForgetting

universe u v

variable {Head : Type u}

/-- A head is supported by a true terminal at that head or by a true successor. -/
structure OrGraph (Head : Type u) where
  successors : Head → List Head
  enabled : State Head

namespace OrGraph

def step (graph : OrGraph Head) (state : State Head) (head : Head) : Bool :=
  graph.enabled head || (graph.successors head).any state

def Edge (graph : OrGraph Head) (source target : Head) : Prop :=
  target ∈ graph.successors source

theorem step_true_iff (graph : OrGraph Head) (state : State Head) (head : Head) :
    graph.step state head = true ↔
      graph.enabled head = true ∨ ∃ target, graph.Edge head target ∧ state target = true := by
  simp only [step, Edge, Bool.or_eq_true, List.any_eq_true]

theorem step_mono (graph : OrGraph Head) : State.Monotone graph.step := by
  intro left right included head supported
  apply (graph.step_true_iff right head).mpr
  rcases (graph.step_true_iff left head).mp supported with enabled | ⟨target, edge, alive⟩
  · exact Or.inl enabled
  · exact Or.inr ⟨target, edge, included target alive⟩

inductive Path (graph : OrGraph Head) : Head → Head → Prop where
  | refl (head : Head) : Path graph head head
  | cons {source next target : Head} (edge : graph.Edge source next) (rest : Path graph next target) :
    Path graph source target

def Cycle (graph : OrGraph Head) (head : Head) : Prop :=
  ∃ next, graph.Edge head next ∧ graph.Path next head

def ReachesSupport (graph : OrGraph Head) (source : Head) : Prop :=
  ∃ target, graph.Path source target ∧ (graph.enabled target = true ∨ graph.Cycle target)

private theorem reachesSupport_step (graph : OrGraph Head) {head : Head}
    (reaches : graph.ReachesSupport head) :
    graph.enabled head = true ∨ ∃ next, graph.Edge head next ∧ graph.ReachesSupport next := by
  obtain ⟨target, path, support⟩ := reaches
  cases path with
  | refl head =>
    rcases support with enabled | ⟨next, edge, cyclePath⟩
    · exact Or.inl enabled
    · exact Or.inr ⟨next, edge, head, cyclePath, Or.inr ⟨next, edge, cyclePath⟩⟩
  | cons edge rest => exact Or.inr ⟨_, edge, target, rest, support⟩

theorem descend_true_of_reachesSupport (graph : OrGraph Head) (round : Nat) {head : Head}
    (reaches : graph.ReachesSupport head) : State.descend graph.step round head = true := by
  induction round generalizing head with
  | zero => rfl
  | succ round ih =>
    apply (graph.step_true_iff (State.descend graph.step round) head).mpr
    rcases graph.reachesSupport_step reaches with enabled | ⟨next, edge, supportsNext⟩
    · exact Or.inl enabled
    · exact Or.inr ⟨next, edge, ih supportsNext⟩

private inductive Walk (graph : OrGraph Head) : Head → List Head → Prop where
  | stop (head : Head) : Walk graph head []
  | cons {head next : Head} {trail : List Head} (edge : graph.Edge head next)
      (rest : Walk graph next trail) : Walk graph head (next :: trail)

private theorem Walk.path_to_member {graph : OrGraph Head} {head target : Head} {trail : List Head}
    (walk : Walk graph head trail) (member : target ∈ head :: trail) : graph.Path head target := by
  induction walk with
  | stop head =>
    have same := List.mem_singleton.mp member
    exact same ▸ .refl _
  | cons edge rest ih =>
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ .refl _
    · exact .cons edge (ih later)

private theorem Walk.reachesSupport_of_repeat [DecidableEq Head] {graph : OrGraph Head}
    {head : Head} {trail : List Head} (walk : Walk graph head trail)
    (repeated : ¬ (head :: trail).Nodup) : graph.ReachesSupport head := by
  induction walk with
  | stop head => exact False.elim (repeated (by simp))
  | @cons head next trail edge rest ih =>
    by_cases returns : head ∈ next :: trail
    · exact ⟨head, .refl _, Or.inr ⟨next, edge, rest.path_to_member returns⟩⟩
    · have tailRepeat : ¬ (next :: trail).Nodup := fun distinct =>
        repeated (List.nodup_cons.mpr ⟨returns, distinct⟩)
      obtain ⟨target, path, support⟩ := ih tailRepeat
      exact ⟨target, .cons edge path, support⟩

private theorem reachesSupport_or_walk (graph : OrGraph Head) {state : State Head}
    (postfixed : State.Included state (graph.step state)) (length : Nat) {head : Head}
    (alive : state head = true) : graph.ReachesSupport head ∨
      ∃ trail, trail.length = length ∧ Walk graph head trail := by
  induction length generalizing head with
  | zero => exact Or.inr ⟨[], rfl, .stop _⟩
  | succ length ih =>
    rcases (graph.step_true_iff state head).mp (postfixed head alive) with enabled | ⟨next, edge, nextAlive⟩
    · exact Or.inl ⟨head, .refl _, Or.inl enabled⟩
    · rcases ih nextAlive with ⟨target, path, support⟩ | ⟨trail, sized, walk⟩
      · exact Or.inl ⟨target, .cons edge path, support⟩
      · exact Or.inr ⟨next :: trail, by simp [sized], .cons edge walk⟩

/-- A head belongs to the greatest state exactly when it can reach an enabled
    terminal or a directed cycle, including a self-loop. -/
theorem descend_true_iff_reachesSupport [DecidableEq Head] (graph : OrGraph Head)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (head : Head) :
    State.descend graph.step heads.length head = true ↔ graph.ReachesSupport head := by
  constructor
  · intro alive
    have greatest := State.descend_greatest graph.step_mono heads covers
    rcases graph.reachesSupport_or_walk greatest.postfixed heads.length alive with supports | ⟨trail, sized, walk⟩
    · exact supports
    · apply walk.reachesSupport_of_repeat
      intro distinct
      have bound := distinct.length_le_of_subset (l₂ := heads) (fun {_} _ => covers _)
      exact Nat.not_succ_le_self heads.length (by simpa [sized] using bound)
  · exact graph.descend_true_of_reachesSupport heads.length

end OrGraph

variable {Terminal : Type v} {system : RuleSystem Head Terminal}

def RulePolicy.graph (policy : RulePolicy system) (retained : Terminal → Bool) : OrGraph Head where
  successors := fun head => match policy.selected head with
    | none => []
    | some rule => rule.successors
  enabled := fun head => match policy.selected head with
    | none => true
    | some rule => rule.terminals.any retained

theorem RulePolicy.graph_step (policy : RulePolicy system) (retained : Terminal → Bool) :
    (policy.graph retained).step = policy.asSystem.step retained := by
  funext state head
  cases choice : policy.selected head <;> simp [graph, OrGraph.step, asSystem, RuleSystem.step, Rule.eval, choice]

theorem RulePolicy.descend_true_iff_reachesSupport [DecidableEq Head] (policy : RulePolicy system)
    (retained : Terminal → Bool) (heads : List Head) (covers : ∀ head, head ∈ heads) (head : Head) :
    State.descend (policy.asSystem.step retained) heads.length head = true ↔
      (policy.graph retained).ReachesSupport head := by
  rw [← policy.graph_step retained]
  exact (policy.graph retained).descend_true_iff_reachesSupport heads covers head

end SatForgetting
