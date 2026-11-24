import Init.Data.List.Count
import Init.Data.List.Nat.Range
import Init.Omega

namespace SatForgetting

universe u v

abbrev State (Head : Type u) := Head → Bool

namespace State

variable {Head : Type u}

def Included (left right : State Head) : Prop :=
  ∀ head, left head = true → right head = true

theorem Included.refl (state : State Head) : Included state state := fun _ h => h

theorem Included.trans {left middle right : State Head}
    (first : Included left middle) (second : Included middle right) : Included left right :=
  fun head alive => second head (first head alive)

def Monotone (step : State Head → State Head) : Prop :=
  ∀ {left right}, Included left right → Included (step left) (step right)

structure Greatest (step : State Head → State Head) (state : State Head) : Prop where
  postfixed : Included state (step state)
  dominates : ∀ candidate, Included candidate (step candidate) → Included candidate state

theorem Greatest.unique {step : State Head → State Head} {left right : State Head}
    (first : Greatest step left) (second : Greatest step right) : left = right := by
  funext head
  exact Bool.eq_iff_iff.mpr
    ⟨second.dominates left first.postfixed head, first.dominates right second.postfixed head⟩

theorem Greatest.projection_iff {step : State Head → State Head} {state : State Head}
    (greatest : Greatest step state) (output : State Head → Bool)
    (monotone : ∀ {left right}, Included left right → output left = true → output right = true) :
    output state = true ↔ ∃ candidate, Included candidate (step candidate) ∧ output candidate = true := by
  constructor
  · exact fun supported => ⟨state, greatest.postfixed, supported⟩
  · rintro ⟨candidate, postfixed, supported⟩
    exact monotone (greatest.dominates candidate postfixed) supported

/-- Synchronous descent from the state in which every head is alive. -/
def descend (step : State Head → State Head) : Nat → State Head
  | 0 => fun _ => true
  | round + 1 => step (descend step round)

theorem descend_succ_included {step : State Head → State Head} (monotone : Monotone step)
    (round : Nat) : Included (descend step (round + 1)) (descend step round) := by
  induction round with
  | zero => exact fun _ _ => rfl
  | succ round ih => exact monotone ih

theorem descend_included {step : State Head → State Head} (monotone : Monotone step)
    {earlier later : Nat} (order : earlier ≤ later) :
    Included (descend step later) (descend step earlier) := by
  induction order with
  | refl => exact Included.refl _
  | step order ih => exact (descend_succ_included monotone _).trans ih

theorem included_descend {step : State Head → State Head} (monotone : Monotone step)
    {candidate : State Head} (postfixed : Included candidate (step candidate)) (round : Nat) :
    Included candidate (descend step round) := by
  induction round with
  | zero => exact fun _ _ => rfl
  | succ round ih => exact postfixed.trans (monotone ih)

private theorem countP_lt_of_change {left right : State Head} (included : Included left right)
    {heads : List Head} {changed : Head} (listed : changed ∈ heads)
    (leftFalse : left changed = false) (rightTrue : right changed = true) :
    heads.countP left < heads.countP right := by
  induction heads with
  | nil => simp at listed
  | cons head tail ih =>
    rcases List.mem_cons.mp listed with equal | rest
    · subst head
      have le : tail.countP left ≤ tail.countP right :=
        List.countP_mono_left (fun head _ => included head)
      simpa [List.countP_cons, leftFalse, rightTrue] using Nat.lt_succ_of_le le
    · have tailLt := ih rest
      by_cases alive : left head = true
      · simpa [List.countP_cons, alive, included head alive] using tailLt
      · simpa [List.countP_cons, alive] using
          Nat.lt_of_lt_of_le tailLt (Nat.le_add_right (tail.countP right) (if right head then 1 else 0))

private theorem descend_fixed_or_count_lt {step : State Head → State Head} (monotone : Monotone step)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (round : Nat) :
    descend step (round + 1) = descend step round ∨
      heads.countP (descend step (round + 1)) < heads.countP (descend step round) := by
  let next := descend step (round + 1)
  let current := descend step round
  have included : Included next current := descend_succ_included monotone round
  cases same : heads.all (fun head => next head == current head) with
  | true =>
    left
    funext head
    simpa using List.all_eq_true.mp same head (covers head)
  | false =>
    right
    obtain ⟨head, member, changed⟩ := List.all_eq_false.mp same
    have nextFalse : next head = false := Bool.eq_false_iff.mpr fun nextTrue =>
      changed (by simp [nextTrue, included head nextTrue])
    have currentTrue : current head = true := by
      cases value : current head with
      | true => rfl
      | false => exact False.elim (changed (by simp [nextFalse, value]))
    exact countP_lt_of_change included member nextFalse currentTrue

private theorem descend_fixed_or_count_add_le {step : State Head → State Head} (monotone : Monotone step)
    (heads : List Head) (covers : ∀ head, head ∈ heads) (round : Nat) :
    descend step (round + 1) = descend step round ∨
      heads.countP (descend step round) + round ≤ heads.length := by
  induction round with
  | zero => exact Or.inr (by simp [List.countP_le_length])
  | succ round ih =>
    rcases ih with fixed | bound
    · exact Or.inl (congrArg step fixed)
    · rcases descend_fixed_or_count_lt monotone heads covers round with fixed | drops
      · exact Or.inl (congrArg step fixed)
      · exact Or.inr (by omega)

/-- One step without a deletion is permanent, and each earlier step deletes a listed head.
    The enumeration is allowed to contain duplicates. -/
theorem descend_fixed {step : State Head → State Head} (monotone : Monotone step)
    (heads : List Head) (covers : ∀ head, head ∈ heads) :
    step (descend step heads.length) = descend step heads.length := by
  rcases descend_fixed_or_count_lt monotone heads covers heads.length with fixed | drops
  · exact fixed
  · rcases descend_fixed_or_count_add_le monotone heads covers heads.length with fixed | bound
    · exact fixed
    · omega

theorem descend_greatest {step : State Head → State Head} (monotone : Monotone step)
    (heads : List Head) (covers : ∀ head, head ∈ heads) : Greatest step (descend step heads.length) where
  postfixed := by
    rw [descend_fixed monotone heads covers]
    exact Included.refl _
  dominates := fun _ postfixed => included_descend monotone postfixed heads.length

/-- A missing head's rank is the first round at which it is absent. -/
def deletionRound (step : State Head → State Head) (fuel : Nat) (head : Head) : Option Nat :=
  (List.range (fuel + 1)).find? (fun round => !(descend step round head))

def deletionRank (step : State Head → State Head) (fuel : Nat) (head : Head) : Nat :=
  (deletionRound step fuel head).getD 0

theorem deletionRound_exists (step : State Head → State Head) (fuel : Nat) (head : Head)
    (absent : descend step fuel head = false) : ∃ round, deletionRound step fuel head = some round := by
  cases found : deletionRound step fuel head with
  | some round => exact ⟨round, rfl⟩
  | none =>
    have stillAlive := List.find?_range_eq_none.mp found fuel (Nat.lt_succ_self fuel)
    simp [absent] at stillAlive

theorem deletionRound_spec {step : State Head → State Head} {fuel : Nat} {head : Head} {round : Nat}
    (found : deletionRound step fuel head = some round) :
    descend step round head = false ∧ round ≤ fuel ∧
      ∀ earlier, earlier < round → descend step earlier head = true := by
  simpa [Nat.lt_succ_iff] using List.find?_range_eq_some.mp found

end State

variable {Head : Type u} {Terminal : Type v}

structure Rule (Head : Type u) (Terminal : Type v) where
  successors : List Head
  terminals : List Terminal
  deriving DecidableEq, Repr

def Rule.eval (rule : Rule Head Terminal) (retained : Terminal → Bool) (state : State Head) : Bool :=
  rule.terminals.any retained || rule.successors.any state

theorem Rule.eval_mono (rule : Rule Head Terminal) (retained : Terminal → Bool) {left right : State Head}
    (included : State.Included left right) : rule.eval retained left = true → rule.eval retained right = true := by
  simp only [eval, Bool.or_eq_true, List.any_eq_true]
  rintro (terminal | ⟨successor, member, alive⟩)
  · exact Or.inl terminal
  · exact Or.inr ⟨successor, member, included successor alive⟩

abbrev RuleSystem (Head : Type u) (Terminal : Type v) := Head → List (Rule Head Terminal)

def RuleSystem.step (system : RuleSystem Head Terminal) (retained : Terminal → Bool)
    (state : State Head) (head : Head) : Bool :=
  (system head).all (fun rule => rule.eval retained state)

theorem RuleSystem.step_mono (system : RuleSystem Head Terminal) (retained : Terminal → Bool) :
    State.Monotone (system.step retained) := by
  intro left right included head alive
  refine List.all_eq_true.mpr (fun rule member => rule.eval_mono retained included ?_)
  exact List.all_eq_true.mp alive rule member

theorem RuleSystem.step_true_iff (system : RuleSystem Head Terminal) (retained : Terminal → Bool)
    (state : State Head) (head : Head) :
    system.step retained state head = true ↔ ∀ rule ∈ system head, rule.eval retained state = true :=
  List.all_eq_true

theorem RuleSystem.step_false_iff (system : RuleSystem Head Terminal) (retained : Terminal → Bool)
    (state : State Head) (head : Head) :
    system.step retained state head = false ↔ ∃ rule ∈ system head, rule.eval retained state = false := by
  rw [RuleSystem.step, List.all_eq_false]
  simp only [Bool.eq_false_iff]

/-- A certificate for each losing head records a rule with no true terminal and
    only losing successors of strictly smaller rank. -/
def RuleSystem.RankedLosses (system : RuleSystem Head Terminal) (retained : Terminal → Bool)
    (winning : State Head) (rank : Head → Nat) : Prop :=
  ∀ head, winning head = false → ∃ rule ∈ system head,
    rule.terminals.any retained = false ∧ ∀ successor ∈ rule.successors,
      winning successor = false ∧ rank successor < rank head

theorem RuleSystem.descend_rankedLosses (system : RuleSystem Head Terminal)
    (retained : Terminal → Bool) (fuel : Nat) :
    system.RankedLosses retained (State.descend (system.step retained) fuel)
      (State.deletionRank (system.step retained) fuel) := by
  intro head absent
  obtain ⟨round, found⟩ := State.deletionRound_exists (system.step retained) fuel head absent
  obtain ⟨roundAbsent, roundBound, _⟩ := State.deletionRound_spec found
  cases round with
  | zero => simp [State.descend] at roundAbsent
  | succ previous =>
    obtain ⟨rule, member, unsatisfied⟩ := (system.step_false_iff retained _ head).mp roundAbsent
    obtain ⟨terminalsFalse, successorsAbsent⟩ := Bool.or_eq_false_iff.mp unsatisfied
    refine ⟨rule, member, terminalsFalse, ?_⟩
    intro successor successorMem
    have earlierAbsent := Bool.eq_false_iff.mpr (List.any_eq_false.mp successorsAbsent successor successorMem)
    have finalAbsent : State.descend (system.step retained) fuel successor = false :=
      Bool.eq_false_iff.mpr fun finalAlive =>
        Bool.eq_false_iff.mp earlierAbsent
          (State.descend_included (system.step_mono retained) (Nat.le_of_succ_le roundBound) successor finalAlive)
    obtain ⟨earlier, successorFound⟩ := State.deletionRound_exists (system.step retained) fuel successor finalAbsent
    obtain ⟨_, _, beforeEarlier⟩ := State.deletionRound_spec successorFound
    have earlierBound : earlier ≤ previous := Nat.le_of_not_gt fun smaller =>
      Bool.eq_false_iff.mp earlierAbsent (beforeEarlier previous smaller)
    exact ⟨finalAbsent, by simpa [State.deletionRank, found, successorFound] using Nat.lt_succ_of_le earlierBound⟩

end SatForgetting
