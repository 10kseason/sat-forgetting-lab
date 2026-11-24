import Formal.CNF

/-! In a nonempty Boolean relation closed under majority, a list of coordinates can
all be true exactly when each pair can be true together. Signed 2-CNF relations
satisfy the closure assumption. -/

namespace PairExtension

universe u

abbrev State (ι : Type u) := ι → Bool

def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def majorityState {ι : Type u} (x y z : State ι) : State ι :=
  fun i => majority (x i) (y i) (z i)

def MajorityClosed {ι : Type u} (relation : State ι → Prop) : Prop :=
  ∀ ⦃x y z⦄, relation x → relation y → relation z → relation (majorityState x y z)

private theorem majority_of_two {a b c value : Bool}
    (h : (a = value ∧ b = value) ∨ (a = value ∧ c = value) ∨
      (b = value ∧ c = value)) : majority a b c = value := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rw [ha, hb] <;> cases value <;> simp [majority]

def Extendible {ι : Type u} (relation : State ι → Prop) (requests : List ι) : Prop :=
  ∃ x, relation x ∧ ∀ i ∈ requests, x i = true

def PairwiseExtendible {ι : Type u} (relation : State ι → Prop) (requests : List ι) : Prop :=
  ∀ i ∈ requests, ∀ j ∈ requests, ∃ x, relation x ∧ x i = true ∧ x j = true

private theorem pairs_of_subset {ι : Type u} {relation : State ι → Prop}
    {short long : List ι} (sub : ∀ i ∈ short, i ∈ long)
    (pairs : PairwiseExtendible relation long) : PairwiseExtendible relation short :=
  fun i hi j hj => pairs i (sub i hi) j (sub j hj)

/-- In a nonempty majority-closed relation, pair witnesses suffice. A coordinate may
be paired with itself, so the criterion also covers a single request. -/
theorem extendible_iff_pairwise {ι : Type u} {relation : State ι → Prop}
    (nonempty : ∃ x, relation x) (closed : MajorityClosed relation) (requests : List ι) :
    Extendible relation requests ↔ PairwiseExtendible relation requests := by
  constructor
  · rintro ⟨x, hx, holds⟩ i hi j hj
    exact ⟨x, hx, holds i hi, holds j hj⟩
  · suffices build : ∀ n (S : List ι), S.length = n →
        PairwiseExtendible relation S → Extendible relation S from
      build requests.length requests rfl
    intro n
    induction n using Nat.strongRecOn with
    | ind n smaller =>
      intro S size pairs
      match S with
      | [] =>
        obtain ⟨x, hx⟩ := nonempty
        exact ⟨x, hx, by simp⟩
      | [a] =>
        obtain ⟨x, hx, ha, _⟩ := pairs a (by simp) a (by simp)
        refine ⟨x, hx, ?_⟩
        intro i hi
        simpa using (show i = a from by simpa using hi) ▸ ha
      | [a, b] =>
        obtain ⟨x, hx, ha, hb⟩ := pairs a (by simp) b (by simp)
        refine ⟨x, hx, ?_⟩
        intro i hi
        rcases (show i = a ∨ i = b from by simpa using hi) with rfl | rfl
        · exact ha
        · exact hb
      | a :: b :: c :: tail =>
        have omitA : ∀ i ∈ b :: c :: tail, i ∈ a :: b :: c :: tail :=
          fun _ hi => List.mem_cons_of_mem _ hi
        have omitB : ∀ i ∈ a :: c :: tail, i ∈ a :: b :: c :: tail := by
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)
        have omitC : ∀ i ∈ a :: b :: tail, i ∈ a :: b :: c :: tail := by
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact List.mem_cons_self
          rcases List.mem_cons.mp hi with rfl | hi
          · exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))
        have shorter : (b :: c :: tail).length < n := by
          rw [← size]
          exact Nat.lt_succ_self _
        obtain ⟨x, hx, hasX⟩ := smaller _ shorter (b :: c :: tail) rfl (pairs_of_subset omitA pairs)
        obtain ⟨y, hy, hasY⟩ := smaller _ shorter (a :: c :: tail) rfl (pairs_of_subset omitB pairs)
        obtain ⟨z, hz, hasZ⟩ := smaller _ shorter (a :: b :: tail) rfl (pairs_of_subset omitC pairs)
        refine ⟨majorityState x y z, closed hx hy hz, ?_⟩
        intro i hi
        change majority (x i) (y i) (z i) = true
        apply majority_of_two
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inr (Or.inr ⟨hasY i (by simp), hasZ i (by simp)⟩)
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inr (Or.inl ⟨hasX i (by simp), hasZ i (by simp)⟩)
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inl ⟨hasX i (by simp), hasY i (by simp)⟩
        · exact Or.inl ⟨hasX i (by simp [hi]), hasY i (by simp [hi])⟩

abbrev Literal (ι : Type u) := SatForgetting.Literal ι
abbrev CNF (ι : Type u) := SatForgetting.CNF ι

abbrev SatisfiesLiteral {ι : Type u} (x : State ι) (lit : Literal ι) : Prop :=
  SatForgetting.Literal.Satisfies lit x

abbrev SatisfiesClause {ι : Type u} (x : State ι) (clause : List (Literal ι)) : Prop :=
  SatForgetting.Clause.Satisfies clause x

abbrev Models {ι : Type u} (formula : CNF ι) (x : State ι) : Prop :=
  SatForgetting.CNF.Satisfies formula x

def WidthTwo {ι : Type u} (formula : CNF ι) : Prop :=
  ∀ clause ∈ formula, clause.length ≤ 2

private theorem binary_majority {ι : Type u} {x y z : State ι} {p q : Literal ι}
    (hx : SatisfiesLiteral x p ∨ SatisfiesLiteral x q)
    (hy : SatisfiesLiteral y p ∨ SatisfiesLiteral y q)
    (hz : SatisfiesLiteral z p ∨ SatisfiesLiteral z q) :
    SatisfiesLiteral (majorityState x y z) p ∨ SatisfiesLiteral (majorityState x y z) q := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  all_goals
    first
    | exact Or.inl (majority_of_two (Or.inl ⟨hx, hy⟩))
    | exact Or.inl (majority_of_two (Or.inr (Or.inl ⟨hx, hz⟩)))
    | exact Or.inl (majority_of_two (Or.inr (Or.inr ⟨hy, hz⟩)))
    | exact Or.inr (majority_of_two (Or.inl ⟨hx, hy⟩))
    | exact Or.inr (majority_of_two (Or.inr (Or.inl ⟨hx, hz⟩)))
    | exact Or.inr (majority_of_two (Or.inr (Or.inr ⟨hy, hz⟩)))

private theorem satisfies_binary_iff {ι : Type u} {x : State ι} {p q : Literal ι} :
    SatisfiesClause x [p, q] ↔ SatisfiesLiteral x p ∨ SatisfiesLiteral x q := by
  constructor
  · rintro ⟨lit, member, sat⟩
    rcases (show lit = p ∨ lit = q from by simpa using member) with rfl | rfl
    · exact Or.inl sat
    · exact Or.inr sat
  · rintro (hp | hq)
    · exact ⟨p, by simp, hp⟩
    · exact ⟨q, by simp, hq⟩

/-- Signed unit and binary clauses preserve majority. An empty clause has no models. -/
theorem models_majority_closed {ι : Type u} {formula : CNF ι} (width : WidthTwo formula) :
    MajorityClosed (Models formula) := by
  intro x y z hx hy hz clause member
  have size := width clause member
  match clause with
  | [] => exact hx [] member |>.elim fun lit ⟨hm, _⟩ => (List.not_mem_nil hm).elim
  | [p] =>
    have one (state : State ι) (sat : Models formula state) : SatisfiesLiteral state p := by
      obtain ⟨lit, listed, holds⟩ := sat [p] member
      have equal : lit = p := by simpa using listed
      exact equal ▸ holds
    exact ⟨p, by simp, majority_of_two (Or.inl ⟨one x hx, one y hy⟩)⟩
  | [p, q] =>
    exact satisfies_binary_iff.mpr (binary_majority (satisfies_binary_iff.mp (hx _ member))
      (satisfies_binary_iff.mp (hy _ member)) (satisfies_binary_iff.mp (hz _ member)))
  | p :: q :: r :: tail =>
    exact (Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ size))).elim

/-- Extension property for a satisfiable signed 2-CNF under positive unit requests.
The tests include equal coordinates, and an empty list of requests is permitted. -/
theorem twoCNF_pair_extension {ι : Type u} {formula : CNF ι} (width : WidthTwo formula)
    (satisfiable : ∃ x, Models formula x) (requests : List ι) :
    (∃ x, Models formula x ∧ ∀ i ∈ requests, x i = true) ↔
      (∀ i ∈ requests, ∀ j ∈ requests, ∃ x, Models formula x ∧ x i = true ∧ x j = true) :=
  extendible_iff_pairwise satisfiable (models_majority_closed width) requests

private def literalView {ι : Type u} (x : State ι) : State (Literal ι) :=
  fun lit => x lit.1 == lit.2

private theorem literalView_true {ι : Type u} {x : State ι} {lit : Literal ι} :
    literalView x lit = true ↔ SatisfiesLiteral x lit := by
  simp [literalView, SatisfiesLiteral, SatForgetting.Literal.Satisfies]

private theorem literalView_majority {ι : Type u} (x y z : State ι) :
    literalView (majorityState x y z) = majorityState (literalView x) (literalView y) (literalView z) := by
  funext lit
  obtain ⟨i, sign⟩ := lit
  change (majority (x i) (y i) (z i) == sign) =
    majority (x i == sign) (y i == sign) (z i == sign)
  cases sign <;> cases x i <;> cases y i <;> cases z i <;> rfl

/-- Pair tests also suffice for arbitrary signed assumptions, as used by a conflict
graph on individually feasible literals. -/
theorem twoCNF_signed_pair_extension {ι : Type u} {formula : CNF ι} (width : WidthTwo formula)
    (satisfiable : ∃ x, Models formula x) (requests : List (Literal ι)) :
    (∃ x, Models formula x ∧ ∀ lit ∈ requests, SatisfiesLiteral x lit) ↔
      (∀ p ∈ requests, ∀ q ∈ requests,
        ∃ x, Models formula x ∧ SatisfiesLiteral x p ∧ SatisfiesLiteral x q) := by
  constructor
  · rintro ⟨x, hx, holds⟩ p hp q hq
    exact ⟨x, hx, holds p hp, holds q hq⟩
  · intro pairs
    let relation (w : State (Literal ι)) := ∃ x, Models formula x ∧ literalView x = w
    have nonempty : ∃ w, relation w := by
      obtain ⟨x, hx⟩ := satisfiable
      exact ⟨literalView x, x, hx, rfl⟩
    have closed : MajorityClosed relation := by
      rintro _ _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
      exact ⟨majorityState x y z, models_majority_closed width hx hy hz, literalView_majority x y z⟩
    have witnesses : PairwiseExtendible relation requests := by
      intro p hp q hq
      obtain ⟨x, hx, trueP, trueQ⟩ := pairs p hp q hq
      exact ⟨literalView x, ⟨x, hx, rfl⟩, literalView_true.mpr trueP, literalView_true.mpr trueQ⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, holds⟩ := (extendible_iff_pairwise nonempty closed requests).mpr witnesses
    exact ⟨x, hx, fun lit member => literalView_true.mp (holds lit member)⟩

end PairExtension
