import Formal.RuleSystems

namespace SatForgetting.Frontier

universe u

variable {Var : Type u}

def Maximal (admissible : State Var → Prop) (state : State Var) : Prop :=
  admissible state ∧ ∀ larger, admissible larger → State.Included state larger → State.Included larger state

def Monotone (predicate : State Var → Bool) : Prop :=
  ∀ {left right}, State.Included left right → predicate left = true → predicate right = true

private theorem eq_of_mutually_included {left right : State Var}
    (forward : State.Included left right) (reverse : State.Included right left) : left = right := by
  funext var
  exact Bool.eq_iff_iff.mpr ⟨forward var, reverse var⟩

private theorem extend_maximal_on (admissible : State Var → Prop) (coordinates : List Var)
    {start : State Var} (valid : admissible start) :
    ∃ result, admissible result ∧ State.Included start result ∧
      ∀ larger, admissible larger → State.Included result larger →
        ∀ var ∈ coordinates, larger var = true → result var = true := by
  classical
  induction coordinates generalizing start with
  | nil => exact ⟨start, valid, State.Included.refl _, by simp⟩
  | cons var rest ih =>
    by_cases possible : ∃ grown, admissible grown ∧ State.Included start grown ∧ grown var = true
    · obtain ⟨grown, grownValid, startLe, varTrue⟩ := possible
      obtain ⟨result, resultValid, grownLe, maximalRest⟩ := ih grownValid
      refine ⟨result, resultValid, startLe.trans grownLe, ?_⟩
      intro larger largerValid resultLe coordinate member trueAt
      rcases List.mem_cons.mp member with rfl | inRest
      · exact grownLe _ varTrue
      · exact maximalRest larger largerValid resultLe coordinate inRest trueAt
    · obtain ⟨result, resultValid, startLe, maximalRest⟩ := ih valid
      refine ⟨result, resultValid, startLe, ?_⟩
      intro larger largerValid resultLe coordinate member trueAt
      rcases List.mem_cons.mp member with rfl | inRest
      · exact False.elim (possible ⟨larger, largerValid, startLe.trans resultLe, trueAt⟩)
      · exact maximalRest larger largerValid resultLe coordinate inRest trueAt

/-- Every model of a relation on finitely many Boolean coordinates extends to an
    inclusion-maximal model. The enumeration may contain duplicates. -/
theorem exists_maximal_extension (admissible : State Var → Prop) (coordinates : List Var)
    (covers : ∀ var, var ∈ coordinates) {start : State Var} (valid : admissible start) :
    ∃ result, Maximal admissible result ∧ State.Included start result := by
  obtain ⟨result, resultValid, startLe, maximalOn⟩ := extend_maximal_on admissible coordinates valid
  exact ⟨result, ⟨resultValid, fun larger largerValid resultLe var =>
    maximalOn larger largerValid resultLe var (covers var)⟩, startLe⟩

theorem exists_satisfying_iff_exists_maximal (admissible : State Var → Prop) (coordinates : List Var)
    (covers : ∀ var, var ∈ coordinates) (predicate : State Var → Bool) (monotone : Monotone predicate) :
    (∃ state, admissible state ∧ predicate state = true) ↔
      ∃ state, Maximal admissible state ∧ predicate state = true := by
  constructor
  · rintro ⟨state, model, supported⟩
    obtain ⟨result, maximal, included⟩ := exists_maximal_extension admissible coordinates covers model
    exact ⟨result, maximal, monotone included supported⟩
  · rintro ⟨state, maximal, supported⟩
    exact ⟨state, maximal.1, supported⟩

def Extendible (admissible : State Var → Prop) (support : State Var) : Prop :=
  ∃ model, admissible model ∧ State.Included support model

/-- A support maximal among extendible supports is itself a model. -/
theorem maximal_iff_maximal_extendible (admissible : State Var → Prop) (support : State Var) :
    Maximal admissible support ↔ Maximal (Extendible admissible) support := by
  constructor
  · intro maximal
    refine ⟨⟨support, maximal.1, State.Included.refl _⟩, ?_⟩
    rintro larger ⟨model, valid, largerLe⟩ supportLe
    exact largerLe.trans (maximal.2 model valid (supportLe.trans largerLe))
  · intro maximal
    obtain ⟨model, valid, supportLe⟩ := maximal.1
    have modelLe := maximal.2 model ⟨model, valid, State.Included.refl _⟩ supportLe
    refine ⟨(eq_of_mutually_included supportLe modelLe).symm ▸ valid, ?_⟩
    exact fun larger largerValid included => maximal.2 larger ⟨larger, largerValid, State.Included.refl _⟩ included

def Independent (eligible : Var → Prop) (edge : Var → Var → Prop) (support : State Var) : Prop :=
  (∀ var, support var = true → eligible var) ∧
    ∀ left right, support left = true → support right = true → ¬ edge left right

def VertexCover (edge : Var → Var → Prop) (cover : Var → Prop) : Prop :=
  ∀ left right, edge left right → cover left ∨ cover right

/-- Two maximal independent supports with the same intersection with a vertex
    cover are equal. Their union remains independent. -/
theorem maximal_independent_eq_of_agree_on_cover {eligible : Var → Prop} {edge : Var → Var → Prop}
    {cover : Var → Prop} (covers : VertexCover edge cover) {left right : State Var}
    (leftMax : Maximal (Independent eligible edge) left) (rightMax : Maximal (Independent eligible edge) right)
    (agree : ∀ var, cover var → left var = right var) : left = right := by
  let union : State Var := fun var => left var || right var
  have leftLe : State.Included left union := fun var alive => by simp [union, alive]
  have rightLe : State.Included right union := fun var alive => by simp [union, alive]
  have independent : Independent eligible edge union := by
    constructor
    · intro var alive
      rcases Bool.or_eq_true_iff.mp alive with leftTrue | rightTrue
      · exact leftMax.1.1 var leftTrue
      · exact rightMax.1.1 var rightTrue
    · intro source target sourceAlive targetAlive connected
      rcases Bool.or_eq_true_iff.mp sourceAlive with sourceLeft | sourceRight <;>
        rcases Bool.or_eq_true_iff.mp targetAlive with targetLeft | targetRight
      · exact leftMax.1.2 source target sourceLeft targetLeft connected
      · rcases covers source target connected with sourceIn | targetIn
        · exact rightMax.1.2 source target ((agree source sourceIn).symm.trans sourceLeft) targetRight connected
        · exact leftMax.1.2 source target sourceLeft ((agree target targetIn).trans targetRight) connected
      · rcases covers source target connected with sourceIn | targetIn
        · exact leftMax.1.2 source target ((agree source sourceIn).trans sourceRight) targetLeft connected
        · exact rightMax.1.2 source target sourceRight ((agree target targetIn).symm.trans targetLeft) connected
      · exact rightMax.1.2 source target sourceRight targetRight connected
  exact eq_of_mutually_included (leftLe.trans (rightMax.2 _ independent rightLe))
    (rightLe.trans (leftMax.2 _ independent leftLe))

end SatForgetting.Frontier
