import Formal.FrontierDecision
import Reductions.PairExtension

namespace SatForgetting.Frontier

universe u

variable {Var : Type u}

def Eligible (admissible : State Var → Prop) (var : Var) : Prop :=
  ∃ model, admissible model ∧ model var = true

def JointlyFeasible (admissible : State Var → Prop) (left right : Var) : Prop :=
  ∃ model, admissible model ∧ model left = true ∧ model right = true

/-- The graph uses individually feasible coordinates as vertices. An edge joins
    distinct coordinates whose two true requests cannot be satisfied together. -/
def PairConflict (admissible : State Var → Prop) (left right : Var) : Prop :=
  Eligible admissible left ∧ Eligible admissible right ∧ left ≠ right ∧
    ¬ JointlyFeasible admissible left right

theorem PairConflict.symm {admissible : State Var → Prop} {left right : Var}
    (conflict : PairConflict admissible left right) : PairConflict admissible right left := by
  obtain ⟨leftEligible, rightEligible, distinct, conflict⟩ := conflict
  refine ⟨rightEligible, leftEligible, Ne.symm distinct, ?_⟩
  rintro ⟨model, valid, rightTrue, leftTrue⟩
  exact conflict ⟨model, valid, leftTrue, rightTrue⟩

theorem PairConflict.irreflexive (admissible : State Var → Prop) (var : Var) :
    ¬ PairConflict admissible var var := fun conflict => conflict.2.2.1 rfl

theorem extendible_iff_independent {admissible : State Var → Prop}
    (nonempty : ∃ state, admissible state) (majorityClosed : PairExtension.MajorityClosed admissible)
    (coordinates : List Var) (covers : ∀ var, var ∈ coordinates) (support : State Var) :
    Extendible admissible support ↔ Independent (Eligible admissible) (PairConflict admissible) support := by
  constructor
  · rintro ⟨model, valid, included⟩
    constructor
    · exact fun var alive => ⟨model, valid, included var alive⟩
    · intro left right leftTrue rightTrue conflict
      exact conflict.2.2.2 ⟨model, valid, included left leftTrue, included right rightTrue⟩
  · intro independent
    have pairs : PairExtension.PairwiseExtendible admissible (coordinates.filter support) := by
      intro left leftMem right rightMem
      have leftTrue := (List.mem_filter.mp leftMem).2
      have rightTrue := (List.mem_filter.mp rightMem).2
      have leftEligible := independent.1 left leftTrue
      classical
      by_cases same : left = right
      · subst right
        obtain ⟨model, valid, alive⟩ := leftEligible
        exact ⟨model, valid, alive, alive⟩
      · exact Classical.byContradiction (fun missing => independent.2 left right leftTrue rightTrue
          ⟨leftEligible, independent.1 right rightTrue, same, missing⟩)
    obtain ⟨model, valid, allTrue⟩ :=
      (PairExtension.extendible_iff_pairwise nonempty majorityClosed _).mpr pairs
    exact ⟨model, valid, fun var alive => allTrue var (List.mem_filter.mpr ⟨covers var, alive⟩)⟩

theorem maximal_iff_maximal_independent {admissible : State Var → Prop}
    (nonempty : ∃ state, admissible state) (majorityClosed : PairExtension.MajorityClosed admissible)
    (coordinates : List Var) (covers : ∀ var, var ∈ coordinates) (support : State Var) :
    Maximal admissible support ↔ Maximal (Independent (Eligible admissible) (PairConflict admissible)) support := by
  have same : Extendible admissible = Independent (Eligible admissible) (PairConflict admissible) :=
    funext (fun state => propext (extendible_iff_independent nonempty majorityClosed coordinates covers state))
  rw [← same]
  exact maximal_iff_maximal_extendible admissible support

theorem exists_satisfying_iff_exists_maximal_independent {admissible : State Var → Prop}
    (nonempty : ∃ state, admissible state) (majorityClosed : PairExtension.MajorityClosed admissible)
    (coordinates : List Var) (covers : ∀ var, var ∈ coordinates)
    (predicate : State Var → Bool) (monotone : Monotone predicate) :
    (∃ state, admissible state ∧ predicate state = true) ↔
      ∃ state, Maximal (Independent (Eligible admissible) (PairConflict admissible)) state ∧ predicate state = true := by
  exact (exists_satisfying_iff_exists_maximal admissible coordinates covers predicate monotone).trans
    (exists_congr (fun state => and_congr_left' (maximal_iff_maximal_independent nonempty majorityClosed
      coordinates covers state)))

theorem twoCNF_exists_satisfying_iff_exists_maximal_independent {formula : PairExtension.CNF Var}
    (width : PairExtension.WidthTwo formula) (satisfiable : ∃ state, PairExtension.Models formula state)
    (coordinates : List Var) (covers : ∀ var, var ∈ coordinates)
    (predicate : State Var → Bool) (monotone : Monotone predicate) :
    (∃ state, PairExtension.Models formula state ∧ predicate state = true) ↔
      ∃ state, Maximal (Independent (Eligible (PairExtension.Models formula))
        (PairConflict (PairExtension.Models formula))) state ∧ predicate state = true :=
  exists_satisfying_iff_exists_maximal_independent satisfiable
    (PairExtension.models_majority_closed width) coordinates covers predicate monotone

end SatForgetting.Frontier
