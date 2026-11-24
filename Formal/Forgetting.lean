import Init.Data.List.Lemmas

namespace SatForgetting

universe u v

structure Literal (Var : Type u) where
  var : Var
  positive : Bool
  deriving DecidableEq, Repr

abbrev Clause (Var : Type u) := List (Literal Var)
abbrev CNF (Var : Type u) := List (Clause Var)

variable {Var : Type u} {Var' : Type v}

def Literal.eval (literal : Literal Var) (valuation : Var → Bool) : Bool :=
  if literal.positive then valuation literal.var else !(valuation literal.var)

def Clause.eval (clause : Clause Var) (valuation : Var → Bool) : Bool :=
  clause.any (fun literal => literal.eval valuation)

def CNF.eval (formula : CNF Var) (valuation : Var → Bool) : Bool :=
  formula.all (fun clause => clause.eval valuation)

@[simp] theorem Clause.eval_nil (valuation : Var → Bool) :
    Clause.eval [] valuation = false := rfl

@[simp] theorem Clause.eval_cons (literal : Literal Var) (tail : Clause Var)
    (valuation : Var → Bool) :
    Clause.eval (literal :: tail) valuation = (literal.eval valuation || tail.eval valuation) := rfl

@[simp] theorem Clause.eval_append (first second : Clause Var) (valuation : Var → Bool) :
    (first ++ second).eval valuation = (first.eval valuation || second.eval valuation) :=
  List.any_append

@[simp] theorem CNF.eval_nil (valuation : Var → Bool) :
    CNF.eval [] valuation = true := rfl

@[simp] theorem CNF.eval_cons (clause : Clause Var) (tail : CNF Var) (valuation : Var → Bool) :
    CNF.eval (clause :: tail) valuation = (clause.eval valuation && tail.eval valuation) := rfl

@[simp] theorem CNF.eval_append (first second : CNF Var) (valuation : Var → Bool) :
    (first ++ second).eval valuation = (first.eval valuation && second.eval valuation) :=
  List.all_append

theorem CNF.eval_eq_true (formula : CNF Var) (valuation : Var → Bool) :
    formula.eval valuation = true ↔ ∀ clause ∈ formula, clause.eval valuation = true :=
  List.all_eq_true

def Literal.rename (literal : Literal Var) (f : Var → Var') : Literal Var' :=
  ⟨f literal.var, literal.positive⟩

def Clause.rename (clause : Clause Var) (f : Var → Var') : Clause Var' :=
  clause.map (fun literal => literal.rename f)

def CNF.rename (formula : CNF Var) (f : Var → Var') : CNF Var' :=
  formula.map (fun clause => clause.rename f)

@[simp] theorem Literal.eval_rename (literal : Literal Var) (f : Var → Var')
    (valuation : Var' → Bool) :
    (literal.rename f).eval valuation = literal.eval (valuation ∘ f) := rfl

@[simp] theorem Clause.eval_rename (clause : Clause Var) (f : Var → Var')
    (valuation : Var' → Bool) :
    (clause.rename f).eval valuation = clause.eval (valuation ∘ f) := by
  induction clause with
  | nil => rfl
  | cons literal tail ih =>
    change ((literal.rename f).eval valuation || (Clause.rename tail f).eval valuation) = _
    rw [Literal.eval_rename, ih, Clause.eval_cons]

@[simp] theorem CNF.eval_rename (formula : CNF Var) (f : Var → Var')
    (valuation : Var' → Bool) :
    (formula.rename f).eval valuation = formula.eval (valuation ∘ f) := by
  induction formula with
  | nil => rfl
  | cons clause tail ih =>
    change ((clause.rename f).eval valuation && (CNF.rename tail f).eval valuation) = _
    rw [Clause.eval_rename, ih, CNF.eval_cons]

/-- An original tail, selected on its own side, entails each tail assigned to it
    under the pivot-free background from this step. -/
structure SideCertificate (background tails representatives : CNF Var) : Prop where
  selected : ∀ rep ∈ representatives, rep ∈ tails
  covers : ∀ tail ∈ tails, ∃ rep ∈ representatives, ∀ valuation : Var → Bool,
    background.eval valuation = true → rep.eval valuation = true → tail.eval valuation = true

theorem SideCertificate.identity (background tails : CNF Var) :
    SideCertificate background tails tails where
  selected := fun _ member => member
  covers := fun tail member => ⟨tail, member, fun _ _ satisfied => satisfied⟩

theorem SideCertificate.singleton {background tails : CNF Var} {rep : Clause Var}
    (selected : rep ∈ tails)
    (covers : ∀ tail ∈ tails, ∀ valuation : Var → Bool,
      background.eval valuation = true → rep.eval valuation = true → tail.eval valuation = true) :
    SideCertificate background tails [rep] where
  selected := by
    intro clause member
    simpa [List.mem_singleton.mp member] using selected
  covers := fun tail member => ⟨rep, by simp, covers tail member⟩

theorem SideCertificate.eval_eq {background tails representatives : CNF Var}
    (cert : SideCertificate background tails representatives) (valuation : Var → Bool)
    (satisfied : background.eval valuation = true) :
    representatives.eval valuation = tails.eval valuation := by
  apply Bool.eq_iff_iff.mpr
  rw [CNF.eval_eq_true, CNF.eval_eq_true]
  constructor
  · intro repsTrue tail tailMem
    obtain ⟨rep, repMem, entailment⟩ := cert.covers tail tailMem
    exact entailment valuation satisfied (repsTrue rep repMem)
  · intro tailsTrue rep repMem
    exact tailsTrue rep (cert.selected rep repMem)

/-- Each output clause is the disjunction of one representative from each side. -/
def resolvents (positive negative : CNF Var) : CNF Var :=
  positive.flatMap (fun first => negative.map (fun second => first ++ second))

private theorem eval_append_each (first : Clause Var) (others : CNF Var)
    (valuation : Var → Bool) :
    CNF.eval (others.map (fun second => first ++ second)) valuation =
      (first.eval valuation || others.eval valuation) := by
  induction others with
  | nil => simp
  | cons clause tail ih =>
    simp only [List.map_cons, CNF.eval_cons, Clause.eval_append, ih]
    cases first.eval valuation <;> simp

theorem eval_resolvents (positive negative : CNF Var) (valuation : Var → Bool) :
    (resolvents positive negative).eval valuation =
      (positive.eval valuation || negative.eval valuation) := by
  induction positive with
  | nil => simp [resolvents]
  | cons clause tail ih =>
    change CNF.eval ((negative.map (fun second => clause ++ second)) ++ resolvents tail negative)
      valuation = _
    simp only [CNF.eval_append, eval_append_each, ih, CNF.eval_cons]
    cases negative.eval valuation <;> simp

theorem length_resolvents (positive negative : CNF Var) :
    (resolvents positive negative).length = positive.length * negative.length := by
  induction positive with
  | nil => simp [resolvents]
  | cons clause tail ih =>
    change ((negative.map (fun second => clause ++ second)) ++ resolvents tail negative).length = _
    rw [List.length_append, List.length_map, ih, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.add_comm]

/-- The pivot is `none`. Background clauses and tails use retained variables only. -/
structure PivotCNF (Var : Type u) where
  background : CNF Var
  positive : CNF Var
  negative : CNF Var
  deriving Repr

def extend (valuation : Var → Bool) (pivot : Bool) : Option Var → Bool
  | none => pivot
  | some var => valuation var

@[simp] theorem extend_some (valuation : Var → Bool) (pivot : Bool) (var : Var) :
    extend valuation pivot (some var) = valuation var := rfl

@[simp] theorem extend_none (valuation : Var → Bool) (pivot : Bool) :
    extend valuation pivot none = pivot := rfl

theorem extend_restrict (valuation : Option Var → Bool) :
    extend (fun var => valuation (some var)) (valuation none) = valuation := by
  funext var
  cases var <;> rfl

private def withPivot (polarity : Bool) (clause : Clause Var) : Clause (Option Var) :=
  ⟨none, polarity⟩ :: clause.rename some

def PivotCNF.materialize (input : PivotCNF Var) : CNF (Option Var) :=
  input.background.rename some ++
    (input.positive.map (withPivot true) ++ input.negative.map (withPivot false))

def PivotCNF.eliminate (input : PivotCNF Var) (positive negative : CNF Var) : CNF Var :=
  input.background ++ resolvents positive negative

private theorem eval_withPivot (polarity pivot : Bool) (tail : Clause Var)
    (valuation : Var → Bool) :
    (withPivot polarity tail).eval (extend valuation pivot) =
      ((if polarity then pivot else !pivot) || tail.eval valuation) := by
  simp [withPivot, Literal.eval, Function.comp_def]

private theorem eval_map_withPivot (polarity pivot : Bool) (tails : CNF Var)
    (valuation : Var → Bool) :
    CNF.eval (tails.map (withPivot polarity)) (extend valuation pivot) =
      ((if polarity then pivot else !pivot) || tails.eval valuation) := by
  induction tails with
  | nil => simp
  | cons tail rest ih =>
    simp only [List.map_cons, CNF.eval_cons, eval_withPivot, ih]
    cases polarity <;> cases pivot <;> simp

@[simp] theorem PivotCNF.eval_materialize_false (input : PivotCNF Var)
    (valuation : Var → Bool) :
    input.materialize.eval (extend valuation false) =
      (input.background.eval valuation && input.positive.eval valuation) := by
  simp [materialize, eval_map_withPivot, Function.comp_def]

@[simp] theorem PivotCNF.eval_materialize_true (input : PivotCNF Var)
    (valuation : Var → Bool) :
    input.materialize.eval (extend valuation true) =
      (input.background.eval valuation && input.negative.eval valuation) := by
  simp [materialize, eval_map_withPivot, Function.comp_def]

/-- Exact forgetting for every retained assignment, with independently certified
    representative families on the two pivot sides. -/
theorem PivotCNF.eval_eliminate (input : PivotCNF Var) {positive negative : CNF Var}
    (positiveCert : SideCertificate input.background input.positive positive)
    (negativeCert : SideCertificate input.background input.negative negative)
    (valuation : Var → Bool) :
    (input.eliminate positive negative).eval valuation =
      (input.materialize.eval (extend valuation false) ||
        input.materialize.eval (extend valuation true)) := by
  simp only [eliminate, CNF.eval_append, eval_resolvents, input.eval_materialize_false,
    input.eval_materialize_true]
  by_cases satisfied : input.background.eval valuation = true
  · rw [positiveCert.eval_eq valuation satisfied, negativeCert.eval_eq valuation satisfied]
    simp [satisfied]
  · simp [Bool.eq_false_iff.mpr satisfied]

theorem PivotCNF.projection_iff (input : PivotCNF Var) {positive negative : CNF Var}
    (positiveCert : SideCertificate input.background input.positive positive)
    (negativeCert : SideCertificate input.background input.negative negative)
    (valuation : Var → Bool) :
    (input.eliminate positive negative).eval valuation = true ↔
      ∃ pivot, input.materialize.eval (extend valuation pivot) = true := by
  rw [input.eval_eliminate positiveCert negativeCert, Bool.or_eq_true]
  constructor
  · rintro (satisfied | satisfied)
    · exact ⟨false, satisfied⟩
    · exact ⟨true, satisfied⟩
  · rintro ⟨pivot, satisfied⟩
    cases pivot
    · exact Or.inl satisfied
    · exact Or.inr satisfied

@[simp] theorem PivotCNF.length_materialize (input : PivotCNF Var) :
    input.materialize.length = input.background.length + (input.positive.length + input.negative.length) := by
  simp [materialize, CNF.rename]

@[simp] theorem PivotCNF.length_eliminate (input : PivotCNF Var) (positive negative : CNF Var) :
    (input.eliminate positive negative).length = input.background.length + positive.length * negative.length := by
  simp [eliminate, length_resolvents]

theorem PivotCNF.length_eliminate_le (input : PivotCNF Var) (positive negative : CNF Var)
    (budget : positive.length * negative.length ≤ input.positive.length + input.negative.length) :
    (input.eliminate positive negative).length ≤ input.materialize.length := by
  simpa using Nat.add_le_add_left budget input.background.length

theorem PivotCNF.length_eliminate_single_positive (input : PivotCNF Var) (rep : Clause Var) :
    (input.eliminate [rep] input.negative).length ≤ input.materialize.length := by
  apply input.length_eliminate_le
  simp [Nat.le_add_left]

theorem PivotCNF.length_eliminate_single_negative (input : PivotCNF Var) (rep : Clause Var) :
    (input.eliminate input.positive [rep]).length ≤ input.materialize.length := by
  apply input.length_eliminate_le
  simp [Nat.le_add_right]

end SatForgetting
