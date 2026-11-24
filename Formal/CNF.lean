import Init.Data.List.Lemmas

namespace SatForgetting

universe u v w

/-! Signed literals use the tuple representation accepted by the reductions.
The named constructor and projections remain available to the projection proofs. -/

abbrev Literal (Var : Type u) := Var × Bool
abbrev Clause (Var : Type u) := List (Literal Var)
abbrev CNF (Var : Type u) := List (Clause Var)

variable {Var : Type u} {Var' : Type v}

abbrev Literal.var (literal : Literal Var) : Var := literal.1
abbrev Literal.positive (literal : Literal Var) : Bool := literal.2

@[simp] theorem Literal.var_pair (var : Var) (positive : Bool) : Literal.var (var, positive) = var := rfl
@[simp] theorem Literal.positive_pair (var : Var) (positive : Bool) : Literal.positive (var, positive) = positive := rfl

@[match_pattern] abbrev Literal.mk (var : Var) (positive : Bool) : Literal Var := (var, positive)

@[elab_as_elim] abbrev Literal.rec {motive : Literal Var → Sort w}
    (mk : ∀ var positive, motive (Literal.mk var positive)) (literal : Literal Var) : motive literal :=
  match literal with
  | (var, positive) => mk var positive

@[elab_as_elim] abbrev Literal.recOn {motive : Literal Var → Sort w} (literal : Literal Var)
    (mk : ∀ var positive, motive (Literal.mk var positive)) : motive literal :=
  Literal.rec mk literal

@[elab_as_elim] abbrev Literal.casesOn {motive : Literal Var → Sort w} (literal : Literal Var)
    (mk : ∀ var positive, motive (Literal.mk var positive)) : motive literal :=
  Literal.rec mk literal

theorem Literal.mk.inj {var other : Var} {positive otherPositive : Bool} :
    Literal.mk var positive = Literal.mk other otherPositive → var = other ∧ positive = otherPositive :=
  Prod.mk.inj

theorem Literal.mk.injEq (var : Var) (positive : Bool) (other : Var) (otherPositive : Bool) :
    (Literal.mk var positive = Literal.mk other otherPositive) = (var = other ∧ positive = otherPositive) :=
  Prod.mk.injEq _ _ _ _

def Literal.eval (literal : Literal Var) (valuation : Var → Bool) : Bool :=
  if literal.positive then valuation literal.var else !(valuation literal.var)

def Clause.eval (clause : Clause Var) (valuation : Var → Bool) : Bool :=
  clause.any (fun literal => literal.eval valuation)

def CNF.eval (formula : CNF Var) (valuation : Var → Bool) : Bool :=
  formula.all (fun clause => clause.eval valuation)

@[simp] def Literal.Satisfies (literal : Literal Var) (valuation : Var → Bool) : Prop :=
  valuation literal.var = literal.positive

@[simp] def Clause.Satisfies (clause : Clause Var) (valuation : Var → Bool) : Prop :=
  ∃ literal ∈ clause, literal.Satisfies valuation

@[simp] def CNF.Satisfies (formula : CNF Var) (valuation : Var → Bool) : Prop :=
  ∀ clause ∈ formula, clause.Satisfies valuation

theorem Literal.eval_true_iff (literal : Literal Var) (valuation : Var → Bool) :
    literal.eval valuation = true ↔ literal.Satisfies valuation := by
  obtain ⟨var, positive⟩ := literal
  cases positive <;> cases value : valuation var <;> simp [eval, Satisfies, value]

theorem Clause.eval_true_iff (clause : Clause Var) (valuation : Var → Bool) :
    clause.eval valuation = true ↔ clause.Satisfies valuation := by
  simp only [eval, Satisfies, List.any_eq_true, Literal.eval_true_iff]

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

theorem CNF.eval_true_iff (formula : CNF Var) (valuation : Var → Bool) :
    formula.eval valuation = true ↔ formula.Satisfies valuation := by
  simp only [eval_eq_true, Satisfies, Clause.eval_true_iff]

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

end SatForgetting
