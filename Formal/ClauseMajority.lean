import Formal.CNF

namespace SatForgetting.ClauseMajority

def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def median {V : Type u} (x y z : V → Bool) (v : V) : Bool := majority (x v) (y v) (z v)

theorem literal_median {V : Type u} (l : Literal V) (x y z : V → Bool) :
    l.eval (median x y z) = majority (l.eval x) (l.eval y) (l.eval z) := by
  rcases l with ⟨v, sign⟩
  cases sign <;> cases a : x v <;> cases b : y v <;> cases c : z v <;>
    simp [Literal.eval, Literal.positive, Literal.var, median, majority, a, b, c]

private theorem pair_closed : ∀ a b c d e f : Bool,
    (a || d) = true → (b || e) = true → (c || f) = true →
    (majority a b c || majority d e f) = true := by decide

theorem clause_closed {V : Type u} (c : Clause V) (width : c.length ≤ 2)
    (x y z : V → Bool) (hx : c.eval x = true) (hy : c.eval y = true)
    (hz : c.eval z = true) : c.eval (median x y z) = true := by
  cases c with
  | nil => simp at hx
  | cons l tail =>
    cases tail with
    | nil => simp [literal_median, majority, show l.eval x = true by simpa using hx,
                    show l.eval y = true by simpa using hy]
    | cons r rest =>
      cases rest with
      | nil =>
        simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false] at *
        simp only [literal_median]
        exact pair_closed _ _ _ _ _ _ hx hy hz
      | cons s rest =>
        simp at width

theorem cnf_closed {V : Type u} (B : CNF V) (width : ∀ c ∈ B, c.length ≤ 2)
    (x y z : V → Bool) (hx : B.eval x = true) (hy : B.eval y = true)
    (hz : B.eval z = true) : B.eval (median x y z) = true := by
  apply (CNF.eval_eq_true _ _).mpr
  intro c member
  exact clause_closed c (width c member) x y z ((CNF.eval_eq_true _ _).mp hx c member)
    ((CNF.eval_eq_true _ _).mp hy c member) ((CNF.eval_eq_true _ _).mp hz c member)

/-- A failed majority test obstructs every 2-CNF encoding even with hidden bits. -/
theorem obstruction {V : Type u} {H : Type v} (R : (V → Bool) → Prop)
    (x y z : V → Bool) (hx : R x) (hy : R y) (hz : R z) (bad : ¬R (median x y z))
    (B : CNF (V ⊕ H)) (width : ∀ c ∈ B, c.length ≤ 2) :
    ¬ (∀ σ, R σ ↔ ∃ τ : H → Bool, B.eval (Sum.elim σ τ) = true) := by
  intro represents
  obtain ⟨a, ha⟩ := (represents x).mp hx
  obtain ⟨b, hb⟩ := (represents y).mp hy
  obtain ⟨c, hc⟩ := (represents z).mp hz
  apply bad
  apply (represents _).mpr
  refine ⟨median a b c, ?_⟩
  have h := cnf_closed B width _ _ _ ha hb hc
  have pointwise : Sum.elim (median x y z) (median a b c) =
      median (Sum.elim x a) (Sum.elim y b) (Sum.elim z c) := by
    funext v
    cases v <;> rfl
  rwa [pointwise]

end SatForgetting.ClauseMajority
