import Formal.CNF

/-! The monotone formula built from a CNF agrees with its binary envelope
exactly when the input CNF is unsatisfiable. The three fresh guards keep
all width-two tests independent of the encoded CNF. -/

namespace BinaryExactness

abbrev Literal (n : Nat) := SatForgetting.Literal (Fin n)
abbrev Formula (n : Nat) := SatForgetting.CNF (Fin n)

abbrev Satisfies {n} (φ : Formula n) (σ : Fin n → Bool) : Prop :=
  SatForgetting.CNF.Satisfies φ σ

inductive Wire (n : Nat) where
  | rail (i : Fin n) (sign : Bool)
  | guard (i : Fin 3)
  deriving DecidableEq

abbrev Input (n : Nat) := Wire n → Bool

def matching {n} (x : Input n) : Prop :=
  ∀ i, x (.rail i true) = true ∨ x (.rail i false) = true

def encoded {n} (φ : Formula n) (x : Input n) : Prop :=
  matching x ∧ ((∃ i, x (.guard i) = true) ∨
    ∃ c ∈ φ, ∀ l ∈ c, x (.rail l.1 l.2) = true)

/-- Conjoin every entailed pair. A repeated port represents a unit clause.
The encoded function is satisfiable at all-true, so it never entails an empty clause. -/
def envelope {n} (f : Input n → Prop) (x : Input n) : Prop :=
  ∀ a b : Wire n, (∀ y, f y → y a = true ∨ y b = true) →
    x a = true ∨ x b = true

private def slot {n} : Wire n → Fin 3
  | .guard i => i
  | .rail _ _ => 0

private theorem freshGuard {n} (a b : Wire n) :
    ∃ k : Fin 3, a ≠ .guard k ∧ b ≠ .guard k := by
  have spare : ∀ i j : Fin 3, ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, ha, hb⟩ := spare (slot a) (slot b)
  exact ⟨k, fun e => ha (by rw [e]; rfl), fun e => hb (by rw [e]; rfl)⟩

theorem envelope_eq_matching {n} (φ : Formula n) (x : Input n) :
    envelope (encoded φ) x ↔ matching x := by
  constructor
  · intro h i
    exact h (.rail i true) (.rail i false) (fun _ hy => hy.1 i)
  · intro hx a b entails
    obtain ⟨k, hka, hkb⟩ := freshGuard a b
    let y : Input n := fun w => if w = .guard k then true else x w
    have hy : encoded φ y := by
      refine ⟨?_, Or.inl ⟨k, by simp [y]⟩⟩
      intro i
      simpa [y] using hx i
    simpa [y, hka, hkb] using entails y hy

theorem counterexample_iff_sat {n} (φ : Formula n) :
    (∃ x, matching x ∧ ¬encoded φ x) ↔ ∃ σ, Satisfies φ σ := by
  classical
  constructor
  · rintro ⟨x, hm, bad⟩
    let σ (i : Fin n) := !(x (.rail i true))
    refine ⟨σ, ?_⟩
    intro c hc
    have missing : ∃ l ∈ c, x (.rail l.1 l.2) = false := by
      apply Classical.byContradiction
      intro h
      apply bad
      refine ⟨hm, Or.inr ⟨c, hc, ?_⟩⟩
      intro l hl
      cases he : x (.rail l.1 l.2) with
      | false => exact (h ⟨l, hl, he⟩).elim
      | true => rfl
    obtain ⟨⟨i, sign⟩, hi, zero⟩ := missing
    refine ⟨(i, sign), hi, ?_⟩
    change σ i = sign
    cases sign with
    | true => simpa [σ] using zero
    | false =>
      have pos : x (.rail i true) = true := (hm i).resolve_right (by simpa using zero)
      simp [σ, pos]
  · rintro ⟨σ, hs⟩
    let x : Input n
      | .rail i sign => !(σ i == sign)
      | .guard _ => false
    have hm : matching x := by
      intro i
      cases h : σ i <;> simp [x, h]
    refine ⟨x, hm, ?_⟩
    rintro ⟨_, ⟨i, h⟩ | ⟨c, hc, all⟩⟩
    · cases h
    · obtain ⟨l, hl, e⟩ := hs c hc
      change σ l.1 = l.2 at e
      simpa [x, e] using all l hl

theorem exact_iff_unsat {n} (φ : Formula n) :
    (∀ x, envelope (encoded φ) x ↔ encoded φ x) ↔ ¬∃ σ, Satisfies φ σ := by
  classical
  constructor
  · intro exactness sat
    obtain ⟨x, hm, bad⟩ := (counterexample_iff_sat φ).mpr sat
    exact bad ((exactness x).mp ((envelope_eq_matching φ x).mpr hm))
  · intro unsat x
    rw [envelope_eq_matching]
    refine ⟨?_, fun h => h.1⟩
    intro hm
    exact Classical.byContradiction (fun h => unsat ((counterexample_iff_sat φ).mp ⟨x,hm,h⟩))

/-- A signed binary clause, including units by repetition. An empty clause
cannot occur in a representation of encoded, since the all-true input satisfies it. -/
abbrev PairClause (n : Nat) := SatForgetting.Literal (Wire n) × SatForgetting.Literal (Wire n)

def signedModel {n} (D : List (PairClause n)) (x : Input n) : Prop :=
  ∀ p ∈ D, x p.1.1 = p.1.2 ∨ x p.2.1 = p.2.2

private def matchPairs (n : Nat) : List (PairClause n) :=
  (List.finRange n).map (fun i => ((.rail i true, true), (.rail i false, true)))

private theorem matchPairs_model {n} (x : Input n) :
    signedModel (matchPairs n) x ↔ matching x := by
  simp [matchPairs, signedModel, matching]

theorem signed_representable_iff_unsat {n} (φ : Formula n) :
    (∃ D, ∀ x, signedModel D x ↔ encoded φ x) ↔ ¬∃ σ, Satisfies φ σ := by
  constructor
  · rintro ⟨D, hd⟩ sat
    obtain ⟨x, hm, bad⟩ := (counterexample_iff_sat φ).mpr sat
    apply bad
    apply (hd x).mp
    intro p hp
    obtain ⟨k, ha, hb⟩ := freshGuard p.1.1 p.2.1
    let y : Input n := fun w => if w = .guard k then true else x w
    have good : encoded φ y := by
      refine ⟨?_, Or.inl ⟨k, by simp [y]⟩⟩
      intro i
      simpa [y] using hm i
    simpa [y, ha, hb] using ((hd y).mpr good) p hp
  · intro unsat
    refine ⟨matchPairs n, ?_⟩
    intro x
    exact (matchPairs_model x).trans ((envelope_eq_matching φ x).symm.trans
      ((exact_iff_unsat φ).mpr unsat x))

/-- The guards make the body true on the all-true input and every input with
one zero. With the matching as a separate background, asking whether the body
can be dropped already encodes UNSAT. -/
def body {n} (φ : Formula n) (x : Input n) : Prop :=
  (∃ i, x (.guard i) = true) ∨ ∃ c ∈ φ, ∀ l ∈ c, x (.rail l.1 l.2) = true

theorem relative_redundancy_iff_unsat {n} (φ : Formula n) :
    (∀ x, matching x → body φ x) ↔ ¬∃ σ, Satisfies φ σ := by
  constructor
  · intro h sat
    obtain ⟨x, hm, bad⟩ := (counterexample_iff_sat φ).mpr sat
    exact bad ⟨hm, h x hm⟩
  · intro unsat x hm
    exact (((exact_iff_unsat φ).mpr unsat x).mp ((envelope_eq_matching φ x).mpr hm)).2

end BinaryExactness
