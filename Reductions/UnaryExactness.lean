/-! A monotone function's unary envelope has a unique least model whenever the
function is satisfiable. One evaluation there decides whether the envelope is exact. -/

namespace UnaryExactness

abbrev State (ι : Type) := ι → Bool
def below {ι} (x y : State ι) := ∀ i, x i = true → y i = true
def monotone {ι} (g : State ι → Bool) := ∀ x y, below x y → g x = true → g y = true

def top {ι} : State ι := fun _ => true
def exceptAt {ι} [DecidableEq ι] (i : ι) : State ι := fun j => decide (j ≠ i)
def units {ι} [DecidableEq ι] (g : State ι → Bool) : State ι := fun i => !(g (exceptAt i))
def unary {ι} [DecidableEq ι] (g : State ι → Bool) (x : State ι) :=
  g top = true ∧ below (units g) x

theorem forced_iff {ι} [DecidableEq ι] (g : State ι → Bool) (hm : monotone g) (i : ι) :
    units g i = true ↔ ∀ x, g x = true → x i = true := by
  constructor
  · intro hu x hx
    cases hv : x i with
    | true => rfl
    | false =>
      have hle : below x (exceptAt i) := by
        intro j hj
        by_cases e : j = i
        · simp [e, hv] at hj
        · simp [exceptAt, e]
      have ht := hm _ _ hle hx
      simp [units, ht] at hu
  · intro h
    cases he : g (exceptAt i) with
    | false => simp [units, he]
    | true =>
      have bad := h _ he
      simp [exceptAt] at bad

theorem exact_iff {ι} [DecidableEq ι] (g : State ι → Bool) (hm : monotone g) :
    (∀ x, unary g x ↔ g x = true) ↔ g top = false ∨ g (units g) = true := by
  have upper (x) (hx : g x = true) : unary g x :=
    ⟨hm x top (fun _ _ => rfl) hx, fun i hi => (forced_iff g hm i).mp hi x hx⟩
  constructor
  · intro he
    cases ht : g top with
    | false => exact Or.inl rfl
    | true => exact Or.inr ((he _).mp ⟨ht, fun _ h => h⟩)
  · intro he x
    refine ⟨?_, upper x⟩
    intro hu
    rcases he with hf | hleast
    · cases hu.1.symm.trans hf
    · exact hm _ _ hu.2 hleast

end UnaryExactness
