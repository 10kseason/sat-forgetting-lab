import Formal.CNF
import Std.Tactic

namespace SatForgetting.GuardedPath

variable {V : Type} {m : Nat}

/-- Indices distinguish repeated occurrences of the same literal in one clause. -/
abbrev Occ (φ : Fin m → Clause V) := (j : Fin m) × Fin (φ j).length

def litAt {φ : Fin m → Clause V} (i : Occ φ) : Literal V := (φ i.1)[i.2]

/-- The only path coordinates observed are the vertices from 0 through m. -/
def Endpoints (m : Nat) (path : Nat → Bool) : Prop :=
  path 0 = false ∧ path m = true

def Active {φ : Fin m → Clause V} (i : Occ φ) (σ : V → Bool) (path : Nat → Bool) : Prop :=
  (litAt i).Satisfies σ ∧ path i.1.val = path (i.1.val + 1)

def Joint {φ : Fin m → Clause V} (s : Occ φ → Prop) : Prop :=
  ∃ σ path, Endpoints m path ∧ ∀ i, s i → Active i σ path

def Pairwise {φ : Fin m → Clause V} (s : Occ φ → Prop) : Prop :=
  ∀ i, s i → ∀ j, s j → ∃ σ path, Endpoints m path ∧ Active i σ path ∧ Active j σ path

private def cut (j i : Nat) := decide (j < i)

private theorem cut_endpoints (j : Fin m) : Endpoints m (cut j.val) := by
  simp [Endpoints, cut, j.isLt]

private theorem cut_edge {j i : Nat} (different : i ≠ j) : cut j i = cut j (i+1) := by
  by_cases h : j < i
  · simp [cut, h, show j < i+1 by omega]
  · simp [cut, h, show ¬ j < i+1 by omega]

private theorem path_needs_gap (path : Nat → Bool) (ends : Endpoints m path) :
    ∃ j : Fin m, path j.val ≠ path (j.val+1) := by
  classical
  apply Classical.byContradiction
  intro noGap
  have allEqual (j : Fin m) : path j.val = path (j.val+1) :=
    Classical.byContradiction (fun h => noGap ⟨j, h⟩)
  have constant : ∀ i, i ≤ m → path i = false := by
    intro i
    induction i with
    | zero => exact fun _ => ends.1
    | succ i ih =>
      intro bound
      exact (allEqual ⟨i, by omega⟩).symm.trans (ih (by omega))
  have impossible := (constant m (Nat.le_refl m)).symm.trans ends.2
  contradiction

private theorem spare (hm : 3 ≤ m) (a b : Fin m) :
    ∃ k : Fin m, a.val ≠ k.val ∧ b.val ≠ k.val := by
  by_cases zero : a.val ≠ 0 ∧ b.val ≠ 0
  · exact ⟨⟨0, by omega⟩, zero⟩
  by_cases one : a.val ≠ 1 ∧ b.val ≠ 1
  · exact ⟨⟨1, by omega⟩, one⟩
  exact ⟨⟨2, by omega⟩, by change a.val ≠ 2 ∧ b.val ≠ 2; omega⟩

private theorem compatible_signs {φ : Fin m → Clause V} {s : Occ φ → Prop}
    (hp : Pairwise s) : ∃ σ, ∀ i, s i → (litAt i).Satisfies σ := by
  classical
  let σ := fun v => decide (∃ i, s i ∧ (litAt i).1 = v ∧ (litAt i).2 = true)
  refine ⟨σ, ?_⟩
  intro i hi
  change σ (litAt i).1 = (litAt i).2
  cases sign : (litAt i).2 with
  | true => exact decide_eq_true ⟨i, hi, rfl, sign⟩
  | false =>
    apply decide_eq_false
    rintro ⟨j, hj, same, pos⟩
    obtain ⟨τ, _, _, ai, aj⟩ := hp i hi j hj
    have eqi : τ (litAt i).1 = (litAt i).2 := ai.1
    have eqj : τ (litAt j).1 = (litAt j).2 := aj.1
    rw [same, eqi, sign, pos] at eqj
    contradiction

/-- A clause family is satisfiable iff its two-row occurrence bundles have
some pairwise-feasible but jointly infeasible support. Fixed endpoints are
constants in the encoded equations. -/
theorem gap_iff_sat (φ : Fin m → Clause V) (hm : 3 ≤ m) :
    (∃ s : Occ φ → Prop, Pairwise s ∧ ¬ Joint s) ↔
      ∃ σ, ∀ j, (φ j).Satisfies σ := by
  classical
  constructor
  · rintro ⟨s, hp, bad⟩
    obtain ⟨σ, signs⟩ := compatible_signs hp
    refine ⟨σ, ?_⟩
    intro j
    have covered : ∃ i : Occ φ, s i ∧ i.1 = j := by
      apply Classical.byContradiction
      intro missing
      apply bad
      refine ⟨σ, cut j.val, cut_endpoints j, ?_⟩
      intro i hi
      exact ⟨signs i hi, cut_edge (fun e => missing ⟨i, hi, Fin.ext e⟩)⟩
    obtain ⟨⟨k, p⟩, hk, eq⟩ := covered
    change k = j at eq
    subst k
    exact ⟨_, List.getElem_mem p.isLt, signs ⟨j, p⟩ hk⟩
  · rintro ⟨σ, sat⟩
    let s := fun i : Occ φ => (litAt i).Satisfies σ
    refine ⟨s, ?_, ?_⟩
    · intro i hi j hj
      obtain ⟨k, ha, hb⟩ := spare hm i.1 j.1
      exact ⟨σ, cut k.val, cut_endpoints k, ⟨hi, cut_edge ha⟩, hj, cut_edge hb⟩
    · rintro ⟨_, path, ends, active⟩
      obtain ⟨j, gap⟩ := path_needs_gap path ends
      obtain ⟨l, hl, ok⟩ := sat j
      obtain ⟨p, hlt, eq⟩ := List.mem_iff_getElem.mp hl
      let i : Occ φ := ⟨j, ⟨p, hlt⟩⟩
      have selected : s i := by simpa [s, i, litAt, eq] using ok
      exact gap (active i selected).2

end SatForgetting.GuardedPath
