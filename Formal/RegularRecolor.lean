import Std

namespace SatForgetting.RegularRecolor

abbrev Edge (V : Type) := V × V × V
variable {V : Type}

def ends (e : Edge V) := [e.1,e.2.1,e.2.2]
def weight (color : V → Bool) (xs : List V) := (xs.filter color).length
def proper (color : V → Bool) (e : Edge V) :=
  color e.1 ≠ color e.2.1 ∨ color e.2.1 ≠ color e.2.2
def simple (e : Edge V) := e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2
def minority (color : V → Bool) (e : Edge V) :=
  if color e.1 == color e.2.1 then e.2.2 else
  if color e.1 == color e.2.2 then e.2.1 else e.1

private theorem local_count (color : V → Bool) (e : Edge V) (h : proper color e) :
    weight color (ends e) + (if color (minority color e) then 1 else 0) = 2 := by
  obtain ⟨a,b,c⟩ := e
  cases ha : color a <;> cases hb : color b <;> cases hc : color c <;>
    simp_all [proper,weight,ends,minority]

private theorem global_count (color : V → Bool) (edges : List (Edge V))
    (h : ∀ e ∈ edges, proper color e) :
    weight color (edges.flatMap ends) + weight color (edges.map (minority color)) =
      2 * edges.length := by
  induction edges with
  | nil => simp [weight]
  | cons e es ih =>
    have head := local_count color e (h e (by simp))
    have tail := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons,List.map_cons,List.length_cons]
    simp only [weight,List.filter_append,List.length_append] at *
    cases q : color (minority color e) <;> simp [q] at * <;> omega

private theorem incidence_length (es : List (Edge V)) :
    (es.flatMap ends).length = 3 * es.length := by
  induction es with
  | nil => rfl
  | cons x xs ih => simp [ends,ih]; omega

theorem free_one (vertices : List V) (unique : vertices.Nodup) (es : List (Edge V))
    (regular : (es.flatMap ends).Perm (vertices ++ vertices ++ vertices ++ vertices))
    (color : V → Bool) (ok : ∀ e ∈ es, proper color e)
    (high : 8*vertices.length < 15*weight color vertices) :
    ∃ v ∈ vertices, color v = true ∧ v ∉ es.map (minority color) := by
  classical
  apply Classical.byContradiction
  intro none
  have included : vertices.filter color ⊆ (es.map (minority color)).filter color := by
    intro v hv
    obtain ⟨member,on⟩ := List.mem_filter.mp hv
    apply List.mem_filter.mpr
    exact ⟨Classical.byContradiction (fun miss => none ⟨v,member,on,miss⟩),on⟩
  have nodup : (vertices.filter color).Nodup := unique.filter color
  have covered := nodup.length_le_of_subset included
  have mass := (regular.filter color).length_eq
  have sizes := regular.length_eq
  rw [incidence_length] at sizes
  have counts := global_count color es ok
  simp only [weight,List.filter_append,List.length_append] at *
  omega

def flip [DecidableEq V] (color : V → Bool) (v u : V) :=
  if u = v then !(color u) else color u

theorem flip_preserves [DecidableEq V] (color : V → Bool) (v : V) (e : Edge V)
    (no_repeat : simple e) (ok : proper color e) (free : v ≠ minority color e) :
    proper (flip color v) e := by
  obtain ⟨a,b,c⟩ := e
  obtain ⟨ab,ac,bc⟩ := no_repeat
  by_cases av : a = v <;> by_cases bv : b = v <;> by_cases cv : c = v <;>
    cases ha : color a <;> cases hb : color b <;> cases hc : color c <;>
    simp_all [proper,minority,flip]

private def invert (c : V → Bool) (v : V) := !(c v)

private theorem inv_ok (c : V → Bool) (e : Edge V) (h : proper c e) : proper (invert c) e := by
  obtain ⟨a,b,d⟩ := e
  cases ha : c a <;> cases hb : c b <;> cases hd : c d <;> simp_all [proper,invert]

private theorem inv_weight (c : V → Bool) (vs : List V) :
    weight (invert c) vs + weight c vs = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases h : c v <;> simp [weight,invert,h] at * <;> omega

private theorem untouched [DecidableEq V] (c : V → Bool) (v : V) (vs : List V) (away : v ∉ vs) :
    weight (flip c v) vs = weight c vs := by
  induction vs with
  | nil => rfl
  | cons u us ih =>
    have ne : u ≠ v := fun eq => away (by simp [eq])
    have rest := ih (fun h => away (by simp [h]))
    cases val : c u <;> simp [weight,flip,ne,val] at * <;> omega

private theorem drop_one [DecidableEq V] (vs : List V) (unique : vs.Nodup) (c : V → Bool)
    (v : V) (member : v ∈ vs) (on : c v = true) :
    weight (flip c v) vs + 1 = weight c vs := by
  induction vs with
  | nil => simp at member
  | cons u us ih =>
    obtain ⟨absent,tailUnique⟩ := List.nodup_cons.mp unique
    by_cases eq : u=v
    · subst u
      have same := untouched c v us absent
      simpa [weight,flip,on] using same
    · have tail := ih tailUnique ((List.mem_cons.mp member).resolve_left (Ne.symm eq))
      cases val : c u <;> simp [weight,flip,eq,val] at * <;> omega

/-- A sequence of individual flips, with every visited successor proper. -/
inductive Path [DecidableEq V] (vs : List V) (es : List (Edge V)) :
    (V → Bool) → (V → Bool) → Prop
  | stay (c) : Path vs es c c
  | next {c d} (v) (mem : v ∈ vs) (ok : ∀ e ∈ es, proper (flip c v) e)
      (tail : Path vs es (flip c v) d) : Path vs es c d

private theorem invert_path [DecidableEq V] {vs : List V} {es : List (Edge V)}
    {c d : V → Bool} (p : Path vs es c d) : Path vs es (invert c) (invert d) := by
  induction p with
  | stay => exact .stay _
  | @next c d v mem ok _ ih =>
    have commute : flip (invert c) v = invert (flip c v) := by
      funext u
      by_cases eq : u=v <;> simp [flip,invert,eq]
    exact .next v mem (fun e h => commute ▸ inv_ok _ e (ok e h)) (commute ▸ ih)

private theorem descend [DecidableEq V] (vs : List V) (unique : vs.Nodup) (es : List (Edge V))
    (reg : (es.flatMap ends).Perm (vs ++ vs ++ vs ++ vs)) (distinct : ∀ e ∈ es, simple e)
    (target steps : Nat) (threshold : 8*vs.length < 15*(target+1)) :
    ∀ c : V → Bool, (∀ e ∈ es, proper c e) → weight c vs = target+steps →
      ∃ d, Path vs es c d ∧ weight d vs = target := by
  induction steps with
  | zero =>
    intro c _ w
    exact ⟨c,.stay c,by omega⟩
  | succ k ih =>
    intro c ok w
    obtain ⟨v,mem,on,free⟩ := free_one vs unique es reg c ok (by omega)
    have after (e) (he : e ∈ es) : proper (flip c v) e :=
      flip_preserves c v e (distinct e he) (ok e he)
        (fun eq => free (eq ▸ List.mem_map_of_mem he))
    have drops := drop_one vs unique c v mem on
    obtain ⟨d,tail,last⟩ := ih (flip c v) after (by omega)
    exact ⟨d,.next v mem after tail,last⟩

/-- Every proper coloring reaches the sharp band by proper one-vertex flips. -/
theorem reaches_band [DecidableEq V] (vs : List V) (unique : vs.Nodup) (large : 15 ≤ vs.length)
    (es : List (Edge V)) (reg : (es.flatMap ends).Perm (vs ++ vs ++ vs ++ vs))
    (distinct : ∀ e ∈ es, simple e) (c : V → Bool) (ok : ∀ e ∈ es, proper c e) :
    ∃ d, Path vs es c d ∧ 7*vs.length ≤ 15*weight d vs ∧ 15*weight d vs ≤ 8*vs.length := by
  let top := 8*vs.length/15
  have bound : 8*vs.length < 15*(top+1) := by dsimp [top]; omega
  by_cases high : top < weight c vs
  · obtain ⟨d,p,w⟩ := descend vs unique es reg distinct top (weight c vs-top) bound c ok (by omega)
    exact ⟨d,p,by dsimp [top] at w; omega⟩
  by_cases low : 15*weight c vs < 7*vs.length
  · have both := inv_weight c vs
    have h : top ≤ weight (invert c) vs := by dsimp [top]; omega
    obtain ⟨d,p,w⟩ := descend vs unique es reg distinct top (weight (invert c) vs-top) bound
      (invert c) (fun e he => inv_ok c e (ok e he)) (by omega)
    have invinv : invert (invert c) = c := by funext v; simp [invert]
    have terminal := inv_weight d vs
    refine ⟨invert d, invinv ▸ invert_path p, ?_⟩
    dsimp [top] at w
    omega
  · exact ⟨c,.stay c,by dsimp [top] at high; omega⟩

end SatForgetting.RegularRecolor
