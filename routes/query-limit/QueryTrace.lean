import Init.Data.List.Perm

namespace SatForgetting.QueryLimit

universe u

inductive QueryTree (Assignment : Type u) where
  | result (answer : Bool)
  | ask (assignment : Assignment) (onTrue onFalse : QueryTree Assignment)

variable {Assignment : Type u}

def run (oracle : Assignment → Bool) : QueryTree Assignment → Bool
  | .result answer => answer
  | .ask assignment onTrue onFalse =>
      if oracle assignment then run oracle onTrue else run oracle onFalse

def trace (oracle : Assignment → Bool) : QueryTree Assignment → List Assignment
  | .result _ => []
  | .ask assignment onTrue onFalse =>
      assignment :: if oracle assignment then trace oracle onTrue else trace oracle onFalse

theorem run_eq_of_agrees_on_reference_trace (tree : QueryTree Assignment)
    (reference alternative : Assignment → Bool)
    (agrees : ∀ assignment ∈ trace reference tree,
      alternative assignment = reference assignment) :
    run reference tree = run alternative tree := by
  induction tree with
  | result answer => rfl
  | ask assignment onTrue onFalse trueIH falseIH =>
    have atQuery : alternative assignment = reference assignment :=
      agrees assignment (by simp [trace])
    cases answer : reference assignment with
    | false =>
      have altAnswer : alternative assignment = false := atQuery.trans answer
      have sub : ∀ row ∈ trace reference onFalse, alternative row = reference row := by
        intro row mem
        exact agrees row (by simp [trace, answer, mem])
      simpa [run, answer, altAnswer] using falseIH sub
    | true =>
      have altAnswer : alternative assignment = true := atQuery.trans answer
      have sub : ∀ row ∈ trace reference onTrue, alternative row = reference row := by
        intro row mem
        exact agrees row (by simp [trace, answer, mem])
      simpa [run, answer, altAnswer] using trueIH sub

def puncture [DecidableEq Assignment] (reference : Assignment → Bool)
    (row assignment : Assignment) : Bool :=
  if assignment = row then false else reference assignment

theorem mem_trace_of_distinguishes [DecidableEq Assignment] (tree : QueryTree Assignment)
    (reference : Assignment → Bool) (row : Assignment)
    (different : run reference tree ≠ run (puncture reference row) tree) :
    row ∈ trace reference tree := by
  by_cases queried : row ∈ trace reference tree
  · exact queried
  · exfalso
    apply different
    apply run_eq_of_agrees_on_reference_trace
    intro assignment visited
    have other : assignment ≠ row := by
      intro same
      subst assignment
      exact queried visited
    simp [puncture, other]

theorem reference_queries_ge [DecidableEq Assignment] (tree : QueryTree Assignment)
    (reference : Assignment → Bool) (rows : List Assignment) (distinct : rows.Nodup)
    (separates : ∀ row ∈ rows, run reference tree ≠ run (puncture reference row) tree) :
    rows.length ≤ (trace reference tree).length := by
  apply distinct.length_le_of_subset
  intro row listed
  exact mem_trace_of_distinguishes tree reference row (separates row listed)

#print axioms run_eq_of_agrees_on_reference_trace
#print axioms reference_queries_ge

end SatForgetting.QueryLimit
