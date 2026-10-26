import FamilyDescent

namespace CollatzResearch

theorem word_trace_append {first later : List Nat} {n m z : Nat}
    (hfirst : WordTrace first n m) (hlater : WordTrace later m z) :
    WordTrace (first ++ later) n z := by
  induction first generalizing n with
  | nil =>
      have eq : m = n := hfirst
      subst m
      exact hlater
  | cons a rest ih =>
      rcases hfirst with ⟨middle, step, tail⟩
      exact ⟨middle, step, ih tail⟩

/-- This proves an implication. Its universal descent hypothesis remains open. -/
theorem universal_descent_implies_convergence
    (hdescent : ∀ n : Nat, 0 < n → n % 2 = 1 → n ≠ 1 →
      ∃ (word : List Nat) (m : Nat), WordTrace word n m ∧
        0 < m ∧ m % 2 = 1 ∧ m < n) :
    ∀ n : Nat, 0 < n → n % 2 = 1 →
      ∃ word : List Nat, WordTrace word n 1 := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih positive odd
  by_cases terminal : n = 1
  · subst n
    exact ⟨[], rfl⟩
  · obtain ⟨first, m, trace, mpositive, modd, smaller⟩ :=
      hdescent n positive odd terminal
    obtain ⟨later, remainder⟩ := ih m smaller mpositive modd
    exact ⟨first ++ later, word_trace_append trace remainder⟩

#print axioms word_trace_append
#print axioms universal_descent_implies_convergence

end CollatzResearch
