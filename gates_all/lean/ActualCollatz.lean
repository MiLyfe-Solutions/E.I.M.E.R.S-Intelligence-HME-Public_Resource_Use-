import FamilyDescent

namespace CollatzResearch

/-- The usual Collatz map, iterated in execution order. -/
def iterateCollatz : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterateCollatz k (collatzStep n)

theorem iterateCollatz_add (a b n : Nat) :
    iterateCollatz (a + b) n = iterateCollatz b (iterateCollatz a n) := by
  induction a generalizing n with
  | zero => simp [iterateCollatz]
  | succ a ih => simpa [Nat.succ_add, iterateCollatz] using ih (collatzStep n)

theorem iterateCollatz_halves (a y : Nat) :
    iterateCollatz a (2 ^ a * y) = y := by
  induction a with
  | zero => simp [iterateCollatz]
  | succ a ih =>
      have hp : 2 ^ (a + 1) * y = 2 * (2 ^ a * y) := by
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      rw [hp]
      change iterateCollatz a (collatzStep (2 * (2 ^ a * y))) = y
      have hs : collatzStep (2 * (2 ^ a * y)) = 2 ^ a * y := by
        simp [collatzStep]
      rw [hs]
      exact ih

/-- An exact odd step is one 3n+1 update followed by all prescribed halvings. -/
theorem exact_step_actual {a x y : Nat} (h : ExactOddStep a x y) :
    iterateCollatz (a + 1) x = y := by
  rcases h with ⟨hx, hy, ha, he⟩
  have hs : collatzStep x = 3 * x + 1 := by simp [collatzStep, hx]
  rw [Nat.add_comm a 1, iterateCollatz_add]
  simp only [iterateCollatz, hs]
  rw [he]
  exact iterateCollatz_halves a y

/-- Exact accelerated traces correspond to a concrete number of ordinary steps. -/
theorem word_trace_actual (word : List Nat) {x y : Nat}
    (h : WordTrace word x y) :
    iterateCollatz (word.sum + word.length) x = y := by
  induction word generalizing x y with
  | nil => simpa [WordTrace, iterateCollatz] using h.symm
  | cons a word ih =>
      rcases h with ⟨z, step, rest⟩
      have hc : (a :: word).sum + (a :: word).length =
          (a + 1) + (word.sum + word.length) := by
        simp only [List.sum_cons, List.length_cons]
        omega
      rw [hc, iterateCollatz_add, exact_step_actual step]
      exact ih rest

theorem family_actual_descends (word : List Nat) {r y b : Nat}
    (trace : WordTrace word r y) (stable : word.sum < b)
    (contract : 3 ^ word.length < 2 ^ word.sum) (descent : y < r)
    (q : Nat) :
    iterateCollatz (word.sum + word.length) (r + q * 2 ^ b) < r + q * 2 ^ b := by
  obtain ⟨endpoint, ht, hd⟩ := family_descends word trace stable contract descent q
  rw [word_trace_actual word ht]
  exact hd

#print axioms iterateCollatz_add
#print axioms iterateCollatz_halves
#print axioms exact_step_actual
#print axioms word_trace_actual
#print axioms family_actual_descends

end CollatzResearch
