import FiniteStepDescent.FiniteStepDescent

namespace FiniteStepDescent

/-- A non-Collatz process: repeatedly replace a natural number by half of it. -/
def halve (n : Nat) : Nat := n / 2

theorem halve_strictly_decreases (n : Nat) (hn : 0 < n) : halve n < n := by
  exact Nat.div_lt_self hn (by decide)

/-- Every starting natural number reaches zero after finitely many halvings. -/
theorem halve_eventually_zero (n : Nat) :
    ∃ k, iterate halve k n = 0 := by
  obtain ⟨k, hk⟩ :=
    finite_step_descent
      (rank := fun x : Nat => x)
      (block := halve)
      (target := 0)
      (decrease := by
        intro x hx
        exact halve_strictly_decreases x hx)
      n
  exact ⟨k, Nat.le_antisymm hk (Nat.zero_le _)⟩

end FiniteStepDescent
