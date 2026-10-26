import Mathlib
import GeneralFiniteStepDescent

namespace EimersNonCollatz

open EimersFiniteStep

/-- A two-branch integer process: odd inputs rise by 3; even inputs halve. -/
def T (n : Nat) : Nat :=
  if n % 2 = 1 then n + 3 else n / 2

/-- The second iterate has an exact affine bound on odd inputs. -/
theorem T_two_step_affine_bound (n : Nat) (hodd : n % 2 = 1) :
    2 * iterate T 2 n ≤ n + 3 := by
  have heven : (n + 3) % 2 = 0 := by omega
  have hexact : iterate T 2 n = (n + 3) / 2 := by
    simp [iterate, T, hodd, heven]
  rw [hexact]
  omega

/-- For every odd n ≥ 5, the process rises once and then descends by step 2. -/
theorem T_two_step_descent (n : Nat) (hodd : n % 2 = 1) (hn : 5 ≤ n) :
    iterate T 2 n < n := by
  apply affine_finite_step_descent T 2 n 2 1 3
  · omega
  · simpa using T_two_step_affine_bound n hodd
  · omega

/-- The first transition is increasing on every odd input. -/
theorem T_first_step_increases (n : Nat) (hodd : n % 2 = 1) :
    T n > n := by
  simp [T, hodd]

end EimersNonCollatz

#print axioms EimersNonCollatz.T_two_step_descent
#print axioms EimersNonCollatz.T_first_step_increases
