import Mathlib

namespace EimersFiniteStep

/-- The result of applying F exactly k times. -/
def iterate (F : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => F (iterate F k n)

/--
If an exact upper bound on an M-scaled k-step state has a strictly smaller
linear coefficient than M, and the starting state is above the resulting
additive threshold, then the k-step state is strictly smaller than the start.

This is a conditional finite-step descent lemma. It does not assert that the
hypotheses hold for any particular system.
-/
theorem affine_finite_step_descent
    (F : Nat → Nat) (k n M a b : Nat)
    (hAM : a < M)
    (hbound : M * iterate F k n ≤ a * n + b)
    (hthreshold : b < (M - a) * n) :
    iterate F k n < n := by
  have hdecomp : M = a + (M - a) :=
    (Nat.add_sub_of_le (Nat.le_of_lt hAM)).symm
  have hlinear : a * n + b < M * n := by
    calc
      a * n + b < a * n + (M - a) * n :=
        Nat.add_lt_add_left hthreshold (a * n)
      _ = (a + (M - a)) * n := by ring
      _ = M * n := by rw [← hdecomp]
  have hscaled : M * iterate F k n < M * n :=
    lt_of_le_of_lt hbound hlinear
  exact (Nat.mul_lt_mul_left (by omega : 0 < M)).mp hscaled

end EimersFiniteStep

#print axioms EimersFiniteStep.affine_finite_step_descent
