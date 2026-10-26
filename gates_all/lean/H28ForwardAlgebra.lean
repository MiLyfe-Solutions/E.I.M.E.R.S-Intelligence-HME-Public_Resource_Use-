import Lean

namespace H28ForwardAlgebra

/-- Isolated algebraic induction step. No V185 sources are modified. -/
theorem forward_cons_algebra
    (a s n x z y c : Nat)
    (hstep : 3 * x + 1 = 2 ^ a * z)
    (ih : 2 ^ s * y = 3 ^ n * z + c) :
    2 ^ (a + s) * y = 3 ^ (n + 1) * x + (3 ^ n + 2 ^ a * c) := by
  calc
    2 ^ (a + s) * y = 2 ^ a * (2 ^ s * y) := by
      rw [pow_add]
      ac_rfl
    _ = 2 ^ a * (3 ^ n * z + c) := by rw [ih]
    _ = 3 ^ n * (2 ^ a * z) + 2 ^ a * c := by
      simp only [Nat.mul_add]
      ac_rfl
    _ = 3 ^ n * (3 * x + 1) + 2 ^ a * c := by rw [hstep]
    _ = 3 ^ (n + 1) * x + (3 ^ n + 2 ^ a * c) := by
      rw [pow_succ]
      simp only [Nat.mul_add, Nat.mul_one]
      ac_rfl

#print axioms H28ForwardAlgebra.forward_cons_algebra
end H28ForwardAlgebra
