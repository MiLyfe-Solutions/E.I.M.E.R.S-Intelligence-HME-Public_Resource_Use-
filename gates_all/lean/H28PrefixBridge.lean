import H28Divisibility

namespace H28Affine

/-- The scaled terminal equation determines not only the terminal odd
predecessor but also the exact affine value of the preceding prefix.
This is the missing cancellation needed for reverse snoc induction. -/
theorem terminal_predecessor_and_prefix
    (s b y t : Nat) (hb : 0 < b) (hy : y % 2 = 1)
    (heq : 2 ^ s * (2 ^ b * y) = 2 ^ s + 3 * t) :
    ∃ z : Nat, (3 * z + 1 = 2 ^ b * y) ∧
      z % 2 = 1 ∧ 2 ^ s * z = t := by
  obtain ⟨z, hstep, hzodd⟩ :=
    terminal_predecessor_from_scaled s b y t hb hy heq
  have hcancel : 3 * (2 ^ s * z) + 2 ^ s = 2 ^ s + 3 * t := by
    calc
      3 * (2 ^ s * z) + 2 ^ s = 2 ^ s * (3 * z + 1) := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
          Nat.add_comm, Nat.add_left_comm]
      _ = 2 ^ s * (2 ^ b * y) := by rw [hstep]
      _ = 2 ^ s + 3 * t := heq
  have hprefix : 2 ^ s * z = t := by omega
  exact ⟨z, hstep, hzodd, hprefix⟩

#print axioms H28Affine.terminal_predecessor_and_prefix
end H28Affine
