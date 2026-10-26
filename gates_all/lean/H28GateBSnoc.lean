import H28AffineForward

namespace H28Affine

/-- The exact constant for a valuation word ending with exponent b. -/
theorem offset_snoc (pref : List Nat) (b : Nat) :
    offset (pref ++ [b]) = 3 * offset pref + 2 ^ pref.sum := by
  induction pref with
  | nil =>
      simp [offset]
  | cons a rest ih =>
      simp only [List.cons_append, List.sum_cons, offset]
      simp only [List.length_append, List.length_cons, List.length_singleton,
        Nat.add_one, Nat.pow_succ, Nat.pow_add, ih]
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A terminal exact step forces its predecessor to be odd. -/
theorem predecessor_odd_of_step {b z y : Nat}
    (hb : 0 < b) (hstep : 3 * z + 1 = 2 ^ b * y) :
    z % 2 = 1 := by
  have heven : (2 ^ b * y) % 2 = 0 := by
    rw [Nat.mul_mod, CollatzResearch.pow_two_even hb]
    simp
  have hz : (3 * z + 1) % 2 = 0 := by rw [hstep]; exact heven
  omega

#print axioms H28Affine.offset_snoc
#print axioms H28Affine.predecessor_odd_of_step
end H28Affine
