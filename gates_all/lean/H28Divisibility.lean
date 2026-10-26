import Std

namespace H28Affine

/-- Every power of two is nonzero modulo three. -/
theorem pow_two_mod_three (s : Nat) :
    2 ^ s % 3 = 1 ∨ 2 ^ s % 3 = 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h | h
      · rw [h]
        omega
      · rw [h]
        omega

/-- Division by three survives removal of an arbitrary power-of-two factor. -/
theorem three_dvd_of_two_pow_mul (s m : Nat)
    (h : 3 ∣ 2 ^ s * m) : 3 ∣ m := by
  have hmod : (2 ^ s * m) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod] at hmod
  rcases pow_two_mod_three s with hp | hp
  · rw [hp] at hmod
    have hm : m % 3 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero hm
  · rw [hp] at hmod
    have hm : m % 3 < 3 := Nat.mod_lt _ (by omega)
    have hz : m % 3 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero hz

/-- The scaled terminal affine equation forces an integer predecessor.
    The variable t is the right-side quotient from the affine prefix split. -/
theorem terminal_predecessor_from_scaled
    (s b y t : Nat) (hb : 0 < b) (hy : y % 2 = 1)
    (heq : 2 ^ s * (2 ^ b * y) = 2 ^ s + 3 * t) :
    ∃ z : Nat, 3 * z + 1 = 2 ^ b * y ∧ z % 2 = 1 := by
  have hypos : 0 < y := by omega
  have hpow : 0 < 2 ^ b := by
    have aux : ∀ n : Nat, 0 < 2 ^ n := by
      intro n
      induction n with
      | zero => decide
      | succ n ih =>
          simpa only [Nat.pow_succ] using
            (Nat.mul_pos ih (by decide : 0 < (2 : Nat)))
    exact aux b
  have hpos : 0 < 2 ^ b * y := Nat.mul_pos hpow hypos
  have hscaled : 2 ^ s * (2 ^ b * y - 1) = 3 * t := by
    rw [Nat.mul_sub_left_distrib]
    simp only [Nat.mul_one]
    omega
  have hdiv : 3 ∣ 2 ^ b * y - 1 :=
    three_dvd_of_two_pow_mul s _ (by rw [hscaled]; exact ⟨t, rfl⟩)
  let z := (2 ^ b * y - 1) / 3
  have hmod : (2 ^ b * y - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hreconstruct : 3 * z + 1 = 2 ^ b * y := by
    dsimp [z]
    omega
  have hodd : z % 2 = 1 := by
    have hpow_even : 2 ^ b % 2 = 0 := by
      have hform : b = (b - 1) + 1 := by omega
      rw [hform, Nat.pow_succ, Nat.mul_mod]
      omega
    have heven : (2 ^ b * y) % 2 = 0 := by
      rw [Nat.mul_mod, hpow_even]
      omega
    omega
  exact ⟨z, hreconstruct, hodd⟩

#print axioms H28Affine.pow_two_mod_three
#print axioms H28Affine.three_dvd_of_two_pow_mul
#print axioms H28Affine.terminal_predecessor_from_scaled

end H28Affine
