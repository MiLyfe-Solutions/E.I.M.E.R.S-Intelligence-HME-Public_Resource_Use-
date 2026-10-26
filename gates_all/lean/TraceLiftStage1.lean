import Mathlib

/-!
Isolated E.I.M.E.R.S. actual-step lifting bridge, stage 1.
A step is exact only if its output is odd and the exponent is positive.
This is not a universal convergence claim.
-/

namespace EimersCollatz

def ExactOddStep (x y v : Nat) : Prop :=
  Odd x ∧ Odd y ∧ 0 < v ∧ 2 ^ v * y = 3 * x + 1

theorem exact_odd_step_lift
    (x y v t q : Nat)
    (hstep : ExactOddStep x y v)
    (ht : v < t) :
    ExactOddStep
      (x + 2 ^ t * q)
      (y + 3 * 2 ^ (t - v) * q)
      v := by
  obtain ⟨hx, hy, hv, heq⟩ := hstep
  have hrem : 0 < t - v := by omega
  obtain ⟨j, hj⟩ : ∃ j, t - v = j + 1 := by
    exact ⟨t - v - 1, by omega⟩
  obtain ⟨i, hi⟩ : ∃ i, t = i + 1 := by
    exact ⟨t - 1, by omega⟩
  have hxodd : Odd (x + 2 ^ t * q) := by
    obtain ⟨a, ha⟩ := hx
    refine ⟨a + 2 ^ i * q, ?_⟩
    rw [hi, pow_succ]
    omega
  have hyodd : Odd (y + 3 * 2 ^ (t - v) * q) := by
    obtain ⟨a, ha⟩ := hy
    refine ⟨a + 3 * 2 ^ j * q, ?_⟩
    rw [hj, pow_succ]
    omega
  have hpow : 2 ^ v * 2 ^ (t - v) = 2 ^ t := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt ht)]
  refine ⟨hxodd, hyodd, hv, ?_⟩
  calc
    2 ^ v * (y + 3 * 2 ^ (t - v) * q)
      = 2 ^ v * y + 3 * (2 ^ v * 2 ^ (t - v)) * q := by ring
    _ = 3 * x + 1 + 3 * 2 ^ t * q := by rw [hpow, heq]
    _ = 3 * (x + 2 ^ t * q) + 1 := by ring

#print axioms exact_odd_step_lift

end EimersCollatz
