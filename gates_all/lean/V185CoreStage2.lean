import Mathlib

/-!
V185 accelerated-map connection candidate. This is a NEW formal proof layer.
Not kernel-compiled by the producer. Prior compiled bridge is a separate source
preserved under V185StepBridge.KERNEL_PASS.lean on the founder Mac.
The function `stripTwos` removes powers of 2 by repeated exact division.
`accelerated` therefore represents the accelerated odd Collatz map for odd inputs.
No placeholders, custom axioms, or trusted external computations.
-/

namespace EimersV185Actual

-- A decreasing recursion: while even and nonzero, divide by two.
def stripTwos (n : ℕ) : ℕ :=
  if hz : n = 0 then 0
  else if he : n % 2 = 0 then stripTwos (n / 2) else n
termination_by n
decreasing_by omega

private theorem strip_odd (n : ℕ) (hodd : n % 2 = 1) :
    stripTwos n = n := by
  rw [stripTwos]
  have hnonzero : n ≠ 0 := by omega
  have hnotEven : ¬ n % 2 = 0 := by omega
  simp [hnonzero, hnotEven]

private theorem strip_double (n : ℕ) (hn : 0 < n) :
    stripTwos (2 * n) = stripTwos n := by
  have hnonzero : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [stripTwos]
  simp only [if_neg hnonzero, if_pos heven, hdiv]

private theorem strip_pow_two (a y : ℕ) (hy : y % 2 = 1) :
    stripTwos (2 ^ a * y) = y := by
  induction a with
  | zero => simpa using strip_odd y hy
  | succ a ih =>
      have hpos : 0 < 2 ^ a * y := by
        have h2 : 0 < 2 ^ a := pow_pos (by omega : 0 < (2:ℕ)) _
        have hypos : 0 < y := by omega
        exact Nat.mul_pos h2 hypos
      calc
        stripTwos (2 ^ (a+1) * y) = stripTwos (2 * (2^a*y)) := by congr 1; ring
        _ = stripTwos (2^a*y) := strip_double _ hpos
        _ = y := ih

end EimersV185Actual
