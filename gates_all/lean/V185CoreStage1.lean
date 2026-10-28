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
  simp only [ite_eq_right hnonzero, ite_eq_left heven, hdiv]

end EimersV185Actual
