import Mathlib
import V185StepBridge

/-!
V185 accelerated-map connection candidate. This is a NEW formal proof layer.
Not kernel-compiled by the producer. Prior compiled bridge is a separate source
preserved under V185StepBridge.KERNEL_PASS.lean on the founder Mac.
The function `stripTwos` removes powers of 2 by repeated exact division.
`accelerated` therefore represents the accelerated odd Collatz map for odd inputs.
No placeholders, custom axioms, or trusted external computations.
-/

namespace EimersV185Actual
open EimersV185Bridge

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
  rw [stripTwos]
  have hnonzero : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  simp only [ite_eq_right hnonzero, ite_eq_left heven, hdiv]

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

def accelerated (n : ℕ) : ℕ := stripTwos (3*n+1)

private theorem exact_step (x y a : ℕ)
    (hxy : 3*x+1 = 2^a*y) (hy : y%2=1) :
    accelerated x = y := by
  unfold accelerated
  rw [hxy]
  exact strip_pow_two a y hy

-- Every step is now connected to an actual remove-all-factors-of-two map.
theorem actual_step1 (q : ℕ) :
    accelerated (state0 q) = state1 q := by
  apply exact_step (state0 q) (state1 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step1_identity q
  · exact step1_odd q

theorem actual_step2 (q : ℕ) :
    accelerated (state1 q) = state2 q := by
  apply exact_step (state1 q) (state2 q) 2
  · simpa only [show (2:ℕ) ^ 2 = 4 by norm_num] using
      step2_identity q
  · exact step2_odd q

theorem actual_step3 (q : ℕ) :
    accelerated (state2 q) = state3 q := by
  apply exact_step (state2 q) (state3 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step3_identity q
  · exact step3_odd q

theorem actual_step4 (q : ℕ) :
    accelerated (state3 q) = state4 q := by
  apply exact_step (state3 q) (state4 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step4_identity q
  · exact step4_odd q

theorem actual_step5 (q : ℕ) :
    accelerated (state4 q) = state5 q := by
  apply exact_step (state4 q) (state5 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step5_identity q
  · exact step5_odd q

theorem actual_step6 (q : ℕ) :
    accelerated (state5 q) = state6 q := by
  apply exact_step (state5 q) (state6 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step6_identity q
  · exact step6_odd q

theorem actual_step7 (q : ℕ) :
    accelerated (state6 q) = state7 q := by
  apply exact_step (state6 q) (state7 q) 2
  · simpa only [show (2:ℕ) ^ 2 = 4 by norm_num] using
      step7_identity q
  · exact step7_odd q

theorem actual_step8 (q : ℕ) :
    accelerated (state7 q) = state8 q := by
  apply exact_step (state7 q) (state8 q) 2
  · simpa only [show (2:ℕ) ^ 2 = 4 by norm_num] using
      step8_identity q
  · exact step8_odd q

theorem actual_step9 (q : ℕ) :
    accelerated (state8 q) = state9 q := by
  apply exact_step (state8 q) (state9 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step9_identity q
  · exact step9_odd q

theorem actual_step10 (q : ℕ) :
    accelerated (state9 q) = state10 q := by
  apply exact_step (state9 q) (state10 q) 2
  · simpa only [show (2:ℕ) ^ 2 = 4 by norm_num] using
      step10_identity q
  · exact step10_odd q

theorem actual_step11 (q : ℕ) :
    accelerated (state10 q) = state11 q := by
  apply exact_step (state10 q) (state11 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step11_identity q
  · exact step11_odd q

theorem actual_step12 (q : ℕ) :
    accelerated (state11 q) = state12 q := by
  apply exact_step (state11 q) (state12 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step12_identity q
  · exact step12_odd q

theorem actual_step13 (q : ℕ) :
    accelerated (state12 q) = state13 q := by
  apply exact_step (state12 q) (state13 q) 2
  · simpa only [show (2:ℕ) ^ 2 = 4 by norm_num] using
      step13_identity q
  · exact step13_odd q

theorem actual_step14 (q : ℕ) :
    accelerated (state13 q) = state14 q := by
  apply exact_step (state13 q) (state14 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step14_identity q
  · exact step14_odd q

theorem actual_step15 (q : ℕ) :
    accelerated (state14 q) = state15 q := by
  apply exact_step (state14 q) (state15 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step15_identity q
  · exact step15_odd q

theorem actual_step16 (q : ℕ) :
    accelerated (state15 q) = state16 q := by
  apply exact_step (state15 q) (state16 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step16_identity q
  · exact step16_odd q

theorem actual_step17 (q : ℕ) :
    accelerated (state16 q) = state17 q := by
  apply exact_step (state16 q) (state17 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step17_identity q
  · exact step17_odd q

theorem actual_step18 (q : ℕ) :
    accelerated (state17 q) = state18 q := by
  apply exact_step (state17 q) (state18 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step18_identity q
  · exact step18_odd q

theorem actual_step19 (q : ℕ) :
    accelerated (state18 q) = state19 q := by
  apply exact_step (state18 q) (state19 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step19_identity q
  · exact step19_odd q

theorem actual_step20 (q : ℕ) :
    accelerated (state19 q) = state20 q := by
  apply exact_step (state19 q) (state20 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step20_identity q
  · exact step20_odd q

theorem actual_step21 (q : ℕ) :
    accelerated (state20 q) = state21 q := by
  apply exact_step (state20 q) (state21 q) 3
  · simpa only [show (2:ℕ) ^ 3 = 8 by norm_num] using
      step21_identity q
  · exact step21_odd q

theorem actual_step22 (q : ℕ) :
    accelerated (state21 q) = state22 q := by
  apply exact_step (state21 q) (state22 q) 1
  · simpa only [show (2:ℕ) ^ 1 = 2 by norm_num] using
      step22_identity q
  · exact step22_odd q

theorem actual_22_steps (q : ℕ) :
    (accelerated^[22]) (start q) = state22 q := by
  -- Explicitly unfold the 22 iterations; then use individual exact-step lemmas.
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
  rw [start_eq_state0]
  rw [actual_step1]
  rw [actual_step2]
  rw [actual_step3]
  rw [actual_step4]
  rw [actual_step5]
  rw [actual_step6]
  rw [actual_step7]
  rw [actual_step8]
  rw [actual_step9]
  rw [actual_step10]
  rw [actual_step11]
  rw [actual_step12]
  rw [actual_step13]
  rw [actual_step14]
  rw [actual_step15]
  rw [actual_step16]
  rw [actual_step17]
  rw [actual_step18]
  rw [actual_step19]
  rw [actual_step20]
  rw [actual_step21]
  rw [actual_step22]

-- NEXT OBLIGATION (not claimed here): formally show the 23rd odd part is
-- bounded by the quotient after removing at least eight factors of 2,
-- then use `bound_if_tail_endpoint` to obtain the final descent.
end EimersV185Actual
