import V185Iter22

/- An additive contraction corollary for the actual V185 accelerated map.
   The stripping lemmas reproduce the proof pattern in the unchanged
   V185FinalCandidate source, inside a separate namespace. No exact terminal
   valuation is assumed: additional terminal divisions can only reduce the
   accelerated endpoint. Kernel acceptance requires a separate build receipt. -/

namespace EimersV185Full
namespace ContractionFollowup

open EimersV185Bridge

private theorem strip_le_for_bound (n : Nat) : stripTwosPower n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hz : n = 0
      · simp [stripTwosPower, hz]
      · by_cases he : n % 2 = 0
        · have hlt : n / 2 < n := by omega
          have hrec := ih (n / 2) hlt
          rw [stripTwosPower]
          simp only [if_neg hz, if_pos he]
          omega
        · simp [stripTwosPower, hz, he]

private theorem strip_double_for_bound (n : Nat) (hn : 0 < n) :
    stripTwosPower (2 * n) = stripTwosPower n := by
  have hnonzero : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [stripTwosPower]
  simp [hnonzero, heven, hdiv]

private theorem strip_power_for_bound (a y : Nat) (hy : 0 < y) :
    stripTwosPower (2 ^ a * y) = stripTwosPower y := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hpos : 0 < 2 ^ a * y := Nat.mul_pos (by positivity) hy
      calc
        stripTwosPower (2 ^ (a + 1) * y) = stripTwosPower (2 * (2 ^ a * y)) := by
          congr 1
          ring
        _ = stripTwosPower (2 ^ a * y) := strip_double_for_bound _ hpos
        _ = stripTwosPower y := ih

private theorem tail_endpoint_le (q : Nat) :
    acceleratedTest (state22 q) ≤ 38265777571 + q * 94143178827 := by
  have ht := tail_divisible q
  let y : Nat := 38265777571 + q * 94143178827
  have hy : 0 < y := by dsimp [y]; omega
  have hstrip : stripTwosPower (256 * y) = stripTwosPower y := by
    simpa only [show (2 : Nat) ^ 8 = 256 by norm_num] using strip_power_for_bound 8 y hy
  unfold acceleratedTest
  rw [ht]
  change stripTwosPower (256 * y) ≤ y
  rw [hstrip]
  exact strip_le_for_bound y

/-- The actual 23-step accelerated endpoint is bounded by the affine endpoint.
    The bound permits additional terminal halving when that endpoint is even. -/
theorem accelerated23_endpoint_bound (q : Nat) :
    iterateA 23 (start q) ≤ 38265777571 + q * 94143178827 := by
  change acceleratedTest (iterateA 22 (start q)) ≤ 38265777571 + q * 94143178827
  rw [iter22 q]
  exact tail_endpoint_le q

private theorem affine_margin_685 (q : Nat) :
    1000 * (38265777571 + q * 94143178827) < 685 * start q := by
  simp only [start]
  omega

/-- Strict 0.685 contraction after 23 actual accelerated Collatz steps,
    uniformly for every natural parameter in the canonical V185 family. -/
theorem accelerated23_contraction_685 (q : Nat) :
    1000 * iterateA 23 (start q) < 685 * start q := by
  have hbound := accelerated23_endpoint_bound q
  have hscaled := Nat.mul_le_mul_left 1000 hbound
  exact lt_of_le_of_lt hscaled (affine_margin_685 q)

end ContractionFollowup
end EimersV185Full

#check EimersV185Full.ContractionFollowup.accelerated23_endpoint_bound
#check EimersV185Full.ContractionFollowup.accelerated23_contraction_685
#print axioms EimersV185Full.ContractionFollowup.accelerated23_endpoint_bound
#print axioms EimersV185Full.ContractionFollowup.accelerated23_contraction_685
