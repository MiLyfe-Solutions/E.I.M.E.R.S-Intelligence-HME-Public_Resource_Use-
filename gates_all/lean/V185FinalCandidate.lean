import V185Iter22

namespace EimersV185Full
open EimersV185Bridge

private theorem strip_le (n : Nat) : stripTwosPower n <= n := by
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

private theorem strip_double_positive (n : Nat) (hn : 0 < n) :
    stripTwosPower (2 * n) = stripTwosPower n := by
  have hnonzero : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [stripTwosPower]
  simp [hnonzero, heven, hdiv]

private theorem strip_pow_eq (a y : Nat) (hy : 0 < y) :
    stripTwosPower (2 ^ a * y) = stripTwosPower y := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hpos : 0 < 2 ^ a * y := Nat.mul_pos (by positivity) hy
      calc
        stripTwosPower (2 ^ (a + 1) * y) = stripTwosPower (2 * (2 ^ a * y)) := by congr 1; ring
        _ = stripTwosPower (2 ^ a * y) := strip_double_positive _ hpos
        _ = stripTwosPower y := ih

private theorem tail_endpoint_bound (q : Nat) :
    256 * acceleratedTest (state22 q) <= 3 * state22 q + 1 := by
  have ht := tail_divisible q
  let y : Nat := 38265777571 + q * 94143178827
  have hy : 0 < y := by dsimp [y]; omega
  have hstrip : stripTwosPower (256 * y) = stripTwosPower y := by
    simpa only [show (2:Nat)^8 = 256 by norm_num] using strip_pow_eq 8 y hy
  have hle := strip_le y
  unfold acceleratedTest
  rw [ht]
  rw [hstrip]
  dsimp [y] at *
  omega

theorem V185_finite_descent (q : Nat) :
    iterateA 23 (start q) < start q := by
  change acceleratedTest (iterateA 22 (start q)) < start q
  rw [iter22 q]
  exact bound_if_tail_endpoint q (acceleratedTest (state22 q)) (tail_endpoint_bound q)

end EimersV185Full
