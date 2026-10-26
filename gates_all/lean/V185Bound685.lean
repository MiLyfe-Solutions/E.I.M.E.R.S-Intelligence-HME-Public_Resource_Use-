import V185Iter22

/-!
V185 quantitative corollary: A^23(n) < 0.685 * n, i.e. 200 * A^23(n) < 137 * n,
for every n = 55,863,935,003 + q * 2^37. Uses the existing V185 bridge unchanged;
the two helper lemmas below re-state private lemmas from V185FinalCandidate.
-/

namespace EimersV185Bound685
open EimersV185Bridge EimersV185Full

theorem strip_le' (n : Nat) : stripTwosPower n <= n := by
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

theorem endpoint_le_y (q : Nat) :
    acceleratedTest (state22 q) <= 38265777571 + q * 94143178827 := by
  have ht := tail_divisible q
  unfold acceleratedTest
  rw [ht]
  -- stripping factors of two from 256*y never exceeds y
  have hy : 0 < 38265777571 + q * 94143178827 := by omega
  have key : ∀ (a y : Nat), 0 < y → stripTwosPower (2 ^ a * y) <= y := by
    intro a y hy
    induction a with
    | zero => simpa using strip_le' y
    | succ a ih =>
        have hpos : 0 < 2 ^ a * y := Nat.mul_pos (by positivity) hy
        have h2 : 2 ^ (a + 1) * y = 2 * (2 ^ a * y) := by ring
        rw [h2, stripTwosPower]
        have hnz : 2 * (2 ^ a * y) ≠ 0 := by omega
        have hev : (2 * (2 ^ a * y)) % 2 = 0 := by omega
        have hd : (2 * (2 ^ a * y)) / 2 = 2 ^ a * y := by omega
        simp only [if_neg hnz, if_pos hev, hd]
        exact ih
  simpa only [show (2:Nat)^8 = 256 by norm_num] using
    key 8 (38265777571 + q * 94143178827) hy

theorem V185_contraction_685 (q : Nat) :
    200 * iterateA 23 (start q) < 137 * start q := by
  change 200 * acceleratedTest (iterateA 22 (start q)) < 137 * start q
  rw [iter22 q]
  have h := endpoint_le_y q
  simp only [start]
  omega

end EimersV185Bound685

#print EimersV185Bound685.V185_contraction_685
#print axioms EimersV185Bound685.V185_contraction_685
