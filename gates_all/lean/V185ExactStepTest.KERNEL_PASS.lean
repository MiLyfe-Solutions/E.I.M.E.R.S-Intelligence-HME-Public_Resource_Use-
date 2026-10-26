import Mathlib

def stripTwosPower (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 0 then stripTwosPower (n / 2)
  else n
termination_by n
decreasing_by omega

private theorem strip_odd (n : Nat) (h : n % 2 = 1) :
    stripTwosPower n = n := by
  have hn : n ≠ 0 := by omega
  have he : n % 2 ≠ 0 := by omega
  unfold stripTwosPower
  simp [hn, he]

private theorem strip_double (n : Nat) (hn : 0 < n) :
    stripTwosPower (2 * n) = stripTwosPower n := by
  have hnonzero : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [stripTwosPower]
  simp only [if_neg hnonzero, if_pos heven, hdiv]

theorem strip_pow_two (a y : Nat) (hy : y % 2 = 1) :
    stripTwosPower (2 ^ a * y) = y := by
  induction a with
  | zero =>
      simpa using strip_odd y hy
  | succ a ih =>
      have hypos : 0 < y := by omega
      have hpow : 0 < 2 ^ a := by positivity
      have hpos : 0 < 2 ^ a * y :=
        Nat.mul_pos hpow hypos
      calc
        stripTwosPower (2 ^ (a + 1) * y)
            = stripTwosPower (2 * (2 ^ a * y)) := by
                congr 1
                ring
        _ = stripTwosPower (2 ^ a * y) :=
          strip_double _ hpos
        _ = y := ih

def acceleratedTest (n : Nat) : Nat :=
  stripTwosPower (3 * n + 1)

theorem exact_accelerated_step (x y a : Nat)
    (hxy : 3 * x + 1 = 2 ^ a * y)
    (hy : y % 2 = 1) :
    acceleratedTest x = y := by
  unfold acceleratedTest
  rw [hxy]
  exact strip_pow_two a y hy
