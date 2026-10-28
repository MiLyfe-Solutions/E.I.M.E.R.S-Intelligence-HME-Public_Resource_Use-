import Mathlib

def stripTwosTest (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 0 then stripTwosTest (n / 2)
  else n
termination_by n
decreasing_by omega

theorem strip_double_test (n : Nat) (hn : 0 < n) :
    stripTwosTest (2 * n) = stripTwosTest n := by
  have hnonzero : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [stripTwosTest]
  simp only [ite_eq_right hnonzero, ite_eq_left heven, hdiv]
