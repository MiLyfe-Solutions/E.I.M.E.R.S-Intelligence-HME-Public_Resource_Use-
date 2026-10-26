import Mathlib

def stripTwosSimple (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 0 then stripTwosSimple (n / 2)
  else n
termination_by n
decreasing_by omega

theorem strip_simple_odd (n : Nat) (h : n % 2 = 1) :
    stripTwosSimple n = n := by
  have hn : n != 0 := by omega
  have he : n % 2 != 0 := by omega
  unfold stripTwosSimple
  simp [hn, he]
