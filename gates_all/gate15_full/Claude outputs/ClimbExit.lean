import Std

/-!
# All-ones climb exit (step 3 of the leftover plan)

Shortcut Collatz map: T(n) = n/2 for even n, (3n+1)/2 for odd n.

A lot whose binary code ends in k ones is `2^k * m - 1`. This file proves,
for every k at once:

* `climb_exit`  : `iter k` (T applied k times) sends `2^k * m - 1` exactly to `3^k * m - 1`
* `exit_even`   : if m is odd, that exit value is even (it drops next)
* `exit_above`  : for k ≥ 1 the exit is strictly above the start (it climbed)

No descent claim. Universal Collatz: HOLD_UNPROVEN.
-/

namespace CPOQClimb

/-- Shortcut Collatz step. -/
def shortStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Apply the shortcut step k times (core Lean only, no Mathlib). -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter k (shortStep n)

/-- One climbing step: `2^(k+1)*m - 1` goes to `2^k*(3m) - 1`. -/
theorem step_one (k m : Nat) (hm : 0 < m) :
    shortStep (2 ^ (k + 1) * m - 1) = 2 ^ k * (3 * m) - 1 := by
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have hN : 0 < 2 ^ k * m := Nat.mul_pos hP hm
  have e1 : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
    rw [Nat.pow_succ]; ac_rfl
  have e2 : 2 ^ k * (3 * m) = 3 * (2 ^ k * m) := by ac_rfl
  rw [e1, e2]
  generalize 2 ^ k * m = N at hN ⊢
  unfold shortStep
  split <;> omega

/-- The exit formula, for every number of trailing ones k. -/
theorem climb_exit (k : Nat) : ∀ m : Nat, 0 < m →
    iter k (2 ^ k * m - 1) = 3 ^ k * m - 1 := by
  induction k with
  | zero =>
      intro m _
      simp [iter]
  | succ j ih =>
      intro m hm
      show iter j (shortStep (2 ^ (j + 1) * m - 1)) = 3 ^ (j + 1) * m - 1
      rw [step_one j m hm, ih (3 * m) (by omega)]
      rw [Nat.pow_succ]
      congr 1
      ac_rfl

/-- If m is odd, the exit value `3^k*m - 1` is even, so the next step halves. -/
theorem exit_even (k m : Nat) (hm : m % 2 = 1) : (3 ^ k * m - 1) % 2 = 0 := by
  have h3 : 3 ^ k % 2 = 1 := by
    rw [Nat.pow_mod]; simp
  have h : (3 ^ k * m) % 2 = 1 := by
    rw [Nat.mul_mod, h3, hm]
  generalize 3 ^ k * m = N at h ⊢
  omega

/-- 2^(k+1) < 3^(k+1): the climb factor beats the halving factor. -/
theorem two_pow_lt_three_pow (k : Nat) : 2 ^ (k + 1) < 3 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ j ih =>
      have e2 : 2 ^ (j + 1 + 1) = 2 ^ (j + 1) * 2 := by rw [Nat.pow_succ]
      have e3 : 3 ^ (j + 1 + 1) = 3 ^ (j + 1) * 3 := by rw [Nat.pow_succ]
      rw [e2, e3]
      generalize 2 ^ (j + 1) = A at ih ⊢
      generalize 3 ^ (j + 1) = B at ih ⊢
      omega

/-- For k ≥ 1 the exit is strictly above the start: the lot climbed. -/
theorem exit_above (k m : Nat) (hm : 0 < m) :
    2 ^ (k + 1) * m - 1 < 3 ^ (k + 1) * m - 1 := by
  have h := Nat.mul_lt_mul_of_pos_right (two_pow_lt_three_pow k) hm
  have h2 : 0 < 2 ^ (k + 1) * m := Nat.mul_pos (Nat.two_pow_pos (k + 1)) hm
  generalize 2 ^ (k + 1) * m = A at h h2 ⊢
  generalize 3 ^ (k + 1) * m = B at h ⊢
  omega

/-- Smoke tests: 39 = 2^3*5 - 1 climbs 39 → 59 → 89 → 134 = 3^3*5 - 1. -/
example : iter 3 (2 ^ 3 * 5 - 1) = 3 ^ 3 * 5 - 1 := by decide
example : iter 3 39 = 134 := by decide

#print axioms CPOQClimb.step_one
#print axioms CPOQClimb.climb_exit
#print axioms CPOQClimb.exit_even
#print axioms CPOQClimb.two_pow_lt_three_pow
#print axioms CPOQClimb.exit_above

end CPOQClimb
