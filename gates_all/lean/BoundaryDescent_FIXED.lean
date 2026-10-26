import Mathlib

/-!
E.I.M.E.R.S. Collatz boundary certificate — isolated formalization candidate.

STATUS: REVISED CANDIDATE; RUN LEAN TO CONFIRM KERNEL CHECK.
This file proves conditional arithmetic statements IF it compiles under Lean 4.
It does not establish that all odd integers descend, or that a representative
prefix automatically lifts.  The prefix/trace bridge is a separate obligation.
-/

namespace EimersCollatz

/-- The affine offset update at one accelerated odd step. -/
theorem affine_terminal_update
    (k S x n B : Nat)
    (hprefix : 2 ^ S * x = 3 ^ k * n + B) :
    2 ^ S * (3 * x + 1) = 3 ^ (k + 1) * n + (3 * B + 2 ^ S) := by
  rw [pow_succ]
  nlinarith [hprefix]

/-- If the last valuation crosses precision b, the terminal value has
    an upper bound using 2^b, even if the exact valuation is not fixed. -/
theorem terminal_lower_bound
    (b k S v x y n B : Nat)
    (hprefix : 2 ^ S * x = 3 ^ k * n + B)
    (hstep : 2 ^ v * y = 3 * x + 1)
    (hcross : b <= S + v) :
    2 ^ b * y <= 3 ^ (k + 1) * n + (3 * B + 2 ^ S) := by
  have hpow : 2 ^ b <= 2 ^ (S + v) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 2) hcross
  have hmul : 2 ^ b * y <= 2 ^ (S + v) * y :=
    Nat.mul_le_mul_right y hpow
  calc
    2 ^ b * y <= 2 ^ (S + v) * y := hmul
    _ = 2 ^ S * (3 * x + 1) := by
      rw [pow_add, mul_assoc, hstep]
    _ = 3 ^ (k + 1) * n + (3 * B + 2 ^ S) :=
      affine_terminal_update k S x n B hprefix

/-- A strict affine boundary inequality gives strict descent for this lift. -/
theorem boundary_descent_one
    (b k S v x y n B : Nat)
    (hprefix : 2 ^ S * x = 3 ^ k * n + B)
    (hstep : 2 ^ v * y = 3 * x + 1)
    (hcross : b <= S + v)
    (hineq : 3 ^ (k + 1) * n + (3 * B + 2 ^ S) < 2 ^ b * n) :
    y < n := by
  have hbound := terminal_lower_bound b k S v x y n B hprefix hstep hcross
  by_contra hn
  have hny : n <= y := Nat.le_of_not_gt hn
  have hmul : 2 ^ b * n <= 2 ^ b * y :=
    Nat.mul_le_mul_left (2 ^ b) hny
  omega

/-- A representative certificate inequality suffices for EVERY lift,
    PROVIDED its actual fixed-prefix affine identity and terminal step
    (including the crossing bound) have been established. -/
theorem boundary_descent_all_lifts
    (b k S B r : Nat)
    (hpower : 3 ^ (k + 1) < 2 ^ b)
    (hcert : (2 ^ b - 3 ^ (k + 1)) * r > 3 * B + 2 ^ S)
    (htrace : forall q : Nat, exists x v y : Nat,
      2 ^ S * x = 3 ^ k * (r + 2 ^ b * q) + B /\
      2 ^ v * y = 3 * x + 1 /\
      b <= S + v) :
    forall q : Nat, exists y : Nat, y < r + 2 ^ b * q := by
  intro q
  obtain ⟨x, v, y, hpref, hstep, hcross⟩ := htrace q
  refine ⟨y, ?_⟩
  have hr : r <= r + 2 ^ b * q := by omega
  have hmass : (2 ^ b - 3 ^ (k + 1)) * r <=
      (2 ^ b - 3 ^ (k + 1)) * (r + 2 ^ b * q) :=
    Nat.mul_le_mul_left _ hr
  have hsub : (2 ^ b - 3 ^ (k + 1)) + 3 ^ (k + 1) = 2 ^ b :=
    Nat.sub_add_cancel (Nat.le_of_lt hpower)
  have hineq : 3 ^ (k + 1) * (r + 2 ^ b * q) + (3 * B + 2 ^ S) <
      2 ^ b * (r + 2 ^ b * q) := by
    nlinarith [hmass, hcert]
  exact boundary_descent_one b k S v x y (r + 2 ^ b * q) B
    hpref hstep hcross hineq

/-- Exact affine lift: the endpoint at the fixed prefix is a progression
    with stride 3^k * 2^(b-S). This is algebraic; identifying this endpoint
    with the actual iterate requires a separately checked trace-lift lemma. -/
theorem affine_prefix_lift
    (b k S B r x q : Nat)
    (hbits : S <= b)
    (hrep : 2 ^ S * x = 3 ^ k * r + B) :
    2 ^ S * (x + 3 ^ k * 2 ^ (b - S) * q) =
      3 ^ k * (r + 2 ^ b * q) + B := by
  have hpow : 2 ^ S * 2 ^ (b - S) = 2 ^ b := by
    rw [← pow_add, Nat.add_sub_of_le hbits]
  calc
    2 ^ S * (x + 3 ^ k * 2 ^ (b - S) * q)
        = 2 ^ S * x + 3 ^ k * (2 ^ S * 2 ^ (b - S)) * q := by ring
    _ = 2 ^ S * x + 3 ^ k * 2 ^ b * q := by rw [hpow]
    _ = 3 ^ k * (r + 2 ^ b * q) + B := by
      rw [hrep]
      ring

/-- Divisibility at the boundary is preserved by the affine progression.
    Exact terminal valuations can vary, but the lower bound survives. -/
theorem terminal_divisibility_lifts
    (k t x q : Nat)
    (hdiv : 2 ^ t ∣ 3 * x + 1) :
    2 ^ t ∣ 3 * (x + 3 ^ k * 2 ^ t * q) + 1 := by
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨w + 3 ^ (k + 1) * q, ?_⟩
  calc
    3 * (x + 3 ^ k * 2 ^ t * q) + 1 =
        (3 * x + 1) + 3 ^ (k + 1) * 2 ^ t * q := by
          rw [pow_succ]
          ring
    _ = 2 ^ t * w + 3 ^ (k + 1) * 2 ^ t * q := by rw [hw]
    _ = 2 ^ t * (w + 3 ^ (k + 1) * q) := by ring

#print axioms affine_terminal_update
#print axioms terminal_lower_bound
#print axioms boundary_descent_one
#print axioms boundary_descent_all_lifts
#print axioms affine_prefix_lift
#print axioms terminal_divisibility_lifts

end EimersCollatz

[executed on device: Joshuas-MacBook-Pro.local (d9b9b762-5cf1-40bc-a132-47385a99d657)]