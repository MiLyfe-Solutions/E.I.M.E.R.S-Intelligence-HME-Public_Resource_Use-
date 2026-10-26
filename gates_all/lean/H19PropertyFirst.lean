import Mathlib

/- Candidate Lean proof obligations for the user's local Mathlib environment.
   NOT COMPILED HERE. No theorem claims Collatz convergence. -/

namespace H19PropertyFirst

theorem affine_bound_64 (x y z : Nat)
    (hdiv : 64 * z = 3 * y + 1)
    (hmargin : 3 * y + 1 < 64 * x) : z < x := by
  omega

theorem example_99_step1_rises (u : Nat) :
    99 + 128*u < 149 + 192*u := by
  omega

theorem example_99_valuation_at_least_six (u : Nat) :
    64 ∣ 3 * (149 + 192*u) + 1 := by
  refine ⟨7 + 9*u, ?_⟩
  omega

theorem example_99_step2_bound (u z : Nat)
    (hz : z ≤ 7 + 9*u) : z < 99 + 128*u := by
  omega

theorem affine_margin_contract
    (x0 stride y0 ystride bound : Nat)
    (h0 : 3*y0+1 < bound*x0)
    (hs : 3*ystride ≤ bound*stride)
    (u : Nat) :
    3*(y0+ystride*u)+1 < bound*(x0+stride*u) := by
  have h0' : 3*y0+1 + 3*ystride*u ≤ bound*x0 + 3*ystride*u :=
    Nat.add_le_add_right (Nat.le_of_lt h0) _
  have hs' : 3*ystride*u ≤ bound*stride*u := Nat.mul_le_mul_right u hs
  omega

end H19PropertyFirst
