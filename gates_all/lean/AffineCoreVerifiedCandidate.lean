/-
Affine Margin Transport core v2.
STATUS: DRAFT — algebraically replayed locally, NOT Lean-kernel checked in this container.
Target: Lean 4.35.0 + Mathlib in an additive isolated project.
Universal Collatz remains HOLD_UNPROVEN.
-/

import Mathlib

namespace AffineProofTransport

/-- Affine descent margin for a block `m*y = a*n + C`. -/
def margin (m a n C : Int) : Int := (m - a) * n - C

/-- Exact margin cocycle under source translation `T` and constant change `dC`. -/
theorem affine_margin_transport_identity
    (m a n C T dC : Int) :
    margin m a (n + T) (C + dC)
      = margin m a n C + ((m - a) * T - dC) := by
  unfold margin
  ring

/-- Positivity transports whenever the corrected target margin is positive. -/
theorem affine_margin_transport_positive
    (m a n C T dC : Int)
    (hpos : 0 < margin m a n C + ((m - a) * T - dC)) :
    0 < margin m a (n + T) (C + dC) := by
  rw [affine_margin_transport_identity]
  exact hpos

/-- A reusable lower bound can authorize transport without reproving the full source margin. -/
theorem affine_margin_transport_from_lower_bound
    (m a n C T dC L : Int)
    (hL : L <= margin m a n C)
    (hpos : 0 < L + ((m - a) * T - dC)) :
    0 < margin m a (n + T) (C + dC) := by
  rw [affine_margin_transport_identity]
  linarith

/-- Two consecutive translations add their margin defects exactly. -/
theorem affine_margin_transport_compose
    (m a n C T1 T2 dC1 dC2 : Int) :
    margin m a (n + T1 + T2) (C + dC1 + dC2)
      = margin m a n C
        + ((m - a) * T1 - dC1)
        + ((m - a) * T2 - dC2) := by
  unfold margin
  ring

/-- One shared affine tail update multiplies the constant defect by the common multiplier. -/
theorem common_tail_constant_cocycle_scalar
    (a C C' B : Int) :
    (a * C' + B) - (a * C + B) = a * (C' - C) := by
  ring

/-- If the incoming constant defect is `dC`, one shared update makes it `a*dC`. -/
theorem common_tail_constant_cocycle_step
    (a C C' B dC : Int)
    (h : C' - C = dC) :
    (a * C' + B) - (a * C + B) = a * dC := by
  calc
    (a * C' + B) - (a * C + B) = a * (C' - C) := by ring
    _ = a * dC := by rw [h]

/-- Positive affine margin is equivalent to strict descent when `m>0` and
    `m*y = a*n + C`; stated over integers to avoid division. -/
theorem positive_margin_implies_scaled_descent
    (m a n C y : Int)
    (hm : 0 < m)
    (haff : m * y = a * n + C)
    (hmargin : 0 < margin m a n C) :
    y < n := by
  unfold margin at hmargin
  have hscaled : m * y < m * n := by
    rw [haff]
    linarith
  by_contra h
  have hny : n <= y := le_of_not_gt h
  have hmul : m * n <= m * y :=
    mul_le_mul_of_nonneg_left hny (le_of_lt hm)
  omega

end AffineProofTransport
