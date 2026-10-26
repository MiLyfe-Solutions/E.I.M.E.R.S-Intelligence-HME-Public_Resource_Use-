/-
Affine Margin Transport theorem skeleton.
STATUS: DRAFT ONLY — NOT KERNEL CHECKED IN THIS ENVIRONMENT.
Intended for the user's pinned Lean 4.35.0 project after copying into an additive isolated proof directory.
Universal Collatz remains HOLD_UNPROVEN.
-/

-- Suggested import in the target project:
-- import Mathlib

namespace AffineProofTransport

/-- Affine descent margin for an equation m*y = a*n + C. -/
def margin (m a n C : Int) : Int := (m - a) * n - C

/-- Translating the source by T and changing the affine constant by dC
    changes the margin by exactly (m-a)T-dC. -/
theorem affine_margin_transport_identity
    (m a n C T dC : Int) :
    margin m a (n + T) (C + dC)
      = margin m a n C + ((m - a) * T - dC) := by
  unfold margin
  ring

/-- Guarded positivity transport.  Exact state conjugacy is unnecessary;
    it is enough that the transported margin stays positive. -/
theorem affine_margin_transport_positive
    (m a n C T dC : Int)
    (hpos : 0 < margin m a n C + ((m - a) * T - dC)) :
    0 < margin m a (n + T) (C + dC) := by
  rw [affine_margin_transport_identity]
  exact hpos

/-- Common-tail constant cocycle.
    If two affine constants differ by dC at a cut point and every later
    recurrence updates C <- a*C + B with the same multiplier a and same B,
    then after r shared tail steps the defect is a^r*dC.
    This scalar form is the algebraic core; a list/word version is the next layer. -/
theorem common_tail_constant_cocycle_scalar
    (a C C' B : Int) :
    (a * C' + B) - (a * C + B) = a * (C' - C) := by
  ring

end AffineProofTransport
