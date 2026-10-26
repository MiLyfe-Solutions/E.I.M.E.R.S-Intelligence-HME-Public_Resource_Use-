import Mathlib

namespace O58CylinderGate

/-- If an affine block is valid at a canonical base, its scaled identity
    is valid for a proposed lifted endpoint. The statement does NOT certify
    that the proposed endpoint is an actual Collatz iterate. -/
theorem affine_block_lift_identity
    (m a n0 y0 C u : Int)
    (hbase : m * y0 = a * n0 + C) :
    m * (y0 + a * u) = a * (n0 + m * u) + C := by
  calc
    m * (y0 + a * u) = m * y0 + m * (a * u) := by ring
    _ = a * (n0 + m * u) + C := by rw [hbase]; ring

/-- Conditional whole-cylinder descent: a valid affine identity, base descent,
    positive lift slope, and nonnegative lift imply descent of each proposed
    endpoint. Fixed-word validity remains a separate proof obligation. -/
theorem affine_lift_strict_descent
    (m a n0 y0 u : Int)
    (hbase : y0 < n0)
    (hslope : a < m)
    (hu : 0 <= u) :
    y0 + a * u < n0 + m * u := by
  have hmul : 0 <= (m - a) * u := mul_nonneg (le_of_lt (sub_pos.mpr hslope)) hu
  nlinarith

/-- Integer-scaled contraction; if `Q*y0 < P*n0` and `Q*a <= P*m`,
    every nonnegative lifted endpoint also obeys the same strict ratio.
    This separates quantified contraction from mere descent. -/
theorem affine_lift_scaled_contraction
    (P Q m a n0 y0 u : Int)
    (hbase : Q * y0 < P * n0)
    (hslope : Q * a <= P * m)
    (hu : 0 <= u) :
    Q * (y0 + a * u) < P * (n0 + m * u) := by
  have hmul : 0 <= (P * m - Q * a) * u :=
    mul_nonneg (sub_nonneg.mpr hslope) hu
  nlinarith

end O58CylinderGate

#print axioms O58CylinderGate.affine_block_lift_identity
#print axioms O58CylinderGate.affine_lift_strict_descent
#print axioms O58CylinderGate.affine_lift_scaled_contraction
