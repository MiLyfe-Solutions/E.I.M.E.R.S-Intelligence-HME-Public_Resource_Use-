import Mathlib

namespace CPOQH22

-- A reusable whole-family affine margin contract.
theorem affine_margin_positive (c slope u : Nat)
    (hc : 0 < c) : 0 < c + slope * u := by
  omega

-- General family-wise descent; the transported words still need their own semantic guards.
theorem affine_family_descent
    (x0 y0 stride ystride u : Nat)
    (hbase : y0 < x0)
    (hslope : ystride <= stride) :
    y0 + ystride * u < x0 + stride * u := by
  have hmul := Nat.mul_le_mul_right u hslope
  omega

-- Explicit multiplicative helper repairing the missing nonlinear reasoning in H19.
theorem affine_bound_repair
    (bound x0 y0 stride ystride u : Nat)
    (hbase : 3 * y0 + 1 < bound * x0)
    (hslope : 3 * ystride <= bound * stride) :
    3 * (y0 + ystride * u) + 1 < bound * (x0 + stride * u) := by
  have hmul := Nat.mul_le_mul_right u hslope
  nlinarith [hmul]

-- Lower-bound valuation property, requiring a certified source-specific bound.
theorem valuation_lower_bound_descent
    (bound x y z : Nat)
    (hboundpos : 0 < bound)
    (hstep : bound * z <= 3*y+1)
    (hmargin : 3*y+1 < bound*x) : z < x := by
  have h : bound*z < bound*x := lt_of_le_of_lt hstep hmargin
  exact (Nat.mul_lt_mul_left hboundpos).mp h

#print axioms affine_margin_positive
#print axioms affine_family_descent
#print axioms affine_bound_repair
#print axioms valuation_lower_bound_descent
end CPOQH22
