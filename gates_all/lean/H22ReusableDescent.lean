import Mathlib

namespace H22

/-- Repaired version of the H19 affine margin lemma. -/
theorem affine_margin_contract
    (x0 stride y0 ystride bound u : Nat)
    (h0 : 3*y0+1 < bound*x0)
    (hs : 3*ystride <= bound*stride) :
    3*(y0+ystride*u)+1 < bound*(x0+stride*u) := by
  calc
    3*(y0+ystride*u)+1 = (3*y0+1) + (3*ystride)*u := by ring
    _ < bound*x0 + (3*ystride)*u := Nat.add_lt_add_right h0 _
    _ <= bound*x0 + (bound*stride)*u :=
      Nat.add_le_add_left (Nat.mul_le_mul_right u hs) _
    _ = bound*(x0+stride*u) := by ring

/-- Affine endpoint descent for a transported family. -/
theorem transported_descent
    (x y sourceStride targetStride d : Nat)
    (hbase : y < x)
    (hslope : targetStride <= sourceStride) :
    y + targetStride*d < x + sourceStride*d := by
  have h := Nat.mul_le_mul_right d hslope
  omega

/-- A valuation lower bound suffices for descent without exact valuation. -/
theorem property_first_descent
    (x y z denominator : Nat)
    (hden : 0 < denominator)
    (hvaluation : denominator*z <= 3*y+1)
    (hmargin : 3*y+1 < denominator*x) : z < x := by
  have h : denominator*z < denominator*x := lt_of_le_of_lt hvaluation hmargin
  exact (Nat.mul_lt_mul_left hden).mp h

/-- An exact transported word plus a slope contract proves descent. -/
theorem word_transport_descent
    (x y S k d : Nat)
    (hbase : y < x)
    (hslope : 2*3^k <= 2^(S+1)) :
    y + 2*3^k*d < x + 2^(S+1)*d := by
  exact transported_descent x y (2^(S+1)) (2*3^k) d hbase hslope

#print axioms affine_margin_contract
#print axioms transported_descent
#print axioms property_first_descent
#print axioms word_transport_descent
end H22
