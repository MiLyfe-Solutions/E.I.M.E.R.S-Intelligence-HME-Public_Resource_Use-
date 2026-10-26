import Lean.Elab.Tactic.Omega
import CPOQ.O58ActualPathPositiveContinuationGate8

namespace CPOQ

/-- The affine constant determined directly by a valuation word.  Its recurrence
    is the same recurrence already carried by Gate 8's `ContinuationWordData`. -/
def actualPathAffineConst : List Nat -> Nat
  | [] => 0
  | a :: w => 3^(w.length) + 2^a * actualPathAffineConst w

/-- Gate 8's compressed word certificate carries exactly the affine constant
    reconstructed directly from the valuation word. -/
theorem continuationWordData_const_eq_affineConst
    {w : List Nat} {e C : Nat}
    (h : ContinuationWordData w e C) :
    C = actualPathAffineConst w := by
  induction h with
  | one d =>
      simp [actualPathAffineConst]
  | @cons w e C d h ih =>
      simp [actualPathAffineConst, ih]

/-- Every actual accelerated Collatz path satisfies its exact affine endpoint
    identity.  This theorem uses only the path certificate itself; no search or
    representative sampling is involved. -/
theorem actualAccelPath_affine_endpoint
    {x z : Int} {w : List Nat}
    (hpath : ActualAccelPath x w z) :
    (2 : Int)^(w.sum) * z =
      (3 : Int)^(w.length) * x + (actualPathAffineConst w : Int) := by
  induction hpath with
  | nil x =>
      simp [actualPathAffineConst]
  | @cons x y z a w hstep htail ih =>
      have hs : 3 * x + 1 = (2 : Int)^a * y := hstep.1
      calc
        (2 : Int)^((a :: w).sum) * z
            = (2 : Int)^a * ((2 : Int)^(w.sum) * z) := by
                simp [Int.pow_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = (2 : Int)^a *
              ((3 : Int)^(w.length) * y + (actualPathAffineConst w : Int)) := by
                rw [ih]
        _ = (3 : Int)^(w.length) * ((2 : Int)^a * y) +
              (2 : Int)^a * (actualPathAffineConst w : Int) := by
                simp [Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = (3 : Int)^(w.length) * (3 * x + 1) +
              (2 : Int)^a * (actualPathAffineConst w : Int) := by
                rw [hs]
        _ = (3 : Int)^((a :: w).length) * x +
              (actualPathAffineConst (a :: w) : Int) := by
                simp [actualPathAffineConst, Int.pow_add, Int.add_mul,
                  Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm,
                  Int.add_assoc, Int.add_left_comm, Int.add_comm]

/-- The actual endpoint identity rewritten using the exact Gate-8 word-data
    indices.  The same `e` and `C` are therefore shared by Gates 8, 7, 6 and 9. -/
theorem actualAccelPath_affine_endpoint_from_wordData
    {x z : Int} {w : List Nat} {e C : Nat}
    (hpath : ActualAccelPath x w z)
    (hdata : ContinuationWordData w e C) :
    (2 : Int)^(w.length + e) * z =
      (3 : Int)^(w.length) * x + (C : Int) := by
  have h := actualAccelPath_affine_endpoint hpath
  have hsum : w.sum = w.length + e := continuationWordData_sum hdata
  have hC : C = actualPathAffineConst w :=
    continuationWordData_const_eq_affineConst hdata
  rw [hsum] at h
  rw [hC]
  exact h

/-- Gate 9 meeting theorem: one actual-path certificate simultaneously yields
    the exact Gate-8 word data, the Gate-6 normalized bound, and the exact
    affine endpoint identity with the same `e` and `C`. -/
theorem actualAccelPath_to_gate6_bound_and_affine_endpoint
    {x z : Int} {w : List Nat}
    (hodd : x % 2 = 1)
    (hpath : ActualAccelPath x w z)
    (hne : w ≠ [])
    (t : Nat)
    (hthreshold : w.length + t <= w.sum) :
    exists e C,
      ContinuationWordData w e C /\
      NormalizedConstantBound
        (2^(w.length + e))
        (2^(w.length + t))
        (positiveWordEnvelope w.length t)
        C /\
      (2 : Int)^(w.length + e) * z =
        (3 : Int)^(w.length) * x + (C : Int) := by
  obtain ⟨e, C, hdata, hbound⟩ :=
    actualAccelPath_to_gate6_normalized_bound hodd hpath hne t hthreshold
  refine ⟨e, C, hdata, hbound, ?_⟩
  exact actualAccelPath_affine_endpoint_from_wordData hpath hdata

end CPOQ
