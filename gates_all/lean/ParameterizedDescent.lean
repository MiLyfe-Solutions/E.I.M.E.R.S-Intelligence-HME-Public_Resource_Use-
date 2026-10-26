/- V173 standalone conditional algebra lemma. NOT COMPILED in the package build.
   It does NOT prove a Collatz termination theorem or establish a valuation word. -/
import Mathlib
namespace CollatzResearch

/-- The affine block endpoint is strictly below its source when its
    numerator is strictly smaller than the scaled source. -/
theorem affine_descent (n y P C Q : Nat)
    (hQ : 0 < Q)
    (heq : Q * y = P * n + C)
    (hbound : P * n + C < Q * n) : y < n := by
  have hmul : Q * y < Q * n := by omega
  exact (Nat.mul_lt_mul_left hQ).mp hmul

/-- Convenient criterion using subtraction, with positive contraction gap. -/
theorem affine_descent_from_gap (n y P C Q : Nat)
    (hQ : 0 < Q)
    (hP : P < Q)
    (heq : Q * y = P * n + C)
    (hgap : C < (Q - P) * n) : y < n := by
  apply affine_descent n y P C Q hQ heq
  have hh : Q = P + (Q - P) := by omega
  rw [hh]
  calc
    P * n + C < P * n + (Q - P) * n := Nat.add_lt_add_left hgap _
    _ = (P + (Q - P)) * n := by ring
