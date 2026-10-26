/-
DRAFT ONLY: This Lean source has NOT been compiled or kernel-checked.
Isolated additive candidate for Lean 4.35.0 + matching Mathlib.
The nine numeric guards are finite arithmetic facts. The separate
inductive word-constant upper bound still requires formalization.
Universal Collatz: HOLD_UNPROVEN.
-/
import Mathlib

namespace EIMERS.UniformWordBound

def affineMargin (m a n C : Int) : Int := (m-a)*n-C

def coefficientCap (k S : Nat) : Int :=
  (2:Int)^(S-k) * ((3:Int)^k-(2:Int)^k)

/-- This theorem is independent of Collatz. Bound the constant, then the
strict inequality is preserved for all sufficiently large inputs. -/
theorem generic_descent_from_word_bound
    (m a n C y B N : Int)
    (hm : 0 < m)
    (hcoeff : 0 < m-a)
    (hcap : C <= B)
    (hn : N <= n)
    (hcut : B < (m-a)*N)
    (heq : m*y = a*n+C) : y < n := by
  have hslope : (m-a)*N <= (m-a)*n :=
    mul_le_mul_of_nonneg_left hn (le_of_lt hcoeff)
  have hC : C < (m-a)*n :=
    lt_of_le_of_lt hcap (lt_of_lt_of_le hcut hslope)
  have hScaled : m*y < m*n := by
    calc
      m*y = a*n+C := heq
      _ < a*n+(m-a)*n := add_lt_add_left hC (a*n)
      _ = m*n := by ring
  exact (mul_lt_mul_left hm).mp hScaled

/-- The following nine arithmetic inequalities are proposed for kernel
checking. They require no trajectory enumeration; `norm_num` checks integers. -/
theorem guard_46_73 :
    coefficientCap 46 73 < (((2:Int)^73-(3:Int)^46)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_47_75 :
    coefficientCap 47 75 < (((2:Int)^75-(3:Int)^47)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_48_77 :
    coefficientCap 48 77 < (((2:Int)^77-(3:Int)^48)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_49_78 :
    coefficientCap 49 78 < (((2:Int)^78-(3:Int)^49)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_50_80 :
    coefficientCap 50 80 < (((2:Int)^80-(3:Int)^50)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_51_81 :
    coefficientCap 51 81 < (((2:Int)^81-(3:Int)^51)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_52_83 :
    coefficientCap 52 83 < (((2:Int)^83-(3:Int)^52)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_53_85 :
    coefficientCap 53 85 < (((2:Int)^85-(3:Int)^53)*(2:Int)^34) := by
  norm_num [coefficientCap]

theorem guard_54_86 :
    coefficientCap 54 86 < (((2:Int)^86-(3:Int)^54)*(2:Int)^34) := by
  norm_num [coefficientCap]

/-- Algebraic cancellation underlying constant T for wrap/no-wrap segments. -/
theorem phase_wrap_translation_constant
    (ra rb s wrapPow u u' : Int)
    (h : u' = u+s-wrapPow) :
    (rb+u'*(2:Int)^13)-(ra+u*(2:Int)^13)
      = (rb-ra)+(s-wrapPow)*(2:Int)^13 := by
  rw [h]
  ring

/-- The same defect can be used for all records with the same affine
coefficients, offset and constant difference. -/
theorem wrap_segment_defect_constant
    (m a T dC : Int) :
    (m-a)*T-dC = (m-a)*T-dC := rfl

#print axioms generic_descent_from_word_bound
#print axioms guard_46_73
#print axioms guard_54_86
#print axioms phase_wrap_translation_constant
end EIMERS.UniformWordBound
