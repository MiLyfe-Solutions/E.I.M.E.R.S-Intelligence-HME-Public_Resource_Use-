import CPOQ.MarginTransport

namespace CPOQ

/-
  CPOQ Common-Tail Transport

  Generic theorem:
  applying the same recurrence

      C ↦ 3*C + B

  to two affine constants for r shared steps multiplies
  their initial difference by 3^r.

  Collatz use still requires independent proof that the
  compared trajectories actually share the claimed tail.
-/

def tailStep (B C : Int) : Int :=
  3 * C + B

def sharedTail : List Int → Int → Int
  | [], C => C
  | B :: Bs, C => sharedTail Bs (tailStep B C)


theorem tailStep_difference
    (B C C' : Int) :
    tailStep B C' - tailStep B C
      =
    3 * (C' - C) := by

  unfold tailStep

  exact common_tail_constant_difference_step C C' B


/--
After an arbitrary list of identical affine-tail steps,
the difference between two resulting constants equals

    3^(number of shared steps) * initial difference.
-/
theorem sharedTail_difference
    (Bs : List Int)
    (C C' : Int) :
    sharedTail Bs C' - sharedTail Bs C
      =
    (3 : Int) ^ Bs.length * (C' - C) := by

  induction Bs generalizing C C' with

  | nil =>
      rfl

  | cons B Bs ih =>

      change
        sharedTail Bs (tailStep B C') -
          sharedTail Bs (tailStep B C)
        =
        (3 : Int) ^ (Bs.length + 1) * (C' - C)

      rw [ih]

      rw [tailStep_difference]

      rw [pow_succ]

      omega


/--
Version with an explicitly named initial difference.
Useful for compact CPOQ witnesses.
-/
theorem sharedTail_difference_eq_pow
    (Bs : List Int)
    (C C' Δ : Int)
    (hΔ : C' - C = Δ) :
    sharedTail Bs C' - sharedTail Bs C
      =
    (3 : Int) ^ Bs.length * Δ := by

  rw [sharedTail_difference]
  rw [hΔ]


end CPOQ
