import CPOQ.MarginTransport

namespace CPOQ

/-
  Common-tail affine-constant transport.

  A shared affine tail applies the same recurrence

      C ↦ 3*C + B

  to two starting constants.

  The theorem below proves that after r shared steps,
  their difference is multiplied by 3^r.

  This remains a generic arithmetic theorem.
  A Collatz application separately requires proof that
  the two trajectories really share the claimed tail.
-/

/-- One shared affine recurrence step. -/
def tailStep (B C : Int) : Int :=
  3 * C + B

/--
Apply a list of shared additive constants.

Each list element represents one common affine-tail step.
-/
def sharedTail : List Int → Int → Int
  | [], C => C
  | B :: Bs, C => sharedTail Bs (tailStep B C)

/--
One shared step multiplies the difference by 3.
-/
theorem tailStep_difference
    (B C C' : Int) :
    tailStep B C' - tailStep B C
      =
    3 * (C' - C) := by
  unfold tailStep
  exact common_tail_constant_difference_step C C' B

/--
REAL COMMON-TAIL INDUCTION THEOREM.

After r identical affine-tail steps, represented by Bs,
the difference between the resulting affine constants is

    3^(length Bs) * (C' - C).
-/
theorem sharedTail_difference
    (Bs : List Int)
    (C C' : Int) :
    sharedTail Bs C' - sharedTail Bs C
      =
    (3 : Int) ^ Bs.length * (C' - C) := by
  induction Bs generalizing C C' with

  | nil =>
      simp [sharedTail]

  | cons B Bs ih =>
      simp only [sharedTail, List.length_cons]

      rw [ih]

      unfold tailStep

      rw [tailStep_difference]

      rw [pow_succ]

      omega

/--
Specialized r-step statement when only the tail length
and initial difference are needed.
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
