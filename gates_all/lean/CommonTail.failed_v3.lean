import CPOQ.MarginTransport

namespace CPOQ

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
After an arbitrary shared affine tail Bs,

  ΔC_final = 3^(length Bs) * ΔC_initial.

Generic arithmetic theorem only.

A Collatz application separately requires proof that
both trajectories actually realize the same valuation tail.
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

      change
        sharedTail Bs (tailStep B C') -
          sharedTail Bs (tailStep B C)
        =
        (3 : Int) ^ (Bs.length + 1) * (C' - C)

      rw [ih]

      rw [tailStep_difference]

      change
        (3 : Int) ^ Bs.length *
            (3 * (C' - C))
        =
        (3 : Int) ^ (Bs.length + 1) *
            (C' - C)

      have hpow :
          (3 : Int) ^ (Bs.length + 1)
            =
          (3 : Int) ^ Bs.length * 3 := by

        simp [Int.pow_succ]

      rw [hpow]

      omega


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
