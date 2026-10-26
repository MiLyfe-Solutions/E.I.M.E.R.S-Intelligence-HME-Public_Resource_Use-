import CPOQ.CommonTail

namespace CPOQ

/--
An affine Collatz block relation:

    2^S * x = 3^k * n + C

represented abstractly over Int.
-/
def affineBlock
    (S k : Nat)
    (n x C : Int) : Prop :=
  (2 : Int)^S * x =
    (3 : Int)^k * n + C


/--
One accelerated odd Collatz step relation:

    2^a * y = 3*x + 1.
-/
def oddStepRelation
    (a : Nat)
    (x y : Int) : Prop :=
  (2 : Int)^a * y = 3*x + 1


/--
Extending a valid affine block by one accelerated odd step
updates the affine constant by

    C_next = 3*C + 2^S.
-/
theorem affineBlock_extend
    (S k a : Nat)
    (n x y C : Int)
    (hblock : affineBlock S k n x C)
    (hstep : oddStepRelation a x y) :
    (2 : Int)^(S + a) * y
      =
    (3 : Int)^(k + 1) * n
      +
    (3*C + (2 : Int)^S) := by

  unfold affineBlock at hblock
  unfold oddStepRelation at hstep

  rw [Int.pow_add]
  rw [Int.pow_add]

  simp only [Int.pow_one]

  calc
    (2 : Int)^S * (2 : Int)^a * y
        =
      (2 : Int)^S * ((2 : Int)^a * y) := by
          rw [Int.mul_assoc]

    _ =
      (2 : Int)^S * (3*x + 1) := by
          rw [hstep]

    _ =
      3 * ((2 : Int)^S * x) + (2 : Int)^S := by
          ring

    _ =
      3 * ((3 : Int)^k * n + C) + (2 : Int)^S := by
          rw [hblock]

    _ =
      ((3 : Int)^k * 3) * n +
        (3*C + (2 : Int)^S) := by
          ring


/--
If two affine constants enter the same next affine update
with the same current exponent S, their difference is
multiplied by exactly 3.
-/
theorem affineBlock_constant_delta_step
    (S : Nat)
    (C C' : Int) :
    (3*C' + (2 : Int)^S)
      -
    (3*C + (2 : Int)^S)
      =
    3 * (C' - C) := by

  exact
    common_tail_constant_difference_step
      C C' ((2 : Int)^S)


end CPOQ
