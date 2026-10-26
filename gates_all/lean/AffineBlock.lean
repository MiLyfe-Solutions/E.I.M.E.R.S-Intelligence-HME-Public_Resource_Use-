import CPOQ.CommonTail

namespace CPOQ

def affineBlock
    (S k : Nat)
    (n x C : Int) : Prop :=
  (2 : Int)^S * x =
    (3 : Int)^k * n + C

def oddStepRelation
    (a : Nat)
    (x y : Int) : Prop :=
  (2 : Int)^a * y =
    3*x + 1


theorem mul_three_assoc
    (p x : Int) :
    p * (3*x) = 3*(p*x) := by

  calc
    p * (3*x)
        =
      (p*3)*x := by
        rw [Int.mul_assoc]

    _ =
      (3*p)*x := by
        rw [Int.mul_comm p 3]

    _ =
      3*(p*x) := by
        rw [Int.mul_assoc]


theorem scale_three_plus_one
    (p x : Int) :
    p * (3*x + 1)
      =
    3*(p*x) + p := by

  rw [Int.mul_add]

  rw [mul_three_assoc]

  omega


theorem three_pow_product
    (k : Nat)
    (n : Int) :
    3 * ((3 : Int)^k * n)
      =
    (3 : Int)^k * (3*n) := by

  calc
    3 * ((3 : Int)^k * n)
        =
      (3 * (3 : Int)^k) * n := by
        rw [Int.mul_assoc]

    _ =
      ((3 : Int)^k * 3) * n := by
        rw [Int.mul_comm 3 ((3 : Int)^k)]

    _ =
      (3 : Int)^k * (3*n) := by
        rw [Int.mul_assoc]


/--
Affine Collatz block extension.

If

    2^S*x = 3^k*n + C

and

    2^a*y = 3*x + 1,

then

    2^(S+a)*y
      =
    3^(k+1)*n + (3*C + 2^S).
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

  have h2pow :
      (2 : Int)^(S + a)
        =
      (2 : Int)^S * (2 : Int)^a := by
    simp [Int.pow_add]

  have h3pow :
      (3 : Int)^(k + 1)
        =
      (3 : Int)^k * 3 := by
    simp [Int.pow_succ]

  rw [h2pow]
  rw [h3pow]

  calc
    ((2 : Int)^S * (2 : Int)^a) * y
        =
      (2 : Int)^S * ((2 : Int)^a * y) := by
        rw [Int.mul_assoc]

    _ =
      (2 : Int)^S * (3*x + 1) := by
        rw [hstep]

    _ =
      3*((2 : Int)^S*x) + (2 : Int)^S := by
        exact scale_three_plus_one ((2 : Int)^S) x

    _ =
      3*((3 : Int)^k*n + C) + (2 : Int)^S := by
        rw [hblock]

    _ =
      3*((3 : Int)^k*n)
        + (3*C + (2 : Int)^S) := by
        rw [Int.mul_add]
        omega

    _ =
      (3 : Int)^k*(3*n)
        + (3*C + (2 : Int)^S) := by
        rw [three_pow_product]

    _ =
      ((3 : Int)^k*3)*n
        + (3*C + (2 : Int)^S) := by
        rw [Int.mul_assoc]


theorem affineBlock_constant_delta_step
    (S : Nat)
    (C C' : Int) :
    (3*C' + (2 : Int)^S)
      -
    (3*C + (2 : Int)^S)
      =
    3*(C' - C) := by

  exact
    common_tail_constant_difference_step
      C C' ((2 : Int)^S)


end CPOQ
