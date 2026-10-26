import Lean

namespace CPOQ

/-
  CPOQ Margin Transport — minimal Lean 4 core version.

  Scope:
  Generic exact integer arithmetic only.

  This does NOT establish universal Collatz convergence.
  Collatz application requires independently checked
  valuation-word, boundary, and domain hypotheses.
-/

def margin (M A n C : Int) : Int :=
  (M - A) * n - C

def defect (M A T dC : Int) : Int :=
  (M - A) * T - dC


/-
Distributivity helper.

We expose this explicitly because Presburger automation
does not reason through multiplication of two variables.
-/
theorem mul_add_exact
    (a b c : Int) :
    a * (b + c) = a * b + a * c := by
  exact Int.mul_add a b c


/--
Exact affine-margin transport identity:

D'(n+T,C+dC) = D(n,C) + E
-/
theorem affine_margin_transport_identity
    (M A n C T dC : Int) :
    margin M A (n + T) (C + dC)
      =
    margin M A n C + defect M A T dC := by

  unfold margin defect

  rw [Int.mul_add]

  omega


/--
Positive transported total margin implies
positive target margin.
-/
theorem affine_margin_transport_positive
    (M A n C T dC : Int)
    (h :
      0 <
        margin M A n C +
        defect M A T dC) :
    0 < margin M A (n + T) (C + dC) := by

  rw [affine_margin_transport_identity]
  exact h


/--
Useful sufficient condition:

source margin > 0
and
transport defect >= 0

imply target margin > 0.
-/
theorem affine_margin_transport_nonnegative_defect
    (M A n C T dC : Int)
    (hD : 0 < margin M A n C)
    (hE : 0 <= defect M A T dC) :
    0 < margin M A (n + T) (C + dC) := by

  rw [affine_margin_transport_identity]
  omega


/--
Transport defects compose additively.
-/
theorem defect_compose
    (M A T₁ T₂ dC₁ dC₂ : Int) :
    defect M A (T₁ + T₂) (dC₁ + dC₂)
      =
    defect M A T₁ dC₁ +
    defect M A T₂ dC₂ := by

  unfold defect

  rw [Int.mul_add]

  omega


/--
Two transports collapse into one accumulated
margin equation.
-/
theorem affine_margin_transport_compose
    (M A n C T₁ T₂ dC₁ dC₂ : Int) :
    margin M A (n + T₁ + T₂) (C + dC₁ + dC₂)
      =
    margin M A n C +
      defect M A T₁ dC₁ +
      defect M A T₂ dC₂ := by

  unfold margin defect

  rw [Int.mul_add]
  rw [Int.mul_add]

  omega


/--
One shared Collatz affine-tail step multiplies
the affine-constant difference by 3.
-/
theorem common_tail_constant_difference_step
    (C C' B : Int) :
    (3 * C' + B) - (3 * C + B)
      =
    3 * (C' - C) := by

  rw [Int.mul_sub]
  omega


/--
Generic shared affine-tail step.

If both constants undergo C ↦ a*C+B,
their difference becomes a*(C'-C).
-/
theorem common_tail_constant_difference_scalar
    (a C C' B : Int) :
    (a * C' + B) - (a * C + B)
      =
    a * (C' - C) := by

  rw [Int.mul_sub]
  omega


end CPOQ
