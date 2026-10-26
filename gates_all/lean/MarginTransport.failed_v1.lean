import Lean

namespace CPOQ

/-
  CPOQ Margin Transport
  Generic arithmetic layer.

  IMPORTANT:
  These lemmas do NOT prove Collatz convergence.
  Application to Collatz requires separately checked
  valuation-word and domain/boundary hypotheses.
-/

/-- Affine descent margin. -/
def margin (M A n C : Int) : Int :=
  (M - A) * n - C

/-- Transport defect. -/
def defect (M A T dC : Int) : Int :=
  (M - A) * T - dC

/--
Exact affine-margin transport identity.

D'(n+T,C+dC) = D(n,C) + E
where E = (M-A)T-dC.
-/
theorem affine_margin_transport_identity
    (M A n C T dC : Int) :
    margin M A (n + T) (C + dC)
      =
    margin M A n C + defect M A T dC := by
  simp [margin, defect]
  omega

/--
If the transported total margin is positive,
the target affine margin is positive.
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
A sufficient reusable guard:
positive source margin plus nonnegative defect
implies positive target margin.
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
  simp [defect]
  omega

/--
Two successive transports collapse to one accumulated
translation and one accumulated constant difference.
-/
theorem affine_margin_transport_compose
    (M A n C T₁ T₂ dC₁ dC₂ : Int) :
    margin M A (n + T₁ + T₂) (C + dC₁ + dC₂)
      =
    margin M A n C +
      defect M A T₁ dC₁ +
      defect M A T₂ dC₂ := by
  simp [margin, defect]
  omega

/--
One shared affine tail step multiplies the difference
between two affine constants by 3.

This is the algebraic heart of the common-tail cocycle.
-/
theorem common_tail_constant_difference_step
    (C C' B : Int) :
    (3 * C' + B) - (3 * C + B)
      =
    3 * (C' - C) := by
  omega

/--
Generic scalar version of the shared-tail difference step.
-/
theorem common_tail_constant_difference_scalar
    (a C C' B : Int) :
    (a * C' + B) - (a * C + B)
      =
    a * (C' - C) := by
  simp
  omega

end CPOQ
