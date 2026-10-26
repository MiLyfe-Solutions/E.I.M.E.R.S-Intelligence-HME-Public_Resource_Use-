import CPOQ.O58AdaptiveCompressionGate5

namespace CPOQ

/-- Generic arithmetic certificate connecting an exact continuation block to a
    pre-computed budget envelope.  `powS` and `powT` are explicit so this lemma
    does not need nonlinear normalization tactics. -/
structure ContinuationBudgetCertificate
    (x y : Nat) (powS powT threePow D C : Nat) : Prop where
  powT_le_powS : powT <= powS
  affine : powS * y = threePow * x + C
  scaled_const : powT * C <= powS * D

/-- Generic path-to-budget algebra: an exact affine continuation plus a
    normalized affine-constant bound implies the budget envelope. -/
theorem continuation_budget_bridge
    (x y powS powT threePow D C : Nat)
    (hpowS : 0 < powS)
    (h : ContinuationBudgetCertificate x y powS powT threePow D C) :
    powT * y <= threePow * x + D := by
  have hmain : powS * (powT * y) <= powS * (threePow * x + D) := by
    calc
      powS * (powT * y) = powT * (powS * y) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = powT * (threePow * x + C) := by rw [h.affine]
      _ = powT * (threePow * x) + powT * C := by simp [Nat.mul_add]
      _ <= powS * (threePow * x) + powS * D := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_right (threePow * x) h.powT_le_powS)
          h.scaled_const
      _ = powS * (threePow * x + D) := by simp [Nat.mul_add]
  exact Nat.le_of_mul_le_mul_left hmain hpowS

/-- The scaled-constant condition is the only remaining generic combinatorial
    obligation after the algebraic bridge above. -/
def NormalizedConstantBound (powS powT D C : Nat) : Prop :=
  powT * C <= powS * D

/-- Boundary theorem documenting the exact remaining obligation. -/
theorem continuation_budget_bridge_from_components
    (x y powS powT threePow D C : Nat)
    (hpowS : 0 < powS)
    (hpow : powT <= powS)
    (haff : powS * y = threePow * x + C)
    (hconst : NormalizedConstantBound powS powT D C) :
    powT * y <= threePow * x + D := by
  apply continuation_budget_bridge x y powS powT threePow D C hpowS
  exact {
    powT_le_powS := hpow
    affine := haff
    scaled_const := hconst
  }

end CPOQ
