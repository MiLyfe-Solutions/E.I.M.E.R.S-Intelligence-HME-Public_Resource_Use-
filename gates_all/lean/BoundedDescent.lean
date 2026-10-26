import FamilyDescent
import OrdinaryBridge

set_option linter.unusedSimpArgs false

namespace CollatzResearch

/-- Parameterized lift bits for the 24-bit bifurcation (59 + 24 = 83). -/
def LIFT_BITS : Nat := 83

/-- A word trace whose endpoint is bounded and whose sum satisfies the lift stability condition. -/
def BoundedWordTrace (W : List Nat) (x₀ : Nat) (bound : Nat) : Prop :=
  ∃ y, WordTrace W x₀ y ∧ y ≤ bound ∧ W.sum < LIFT_BITS

/-- Universal family descent theorem driven by a certified upper bound. -/
theorem family_descent_by_bound (W : List Nat) (x₀ : Nat) (bound : Nat) 
  (htrace : BoundedWordTrace W x₀ bound)
  (hcontract : 3^(W.length) < 2^(W.sum)) 
  (hbound : bound < x₀) : 
  ∀ u : Nat, ∃ endpoint, ordinaryRun (W.sum + W.length) (x₀ + u * 2^LIFT_BITS) = endpoint ∧ endpoint < x₀ + u * 2^LIFT_BITS := by
  intro u
  rcases htrace with ⟨y, hwt, hy_le, hstable⟩
  have hdescent : y < x₀ := by omega
  rcases family_descends W (b := LIFT_BITS) hwt hstable hcontract hdescent u with ⟨endpoint, htrace_u, hlt⟩
  refine ⟨endpoint, wordTrace_ordinary htrace_u, hlt⟩

#print axioms family_descent_by_bound

end CollatzResearch
