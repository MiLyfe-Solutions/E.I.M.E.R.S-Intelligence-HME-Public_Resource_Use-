import Mathlib

namespace CPOQSemantics

/-- An exact accelerated odd Collatz step: 3*x+1 is divided by exactly 2^v,
    because the resulting quotient y is odd. -/
def ExactStep (x y v : Nat) : Prop :=
  0 < x ∧ (∃ t : Nat, x = 2*t+1) ∧
  2^v * y = 3*x+1 ∧ (∃ t : Nat, y = 2*t+1)

/-- An exact step remains exact after shifting its odd input by a multiple
    of 2^(v+1). The output shifts by 6*d. -/
theorem exact_step_transport (x y v d : Nat)
    (h : ExactStep x y v) :
    ExactStep (x + 2^(v+1)*d) (y+6*d) v := by
  rcases h with ⟨hx, ⟨a, ha⟩, heq, ⟨b, hb⟩⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · refine ⟨a + 2^v*d, ?_⟩
    rw [ha, pow_succ]
    ring
  · rw [pow_succ]
    nlinarith [heq]
  · refine ⟨b+3*d, ?_⟩
    rw [hb]
    ring

/-- Exact valuation cannot be increased: the quotient after 2^v is odd. -/
theorem exact_step_quotient_odd (x y v : Nat)
    (h : ExactStep x y v) : ∃ t : Nat, y = 2*t+1 := by
  exact h.2.2.2

#print axioms exact_step_transport
#print axioms exact_step_quotient_odd
end CPOQSemantics
