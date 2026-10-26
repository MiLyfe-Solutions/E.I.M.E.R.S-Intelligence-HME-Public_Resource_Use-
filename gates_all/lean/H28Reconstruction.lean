import H28TraceAppend

namespace H28Affine
open CollatzResearch

/-- Once the affine equation supplies divisibility by three, the terminal
    predecessor is uniquely reconstructed in natural arithmetic. -/
theorem reconstruct_terminal_from_divisibility
    (A B T : Nat) (hA : 0 < A) (hT : 0 < T)
    (h : A * T = 3 * B + A)
    (hdiv : 3 ∣ T - 1) :
    ∃ z : Nat, 3 * z + 1 = T ∧ A * z = B := by
  obtain ⟨z, hz⟩ := hdiv
  have hT1 : T = T - 1 + 1 := by omega
  refine ⟨z, ?_, ?_⟩
  · omega
  · omega

/-- A reconstructed terminal state is an exact odd step once the
    endpoint is odd and the exponent is positive. -/
theorem reconstructed_exact_step (b z y : Nat)
    (hb : 0 < b) (hy : y % 2 = 1)
    (hstep : 3 * z + 1 = 2 ^ b * y) :
    ExactOddStep b z y := by
  exact ⟨predecessor_odd_of_step hb hstep, hy, hb, hstep⟩

/-- The remaining arithmetic bottleneck is coprime cancellation:
    derive the required divisibility from the snoc affine equation. -/
theorem terminal_divisibility_of_coprime
    (A B T : Nat) (hA : 0 < A) (hT : 0 < T)
    (h : A * T = 3 * B + A)
    (hcop : Nat.Coprime A 3) :
    3 ∣ T - 1 := by
  have hsub : A * (T - 1) = 3 * B := by
    omega
  have hprod : 3 ∣ A * (T - 1) := by
    rw [hsub]
    exact dvd_mul_right 3 B
  exact (hcop.symm.dvd_mul_left).mp hprod

#print axioms H28Affine.reconstruct_terminal_from_divisibility
#print axioms H28Affine.reconstructed_exact_step
#print axioms H28Affine.terminal_divisibility_of_coprime
end H28Affine
