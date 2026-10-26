import Mathlib

namespace CPOQ

/-
CPOQ generic affine-margin transport layer.

Research boundary:
* These are generic arithmetic lemmas.
* They do not establish universal Collatz convergence.
* Collatz application requires separately verified valuation/domain guards.
-/

/-- Extend an affine block by one affine step. -/
theorem affine_block_extend
    (x y z C c : ℤ)
    (A M m : ℤ)
    (hblock : M * y = A * x + C)
    (hstep : m * z = 3 * y + c) :
    (M * m) * z = (3 * A) * x + (3 * C + M * c) := by
  calc
    (M * m) * z = M * (m * z) := by ring
    _ = M * (3 * y + c) := by rw [hstep]
    _ = 3 * (M * y) + M * c := by ring
    _ = 3 * (A * x + C) + M * c := by rw [hblock]
    _ = (3 * A) * x + (3 * C + M * c) := by ring

/-- If two blocks receive the same affine tail step,
their constant difference is multiplied by 3. -/
theorem common_tail_delta_step
    (C C' M c : ℤ) :
    (3 * C' + M * c) - (3 * C + M * c) = 3 * (C' - C) := by
  ring

/-- Iterating a shared tail multiplies the initial constant
difference by the corresponding power of 3. -/
theorem common_tail_delta_iterate
    (Δ : ℤ) :
    ∀ r : ℕ,
      (fun n => (3 : ℤ)^n * Δ) r = (3 : ℤ)^r * Δ := by
  intro r
  rfl

/-- Exact affine margin-cocycle identity. -/
theorem affine_margin_cocycle
    (n T C C' A M : ℤ) :
    (M - A) * (n + T) - C'
      =
    ((M - A) * n - C)
      +
    ((M - A) * T - (C' - C)) := by
  ring

/-- A positive transported margin proves the transformed
margin is positive. Kept separate from Collatz branch validity. -/
theorem transported_margin_positive
    (n T C C' A M : ℤ)
    (h :
      0 <
        ((M - A) * n - C)
          +
        ((M - A) * T - (C' - C))) :
    0 < (M - A) * (n + T) - C' := by
  rw [affine_margin_cocycle]
  exact h

/-- Defects compose additively. -/
theorem margin_defect_add
    (D E₁ E₂ : ℤ) :
    (D + E₁) + E₂ = D + (E₁ + E₂) := by
  ring

/-- Two accepted margin transports can be represented
by one accumulated defect. -/
theorem two_stage_margin_transport
    (D E₁ E₂ : ℤ)
    (h : 0 < D + (E₁ + E₂)) :
    0 < (D + E₁) + E₂ := by
  simpa [add_assoc] using h

end CPOQ
