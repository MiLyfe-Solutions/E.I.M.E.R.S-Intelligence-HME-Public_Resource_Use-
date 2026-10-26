/-!
General finite-block progress, independent of Collatz arithmetic.
Research artifact. Requires actual Lean checking before it may be labeled VERIFIED.
-/
import Mathlib

namespace PGX.FiniteBlock

/-- Strict rank descent of a block implies that a finite number of blocks
    reaches rank zero. This is a model-only logical statement. -/
theorem reaches_zero_blocks {S : Type} (block : S → S) (rank : S → Nat)
    (desc : ∀ s, 0 < rank s → rank (block s) < rank s) (s : S) :
    ∃ m, m ≤ rank s ∧ rank ((block^[m]) s) = 0 := by
  have aux : ∀ n : Nat, ∀ t : S, rank t = n →
      ∃ m, m ≤ n ∧ rank ((block^[m]) t) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht
      by_cases hz : rank t = 0
      · refine ⟨0, Nat.zero_le n, ?_⟩
        simpa using hz
      · have hp : 0 < rank t := Nat.pos_of_ne_zero hz
        have hlt : rank (block t) < n := by
          rw [← ht]
          exact desc t hp
        obtain ⟨m, hm, heq⟩ := ih _ hlt (block t) rfl
        refine ⟨m + 1, by omega, ?_⟩
        simpa only [Function.iterate_succ_apply] using heq
  exact aux (rank s) s rfl

/-- Fixed k-block descent yields a terminal point by <= k*rank(s)
    abstract steps, for a state whose terminal predicate means rank=0.
    No wall-clock, fairness, concurrency, or executable refinement guarantee. -/
theorem reaches_terminal {S : Type} (step : S → S) (rank : S → Nat)
    (k : Nat) (desc : ∀ s, 0 < rank s → rank ((step^[k]) s) < rank s)
    (s : S) : ∃ m, m ≤ rank s ∧ rank ((step^[k * m]) s) = 0 := by
  obtain ⟨m, hm, hzero⟩ :=
    reaches_zero_blocks (step^[k]) rank desc s
  refine ⟨m, hm, ?_⟩
  simpa only [Function.iterate_mul] using hzero

/-- A finite-block affine inequality suffices for rank descent when the
    rank-dependent gap exceeds the additive term. -/
theorem affine_implies_descent {S : Type} (step : S → S) (rank : S → Nat)
    (k M a b : Nat) (s : S) (ha : a < M)
    (hgap : b < (M - a) * rank s)
    (hbound : M * rank ((step^[k]) s) ≤ a * rank s + b) :
    rank ((step^[k]) s) < rank s := by
  have hsum : a + (M - a) = M := Nat.add_sub_of_le (Nat.le_of_lt ha)
  have hlt : M * rank ((step^[k]) s) < M * rank s := by
    calc
      M * rank ((step^[k]) s) ≤ a * rank s + b := hbound
      _ < a * rank s + (M - a) * rank s := Nat.add_lt_add_left hgap _
      _ = (a + (M - a)) * rank s := by ring
      _ = M * rank s := by rw [hsum]
  exact Nat.lt_of_mul_lt_mul_left hlt

#print axioms reaches_zero_blocks
#print axioms reaches_terminal
#print axioms affine_implies_descent

end PGX.FiniteBlock
