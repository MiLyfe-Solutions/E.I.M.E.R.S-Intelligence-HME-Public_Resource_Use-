/-
  Reusable finite-step descent principle.

  Lean core only; no Mathlib dependency.
-/

namespace FiniteStepDescent

/-- `iterate f k x` applies `f` exactly `k` times to `x`. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => iterate f k (f x)

/--
If every block strictly lowers a natural-valued rank above a target, then
repeating the block finitely many times reaches rank at most that target.

The result is about the supplied `block` and `rank`. It does not assert that
an arbitrary system has such a rank or that its dynamics satisfy `decrease`.
-/
theorem finite_step_descent
    {α : Type}
    (rank : α → Nat)
    (block : α → α)
    (target : Nat)
    (decrease : ∀ x, target < rank x → rank (block x) < rank x)
    (x : α) :
    ∃ k, rank (iterate block k x) ≤ target := by
  have auxiliary : ∀ m, ∀ x, rank x = m →
      ∃ k, rank (iterate block k x) ≤ target := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hx
      by_cases hsmall : rank x ≤ target
      · exact ⟨0, by simpa [iterate] using hsmall⟩
      · have habove : target < rank x := Nat.lt_of_not_ge hsmall
        have hnext : rank (block x) < m := by
          rw [← hx]
          exact decrease x habove
        obtain ⟨k, hk⟩ := ih (rank (block x)) hnext (block x) rfl
        exact ⟨k + 1, by simpa [iterate] using hk⟩
  exact auxiliary (rank x) x rfl

/--
Finite-step form of the result. If a fixed finite number of step transitions
strictly lowers the rank whenever the state is above the target, then
repeating that finite block eventually reaches the target region.
-/
theorem fixed_length_step_descent
    {α : Type}
    (rank : α → Nat)
    (step : α → α)
    (blockLength target : Nat)
    (decrease : ∀ x, target < rank x →
      rank (iterate step blockLength x) < rank x)
    (x : α) :
    ∃ blocks,
      rank (iterate (fun y => iterate step blockLength y) blocks x) ≤ target := by
  exact finite_step_descent
    rank
    (fun y => iterate step blockLength y)
    target
    decrease
    x

/--
Affine comparison lemma used by the final inequality step in uniform
finite-descent arguments: a scaled upper bound below `scale * n` forces the
unscaled endpoint to be strictly below `n`.
-/
theorem strict_descent_from_affine_bound
    {n y scale slope offset : Nat}
    (hbound : scale * y ≤ slope * n + offset)
    (hmargin : slope * n + offset < scale * n) :
    y < n := by
  by_contra hnot
  have hny : n ≤ y := Nat.le_of_not_gt hnot
  have hscaled : scale * n ≤ scale * y := Nat.mul_le_mul_left scale hny
  exact (Nat.not_le_of_gt hmargin) (Nat.le_trans hscaled hbound)

end FiniteStepDescent
