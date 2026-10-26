import Lean

namespace FiniteStepDescent

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => iterate f k (f x)

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
    induction m using Nat.strongRecOn with
    | ind m ih =>
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

theorem strict_descent_from_affine_bound
    {n y scale slope offset : Nat}
    (hbound : scale * y ≤ slope * n + offset)
    (hmargin : slope * n + offset < scale * n) :
    y < n := by
  refine Nat.lt_of_not_le (fun hny => ?_)
  have hscaled : scale * n ≤ scale * y := Nat.mul_le_mul_left scale hny
  exact (Nat.not_le_of_gt hmargin) (Nat.le_trans hscaled hbound)

end FiniteStepDescent
#print axioms FiniteStepDescent.finite_step_descent
#print axioms FiniteStepDescent.fixed_length_step_descent
#print axioms FiniteStepDescent.strict_descent_from_affine_bound
