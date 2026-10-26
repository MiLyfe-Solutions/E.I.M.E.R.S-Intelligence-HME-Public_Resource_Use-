import FamilyDescent

namespace H28Certificate

open CollatzResearch

/-- Computed successor for a proposed accelerated valuation. -/
def nextOdd (a x : Nat) : Nat := (3 * x + 1) / 2 ^ a

/-- One Boolean certificate for a complete finite valuation word.
    The checker still verifies each exact transition computationally. -/
def checkWord : List Nat → Nat → Nat → Bool
  | [], x, y => decide (x = y)
  | a :: rest, x, y =>
      decide (ExactOddStep a x (nextOdd a x)) &&
        checkWord rest (nextOdd a x) y

/-- Soundness bridge to the already existing `WordTrace` definition.
    This does NOT claim affine-only compression or global Collatz convergence. -/
theorem checkWord_sound (word : List Nat) (x y : Nat)
    (h : checkWord word x y = true) : WordTrace word x y := by
  induction word generalizing x with
  | nil =>
      have heq : x = y := of_decide_eq_true (by simpa [checkWord] using h)
      simpa [WordTrace] using heq.symm
  | cons a rest ih =>
      have hp : decide (ExactOddStep a x (nextOdd a x)) = true ∧
          checkWord rest (nextOdd a x) y = true := by
        cases hleft : decide (ExactOddStep a x (nextOdd a x)) <;>
          cases hright : checkWord rest (nextOdd a x) y <;>
          simp [checkWord, hleft, hright] at h ⊢
      have hs : ExactOddStep a x (nextOdd a x) := of_decide_eq_true hp.1
      exact ⟨nextOdd a x, hs, ih (nextOdd a x) hp.2⟩

end H28Certificate
