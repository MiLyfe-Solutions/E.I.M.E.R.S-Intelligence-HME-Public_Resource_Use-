import FamilyDescent

/-!
Collatz reduction: lines 2 and 3 of the outline are proven here.
If every n > 1 eventually drops below itself (line 1, the open step),
then every n ≥ 1 reaches 1. Uses the engine's own `collatzStep`.
-/

namespace CollatzResearch

/-- Iterating the Collatz step `k` times. -/
def stepIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => stepIter k (collatzStep n)

theorem stepIter_add (a b n : Nat) :
    stepIter (a + b) n = stepIter b (stepIter a n) := by
  induction a generalizing n with
  | zero => simp [stepIter]
  | succ a ih =>
      rw [Nat.add_right_comm, stepIter, ih, stepIter]

/-- The open step (line 1), stated as a hypothesis. -/
def EveryNumberDrops : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, stepIter k n < n

/-- Collatz step never hits 0 from a positive number. -/
theorem collatzStep_pos (n : Nat) (h : 0 < n) : 0 < collatzStep n := by
  unfold collatzStep
  split <;> omega

theorem stepIter_pos (k n : Nat) (h : 0 < n) : 0 < stepIter k n := by
  induction k generalizing n with
  | zero => simpa [stepIter] using h
  | succ k ih => exact ih _ (collatzStep_pos n h)

/-- Lines 2 + 3: repeated dropping lands every positive number on 1. -/
theorem reaches_one_of_every_number_drops (hdrop : EveryNumberDrops) :
    ∀ n : Nat, 0 < n → ∃ k : Nat, stepIter k n = 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h1 : n = 1
    · exact ⟨0, by simp [stepIter, h1]⟩
    · have hgt : 1 < n := by omega
      obtain ⟨k, hk⟩ := hdrop n hgt
      have hpos := stepIter_pos k n hn
      obtain ⟨j, hj⟩ := ih (stepIter k n) hk hpos
      exact ⟨k + j, by rw [stepIter_add]; exact hj⟩

#print axioms reaches_one_of_every_number_drops

end CollatzResearch
