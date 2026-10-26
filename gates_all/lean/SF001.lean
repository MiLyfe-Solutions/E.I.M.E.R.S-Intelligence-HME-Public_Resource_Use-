import Mathlib

namespace SF001

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, s => s
  | k + 1, s => f (iterate f k s)

theorem iterate_add {α : Type} (f : α → α) (a b : Nat) (s : α) :
    iterate f (a + b) s = iterate f b (iterate f a s) := by
  induction b with
  | zero => simp [iterate]
  | succ b ih => simpa [iterate, Nat.add_succ] using congrArg f ih

/-- If every nonterminal state admits a positive finite block reducing a
natural-number rank, a terminal state is reached in finitely many steps.
No assertion is made about arbitrary programs or arbitrary transition rules. -/
theorem finite_block_reaches_terminal {α : Type} (f : α → α)
    (rank : α → Nat) (terminal : α → Prop)
    (progress : ∀ s, ¬ terminal s →
      ∃ k : Nat, 0 < k ∧ rank (iterate f k s) < rank s) :
    ∀ s, ∃ steps : Nat, terminal (iterate f steps s) := by
  intro s
  suffices h : ∀ r : Nat, ∀ x : α, rank x = r →
    ∃ steps : Nat, terminal (iterate f steps x) by
    exact h (rank s) s rfl
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro x hx
    by_cases ht : terminal x
    · exact ⟨0, by simpa [iterate] using ht⟩
    · obtain ⟨k, _, hdec⟩ := progress x ht
      have hlt : rank (iterate f k x) < r := by simpa [← hx] using hdec
      obtain ⟨n, hn⟩ := ih _ hlt (iterate f k x) rfl
      exact ⟨k + n, by simpa [iterate_add] using hn⟩

/-- A non-Collatz two-phase countdown: each unit of work passes through
ready and committed phases. Work is never increased. -/
def phaseStep : Nat × Bool → Nat × Bool
  | (n, true) => (n, false)
  | (0, false) => (0, false)
  | (n + 1, false) => (n, true)

def phaseRank (s : Nat × Bool) : Nat :=
  2 * s.1 + if s.2 then 1 else 0

def phaseTerminal (s : Nat × Bool) : Prop := s = (0, false)

theorem phase_two_step_progress (s : Nat × Bool) (h : ¬ phaseTerminal s) :
    phaseRank (iterate phaseStep 2 s) < phaseRank s := by
  rcases s with ⟨n, b⟩
  cases n with
  | zero =>
    cases b <;> simp_all [phaseTerminal, phaseRank, phaseStep, iterate]
  | succ n =>
    cases b <;> simp_all [phaseTerminal, phaseRank, phaseStep, iterate] <;> omega

theorem phase_eventually_terminal (s : Nat × Bool) :
    ∃ steps : Nat, phaseTerminal (iterate phaseStep steps s) := by
  apply finite_block_reaches_terminal phaseStep phaseRank phaseTerminal
  intro x hx
  exact ⟨2, by decide, phase_two_step_progress x hx⟩

#print axioms SF001.finite_block_reaches_terminal
#print axioms SF001.phase_two_step_progress
#print axioms SF001.phase_eventually_terminal
end SF001
