/-! AUTO-GENERATED from AUGL-PGX two-phase model.
    Translation is NOT itself formally verified; proof checking requires Lean.
    Do not edit: run python -m pgx.compiler instead. -/
import Mathlib
import FiniteBlock

namespace PGX.Generated

structure WorkState where
  work : Nat
  phase : Bool
  deriving DecidableEq, Repr

def step (s : WorkState) : WorkState :=
  if s.work = 0 then s
  else if s.phase then ⟨s.work - 4, false⟩
  else ⟨s.work + 3, true⟩

def rank (s : WorkState) : Nat := s.work

def terminal (s : WorkState) : Prop := s.work = 0

/-- Every nonterminal state strictly decreases its work rank after two steps.
    This says nothing about actual scheduler or application semantics. -/
theorem two_phase_strict (s : WorkState) (h : 0 < rank s) :
    rank ((step^[2]) s) < rank s := by
  rcases s with ⟨n, phase⟩
  cases phase <;> simp only [rank, step, Function.iterate_succ_apply,
    Function.iterate_zero_apply] at *
  all_goals split_ifs <;> omega

/-- A non-Collatz application of the abstract finite-block termination result. -/
theorem two_phase_eventual_terminal (s : WorkState) :
    ∃ blocks, blocks ≤ rank s ∧
      terminal ((step^[2 * blocks]) s) := by
  obtain ⟨blocks, hblocks, hzero⟩ :=
    PGX.FiniteBlock.reaches_terminal step rank 2 two_phase_strict s
  exact ⟨blocks, hblocks, hzero⟩

#print axioms two_phase_strict
#print axioms two_phase_eventual_terminal

end PGX.Generated
