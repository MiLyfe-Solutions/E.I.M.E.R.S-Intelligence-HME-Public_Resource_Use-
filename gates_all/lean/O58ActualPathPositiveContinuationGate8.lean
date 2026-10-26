import Lean.Elab.Tactic.Omega
import CPOQ.O58PositiveWordBoundGate7
import CPOQ.O58ActualPathWitness001

namespace CPOQ

/-- Exact structural encoding of a nonempty positive valuation word.
    The indices retain total excess above one valuation bit per step and the
    affine constant used by Gate 7. -/
inductive ContinuationWordData : List Nat -> Nat -> Nat -> Prop where
  | one (d : Nat) : ContinuationWordData [d + 1] d 1
  | cons {w : List Nat} {e C : Nat} (d : Nat) :
      ContinuationWordData w e C ->
      ContinuationWordData ((d + 1) :: w) (d + e)
        (3^(w.length) + 2^(d + 1) * C)

/-- A one-step exact accelerated transition from an odd source has positive
    valuation.  The output is already required to be odd by
    `ActualExactAccelStep`. -/
theorem actualExactAccelStep_valuation_positive
    {x y : Int} {a : Nat}
    (hodd : x % 2 = 1)
    (hstep : ActualExactAccelStep x y a) :
    0 < a := by
  cases a with
  | zero =>
      unfold ActualExactAccelStep at hstep
      rcases hstep with ⟨hxy, hyodd⟩
      simp at hxy
      omega
  | succ d =>
      omega

/-- The word-data certificate has exactly the valuation sum encoded by its
    length plus excess. -/
theorem continuationWordData_sum
    {w : List Nat} {e C : Nat}
    (h : ContinuationWordData w e C) :
    w.sum = w.length + e := by
  induction h with
  | one d =>
      simp [Nat.add_comm]
  | @cons w e C d h ih =>
      simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The word-data encoding and Gate 7's positive-continuation encoding are the
    same recurrence, so every exact word-data certificate yields the generic
    Gate-7 certificate without enumerating the word. -/
theorem continuationWordData_to_positiveContinuation
    {w : List Nat} {e C : Nat}
    (h : ContinuationWordData w e C) :
    PositiveContinuation w.length e C := by
  induction h with
  | one d =>
      simpa using (PositiveContinuation.one d)
  | @cons w e C d h ih =>
      simpa using (PositiveContinuation.cons d ih)

/-- Every nonempty actual accelerated path starting at an odd integer exports
    exact positive word data.  This is the actual-path -> compressed-word
    adapter. -/
theorem actualAccelPath_to_continuationWordData
    {x z : Int} {w : List Nat}
    (hodd : x % 2 = 1)
    (hpath : ActualAccelPath x w z) :
    w ≠ [] -> exists e C, ContinuationWordData w e C := by
  induction hpath with
  | nil x =>
      intro hne
      exact False.elim (hne rfl)
  | @cons x y z a w hstep htail ih =>
      intro _hne
      have ha : 0 < a := actualExactAccelStep_valuation_positive hodd hstep
      have h1 : 1 <= a := ha
      let d : Nat := a - 1
      have had : d + 1 = a := by
        dsimp [d]
        exact Nat.sub_add_cancel h1
      have hyodd : y % 2 = 1 := by
        exact hstep.2
      cases w with
      | nil =>
          refine ⟨d, 1, ?_⟩
          simpa [had] using (ContinuationWordData.one d)
      | cons b ws =>
          have htailne : (b :: ws) ≠ [] := by simp
          obtain ⟨e, C, hdata⟩ := ih hyodd htailne
          refine ⟨d + e, 3^((b :: ws).length) + 2^(d + 1) * C, ?_⟩
          simpa [had] using (ContinuationWordData.cons d hdata)

/-- Actual path to the exact Gate-7 certificate, with word-data retained for
    auditability and exact mass/threshold accounting. -/
theorem actualAccelPath_to_positiveContinuation
    {x z : Int} {w : List Nat}
    (hodd : x % 2 = 1)
    (hpath : ActualAccelPath x w z)
    (hne : w ≠ []) :
    exists e C,
      ContinuationWordData w e C /\
      PositiveContinuation w.length e C := by
  obtain ⟨e, C, hdata⟩ :=
    actualAccelPath_to_continuationWordData hodd hpath hne
  exact ⟨e, C, hdata, continuationWordData_to_positiveContinuation hdata⟩

/-- If the real valuation sum clears a threshold `length + t`, the actual path
    automatically supplies Gate 7's normalized constant bound, now expressed
    directly in Gate 6's `NormalizedConstantBound` predicate. -/
theorem actualAccelPath_to_gate6_normalized_bound
    {x z : Int} {w : List Nat}
    (hodd : x % 2 = 1)
    (hpath : ActualAccelPath x w z)
    (hne : w ≠ [])
    (t : Nat)
    (hthreshold : w.length + t <= w.sum) :
    exists e C,
      ContinuationWordData w e C /\
      NormalizedConstantBound
        (2^(w.length + e))
        (2^(w.length + t))
        (positiveWordEnvelope w.length t)
        C := by
  obtain ⟨e, C, hdata, hpos⟩ :=
    actualAccelPath_to_positiveContinuation hodd hpath hne
  have hsum : w.sum = w.length + e := continuationWordData_sum hdata
  have hte : t <= e := by
    rw [hsum] at hthreshold
    omega
  refine ⟨e, C, hdata, ?_⟩
  exact positiveContinuation_to_gate6_normalized_bound hpos hte

end CPOQ
