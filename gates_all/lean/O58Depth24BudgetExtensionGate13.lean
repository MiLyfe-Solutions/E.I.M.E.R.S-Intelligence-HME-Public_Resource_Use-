import Lean.Elab.Tactic.Omega
import CPOQ.O58FinalIntBudgetCompositionGate10

namespace CPOQ

/-- Gate 13 extension: length 13, total valuation sum at least 22. -/
def BudgetEnvelopeL13 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^22 * y <= (3 : Int)^13 * seg33x46 q + (540532721 : Int)

theorem gate13_envelope_l13 : positiveWordEnvelope 13 9 = 540532721 := by decide

theorem o58_segment33_budget_guard_l13 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL13 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL13, seg33x46, seg33x00] at h ⊢
  omega

theorem o58_segment33_actual_path_descent_l13
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 13)
    (hsum : 22 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := by
    intro hw
    rw [hw] at hlen
    simp at hlen
  have hthreshold : w.length + 9 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 9 hthreshold
  have hg : BudgetEnvelopeL13 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL13, gate13_envelope_l13] using hb
  exact o58_segment33_budget_guard_l13 q y hg

/-- Gate 13 extension: length 14, total valuation sum at least 24. -/
def BudgetEnvelopeL14 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^24 * y <= (3 : Int)^14 * seg33x46 q + (3249990611 : Int)

theorem gate13_envelope_l14 : positiveWordEnvelope 14 10 = 3249990611 := by decide

theorem o58_segment33_budget_guard_l14 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL14 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL14, seg33x46, seg33x00] at h ⊢
  omega

theorem o58_segment33_actual_path_descent_l14
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 14)
    (hsum : 24 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := by
    intro hw
    rw [hw] at hlen
    simp at hlen
  have hthreshold : w.length + 10 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 10 hthreshold
  have hg : BudgetEnvelopeL14 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL14, gate13_envelope_l14] using hb
  exact o58_segment33_budget_guard_l14 q y hg

end CPOQ
