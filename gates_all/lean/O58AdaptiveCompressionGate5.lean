import CPOQ.O58InfiniteClassLiftGate2
import Lean.Elab.Tactic.Omega

namespace CPOQ

/-- A continuation budget envelope.  This is deliberately a guard theorem: later path machinery must prove the actual continuation endpoint satisfies the envelope. -/
def BudgetEnvelopeL01 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^3 * y <= (3 : Int)^1 * seg33x46 q + (1 : Int)

/-- Any endpoint under the L=1, S>=3 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l01 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL01 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL01, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL02 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^5 * y <= (3 : Int)^2 * seg33x46 q + (19 : Int)

/-- Any endpoint under the L=2, S>=5 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l02 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL02 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL02, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL03 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^6 * y <= (3 : Int)^3 * seg33x46 q + (89 : Int)

/-- Any endpoint under the L=3, S>=6 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l03 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL03 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL03, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL04 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^8 * y <= (3 : Int)^4 * seg33x46 q + (635 : Int)

/-- Any endpoint under the L=4, S>=8 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l04 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL04 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL04, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL05 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^9 * y <= (3 : Int)^5 * seg33x46 q + (2161 : Int)

/-- Any endpoint under the L=5, S>=9 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l05 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL05 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL05, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL06 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^11 * y <= (3 : Int)^6 * seg33x46 q + (13747 : Int)

/-- Any endpoint under the L=6, S>=11 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l06 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL06 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL06, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL07 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^13 * y <= (3 : Int)^7 * seg33x46 q + (85849 : Int)

/-- Any endpoint under the L=7, S>=13 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l07 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL07 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL07, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL08 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^14 * y <= (3 : Int)^8 * seg33x46 q + (265739 : Int)

/-- Any endpoint under the L=8, S>=14 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l08 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL08 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL08, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL09 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^16 * y <= (3 : Int)^9 * seg33x46 q + (1620641 : Int)

/-- Any endpoint under the L=9, S>=16 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l09 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL09 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL09, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL10 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^17 * y <= (3 : Int)^10 * seg33x46 q + (4927459 : Int)

/-- Any endpoint under the L=10, S>=17 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l10 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL10 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL10, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL11 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^19 * y <= (3 : Int)^11 * seg33x46 q + (29767849 : Int)

/-- Any endpoint under the L=11, S>=19 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l11 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL11 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL11, seg33x46, seg33x00] at h ⊢
  omega

def BudgetEnvelopeL12 (q : Nat) (y : Int) : Prop :=
  (2 : Int)^20 * y <= (3 : Int)^12 * seg33x46 q + (89827835 : Int)

/-- Any endpoint under the L=12, S>=20 worst-case envelope lies below the original parent-cylinder start. -/
theorem o58_segment33_budget_guard_l12 (q : Nat) (y : Int)
    (h : BudgetEnvelopeL12 q y) : y < seg33x00 q := by
  simp [BudgetEnvelopeL12, seg33x46, seg33x00] at h ⊢
  omega

end CPOQ
