/-- A small, standalone formalization candidate of a pressure threshold gate.
    This is a generic mathematical control law, NOT the canonical Eimers catalog.
    Preserve your original pressure/context definitions before replacing this adapter. -/
namespace EIMERS

structure PressureState where
  failurePressure : Nat
  allowedThreshold : Nat
  evidenceValid : Bool
  permissionValid : Bool

/-- Authorization requires valid evidence, permission, and pressure below threshold. -/
def authorized (s : PressureState) : Prop :=
  s.evidenceValid = true ∧ s.permissionValid = true ∧
  s.failurePressure < s.allowedThreshold

/-- Exceeding the threshold cannot authorize action. -/
theorem threshold_veto (s : PressureState)
    (h : s.allowedThreshold ≤ s.failurePressure) : ¬ authorized s := by
  intro ha
  exact Nat.not_lt_of_ge h ha.2.2

/-- Missing evidence cannot authorize action. -/
theorem evidence_veto (s : PressureState)
    (h : s.evidenceValid = false) : ¬ authorized s := by
  intro ha
  rw [h] at ha
  exact Bool.false_ne_true ha.1

/-- Missing permission cannot authorize action. -/
theorem permission_veto (s : PressureState)
    (h : s.permissionValid = false) : ¬ authorized s := by
  intro ha
  rw [h] at ha
  exact Bool.false_ne_true ha.2.1

end EIMERS
