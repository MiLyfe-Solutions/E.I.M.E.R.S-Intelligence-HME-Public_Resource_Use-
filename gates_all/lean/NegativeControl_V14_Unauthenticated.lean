import CPOQEvidenceV14
open CPOQ
private def req : RecoveryRequest := ⟨101, 7, 31, 42, 5001, 9001⟩
private def bad : RecoveryEvidence := ⟨101, 7, 31, 42, 5001, 9001, false, true⟩
-- Intentionally false: authenticated does not satisfy the bound recovery request.
example : recoveryAccepted req bad = true := by decide
