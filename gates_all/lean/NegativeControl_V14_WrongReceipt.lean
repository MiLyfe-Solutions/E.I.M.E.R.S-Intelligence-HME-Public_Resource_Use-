import CPOQEvidenceV14
open CPOQ
private def req : RecoveryRequest := ⟨101, 7, 31, 42, 5001, 9001⟩
private def bad : RecoveryEvidence := ⟨101, 7, 31, 42, 5001, 9002, true, true⟩
-- Intentionally false: receiptId does not satisfy the bound recovery request.
example : recoveryAccepted req bad = true := by decide
