import CPOQEvidenceV14
open CPOQ
private def req : RecoveryRequest := ⟨101, 7, 31, 42, 5001, 9001⟩
private def good : RecoveryEvidence := ⟨101, 7, 31, 42, 5001, 9001, true, true⟩
example : recoveryAccepted req good = true := by decide
example : EvidenceBound req good := by decide
example : recoveryAccepted req good = true → good.operationId = req.operationId := by
  intro h
  exact accepted_implies_operation_match req good h
