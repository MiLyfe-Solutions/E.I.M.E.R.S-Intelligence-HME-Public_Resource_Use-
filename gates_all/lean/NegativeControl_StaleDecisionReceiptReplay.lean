import CPOQFormalTheoryV2
open CPOQ

def receiptDecision : DecisionBinding := {
  principal := 1001, tenantId := 7, operationLevel := 2, environmentLevel := 1,
  requestId := 9001, stateVersion := 100, dependencyEpoch := 40, authorityEpoch := 42,
  receiptId := 7001, nonce := 5001
}

def staleReceiptAttempt : ExecutionAttempt := {
  principal := 1001, tenantId := 7, operationLevel := 2, environmentLevel := 1,
  requestId := 9001, stateVersion := 100, dependencyEpoch := 40, authorityEpoch := 42,
  receiptId := 6999, nonce := 5001, nonceUnused := true
}

example : ExecutionBoundToDecision receiptDecision staleReceiptAttempt := by
  unfold ExecutionBoundToDecision
  decide
