import CPOQFormalTheoryV2
open CPOQ

def nonceDecision : DecisionBinding := {
  principal := 1001, tenantId := 7, operationLevel := 2, environmentLevel := 1,
  requestId := 9001, stateVersion := 100, dependencyEpoch := 40, authorityEpoch := 42,
  receiptId := 7001, nonce := 5001
}

def duplicateExecutionAttempt : ExecutionAttempt := {
  principal := 1001, tenantId := 7, operationLevel := 2, environmentLevel := 1,
  requestId := 9001, stateVersion := 100, dependencyEpoch := 40, authorityEpoch := 42,
  receiptId := 7001, nonce := 5001, nonceUnused := false
}

example : ExecutionBoundToDecision nonceDecision duplicateExecutionAttempt := by
  unfold ExecutionBoundToDecision
  decide
