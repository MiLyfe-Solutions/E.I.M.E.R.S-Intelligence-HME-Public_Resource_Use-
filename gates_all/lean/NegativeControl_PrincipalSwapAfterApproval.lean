import CPOQFormalTheoryV2
open CPOQ

def principalDecision : DecisionBinding := {
  principal := 1001, tenantId := 7, operationLevel := 2, environmentLevel := 1,
  requestId := 9001, stateVersion := 100, dependencyEpoch := 40, authorityEpoch := 42,
  receiptId := 7001, nonce := 5001
}

def principalSwapAttempt : ExecutionAttempt := {
  principal := 2002, tenantId := 7, operationLevel := 2, environmentLevel := 1,
  requestId := 9001, stateVersion := 100, dependencyEpoch := 40, authorityEpoch := 42,
  receiptId := 7001, nonce := 5001, nonceUnused := true
}

example : ExecutionBoundToDecision principalDecision principalSwapAttempt := by
  unfold ExecutionBoundToDecision
  decide
