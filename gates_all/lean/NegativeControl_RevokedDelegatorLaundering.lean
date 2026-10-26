import CPOQFormalTheoryV2
open CPOQ

def revokedDelegator : DelegationEdge := {
  parentPrincipal := 1001
  childPrincipal := 2002
  parentEnvelope := { tenantId := 7, maxOperationLevel := 3, maxEnvironmentLevel := 2 }
  childEnvelope := { tenantId := 7, maxOperationLevel := 2, maxEnvironmentLevel := 1 }
  parentStatus := ReuseStatus.revoked
}

-- Scope narrows correctly, but a revoked parent cannot delegate live authority.
example : ValidDelegationEdge revokedDelegator := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor <;> decide
