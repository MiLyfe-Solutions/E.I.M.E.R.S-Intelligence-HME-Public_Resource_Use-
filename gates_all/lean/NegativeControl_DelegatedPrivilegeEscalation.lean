import CPOQFormalTheoryV2
open CPOQ

def privilegeEscalation : DelegationEdge := {
  parentPrincipal := 1001
  childPrincipal := 2002
  parentEnvelope := { tenantId := 7, maxOperationLevel := 1, maxEnvironmentLevel := 1 }
  childEnvelope := { tenantId := 7, maxOperationLevel := 2, maxEnvironmentLevel := 1 }
  parentStatus := ReuseStatus.active
}

-- Child attempts operation level 2 from a parent capped at 1.
example : ValidDelegationEdge privilegeEscalation := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor <;> decide
