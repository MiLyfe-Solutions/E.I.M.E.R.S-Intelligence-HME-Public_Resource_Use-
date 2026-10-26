import CPOQFormalTheoryV2
open CPOQ

def scopeExpansion : DelegationEdge := {
  parentPrincipal := 1001
  childPrincipal := 2002
  parentEnvelope := { tenantId := 7, maxOperationLevel := 3, maxEnvironmentLevel := 1 }
  childEnvelope := { tenantId := 8, maxOperationLevel := 3, maxEnvironmentLevel := 2 }
  parentStatus := ReuseStatus.active
}

-- Child changes tenant and widens environment authority.
example : ValidDelegationEdge scopeExpansion := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor <;> decide
