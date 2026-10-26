import CPOQFormalTheoryV2
open CPOQ

def circularRoot : RootAuthority := {
  principal := 1001
  envelope := { tenantId := 7, maxOperationLevel := 2, maxEnvironmentLevel := 1 }
  status := ReuseStatus.revoked
}

-- A <-> B delegation story cannot bootstrap authority from a root that is not independently active.
-- The attack tries to assert the necessary root validity anyway.
example : RootAuthorityValid circularRoot := by
  rfl
