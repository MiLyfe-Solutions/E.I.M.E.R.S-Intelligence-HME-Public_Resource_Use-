import CPOQFormalTheoryV2
open CPOQ

def epochCertificate : Certificate Unit := {
  guard := fun _ => True
  claim := fun _ => True
  sound := by intro _ _; trivial
}

def epochManaged : ManagedCertificate Unit := {
  generation := 7
  certificate := epochCertificate
  status := ReuseStatus.active
}

def epochBoundDependency : BoundDependency Unit := {
  requiredCertificateId := 7007
  presented := { certificateId := 7007, managed := epochManaged }
}

def epochScopedDependency : ScopedDependency Unit := {
  dependency := epochBoundDependency
  authorizedScope := { tenantId := 1, operationId := 10, environmentId := 100 }
}

def epochScopedRequest : ScopedRequest := {
  requestedScope := { tenantId := 1, operationId := 10, environmentId := 100 }
}

def staleEpochApproval : ApprovalReceipt := {
  approvalId := 9004
  issuedAuthorityEpoch := 41
  validFrom := 100
  validThrough := 200
  status := ApprovalStatus.active
}

/-- The underlying v2.8 authority side is deliberately clean. -/
theorem epoch_attack_scope_is_clean :
    ScopedDependencyReusableAt epochScopedDependency epochScopedRequest 7 () := by
  constructor
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · trivial
  · rfl

/-- Forbidden shortcut: exact certificate, identity, generation and scope plus a genuine
    active/in-window approval from epoch 41 are treated as authority in epoch 42. -/
theorem forbidden_stale_authority_epoch_replay :
    AuthorityEpochBound staleEpochApproval 42 := by
  rfl
