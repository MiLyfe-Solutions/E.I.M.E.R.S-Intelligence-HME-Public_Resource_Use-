import CPOQFormalTheoryV2
open CPOQ

def preRevocationApproval : ApprovalReceipt := {
  approvalId := 9003
  issuedAuthorityEpoch := 41
  validFrom := 100
  validThrough := 200
  status := ApprovalStatus.active
}

/-- Forbidden shortcut: an approval issued before authority revocation/epoch advance is
    treated as bound to the post-revocation authority epoch. -/
theorem forbidden_pre_revocation_approval_replay :
    AuthorityEpochBound preRevocationApproval 42 := by
  rfl
