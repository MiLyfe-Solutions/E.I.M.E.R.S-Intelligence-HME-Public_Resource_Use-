import CPOQFormalTheoryV2
open CPOQ

def expiredApproval : ApprovalReceipt := {
  approvalId := 9001
  issuedAuthorityEpoch := 42
  validFrom := 100
  validThrough := 150
  status := ApprovalStatus.active
}

/-- Forbidden shortcut: a genuinely issued but expired approval is treated as current. -/
theorem forbidden_expired_approval_replay : ApprovalValidAt expiredApproval 151 := by
  constructor
  · decide
  · decide
