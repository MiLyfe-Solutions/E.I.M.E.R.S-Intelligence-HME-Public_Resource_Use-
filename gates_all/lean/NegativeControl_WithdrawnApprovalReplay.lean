import CPOQFormalTheoryV2
open CPOQ

def withdrawnApproval : ApprovalReceipt := {
  approvalId := 9002
  issuedAuthorityEpoch := 42
  validFrom := 100
  validThrough := 200
  status := ApprovalStatus.withdrawn
}

/-- Forbidden shortcut: a withdrawn approval is treated as active. -/
theorem forbidden_withdrawn_approval_replay : ApprovalActive withdrawnApproval := by
  rfl
