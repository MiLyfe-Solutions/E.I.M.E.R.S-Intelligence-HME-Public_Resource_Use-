import CPOQCrashV13

namespace CPOQ
/-! Modeled recovery evidence identity binding. A valid receipt is not necessarily
    evidence for this operation. This is a specification, not signature validation. -/
structure RecoveryRequest where
  operationId : Nat
  tenantId : Nat
  principalId : Nat
  authorityEpoch : Nat
  expectedCommitId : Nat
  expectedReceiptId : Nat
  deriving DecidableEq, Repr

structure RecoveryEvidence where
  operationId : Nat
  tenantId : Nat
  principalId : Nat
  authorityEpoch : Nat
  commitId : Nat
  receiptId : Nat
  authenticated : Bool
  committed : Bool
  deriving DecidableEq, Repr

def EvidenceBound (r : RecoveryRequest) (e : RecoveryEvidence) : Prop :=
  e.operationId = r.operationId ∧
  e.tenantId = r.tenantId ∧
  e.principalId = r.principalId ∧
  e.authorityEpoch = r.authorityEpoch ∧
  e.commitId = r.expectedCommitId ∧
  e.receiptId = r.expectedReceiptId ∧
  e.authenticated = true ∧
  e.committed = true

instance (r : RecoveryRequest) (e : RecoveryEvidence) : Decidable (EvidenceBound r e) := by
  unfold EvidenceBound
  infer_instance

def recoveryAccepted (r : RecoveryRequest) (e : RecoveryEvidence) : Bool :=
  decide (EvidenceBound r e)

theorem accepted_implies_bound (r : RecoveryRequest) (e : RecoveryEvidence)
    (h : recoveryAccepted r e = true) : EvidenceBound r e := by
  exact of_decide_eq_true h

theorem accepted_implies_operation_match (r : RecoveryRequest) (e : RecoveryEvidence)
    (h : recoveryAccepted r e = true) : e.operationId = r.operationId := by
  exact (accepted_implies_bound r e h).1

theorem accepted_implies_commit_match (r : RecoveryRequest) (e : RecoveryEvidence)
    (h : recoveryAccepted r e = true) : e.commitId = r.expectedCommitId := by
  rcases accepted_implies_bound r e h with ⟨_, _, _, _, hc, _, _, _⟩
  exact hc

theorem accepted_implies_receipt_match (r : RecoveryRequest) (e : RecoveryEvidence)
    (h : recoveryAccepted r e = true) : e.receiptId = r.expectedReceiptId := by
  rcases accepted_implies_bound r e h with ⟨_, _, _, _, _, hr, _, _⟩
  exact hr

theorem accepted_implies_authenticated (r : RecoveryRequest) (e : RecoveryEvidence)
    (h : recoveryAccepted r e = true) : e.authenticated = true := by
  rcases accepted_implies_bound r e h with ⟨_, _, _, _, _, _, ha, _⟩
  exact ha

theorem accepted_implies_committed (r : RecoveryRequest) (e : RecoveryEvidence)
    (h : recoveryAccepted r e = true) : e.committed = true := by
  rcases accepted_implies_bound r e h with ⟨_, _, _, _, _, _, _, hc⟩
  exact hc

end CPOQ
