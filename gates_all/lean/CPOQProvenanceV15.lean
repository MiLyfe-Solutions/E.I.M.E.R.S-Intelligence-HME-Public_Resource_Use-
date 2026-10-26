import CPOQEvidenceV14

namespace CPOQ
/-! v2.15: trust-root and signature-verification RESULT binding.
    `signatureVerified` is an external verifier's result, NOT a Lean proof
    of real cryptographic signature verification or of an actual effect. -/
structure TrustedRecoveryRequest where
  recovery : RecoveryRequest
  expectedIssuer : Nat
  expectedKeyId : Nat
  expectedTrustEpoch : Nat
  expectedPayloadDigest : Nat
  expectedAudience : Nat
  deriving DecidableEq, Repr

structure ProvenanceEvidence where
  recovery : RecoveryEvidence
  issuer : Nat
  keyId : Nat
  trustEpoch : Nat
  payloadDigest : Nat
  audience : Nat
  signatureVerified : Bool
  keyActive : Bool
  issuerAuthorized : Bool
  algorithmAllowed : Bool
  deriving DecidableEq, Repr

def ProvenanceBound (r : TrustedRecoveryRequest) (e : ProvenanceEvidence) : Prop :=
  EvidenceBound r.recovery e.recovery ∧
  e.issuer = r.expectedIssuer ∧
  e.keyId = r.expectedKeyId ∧
  e.trustEpoch = r.expectedTrustEpoch ∧
  e.payloadDigest = r.expectedPayloadDigest ∧
  e.audience = r.expectedAudience ∧
  e.signatureVerified = true ∧
  e.keyActive = true ∧
  e.issuerAuthorized = true ∧
  e.algorithmAllowed = true

instance (r : TrustedRecoveryRequest) (e : ProvenanceEvidence) : Decidable (ProvenanceBound r e) := by
  unfold ProvenanceBound
  infer_instance

def provenanceAccepted (r : TrustedRecoveryRequest) (e : ProvenanceEvidence) : Bool :=
  decide (ProvenanceBound r e)

theorem accepted_implies_provenance_bound (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : ProvenanceBound r e := by
  exact of_decide_eq_true h

theorem provenance_requires_evidence_bound (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : EvidenceBound r.recovery e.recovery := by
  exact (accepted_implies_provenance_bound r e h).1

theorem provenance_requires_issuer (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : e.issuer = r.expectedIssuer := by
  exact (accepted_implies_provenance_bound r e h).2.1

theorem provenance_requires_key (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : e.keyId = r.expectedKeyId := by
  exact (accepted_implies_provenance_bound r e h).2.2.1

theorem provenance_requires_trust_epoch (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : e.trustEpoch = r.expectedTrustEpoch := by
  exact (accepted_implies_provenance_bound r e h).2.2.2.1

theorem provenance_requires_payload_digest (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : e.payloadDigest = r.expectedPayloadDigest := by
  exact (accepted_implies_provenance_bound r e h).2.2.2.2.1

theorem provenance_requires_verified_signature (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : e.signatureVerified = true := by
  exact (accepted_implies_provenance_bound r e h).2.2.2.2.2.2.1

theorem provenance_requires_authorized_issuer (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (h : provenanceAccepted r e = true) : e.issuerAuthorized = true := by
  exact (accepted_implies_provenance_bound r e h).2.2.2.2.2.2.2.2.1

end CPOQ
