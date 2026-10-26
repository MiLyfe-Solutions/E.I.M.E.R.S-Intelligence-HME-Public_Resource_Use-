import CPOQProvenanceV15

namespace CPOQ
/-! v2.16: a separate, trusted verifier-attestation record must bind
    the exact request, evidence, verification policy, and verifier identity.
    `trustedChannel` and `verificationSucceeded` are ASSUMPTIONS/inputs;
    no cryptographic or independent implementation is verified here. -/
structure VerifierPolicy where
  verifierId : Nat
  verifierKeyId : Nat
  policyVersion : Nat
  evidenceDigest : Nat
  requestId : Nat
  authorityEpoch : Nat
  deriving DecidableEq, Repr

structure VerifierAttestation where
  verifierId : Nat
  verifierKeyId : Nat
  policyVersion : Nat
  evidenceDigest : Nat
  requestId : Nat
  authorityEpoch : Nat
  trustedChannel : Bool
  verifierAuthorized : Bool
  verificationSucceeded : Bool
  verifierKeyActive : Bool
  deriving DecidableEq, Repr

def AttestationBound (p : VerifierPolicy) (a : VerifierAttestation) : Prop :=
  a.verifierId = p.verifierId ∧
  a.verifierKeyId = p.verifierKeyId ∧
  a.policyVersion = p.policyVersion ∧
  a.evidenceDigest = p.evidenceDigest ∧
  a.requestId = p.requestId ∧
  a.authorityEpoch = p.authorityEpoch ∧
  a.trustedChannel = true ∧
  a.verifierAuthorized = true ∧
  a.verificationSucceeded = true ∧
  a.verifierKeyActive = true

instance (p : VerifierPolicy) (a : VerifierAttestation) : Decidable (AttestationBound p a) := by
  unfold AttestationBound
  infer_instance

def attestedRecoveryAccepted (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (p : VerifierPolicy) (a : VerifierAttestation) : Bool :=
  decide (ProvenanceBound r e ∧ AttestationBound p a)

theorem attested_acceptance_requires_provenance
    (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (p : VerifierPolicy) (a : VerifierAttestation)
    (h : attestedRecoveryAccepted r e p a = true) : ProvenanceBound r e := by
  have hb : ProvenanceBound r e ∧ AttestationBound p a := of_decide_eq_true h
  exact hb.1

theorem attested_acceptance_requires_attestation
    (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (p : VerifierPolicy) (a : VerifierAttestation)
    (h : attestedRecoveryAccepted r e p a = true) : AttestationBound p a := by
  have hb : ProvenanceBound r e ∧ AttestationBound p a := of_decide_eq_true h
  exact hb.2

theorem attested_acceptance_requires_trusted_channel
    (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (p : VerifierPolicy) (a : VerifierAttestation)
    (h : attestedRecoveryAccepted r e p a = true) : a.trustedChannel = true := by
  have hb := attested_acceptance_requires_attestation r e p a h
  exact hb.2.2.2.2.2.2.1

theorem attested_acceptance_requires_authorized_verifier
    (r : TrustedRecoveryRequest) (e : ProvenanceEvidence)
    (p : VerifierPolicy) (a : VerifierAttestation)
    (h : attestedRecoveryAccepted r e p a = true) : a.verifierAuthorized = true := by
  have hb := attested_acceptance_requires_attestation r e p a h
  exact hb.2.2.2.2.2.2.2.1

end CPOQ
