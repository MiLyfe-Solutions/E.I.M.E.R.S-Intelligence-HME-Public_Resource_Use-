import CPOQVerifierV16
open CPOQ
private def req : TrustedRecoveryRequest :=
  ⟨⟨101, 7, 31, 42, 5001, 9001⟩, 70, 80, 11, 123456, 501⟩
private def evidence : ProvenanceEvidence :=
  ⟨⟨101, 7, 31, 42, 5001, 9001, true, true⟩,
   70, 80, 11, 123456, 501, true, true, true, true⟩
private def policy : VerifierPolicy := ⟨400, 401, 12, 88888, 5001, 42⟩
private def good : VerifierAttestation :=
  ⟨400, 401, 12, 88888, 5001, 42, true, true, true, true⟩
private def bad : VerifierAttestation := {good with authorityEpoch := 41}
example : attestedRecoveryAccepted req evidence policy bad = true := by decide
