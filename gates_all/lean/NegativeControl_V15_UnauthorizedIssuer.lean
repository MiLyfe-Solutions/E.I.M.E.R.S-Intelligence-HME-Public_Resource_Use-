import CPOQProvenanceV15
open CPOQ
private def req : TrustedRecoveryRequest :=
  ⟨⟨101, 7, 31, 42, 5001, 9001⟩, 70, 80, 11, 123456, 501⟩
private def bad : ProvenanceEvidence :=
  ⟨⟨101, 7, 31, 42, 5001, 9001, true, true⟩,
   70, 80, 11, 123456, 501, true, true, false, true⟩
-- Deliberately false; the provenance gate must reject this case.
example : provenanceAccepted req bad = true := by decide
