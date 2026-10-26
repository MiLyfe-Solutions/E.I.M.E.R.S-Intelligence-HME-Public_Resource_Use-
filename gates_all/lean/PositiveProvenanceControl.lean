import CPOQProvenanceV15
open CPOQ
private def req : TrustedRecoveryRequest :=
  ⟨⟨101, 7, 31, 42, 5001, 9001⟩, 70, 80, 11, 123456, 501⟩
private def good : ProvenanceEvidence :=
  ⟨⟨101, 7, 31, 42, 5001, 9001, true, true⟩,
   70, 80, 11, 123456, 501, true, true, true, true⟩
example : provenanceAccepted req good = true := by decide
example : ProvenanceBound req good := by decide
