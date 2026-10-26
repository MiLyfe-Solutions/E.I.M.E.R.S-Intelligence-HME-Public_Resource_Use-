import CPOQFormalTheoryV2
open CPOQ

private def sameClaimCert : Certificate Unit := {
  guard := fun _ => True
  claim := fun _ => True
  sound := by intro _ _; trivial
}

private def twinManaged : ManagedCertificate Unit := {
  generation := 7
  certificate := sameClaimCert
  status := ReuseStatus.active
}

-- Required and presented objects have the same certificate body, claim, generation, status, and guard.
-- Only the authority-bearing certificate identity differs.
private def evilTwinDependency : BoundDependency Unit := {
  requiredCertificateId := 7007
  presented := { certificateId := 7008, managed := twinManaged }
}

-- Deliberately forbidden shortcut: extensional proof similarity is treated as authority identity.
example : BoundDependencyReusableAt evilTwinDependency 7 () := by
  constructor
  · rfl
  · exact ⟨rfl, rfl, True.intro⟩
