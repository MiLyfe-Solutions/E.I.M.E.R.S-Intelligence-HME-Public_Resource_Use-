import CPOQFormalTheoryV2
open CPOQ

private def alwaysCert : Certificate Unit := {
  guard := fun _ => True
  claim := fun _ => True
  sound := by intro _ _; trivial
}

private def currentManaged : ManagedCertificate Unit := {
  generation := 7
  certificate := alwaysCert
  status := ReuseStatus.active
}

private def substitutedDependency : BoundDependency Unit := {
  requiredCertificateId := 4101
  presented := { certificateId := 9901, managed := currentManaged }
}

-- Deliberately forbidden shortcut: a current active substitute is treated as the required identity.
example : DependencyIdentityBound substitutedDependency := by
  rfl
