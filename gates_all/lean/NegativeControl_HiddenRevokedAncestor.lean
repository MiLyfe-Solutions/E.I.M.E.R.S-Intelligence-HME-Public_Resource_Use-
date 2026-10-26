import CPOQFormalTheoryV2
open CPOQ

def alwaysCertR : Certificate Nat :=
  { guard := fun _ => True, claim := fun _ => True, sound := by intro _ _; trivial }

def hiddenRevoked : DependencyDisclosure3 Nat :=
  { root := { generation := 7, certificate := alwaysCertR, status := ReuseStatus.active }
    middle := { generation := 7, certificate := alwaysCertR, status := ReuseStatus.active }
    leaf := { generation := 7, certificate := alwaysCertR, status := ReuseStatus.revoked }
    leafDeclared := False }

/- Deliberately invalid: a revoked ancestor cannot be erased by omitting its dependency edge. -/
example : DependencyComplete hiddenRevoked := by
  trivial
