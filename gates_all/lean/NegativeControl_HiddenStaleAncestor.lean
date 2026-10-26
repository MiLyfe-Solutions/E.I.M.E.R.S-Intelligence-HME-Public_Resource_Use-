import CPOQFormalTheoryV2
open CPOQ

def alwaysCert : Certificate Nat :=
  { guard := fun _ => True, claim := fun _ => True, sound := by intro _ _; trivial }

def hiddenStale : DependencyDisclosure3 Nat :=
  { root := { generation := 7, certificate := alwaysCert, status := ReuseStatus.active }
    middle := { generation := 7, certificate := alwaysCert, status := ReuseStatus.active }
    leaf := { generation := 6, certificate := alwaysCert, status := ReuseStatus.active }
    leafDeclared := False }

/- Deliberately invalid: an omitted stale authority-bearing leaf is not a complete disclosure. -/
example : DependencyComplete hiddenStale := by
  trivial
