import CPOQFormalTheoryV2
open CPOQ

/- Deliberately invalid: a stale generation-6 dependency cannot be laundered
   through a current generation-7 component. -/
def alwaysCert : Certificate Unit :=
  { guard := fun _ => True
    claim := fun _ => True
    sound := by intro _ _; trivial }

def current7 : ManagedCertificate Unit :=
  { generation := 7, certificate := alwaysCert, status := ReuseStatus.active }

def stale6 : ManagedCertificate Unit :=
  { generation := 6, certificate := alwaysCert, status := ReuseStatus.active }

def mixedComposition : CertificateComposition Unit :=
  { left := current7, right := stale6 }

example : mixedComposition.right.generation = 7 := by
  rfl
