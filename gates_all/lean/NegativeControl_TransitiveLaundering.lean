import CPOQFormalTheoryV2
open CPOQ

/- Deliberately invalid: current root and middle certificates cannot hide a
   stale generation-6 leaf inside a generation-7 authority chain. -/
def chainCert : Certificate Unit :=
  { guard := fun _ => True
    claim := fun _ => True
    sound := by intro _ _; trivial }

def gen7 : ManagedCertificate Unit :=
  { generation := 7, certificate := chainCert, status := ReuseStatus.active }

def gen6 : ManagedCertificate Unit :=
  { generation := 6, certificate := chainCert, status := ReuseStatus.active }

def launderingChain : DependencyChain3 Unit :=
  { root := gen7, middle := gen7, leaf := gen6 }

example : launderingChain.leaf.generation = 7 := by
  rfl
