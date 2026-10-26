import CPOQFormalTheoryV2
open CPOQ

/- Deliberately invalid: replay/cache does not rewrite certificate generation. -/
example :
    (cacheReplay ({ generation := 1
                    certificate := {
                      guard := fun (_ : Nat) => True
                      claim := fun (_ : Nat) => True
                      sound := by intro _ _; trivial }
                    status := ReuseStatus.active } : ManagedCertificate Nat)).generation = 2 := by
  rfl
