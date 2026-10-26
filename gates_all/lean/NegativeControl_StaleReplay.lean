import CPOQFormalTheoryV2
open CPOQ

/- Deliberately invalid: an old generation may not masquerade as current. -/
example : (1 : Nat) = 2 := by
  have h :
      ({ generation := 1
         certificate := {
           guard := fun (_ : Nat) => True
           claim := fun (_ : Nat) => True
           sound := by intro _ _; trivial }
         status := ReuseStatus.active } : ManagedCertificate Nat).generation = 2 := by
    rfl
  exact h
