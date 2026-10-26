import CPOQFormalTheoryV2
open CPOQ

/- Deliberately invalid regression control from v2.3. -/
example :
    (observeConfirmations 100 {
      status := ReuseStatus.revoked
      confirmingObservations := 0
    }).status = ReuseStatus.active := by
  rfl
