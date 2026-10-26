import CPOQAtomicV12
open CPOQ
def used : AtomicNonceState := { available := false, successfulClaims := 1 }
example : claimed used = true := by
  decide
