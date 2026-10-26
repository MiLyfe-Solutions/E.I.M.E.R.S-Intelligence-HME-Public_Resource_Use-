import CPOQAtomicV12
open CPOQ
def initial : AtomicNonceState := { available := true, successfulClaims := 0 }
example : (afterClaim (afterClaim initial)).successfulClaims = 2 := by
  decide
