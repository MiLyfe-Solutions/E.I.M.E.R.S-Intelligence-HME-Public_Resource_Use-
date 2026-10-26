import CPOQAtomicV12
open CPOQ
def initial : AtomicNonceState := { available := true, successfulClaims := 0 }
example : claimed (afterClaim initial) = true := by
  decide
