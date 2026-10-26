import CPOQAtomicV12
open CPOQ
example : claimed ({ available := true, successfulClaims := 0 } : AtomicNonceState) = true := by decide
example : claimed (afterClaim ({ available := true, successfulClaims := 0 } : AtomicNonceState)) = false := by decide
example : (afterClaim (afterClaim ({ available := true, successfulClaims := 0 } : AtomicNonceState))).successfulClaims = 1 := by decide
