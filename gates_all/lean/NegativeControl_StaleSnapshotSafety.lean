import CPOQAtomicV12
open CPOQ
def snapshot : AtomicNonceState := { available := true, successfulClaims := 0 }
-- This intentionally demonstrates the naive snapshot *does* pass twice.
-- The negative control asserts the false claim that the second snapshot is rejected.
example : staleSnapshotCheck snapshot = false := by
  decide
