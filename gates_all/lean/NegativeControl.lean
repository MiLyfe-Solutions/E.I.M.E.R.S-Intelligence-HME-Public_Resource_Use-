import «CPOQFormalTheoryV2»
open CPOQ

/-- Deliberately invalid: refinement alone must NOT silently reactivate a revoked path. -/
example : refineOnly ReuseStatus.revoked = ReuseStatus.active := by
  rfl
