import CPOQAtomicV12
open CPOQ
def externalStart : ExternalEffectState := { effectCount := 0 }
-- A nonce-claim proof alone cannot prove exactly-once external side effects.
example : (externalEffect (externalEffect externalStart)).effectCount = 1 := by
  decide
