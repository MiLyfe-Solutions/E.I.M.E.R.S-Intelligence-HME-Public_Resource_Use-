import CPOQCrashV13
open CPOQ
example : commitOnce ({ phase := .committed, effectCount := 1 } : DurableOperation) =
  { phase := .committed, effectCount := 1 } := by rfl
example : retryAllowed ({ phase := .unknown, effectCount := 1 } : DurableOperation) = false := by rfl
