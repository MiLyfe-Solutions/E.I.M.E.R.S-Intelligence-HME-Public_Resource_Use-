import CPOQCrashV13
open CPOQ
example : (retryAllowed { phase := .unknown, effectCount := 0 } = true) := by
  decide
