import CPOQCrashV13
open CPOQ
example : ((blindExternalRetry (blindExternalRetry { phase := .unknown, effectCount := 0 })).effectCount = 1) := by
  decide
