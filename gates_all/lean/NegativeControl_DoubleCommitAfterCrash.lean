import CPOQCrashV13
open CPOQ
example : ((commitOnce (crashAfterCommit { phase := .pending, effectCount := 0 })).effectCount = 2) := by
  decide
