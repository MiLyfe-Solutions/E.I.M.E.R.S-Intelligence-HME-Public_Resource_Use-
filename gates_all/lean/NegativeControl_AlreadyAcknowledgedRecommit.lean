import CPOQCrashV13
open CPOQ
example : ((commitOnce { phase := .acknowledged, effectCount := 1 }).effectCount = 2) := by
  decide
