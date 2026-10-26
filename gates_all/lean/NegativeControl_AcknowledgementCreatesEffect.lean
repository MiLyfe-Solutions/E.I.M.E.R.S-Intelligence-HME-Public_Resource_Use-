import CPOQCrashV13
open CPOQ
example : ((acknowledge { phase := .committed, effectCount := 1 }).effectCount = 2) := by
  decide
