import V185TrunkScan20Chunk031

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_195284 : List Nat := [2, 4, 1, 3, 3, 1, 6]
def baseStart_195284 : Nat := 118140960795 + 195284 * 2 ^ 59
def prefixEnd_195284 : Nat := 4983230072969 + 3 ^ 40 * 195284 * 2
def baseEnd_195284 : Nat := 9903659864959919422411

theorem tailTrace_195284 : CollatzResearch.WordTrace tailWord_195284 prefixEnd_195284 9903659864959919422411 := by
  unfold tailWord_195284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561296312263447348516453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4748395083017929798021937 3561296312263447348516453)
  ·
    refine ⟨667743058549396377846835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3561296312263447348516453 667743058549396377846835)
    ·
      refine ⟨1001614587824094566770253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667743058549396377846835 1001614587824094566770253)
      ·
        refine ⟨375605470434035462538845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1001614587824094566770253 375605470434035462538845)
        ·
          refine ⟨140852051412763298452067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375605470434035462538845 140852051412763298452067)
          ·
            refine ⟨211278077119144947678101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140852051412763298452067 211278077119144947678101)
            ·
              refine ⟨9903659864959919422411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211278077119144947678101 9903659864959919422411)
              ·
                rfl

theorem cell20_195284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 6].length) (baseStart_195284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195284 prefixEnd_195284 := by exact prefixLift 195284
  have htrace : WordTrace (prefixWord ++ tailWord_195284) baseStart_195284 baseEnd_195284 := by
    simpa [prefixWord, tailWord_195284, baseEnd_195284] using wordTrace_append hprefix tailTrace_195284
  have hstable : (prefixWord ++ tailWord_195284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195284).length < 2 ^ (prefixWord ++ tailWord_195284).sum := by decide
  have hdescent : baseEnd_195284 < baseStart_195284 := by decide
  rcases family_descends (prefixWord ++ tailWord_195284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195288 : List Nat := [2, 1, 2, 2, 3, 4, 6]
def baseStart_195288 : Nat := 118140960795 + 195288 * 2 ^ 59
def prefixEnd_195288 : Nat := 4983230072969 + 3 ^ 40 * 195288 * 2
def baseEnd_195288 : Nat := 9903862721514782074261

theorem tailTrace_195288 : CollatzResearch.WordTrace tailWord_195288 prefixEnd_195288 9903862721514782074261 := by
  unfold tailWord_195288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561369258256201690089259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4748492344341602253452345 3561369258256201690089259)
  ·
    refine ⟨5342053887384302535133889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3561369258256201690089259 5342053887384302535133889)
    ·
      refine ⟨4006540415538226901350417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5342053887384302535133889 4006540415538226901350417)
      ·
        refine ⟨3004905311653670176012813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4006540415538226901350417 3004905311653670176012813)
        ·
          refine ⟨1126839491870126316004805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3004905311653670176012813 1126839491870126316004805)
          ·
            refine ⟨211282404725648684250901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1126839491870126316004805 211282404725648684250901)
            ·
              refine ⟨9903862721514782074261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211282404725648684250901 9903862721514782074261)
              ·
                rfl

theorem cell20_195288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 6].length) (baseStart_195288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195288 prefixEnd_195288 := by exact prefixLift 195288
  have htrace : WordTrace (prefixWord ++ tailWord_195288) baseStart_195288 baseEnd_195288 := by
    simpa [prefixWord, tailWord_195288, baseEnd_195288] using wordTrace_append hprefix tailTrace_195288
  have hstable : (prefixWord ++ tailWord_195288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195288).length < 2 ^ (prefixWord ++ tailWord_195288).sum := by decide
  have hdescent : baseEnd_195288 < baseStart_195288 := by decide
  rcases family_descends (prefixWord ++ tailWord_195288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195295 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_195295 : Nat := 118140960795 + 195295 * 2 ^ 59
def prefixEnd_195295 : Nat := 4983230072969 + 3 ^ 40 * 195295 * 2
def baseEnd_195295 : Nat := 89137959484372125434987

theorem tailTrace_195295 : CollatzResearch.WordTrace tailWord_195295 prefixEnd_195295 89137959484372125434987 := by
  unfold tailWord_195295
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122993827487043575683339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4748662551658029050455559 7122993827487043575683339)
  ·
    refine ⟨10684490741230565363525009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7122993827487043575683339 10684490741230565363525009)
    ·
      refine ⟨8013368055922924022643757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10684490741230565363525009 8013368055922924022643757)
      ·
        refine ⟨3005013020971096508491409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8013368055922924022643757 3005013020971096508491409)
        ·
          refine ⟨2253759765728322381368557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005013020971096508491409 2253759765728322381368557)
          ·
            refine ⟨845159912148120893013209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2253759765728322381368557 845159912148120893013209)
            ·
              refine ⟨633869934111090669759907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845159912148120893013209 633869934111090669759907)
              ·
                refine ⟨950804901166636004639861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633869934111090669759907 950804901166636004639861)
                ·
                  refine ⟨89137959484372125434987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 950804901166636004639861 89137959484372125434987)
                  ·
                    rfl

theorem cell20_195295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_195295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195295 prefixEnd_195295 := by exact prefixLift 195295
  have htrace : WordTrace (prefixWord ++ tailWord_195295) baseStart_195295 baseEnd_195295 := by
    simpa [prefixWord, tailWord_195295, baseEnd_195295] using wordTrace_append hprefix tailTrace_195295
  have hstable : (prefixWord ++ tailWord_195295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195295).length < 2 ^ (prefixWord ++ tailWord_195295).sum := by decide
  have hdescent : baseEnd_195295 < baseStart_195295 := by decide
  rcases family_descends (prefixWord ++ tailWord_195295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195346 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_195346 : Nat := 118140960795 + 195346 * 2 ^ 59
def prefixEnd_195346 : Nat := 4983230072969 + 3 ^ 40 * 195346 * 2
def baseEnd_195346 : Nat := 89161237274042614734779

theorem tailTrace_195346 : CollatzResearch.WordTrace tailWord_195346 prefixEnd_195346 89161237274042614734779 := by
  unfold tailWord_195346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1781213487575569821447473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4749902633534852857193261 1781213487575569821447473)
  ·
    refine ⟨1335910115681677366085605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1781213487575569821447473 1335910115681677366085605)
    ·
      refine ⟨250483146690314506141051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1335910115681677366085605 250483146690314506141051)
      ·
        refine ⟨375724720035471759211577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250483146690314506141051 375724720035471759211577)
        ·
          refine ⟨281793540026603819408683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375724720035471759211577 281793540026603819408683)
          ·
            refine ⟨422690310039905729113025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281793540026603819408683 422690310039905729113025)
            ·
              refine ⟨317017732529929296834769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422690310039905729113025 317017732529929296834769)
              ·
                refine ⟨237763299397446972626077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317017732529929296834769 237763299397446972626077)
                ·
                  refine ⟨89161237274042614734779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237763299397446972626077 89161237274042614734779)
                  ·
                    rfl

theorem cell20_195346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_195346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195346 prefixEnd_195346 := by exact prefixLift 195346
  have htrace : WordTrace (prefixWord ++ tailWord_195346) baseStart_195346 baseEnd_195346 := by
    simpa [prefixWord, tailWord_195346, baseEnd_195346] using wordTrace_append hprefix tailTrace_195346
  have hstable : (prefixWord ++ tailWord_195346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195346).length < 2 ^ (prefixWord ++ tailWord_195346).sum := by decide
  have hdescent : baseEnd_195346 < baseStart_195346 := by decide
  rcases family_descends (prefixWord ++ tailWord_195346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195374 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_195374 : Nat := 118140960795 + 195374 * 2 ^ 59
def prefixEnd_195374 : Nat := 4983230072969 + 3 ^ 40 * 195374 * 2
def baseEnd_195374 : Nat := 89174017236998961801331

theorem tailTrace_195374 : CollatzResearch.WordTrace tailWord_195374 prefixEnd_195374 89174017236998961801331 := by
  unfold tailWord_195374
  simp only [CollatzResearch.WordTrace]
  refine ⟨890734399275105008476147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4750583462800560045206117 890734399275105008476147)
  ·
    refine ⟨1336101598912657512714221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 890734399275105008476147 1336101598912657512714221)
    ·
      refine ⟨501038099592246567267833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1336101598912657512714221 501038099592246567267833)
      ·
        refine ⟨375778574694184925450875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501038099592246567267833 375778574694184925450875)
        ·
          refine ⟨563667862041277388176313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375778574694184925450875 563667862041277388176313)
          ·
            refine ⟨422750896530958041132235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563667862041277388176313 422750896530958041132235)
            ·
              refine ⟨634126344796437061698353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422750896530958041132235 634126344796437061698353)
              ·
                refine ⟨475594758597327796273765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634126344796437061698353 475594758597327796273765)
                ·
                  refine ⟨89174017236998961801331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475594758597327796273765 89174017236998961801331)
                  ·
                    rfl

theorem cell20_195374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_195374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195374 prefixEnd_195374 := by exact prefixLift 195374
  have htrace : WordTrace (prefixWord ++ tailWord_195374) baseStart_195374 baseEnd_195374 := by
    simpa [prefixWord, tailWord_195374, baseEnd_195374] using wordTrace_append hprefix tailTrace_195374
  have hstable : (prefixWord ++ tailWord_195374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195374).length < 2 ^ (prefixWord ++ tailWord_195374).sum := by decide
  have hdescent : baseEnd_195374 < baseStart_195374 := by decide
  rcases family_descends (prefixWord ++ tailWord_195374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195381 : List Nat := [1, 3, 3, 1, 3, 2, 3, 4]
def baseStart_195381 : Nat := 118140960795 + 195381 * 2 ^ 59
def prefixEnd_195381 : Nat := 4983230072969 + 3 ^ 40 * 195381 * 2
def baseEnd_195381 : Nat := 29725737409246016189323

theorem tailTrace_195381 : CollatzResearch.WordTrace tailWord_195381 prefixEnd_195381 29725737409246016189323 := by
  unfold tailWord_195381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126130505175480263313997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4750753670116986842209331 7126130505175480263313997)
  ·
    refine ⟨2672298939440805098742749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7126130505175480263313997 2672298939440805098742749)
    ·
      refine ⟨1002112102290301912028531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2672298939440805098742749 1002112102290301912028531)
      ·
        refine ⟨1503168153435452868042797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002112102290301912028531 1503168153435452868042797)
        ·
          refine ⟨563688057538294825516049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1503168153435452868042797 563688057538294825516049)
          ·
            refine ⟨422766043153721119137037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563688057538294825516049 422766043153721119137037)
            ·
              refine ⟨158537266182645419676389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422766043153721119137037 158537266182645419676389)
              ·
                refine ⟨29725737409246016189323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158537266182645419676389 29725737409246016189323)
                ·
                  rfl

theorem cell20_195381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_195381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195381 prefixEnd_195381 := by exact prefixLift 195381
  have htrace : WordTrace (prefixWord ++ tailWord_195381) baseStart_195381 baseEnd_195381 := by
    simpa [prefixWord, tailWord_195381, baseEnd_195381] using wordTrace_append hprefix tailTrace_195381
  have hstable : (prefixWord ++ tailWord_195381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195381).length < 2 ^ (prefixWord ++ tailWord_195381).sum := by decide
  have hdescent : baseEnd_195381 < baseStart_195381 := by decide
  rcases family_descends (prefixWord ++ tailWord_195381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195398 : List Nat := [6, 1, 1, 2, 2, 1, 7]
def baseStart_195398 : Nat := 118140960795 + 195398 * 2 ^ 59
def prefixEnd_195398 : Nat := 4983230072969 + 3 ^ 40 * 195398 * 2
def baseEnd_195398 : Nat := 9909441276773505000137

theorem tailTrace_195398 : CollatzResearch.WordTrace tailWord_195398 prefixEnd_195398 9909441276773505000137 := by
  unfold tailWord_195398
  simp only [CollatzResearch.WordTrace]
  refine ⟨222710954566059130208839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4751167030742594777788565 222710954566059130208839)
  ·
    refine ⟨334066431849088695313259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222710954566059130208839 334066431849088695313259)
    ·
      refine ⟨501099647773633042969889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334066431849088695313259 501099647773633042969889)
      ·
        refine ⟨375824735830224782227417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501099647773633042969889 375824735830224782227417)
        ·
          refine ⟨281868551872668586670563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375824735830224782227417 281868551872668586670563)
          ·
            refine ⟨422802827809002880005845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281868551872668586670563 422802827809002880005845)
            ·
              refine ⟨9909441276773505000137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 422802827809002880005845 9909441276773505000137)
              ·
                rfl

theorem cell20_195398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 7].length) (baseStart_195398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195398 prefixEnd_195398 := by exact prefixLift 195398
  have htrace : WordTrace (prefixWord ++ tailWord_195398) baseStart_195398 baseEnd_195398 := by
    simpa [prefixWord, tailWord_195398, baseEnd_195398] using wordTrace_append hprefix tailTrace_195398
  have hstable : (prefixWord ++ tailWord_195398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195398).length < 2 ^ (prefixWord ++ tailWord_195398).sum := by decide
  have hdescent : baseEnd_195398 < baseStart_195398 := by decide
  rcases family_descends (prefixWord ++ tailWord_195398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195405 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_195405 : Nat := 118140960795 + 195405 * 2 ^ 59
def prefixEnd_195405 : Nat := 4983230072969 + 3 ^ 40 * 195405 * 2
def baseEnd_195405 : Nat := 89188166481700631767871

theorem tailTrace_195405 : CollatzResearch.WordTrace tailWord_195405 prefixEnd_195405 89188166481700631767871 := by
  unfold tailWord_195405
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127005857088532362187669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4751337238059021574791779 7127005857088532362187669)
  ·
    refine ⟨334078399551024954477547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7127005857088532362187669 334078399551024954477547)
    ·
      refine ⟨501117599326537431716321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334078399551024954477547 501117599326537431716321)
      ·
        refine ⟨375838199494903073787241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501117599326537431716321 375838199494903073787241)
        ·
          refine ⟨281878649621177305340431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375838199494903073787241 281878649621177305340431)
          ·
            refine ⟨422817974431765958010647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281878649621177305340431 422817974431765958010647)
            ·
              refine ⟨634226961647648937015971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422817974431765958010647 634226961647648937015971)
              ·
                refine ⟨951340442471473405523957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634226961647648937015971 951340442471473405523957)
                ·
                  refine ⟨89188166481700631767871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 951340442471473405523957 89188166481700631767871)
                  ·
                    rfl

theorem cell20_195405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_195405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195405 prefixEnd_195405 := by exact prefixLift 195405
  have htrace : WordTrace (prefixWord ++ tailWord_195405) baseStart_195405 baseEnd_195405 := by
    simpa [prefixWord, tailWord_195405, baseEnd_195405] using wordTrace_append hprefix tailTrace_195405
  have hstable : (prefixWord ++ tailWord_195405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195405).length < 2 ^ (prefixWord ++ tailWord_195405).sum := by decide
  have hdescent : baseEnd_195405 < baseStart_195405 := by decide
  rcases family_descends (prefixWord ++ tailWord_195405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195412 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_195412 : Nat := 118140960795 + 195412 * 2 ^ 59
def prefixEnd_195412 : Nat := 4983230072969 + 3 ^ 40 * 195412 * 2
def baseEnd_195412 : Nat := 89191361472439718534509

theorem tailTrace_195412 : CollatzResearch.WordTrace tailWord_195412 prefixEnd_195412 89191361472439718534509 := by
  unfold tailWord_195412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563630584031586278846245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4751507445375448371794993 3563630584031586278846245)
  ·
    refine ⟨668180734505922427283671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3563630584031586278846245 668180734505922427283671)
    ·
      refine ⟨1002271101758883640925507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668180734505922427283671 1002271101758883640925507)
      ·
        refine ⟨1503406652638325461388261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002271101758883640925507 1503406652638325461388261)
        ·
          refine ⟨281888747369686024010299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1503406652638325461388261 281888747369686024010299)
          ·
            refine ⟨422833121054529036015449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281888747369686024010299 422833121054529036015449)
            ·
              refine ⟨317124840790896777011587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422833121054529036015449 317124840790896777011587)
              ·
                refine ⟨475687261186345165517381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317124840790896777011587 475687261186345165517381)
                ·
                  refine ⟨89191361472439718534509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475687261186345165517381 89191361472439718534509)
                  ·
                    rfl

theorem cell20_195412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_195412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195412 prefixEnd_195412 := by exact prefixLift 195412
  have htrace : WordTrace (prefixWord ++ tailWord_195412) baseStart_195412 baseEnd_195412 := by
    simpa [prefixWord, tailWord_195412, baseEnd_195412] using wordTrace_append hprefix tailTrace_195412
  have hstable : (prefixWord ++ tailWord_195412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195412).length < 2 ^ (prefixWord ++ tailWord_195412).sum := by decide
  have hdescent : baseEnd_195412 < baseStart_195412 := by decide
  rcases family_descends (prefixWord ++ tailWord_195412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195423 : List Nat := [1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_195423 : Nat := 118140960795 + 195423 * 2 ^ 59
def prefixEnd_195423 : Nat := 4983230072969 + 3 ^ 40 * 195423 * 2
def baseEnd_195423 : Nat := 29732127390724189722599

theorem tailTrace_195423 : CollatzResearch.WordTrace tailWord_195423 prefixEnd_195423 29732127390724189722599 := by
  unfold tailWord_195423
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127662371023321436342923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4751774914015547624228615 7127662371023321436342923)
  ·
    refine ⟨10691493556534982154514385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7127662371023321436342923 10691493556534982154514385)
    ·
      refine ⟨8018620167401236615885789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10691493556534982154514385 8018620167401236615885789)
      ·
        refine ⟨3006982562775463730957171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8018620167401236615885789 3006982562775463730957171)
        ·
          refine ⟨4510473844163195596435757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006982562775463730957171 4510473844163195596435757)
          ·
            refine ⟨1691427691561198348663409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4510473844163195596435757 1691427691561198348663409)
            ·
              refine ⟨1268570768670898761497557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691427691561198348663409 1268570768670898761497557)
              ·
                refine ⟨29732127390724189722599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1268570768670898761497557 29732127390724189722599)
                ·
                  rfl

theorem cell20_195423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_195423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195423 prefixEnd_195423 := by exact prefixLift 195423
  have htrace : WordTrace (prefixWord ++ tailWord_195423) baseStart_195423 baseEnd_195423 := by
    simpa [prefixWord, tailWord_195423, baseEnd_195423] using wordTrace_append hprefix tailTrace_195423
  have hstable : (prefixWord ++ tailWord_195423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195423).length < 2 ^ (prefixWord ++ tailWord_195423).sum := by decide
  have hdescent : baseEnd_195423 < baseStart_195423 := by decide
  rcases family_descends (prefixWord ++ tailWord_195423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195440 : List Nat := [2, 1, 1, 1, 4, 1, 6, 4]
def baseStart_195440 : Nat := 118140960795 + 195440 * 2 ^ 59
def prefixEnd_195440 : Nat := 4983230072969 + 3 ^ 40 * 195440 * 2
def baseEnd_195440 : Nat := 29734713811798688533687

theorem tailTrace_195440 : CollatzResearch.WordTrace tailWord_195440 prefixEnd_195440 29734713811798688533687 := by
  unfold tailWord_195440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3564141205980866669855887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4752188274641155559807849 3564141205980866669855887)
  ·
    refine ⟨5346211808971300004783831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3564141205980866669855887 5346211808971300004783831)
    ·
      refine ⟨8019317713456950007175747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346211808971300004783831 8019317713456950007175747)
      ·
        refine ⟨12028976570185425010763621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8019317713456950007175747 12028976570185425010763621)
        ·
          refine ⟨2255433106909767189518179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12028976570185425010763621 2255433106909767189518179)
          ·
            refine ⟨3383149660364650784277269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255433106909767189518179 3383149660364650784277269)
            ·
              refine ⟨158585140329593005512997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3383149660364650784277269 158585140329593005512997)
              ·
                refine ⟨29734713811798688533687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158585140329593005512997 29734713811798688533687)
                ·
                  rfl

theorem cell20_195440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_195440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195440 prefixEnd_195440 := by exact prefixLift 195440
  have htrace : WordTrace (prefixWord ++ tailWord_195440) baseStart_195440 baseEnd_195440 := by
    simpa [prefixWord, tailWord_195440, baseEnd_195440] using wordTrace_append hprefix tailTrace_195440
  have hstable : (prefixWord ++ tailWord_195440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195440).length < 2 ^ (prefixWord ++ tailWord_195440).sum := by decide
  have hdescent : baseEnd_195440 < baseStart_195440 := by decide
  rcases family_descends (prefixWord ++ tailWord_195440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195446 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_195446 : Nat := 118140960795 + 195446 * 2 ^ 59
def prefixEnd_195446 : Nat := 4983230072969 + 3 ^ 40 * 195446 * 2
def baseEnd_195446 : Nat := 89206879998886711401037

theorem tailTrace_195446 : CollatzResearch.WordTrace tailWord_195446 prefixEnd_195446 89206879998886711401037 := by
  unfold tailWord_195446
  simp only [CollatzResearch.WordTrace]
  refine ⟨445531328121249772776887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4752334166626664242953461 445531328121249772776887)
  ·
    refine ⟨668296992181874659165331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445531328121249772776887 668296992181874659165331)
    ·
      refine ⟨1002445488272811988747997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668296992181874659165331 1002445488272811988747997)
      ·
        refine ⟨375917058102304495780499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1002445488272811988747997 375917058102304495780499)
        ·
          refine ⟨563875587153456743670749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375917058102304495780499 563875587153456743670749)
          ·
            refine ⟨211453345182546278876531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563875587153456743670749 211453345182546278876531)
            ·
              refine ⟨317180017773819418314797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211453345182546278876531 317180017773819418314797)
              ·
                refine ⟨118942506665182281868049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317180017773819418314797 118942506665182281868049)
                ·
                  refine ⟨89206879998886711401037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118942506665182281868049 89206879998886711401037)
                  ·
                    rfl

theorem cell20_195446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_195446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195446 prefixEnd_195446 := by exact prefixLift 195446
  have htrace : WordTrace (prefixWord ++ tailWord_195446) baseStart_195446 baseEnd_195446 := by
    simpa [prefixWord, tailWord_195446, baseEnd_195446] using wordTrace_append hprefix tailTrace_195446
  have hstable : (prefixWord ++ tailWord_195446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195446).length < 2 ^ (prefixWord ++ tailWord_195446).sum := by decide
  have hdescent : baseEnd_195446 < baseStart_195446 := by decide
  rcases family_descends (prefixWord ++ tailWord_195446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195461 : List Nat := [1, 3, 1, 1, 3, 3, 8]
def baseStart_195461 : Nat := 118140960795 + 195461 * 2 ^ 59
def prefixEnd_195461 : Nat := 4983230072969 + 3 ^ 40 * 195461 * 2
def baseEnd_195461 : Nat := 9912636267512591766775

theorem tailTrace_195461 : CollatzResearch.WordTrace tailWord_195461 prefixEnd_195461 9912636267512591766775 := by
  unfold tailWord_195461
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129048344885653926226237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4752698896590435950817491 7129048344885653926226237)
  ·
    refine ⟨2673393129332120222334839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7129048344885653926226237 2673393129332120222334839)
    ·
      refine ⟨4010089693998180333502259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673393129332120222334839 4010089693998180333502259)
      ·
        refine ⟨6015134540997270500253389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010089693998180333502259 6015134540997270500253389)
        ·
          refine ⟨2255675452873976437595021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6015134540997270500253389 2255675452873976437595021)
          ·
            refine ⟨845878294827741164098133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2255675452873976437595021 845878294827741164098133)
            ·
              refine ⟨9912636267512591766775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 845878294827741164098133 9912636267512591766775)
              ·
                rfl

theorem cell20_195461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_195461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195461 prefixEnd_195461 := by exact prefixLift 195461
  have htrace : WordTrace (prefixWord ++ tailWord_195461) baseStart_195461 baseEnd_195461 := by
    simpa [prefixWord, tailWord_195461, baseEnd_195461] using wordTrace_append hprefix tailTrace_195461
  have hstable : (prefixWord ++ tailWord_195461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195461).length < 2 ^ (prefixWord ++ tailWord_195461).sum := by decide
  have hdescent : baseEnd_195461 < baseStart_195461 := by decide
  rcases family_descends (prefixWord ++ tailWord_195461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195492 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_195492 : Nat := 118140960795 + 195492 * 2 ^ 59
def prefixEnd_195492 : Nat := 4983230072969 + 3 ^ 40 * 195492 * 2
def baseEnd_195492 : Nat := 89227875652314995867515

theorem tailTrace_195492 : CollatzResearch.WordTrace tailWord_195492 prefixEnd_195492 89227875652314995867515 := by
  unfold tailWord_195492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565089503886673110302365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4753452671848897480403153 3565089503886673110302365)
  ·
    refine ⟨1336908563957502416363387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3565089503886673110302365 1336908563957502416363387)
    ·
      refine ⟨2005362845936253624545081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336908563957502416363387 2005362845936253624545081)
      ·
        refine ⟨1504022134452190218408811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2005362845936253624545081 1504022134452190218408811)
        ·
          refine ⟨2256033201678285327613217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504022134452190218408811 2256033201678285327613217)
          ·
            refine ⟨1692024901258713995709913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256033201678285327613217 1692024901258713995709913)
            ·
              refine ⟨1269018675944035496782435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692024901258713995709913 1269018675944035496782435)
              ·
                refine ⟨1903528013916053245173653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269018675944035496782435 1903528013916053245173653)
                ·
                  refine ⟨89227875652314995867515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1903528013916053245173653 89227875652314995867515)
                  ·
                    rfl

theorem cell20_195492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_195492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195492 prefixEnd_195492 := by exact prefixLift 195492
  have htrace : WordTrace (prefixWord ++ tailWord_195492) baseStart_195492 baseEnd_195492 := by
    simpa [prefixWord, tailWord_195492, baseEnd_195492] using wordTrace_append hprefix tailTrace_195492
  have hstable : (prefixWord ++ tailWord_195492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195492).length < 2 ^ (prefixWord ++ tailWord_195492).sum := by decide
  have hdescent : baseEnd_195492 < baseStart_195492 := by decide
  rcases family_descends (prefixWord ++ tailWord_195492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195530 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_195530 : Nat := 118140960795 + 195530 * 2 ^ 59
def prefixEnd_195530 : Nat := 4983230072969 + 3 ^ 40 * 195530 * 2
def baseEnd_195530 : Nat := 89245219887755752600693

theorem tailTrace_195530 : CollatzResearch.WordTrace tailWord_195530 prefixEnd_195530 89245219887755752600693 := by
  unfold tailWord_195530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782891245408919677622011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4754376654423785806992029 1782891245408919677622011)
  ·
    refine ⟨2674336868113379516433017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1782891245408919677622011 2674336868113379516433017)
    ·
      refine ⟨2005752651085034637324763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2674336868113379516433017 2005752651085034637324763)
      ·
        refine ⟨3008628976627551955987145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005752651085034637324763 3008628976627551955987145)
        ·
          refine ⟨2256471732470663966990359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008628976627551955987145 2256471732470663966990359)
          ·
            refine ⟨3384707598705995950485539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256471732470663966990359 3384707598705995950485539)
            ·
              refine ⟨5077061398058993925728309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384707598705995950485539 5077061398058993925728309)
              ·
                refine ⟨475974506068030680537029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5077061398058993925728309 475974506068030680537029)
                ·
                  refine ⟨89245219887755752600693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475974506068030680537029 89245219887755752600693)
                  ·
                    rfl

theorem cell20_195530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_195530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195530 prefixEnd_195530 := by exact prefixLift 195530
  have htrace : WordTrace (prefixWord ++ tailWord_195530) baseStart_195530 baseEnd_195530 := by
    simpa [prefixWord, tailWord_195530, baseEnd_195530] using wordTrace_append hprefix tailTrace_195530
  have hstable : (prefixWord ++ tailWord_195530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195530).length < 2 ^ (prefixWord ++ tailWord_195530).sum := by decide
  have hdescent : baseEnd_195530 < baseStart_195530 := by decide
  rcases family_descends (prefixWord ++ tailWord_195530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195540 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_195540 : Nat := 118140960795 + 195540 * 2 ^ 59
def prefixEnd_195540 : Nat := 4983230072969 + 3 ^ 40 * 195540 * 2
def baseEnd_195540 : Nat := 89249784160240162267319

theorem tailTrace_195540 : CollatzResearch.WordTrace tailWord_195540 prefixEnd_195540 89249784160240162267319 := by
  unfold tailWord_195540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565964855799725209176037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4754619807732966945568049 3565964855799725209176037)
  ·
    refine ⟨668618410462448476720507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3565964855799725209176037 668618410462448476720507)
    ·
      refine ⟨1002927615693672715080761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668618410462448476720507 1002927615693672715080761)
      ·
        refine ⟨752195711770254536310571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1002927615693672715080761 752195711770254536310571)
        ·
          refine ⟨1128293567655381804465857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752195711770254536310571 1128293567655381804465857)
          ·
            refine ⟨846220175741536353349393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128293567655381804465857 846220175741536353349393)
            ·
              refine ⟨634665131806152265012045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846220175741536353349393 634665131806152265012045)
              ·
                refine ⟨237999424427307099379517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 634665131806152265012045 237999424427307099379517)
                ·
                  refine ⟨89249784160240162267319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237999424427307099379517 89249784160240162267319)
                  ·
                    rfl

theorem cell20_195540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_195540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195540 prefixEnd_195540 := by exact prefixLift 195540
  have htrace : WordTrace (prefixWord ++ tailWord_195540) baseStart_195540 baseEnd_195540 := by
    simpa [prefixWord, tailWord_195540, baseEnd_195540] using wordTrace_append hprefix tailTrace_195540
  have hstable : (prefixWord ++ tailWord_195540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195540).length < 2 ^ (prefixWord ++ tailWord_195540).sum := by decide
  have hdescent : baseEnd_195540 < baseStart_195540 := by decide
  rcases family_descends (prefixWord ++ tailWord_195540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195585 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_195585 : Nat := 118140960795 + 195585 * 2 ^ 59
def prefixEnd_195585 : Nat := 4983230072969 + 3 ^ 40 * 195585 * 2
def baseEnd_195585 : Nat := 89270323386420005767135

theorem tailTrace_195585 : CollatzResearch.WordTrace tailWord_195585 prefixEnd_195585 89270323386420005767135 := by
  unfold tailWord_195585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133570996436423103740209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4755713997624282069160139 7133570996436423103740209)
  ·
    refine ⟨5350178247327317327805157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7133570996436423103740209 5350178247327317327805157)
    ·
      refine ⟨1003158421373871998963467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5350178247327317327805157 1003158421373871998963467)
      ·
        refine ⟨1504737632060807998445201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003158421373871998963467 1504737632060807998445201)
        ·
          refine ⟨1128553224045605998833901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504737632060807998445201 1128553224045605998833901)
          ·
            refine ⟨423207459017102249562713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1128553224045605998833901 423207459017102249562713)
            ·
              refine ⟨317405594262826687172035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423207459017102249562713 317405594262826687172035)
              ·
                refine ⟨476108391394240030758053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317405594262826687172035 476108391394240030758053)
                ·
                  refine ⟨89270323386420005767135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476108391394240030758053 89270323386420005767135)
                  ·
                    rfl

theorem cell20_195585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_195585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195585 prefixEnd_195585 := by exact prefixLift 195585
  have htrace : WordTrace (prefixWord ++ tailWord_195585) baseStart_195585 baseEnd_195585 := by
    simpa [prefixWord, tailWord_195585, baseEnd_195585] using wordTrace_append hprefix tailTrace_195585
  have hstable : (prefixWord ++ tailWord_195585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195585).length < 2 ^ (prefixWord ++ tailWord_195585).sum := by decide
  have hdescent : baseEnd_195585 < baseStart_195585 := by decide
  rcases family_descends (prefixWord ++ tailWord_195585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195636 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 2]
def baseStart_195636 : Nat := 118140960795 + 195636 * 2 ^ 59
def prefixEnd_195636 : Nat := 4983230072969 + 3 ^ 40 * 195636 * 2
def baseEnd_195636 : Nat := 89293601176090495066927

theorem tailTrace_195636 : CollatzResearch.WordTrace tailWord_195636 prefixEnd_195636 89293601176090495066927 := by
  unfold tailWord_195636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567715559625829406923381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4756954079501105875897841 3567715559625829406923381)
  ·
    refine ⟨334473333714921506899067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3567715559625829406923381 334473333714921506899067)
    ·
      refine ⟨501710000572382260348601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334473333714921506899067 501710000572382260348601)
      ·
        refine ⟨376282500429286695261451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501710000572382260348601 376282500429286695261451)
        ·
          refine ⟨564423750643930042892177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376282500429286695261451 564423750643930042892177)
          ·
            refine ⟨423317812982947532169133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564423750643930042892177 423317812982947532169133)
            ·
              refine ⟨158744179868605324563425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423317812982947532169133 158744179868605324563425)
              ·
                refine ⟨119058134901453993422569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158744179868605324563425 119058134901453993422569)
                ·
                  refine ⟨89293601176090495066927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119058134901453993422569 89293601176090495066927)
                  ·
                    rfl

theorem cell20_195636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_195636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195636 prefixEnd_195636 := by exact prefixLift 195636
  have htrace : WordTrace (prefixWord ++ tailWord_195636) baseStart_195636 baseEnd_195636 := by
    simpa [prefixWord, tailWord_195636, baseEnd_195636] using wordTrace_append hprefix tailTrace_195636
  have hstable : (prefixWord ++ tailWord_195636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195636).length < 2 ^ (prefixWord ++ tailWord_195636).sum := by decide
  have hdescent : baseEnd_195636 < baseStart_195636 := by decide
  rcases family_descends (prefixWord ++ tailWord_195636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195637 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_195637 : Nat := 118140960795 + 195637 * 2 ^ 59
def prefixEnd_195637 : Nat := 4983230072969 + 3 ^ 40 * 195637 * 2
def baseEnd_195637 : Nat := 89294057603338936033589

theorem tailTrace_195637 : CollatzResearch.WordTrace tailWord_195637 prefixEnd_195637 89294057603338936033589 := by
  unfold tailWord_195637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135467592248035984633165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4756978394832023989755443 7135467592248035984633165)
  ·
    refine ⟨2675800347093013494237437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7135467592248035984633165 2675800347093013494237437)
    ·
      refine ⟨1003425130159880060339039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2675800347093013494237437 1003425130159880060339039)
      ·
        refine ⟨1505137695239820090508559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003425130159880060339039 1505137695239820090508559)
        ·
          refine ⟨2257706542859730135762839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505137695239820090508559 2257706542859730135762839)
          ·
            refine ⟨3386559814289595203644259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257706542859730135762839 3386559814289595203644259)
            ·
              refine ⟨5079839721434392805466389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3386559814289595203644259 5079839721434392805466389)
              ·
                refine ⟨238117486942237162756237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5079839721434392805466389 238117486942237162756237)
                ·
                  refine ⟨89294057603338936033589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238117486942237162756237 89294057603338936033589)
                  ·
                    rfl

theorem cell20_195637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_195637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195637 prefixEnd_195637 := by exact prefixLift 195637
  have htrace : WordTrace (prefixWord ++ tailWord_195637) baseStart_195637 baseEnd_195637 := by
    simpa [prefixWord, tailWord_195637, baseEnd_195637] using wordTrace_append hprefix tailTrace_195637
  have hstable : (prefixWord ++ tailWord_195637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195637).length < 2 ^ (prefixWord ++ tailWord_195637).sum := by decide
  have hdescent : baseEnd_195637 < baseStart_195637 := by decide
  rcases family_descends (prefixWord ++ tailWord_195637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195651 : List Nat := [1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_195651 : Nat := 118140960795 + 195651 * 2 ^ 59
def prefixEnd_195651 : Nat := 4983230072969 + 3 ^ 40 * 195651 * 2
def baseEnd_195651 : Nat := 29766815861605703188955

theorem tailTrace_195651 : CollatzResearch.WordTrace tailWord_195651 prefixEnd_195651 29766815861605703188955 := by
  unfold tailWord_195651
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135978214197316375642807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4757318809464877583761871 7135978214197316375642807)
  ·
    refine ⟨10703967321295974563464211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7135978214197316375642807 10703967321295974563464211)
    ·
      refine ⟨16055950981943961845196317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10703967321295974563464211 16055950981943961845196317)
      ·
        refine ⟨6020981618228985691948619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16055950981943961845196317 6020981618228985691948619)
        ·
          refine ⟨9031472427343478537922929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020981618228985691948619 9031472427343478537922929)
          ·
            refine ⟨6773604320507608903442197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031472427343478537922929 6773604320507608903442197)
            ·
              refine ⟨317512702523794167348853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6773604320507608903442197 317512702523794167348853)
              ·
                refine ⟨29766815861605703188955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317512702523794167348853 29766815861605703188955)
                ·
                  rfl

theorem cell20_195651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_195651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195651 prefixEnd_195651 := by exact prefixLift 195651
  have htrace : WordTrace (prefixWord ++ tailWord_195651) baseStart_195651 baseEnd_195651 := by
    simpa [prefixWord, tailWord_195651, baseEnd_195651] using wordTrace_append hprefix tailTrace_195651
  have hstable : (prefixWord ++ tailWord_195651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195651).length < 2 ^ (prefixWord ++ tailWord_195651).sum := by decide
  have hdescent : baseEnd_195651 < baseStart_195651 := by decide
  rcases family_descends (prefixWord ++ tailWord_195651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195754 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_195754 : Nat := 118140960795 + 195754 * 2 ^ 59
def prefixEnd_195754 : Nat := 4983230072969 + 3 ^ 40 * 195754 * 2
def baseEnd_195754 : Nat := 89347459591406529133111

theorem tailTrace_195754 : CollatzResearch.WordTrace tailWord_195754 prefixEnd_195754 89347459591406529133111 := by
  unfold tailWord_195754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784933733206041241660579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4759823288549443311094877 1784933733206041241660579)
  ·
    refine ⟨2677400599809061862490869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784933733206041241660579 2677400599809061862490869)
    ·
      refine ⟨251006306232099549608519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2677400599809061862490869 251006306232099549608519)
      ·
        refine ⟨376509459348149324412779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251006306232099549608519 376509459348149324412779)
        ·
          refine ⟨564764189022223986619169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376509459348149324412779 564764189022223986619169)
          ·
            refine ⟨423573141766667989964377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564764189022223986619169 423573141766667989964377)
            ·
              refine ⟨317679856325000992473283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423573141766667989964377 317679856325000992473283)
              ·
                refine ⟨476519784487501488709925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317679856325000992473283 476519784487501488709925)
                ·
                  refine ⟨89347459591406529133111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476519784487501488709925 89347459591406529133111)
                  ·
                    rfl

theorem cell20_195754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_195754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195754 prefixEnd_195754 := by exact prefixLift 195754
  have htrace : WordTrace (prefixWord ++ tailWord_195754) baseStart_195754 baseEnd_195754 := by
    simpa [prefixWord, tailWord_195754, baseEnd_195754] using wordTrace_append hprefix tailTrace_195754
  have hstable : (prefixWord ++ tailWord_195754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195754).length < 2 ^ (prefixWord ++ tailWord_195754).sum := by decide
  have hdescent : baseEnd_195754 < baseStart_195754 := by decide
  rcases family_descends (prefixWord ++ tailWord_195754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195778 : List Nat := [3, 5, 1, 1, 2, 1, 1, 6]
def baseStart_195778 : Nat := 118140960795 + 195778 * 2 ^ 59
def prefixEnd_195778 : Nat := 4983230072969 + 3 ^ 40 * 195778 * 2
def baseEnd_195778 : Nat := 29786137948456370777671

theorem tailTrace_195778 : CollatzResearch.WordTrace tailWord_195778 prefixEnd_195778 29786137948456370777671 := by
  unfold tailWord_195778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785152571184304266378997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4760406856491478043677325 1785152571184304266378997)
  ·
    refine ⟨167358053548528524973031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1785152571184304266378997 167358053548528524973031)
    ·
      refine ⟨251037080322792787459547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167358053548528524973031 251037080322792787459547)
      ·
        refine ⟨376555620484189181189321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251037080322792787459547 376555620484189181189321)
        ·
          refine ⟨282416715363141885891991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376555620484189181189321 282416715363141885891991)
          ·
            refine ⟨423625073044712828837987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282416715363141885891991 423625073044712828837987)
            ·
              refine ⟨635437609567069243256981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423625073044712828837987 635437609567069243256981)
              ·
                refine ⟨29786137948456370777671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 635437609567069243256981 29786137948456370777671)
                ·
                  rfl

theorem cell20_195778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_195778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195778 prefixEnd_195778 := by exact prefixLift 195778
  have htrace : WordTrace (prefixWord ++ tailWord_195778) baseStart_195778 baseEnd_195778 := by
    simpa [prefixWord, tailWord_195778, baseEnd_195778] using wordTrace_append hprefix tailTrace_195778
  have hstable : (prefixWord ++ tailWord_195778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195778).length < 2 ^ (prefixWord ++ tailWord_195778).sum := by decide
  have hdescent : baseEnd_195778 < baseStart_195778 := by decide
  rcases family_descends (prefixWord ++ tailWord_195778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195779 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_195779 : Nat := 118140960795 + 195779 * 2 ^ 59
def prefixEnd_195779 : Nat := 4983230072969 + 3 ^ 40 * 195779 * 2
def baseEnd_195779 : Nat := 89358870272617553299675

theorem tailTrace_195779 : CollatzResearch.WordTrace tailWord_195779 prefixEnd_195779 89358870272617553299675 := by
  unfold tailWord_195779
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140646757733594236302391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4760431171822396157534927 7140646757733594236302391)
  ·
    refine ⟨10710970136600391354453587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7140646757733594236302391 10710970136600391354453587)
    ·
      refine ⟨16066455204900587031680381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10710970136600391354453587 16066455204900587031680381)
      ·
        refine ⟨6024920701837720136880143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16066455204900587031680381 6024920701837720136880143)
        ·
          refine ⟨9037381052756580205320215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6024920701837720136880143 9037381052756580205320215)
          ·
            refine ⟨13556071579134870307980323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037381052756580205320215 13556071579134870307980323)
            ·
              refine ⟨20334107368702305461970485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556071579134870307980323 20334107368702305461970485)
              ·
                refine ⟨1906322565815841137059733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20334107368702305461970485 1906322565815841137059733)
                ·
                  refine ⟨89358870272617553299675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1906322565815841137059733 89358870272617553299675)
                  ·
                    rfl

theorem cell20_195779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_195779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195779 prefixEnd_195779 := by exact prefixLift 195779
  have htrace : WordTrace (prefixWord ++ tailWord_195779) baseStart_195779 baseEnd_195779 := by
    simpa [prefixWord, tailWord_195779, baseEnd_195779] using wordTrace_append hprefix tailTrace_195779
  have hstable : (prefixWord ++ tailWord_195779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195779).length < 2 ^ (prefixWord ++ tailWord_195779).sum := by decide
  have hdescent : baseEnd_195779 < baseStart_195779 := by decide
  rcases family_descends (prefixWord ++ tailWord_195779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195823 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 3]
def baseStart_195823 : Nat := 118140960795 + 195823 * 2 ^ 59
def prefixEnd_195823 : Nat := 4983230072969 + 3 ^ 40 * 195823 * 2
def baseEnd_195823 : Nat := 89378953071548955832829

theorem tailTrace_195823 : CollatzResearch.WordTrace tailWord_195823 prefixEnd_195823 89378953071548955832829 := by
  unfold tailWord_195823
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142251569574189750904123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4761501046382793167269415 7142251569574189750904123)
  ·
    refine ⟨10713377354361284626356185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7142251569574189750904123 10713377354361284626356185)
    ·
      refine ⟨8035033015770963469767139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10713377354361284626356185 8035033015770963469767139)
      ·
        refine ⟨12052549523656445204650709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035033015770963469767139 12052549523656445204650709)
        ·
          refine ⟨282481629460697934484001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12052549523656445204650709 282481629460697934484001)
          ·
            refine ⟨211861222095523450863001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282481629460697934484001 211861222095523450863001)
            ·
              refine ⟨158895916571642588147251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211861222095523450863001 158895916571642588147251)
              ·
                refine ⟨238343874857463882220877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158895916571642588147251 238343874857463882220877)
                ·
                  refine ⟨89378953071548955832829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238343874857463882220877 89378953071548955832829)
                  ·
                    rfl

theorem cell20_195823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_195823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195823 prefixEnd_195823 := by exact prefixLift 195823
  have htrace : WordTrace (prefixWord ++ tailWord_195823) baseStart_195823 baseEnd_195823 := by
    simpa [prefixWord, tailWord_195823, baseEnd_195823] using wordTrace_append hprefix tailTrace_195823
  have hstable : (prefixWord ++ tailWord_195823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195823).length < 2 ^ (prefixWord ++ tailWord_195823).sum := by decide
  have hdescent : baseEnd_195823 < baseStart_195823 := by decide
  rcases family_descends (prefixWord ++ tailWord_195823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195827 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_195827 : Nat := 118140960795 + 195827 * 2 ^ 59
def prefixEnd_195827 : Nat := 4983230072969 + 3 ^ 40 * 195827 * 2
def baseEnd_195827 : Nat := 89380778780542719699479

theorem tailTrace_195827 : CollatzResearch.WordTrace tailWord_195827 prefixEnd_195827 89380778780542719699479 := by
  unfold tailWord_195827
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142397461559698434049735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4761598307706465622699823 7142397461559698434049735)
  ·
    refine ⟨10713596192339547651074603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7142397461559698434049735 10713596192339547651074603)
    ·
      refine ⟨16070394288509321476611905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10713596192339547651074603 16070394288509321476611905)
      ·
        refine ⟨12052795716381991107458929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16070394288509321476611905 12052795716381991107458929)
        ·
          refine ⟨9039596787286493330594197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12052795716381991107458929 9039596787286493330594197)
          ·
            refine ⟨423731099404054374871603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9039596787286493330594197 423731099404054374871603)
            ·
              refine ⟨635596649106081562307405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423731099404054374871603 635596649106081562307405)
              ·
                refine ⟨238348743414780585865277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635596649106081562307405 238348743414780585865277)
                ·
                  refine ⟨89380778780542719699479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238348743414780585865277 89380778780542719699479)
                  ·
                    rfl

theorem cell20_195827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_195827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195827 prefixEnd_195827 := by exact prefixLift 195827
  have htrace : WordTrace (prefixWord ++ tailWord_195827) baseStart_195827 baseEnd_195827 := by
    simpa [prefixWord, tailWord_195827, baseEnd_195827] using wordTrace_append hprefix tailTrace_195827
  have hstable : (prefixWord ++ tailWord_195827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195827).length < 2 ^ (prefixWord ++ tailWord_195827).sum := by decide
  have hdescent : baseEnd_195827 < baseStart_195827 := by decide
  rcases family_descends (prefixWord ++ tailWord_195827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195841 : List Nat := [1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_195841 : Nat := 118140960795 + 195841 * 2 ^ 59
def prefixEnd_195841 : Nat := 4983230072969 + 3 ^ 40 * 195841 * 2
def baseEnd_195841 : Nat := 29795722920673631077585

theorem tailTrace_195841 : CollatzResearch.WordTrace tailWord_195841 prefixEnd_195841 29795722920673631077585 := by
  unfold tailWord_195841
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142908083508978825059377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4761938722339319216706251 7142908083508978825059377)
  ·
    refine ⟨5357181062631734118794533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7142908083508978825059377 5357181062631734118794533)
    ·
      refine ⟨1004471449243450147273975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5357181062631734118794533 1004471449243450147273975)
      ·
        refine ⟨1506707173865175220910963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004471449243450147273975 1506707173865175220910963)
        ·
          refine ⟨2260060760797762831366445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506707173865175220910963 2260060760797762831366445)
          ·
            refine ⟨847522785299161061762417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2260060760797762831366445 847522785299161061762417)
            ·
              refine ⟨635642088974370796321813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847522785299161061762417 635642088974370796321813)
              ·
                refine ⟨29795722920673631077585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 635642088974370796321813 29795722920673631077585)
                ·
                  rfl

theorem cell20_195841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_195841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195841 prefixEnd_195841 := by exact prefixLift 195841
  have htrace : WordTrace (prefixWord ++ tailWord_195841) baseStart_195841 baseEnd_195841 := by
    simpa [prefixWord, tailWord_195841, baseEnd_195841] using wordTrace_append hprefix tailTrace_195841
  have hstable : (prefixWord ++ tailWord_195841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195841).length < 2 ^ (prefixWord ++ tailWord_195841).sum := by decide
  have hdescent : baseEnd_195841 < baseStart_195841 := by decide
  rcases family_descends (prefixWord ++ tailWord_195841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195858 : List Nat := [3, 2, 4, 2, 9]
def baseStart_195858 : Nat := 118140960795 + 195858 * 2 ^ 59
def prefixEnd_195858 : Nat := 4983230072969 + 3 ^ 40 * 195858 * 2
def baseEnd_195858 : Nat := 1103641086731412218099

theorem tailTrace_195858 : CollatzResearch.WordTrace tailWord_195858 prefixEnd_195858 1103641086731412218099 := by
  unfold tailWord_195858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785882031111847682107057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4762352082964927152285485 1785882031111847682107057)
  ·
    refine ⟨1339411523333885761580293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1785882031111847682107057 1339411523333885761580293)
    ·
      refine ⟨251139660625103580296305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1339411523333885761580293 251139660625103580296305)
      ·
        refine ⟨188354745468827685222229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251139660625103580296305 188354745468827685222229)
        ·
          refine ⟨1103641086731412218099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 188354745468827685222229 1103641086731412218099)
          ·
            rfl

theorem cell20_195858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 9].length) (baseStart_195858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195858 prefixEnd_195858 := by exact prefixLift 195858
  have htrace : WordTrace (prefixWord ++ tailWord_195858) baseStart_195858 baseEnd_195858 := by
    simpa [prefixWord, tailWord_195858, baseEnd_195858] using wordTrace_append hprefix tailTrace_195858
  have hstable : (prefixWord ++ tailWord_195858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195858).length < 2 ^ (prefixWord ++ tailWord_195858).sum := by decide
  have hdescent : baseEnd_195858 < baseStart_195858 := by decide
  rcases family_descends (prefixWord ++ tailWord_195858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195868 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 2]
def baseStart_195868 : Nat := 118140960795 + 195868 * 2 ^ 59
def prefixEnd_195868 : Nat := 4983230072969 + 3 ^ 40 * 195868 * 2
def baseEnd_195868 : Nat := 89399492297728799332645

theorem tailTrace_195868 : CollatzResearch.WordTrace tailWord_195868 prefixEnd_195868 89399492297728799332645 := by
  unfold tailWord_195868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571946427205581218146129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4762595236274108290861505 3571946427205581218146129)
  ·
    refine ⟨2678959820404185913609597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3571946427205581218146129 2678959820404185913609597)
    ·
      refine ⟨1004609932651569717603599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2678959820404185913609597 1004609932651569717603599)
      ·
        refine ⟨1506914898977354576405399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004609932651569717603599 1506914898977354576405399)
        ·
          refine ⟨2260372348466031864608099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506914898977354576405399 2260372348466031864608099)
          ·
            refine ⟨3390558522699047796912149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260372348466031864608099 3390558522699047796912149)
            ·
              refine ⟨158932430751517865480257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3390558522699047796912149 158932430751517865480257)
              ·
                refine ⟨119199323063638399110193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158932430751517865480257 119199323063638399110193)
                ·
                  refine ⟨89399492297728799332645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119199323063638399110193 89399492297728799332645)
                  ·
                    rfl

theorem cell20_195868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_195868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195868 prefixEnd_195868 := by exact prefixLift 195868
  have htrace : WordTrace (prefixWord ++ tailWord_195868) baseStart_195868 baseEnd_195868 := by
    simpa [prefixWord, tailWord_195868, baseEnd_195868] using wordTrace_append hprefix tailTrace_195868
  have hstable : (prefixWord ++ tailWord_195868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195868).length < 2 ^ (prefixWord ++ tailWord_195868).sum := by decide
  have hdescent : baseEnd_195868 < baseStart_195868 := by decide
  rcases family_descends (prefixWord ++ tailWord_195868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195882 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_195882 : Nat := 118140960795 + 195882 * 2 ^ 59
def prefixEnd_195882 : Nat := 4983230072969 + 3 ^ 40 * 195882 * 2
def baseEnd_195882 : Nat := 89405882279206972865921

theorem tailTrace_195882 : CollatzResearch.WordTrace tailWord_195882 prefixEnd_195882 89405882279206972865921 := by
  unfold tailWord_195882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786100869090110706825475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4762935650906961884867933 1786100869090110706825475)
  ·
    refine ⟨2679151303635166060238213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786100869090110706825475 2679151303635166060238213)
    ·
      refine ⟨502340869431593636294665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2679151303635166060238213 502340869431593636294665)
      ·
        refine ⟨376755652073695227220999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502340869431593636294665 376755652073695227220999)
        ·
          refine ⟨565133478110542840831499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376755652073695227220999 565133478110542840831499)
          ·
            refine ⟨847700217165814261247249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565133478110542840831499 847700217165814261247249)
            ·
              refine ⟨635775162874360695935437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847700217165814261247249 635775162874360695935437)
              ·
                refine ⟨238415686077885260975789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635775162874360695935437 238415686077885260975789)
                ·
                  refine ⟨89405882279206972865921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238415686077885260975789 89405882279206972865921)
                  ·
                    rfl

theorem cell20_195882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_195882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195882 prefixEnd_195882 := by exact prefixLift 195882
  have htrace : WordTrace (prefixWord ++ tailWord_195882) baseStart_195882 baseEnd_195882 := by
    simpa [prefixWord, tailWord_195882, baseEnd_195882] using wordTrace_append hprefix tailTrace_195882
  have hstable : (prefixWord ++ tailWord_195882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195882).length < 2 ^ (prefixWord ++ tailWord_195882).sum := by decide
  have hdescent : baseEnd_195882 < baseStart_195882 := by decide
  rcases family_descends (prefixWord ++ tailWord_195882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195927 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 2]
def baseStart_195927 : Nat := 118140960795 + 195927 * 2 ^ 59
def prefixEnd_195927 : Nat := 4983230072969 + 3 ^ 40 * 195927 * 2
def baseEnd_195927 : Nat := 89426421505386816365737

theorem tailTrace_195927 : CollatzResearch.WordTrace tailWord_195927 prefixEnd_195927 89426421505386816365737 := by
  unfold tailWord_195927
  simp only [CollatzResearch.WordTrace]
  refine ⟨7146044761197415512690035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4764029840798277008460023 7146044761197415512690035)
  ·
    refine ⟨10719067141796123269035053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7146044761197415512690035 10719067141796123269035053)
    ·
      refine ⟨4019650178173546225888145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10719067141796123269035053 4019650178173546225888145)
      ·
        refine ⟨3014737633630159669416109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4019650178173546225888145 3014737633630159669416109)
        ·
          refine ⟨1130526612611309876031041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3014737633630159669416109 1130526612611309876031041)
          ·
            refine ⟨847894959458482407023281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130526612611309876031041 847894959458482407023281)
            ·
              refine ⟨635921219593861805267461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847894959458482407023281 635921219593861805267461)
              ·
                refine ⟨119235228673849088487649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635921219593861805267461 119235228673849088487649)
                ·
                  refine ⟨89426421505386816365737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119235228673849088487649 89426421505386816365737)
                  ·
                    rfl

theorem cell20_195927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 2].length) (baseStart_195927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195927 prefixEnd_195927 := by exact prefixLift 195927
  have htrace : WordTrace (prefixWord ++ tailWord_195927) baseStart_195927 baseEnd_195927 := by
    simpa [prefixWord, tailWord_195927, baseEnd_195927] using wordTrace_append hprefix tailTrace_195927
  have hstable : (prefixWord ++ tailWord_195927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195927).length < 2 ^ (prefixWord ++ tailWord_195927).sum := by decide
  have hdescent : baseEnd_195927 < baseStart_195927 := by decide
  rcases family_descends (prefixWord ++ tailWord_195927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195933 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 3]
def baseStart_195933 : Nat := 118140960795 + 195933 * 2 ^ 59
def prefixEnd_195933 : Nat := 4983230072969 + 3 ^ 40 * 195933 * 2
def baseEnd_195933 : Nat := 89429160068877462165713

theorem tailTrace_195933 : CollatzResearch.WordTrace tailWord_195933 prefixEnd_195933 89429160068877462165713 := by
  unfold tailWord_195933
  simp only [CollatzResearch.WordTrace]
  refine ⟨7146263599175678537408453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4764175732783785691605635 7146263599175678537408453)
  ·
    refine ⟨1339924424845439725764085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7146263599175678537408453 1339924424845439725764085)
    ·
      refine ⟨125617914829259974290383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1339924424845439725764085 125617914829259974290383)
      ·
        refine ⟨188426872243889961435575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125617914829259974290383 188426872243889961435575)
        ·
          refine ⟨282640308365834942153363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188426872243889961435575 282640308365834942153363)
          ·
            refine ⟨423960462548752413230045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282640308365834942153363 423960462548752413230045)
            ·
              refine ⟨158985173455782154961267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423960462548752413230045 158985173455782154961267)
              ·
                refine ⟨238477760183673232441901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158985173455782154961267 238477760183673232441901)
                ·
                  refine ⟨89429160068877462165713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238477760183673232441901 89429160068877462165713)
                  ·
                    rfl

theorem cell20_195933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_195933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195933 prefixEnd_195933 := by exact prefixLift 195933
  have htrace : WordTrace (prefixWord ++ tailWord_195933) baseStart_195933 baseEnd_195933 := by
    simpa [prefixWord, tailWord_195933, baseEnd_195933] using wordTrace_append hprefix tailTrace_195933
  have hstable : (prefixWord ++ tailWord_195933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195933).length < 2 ^ (prefixWord ++ tailWord_195933).sum := by decide
  have hdescent : baseEnd_195933 < baseStart_195933 := by decide
  rcases family_descends (prefixWord ++ tailWord_195933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195948 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_195948 : Nat := 118140960795 + 195948 * 2 ^ 59
def prefixEnd_195948 : Nat := 4983230072969 + 3 ^ 40 * 195948 * 2
def baseEnd_195948 : Nat := 89436006477604076665651

theorem tailTrace_195948 : CollatzResearch.WordTrace tailWord_195948 prefixEnd_195948 89436006477604076665651 := by
  unfold tailWord_195948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573405347060668049602249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4764540462747557399469665 3573405347060668049602249)
  ·
    refine ⟨2680054010295501037201687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3573405347060668049602249 2680054010295501037201687)
    ·
      refine ⟨4020081015443251555802531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680054010295501037201687 4020081015443251555802531)
      ·
        refine ⟨6030121523164877333703797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020081015443251555802531 6030121523164877333703797)
        ·
          refine ⟨565323892796707250034731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6030121523164877333703797 565323892796707250034731)
          ·
            refine ⟨847985839195060875052097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565323892796707250034731 847985839195060875052097)
            ·
              refine ⟨635989379396295656289073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847985839195060875052097 635989379396295656289073)
              ·
                refine ⟨476992034547221742216805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635989379396295656289073 476992034547221742216805)
                ·
                  refine ⟨89436006477604076665651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476992034547221742216805 89436006477604076665651)
                  ·
                    rfl

theorem cell20_195948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_195948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195948 prefixEnd_195948 := by exact prefixLift 195948
  have htrace : WordTrace (prefixWord ++ tailWord_195948) baseStart_195948 baseEnd_195948 := by
    simpa [prefixWord, tailWord_195948, baseEnd_195948] using wordTrace_append hprefix tailTrace_195948
  have hstable : (prefixWord ++ tailWord_195948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195948).length < 2 ^ (prefixWord ++ tailWord_195948).sum := by decide
  have hdescent : baseEnd_195948 < baseStart_195948 := by decide
  rcases family_descends (prefixWord ++ tailWord_195948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195982 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_195982 : Nat := 118140960795 + 195982 * 2 ^ 59
def prefixEnd_195982 : Nat := 4983230072969 + 3 ^ 40 * 195982 * 2
def baseEnd_195982 : Nat := 89451525004051069532179

theorem tailTrace_195982 : CollatzResearch.WordTrace tailWord_195982 prefixEnd_195982 89451525004051069532179 := by
  unfold tailWord_195982
  simp only [CollatzResearch.WordTrace]
  refine ⟨893506346999769988242775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4765367183998773270628133 893506346999769988242775)
  ·
    refine ⟨1340259520499654982364163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 893506346999769988242775 1340259520499654982364163)
    ·
      refine ⟨2010389280749482473546245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340259520499654982364163 2010389280749482473546245)
      ·
        refine ⟨376947990140527963789921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2010389280749482473546245 376947990140527963789921)
        ·
          refine ⟨282710992605395972842441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376947990140527963789921 282710992605395972842441)
          ·
            refine ⟨212033244454046979631831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282710992605395972842441 212033244454046979631831)
            ·
              refine ⟨318049866681070469447747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212033244454046979631831 318049866681070469447747)
              ·
                refine ⟨477074800021605704171621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318049866681070469447747 477074800021605704171621)
                ·
                  refine ⟨89451525004051069532179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477074800021605704171621 89451525004051069532179)
                  ·
                    rfl

theorem cell20_195982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_195982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195982 prefixEnd_195982 := by exact prefixLift 195982
  have htrace : WordTrace (prefixWord ++ tailWord_195982) baseStart_195982 baseEnd_195982 := by
    simpa [prefixWord, tailWord_195982, baseEnd_195982] using wordTrace_append hprefix tailTrace_195982
  have hstable : (prefixWord ++ tailWord_195982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195982).length < 2 ^ (prefixWord ++ tailWord_195982).sum := by decide
  have hdescent : baseEnd_195982 < baseStart_195982 := by decide
  rcases family_descends (prefixWord ++ tailWord_195982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195992 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 3]
def baseStart_195992 : Nat := 118140960795 + 195992 * 2 ^ 59
def prefixEnd_195992 : Nat := 4983230072969 + 3 ^ 40 * 195992 * 2
def baseEnd_195992 : Nat := 89456089276535479198805

theorem tailTrace_195992 : CollatzResearch.WordTrace tailWord_195992 prefixEnd_195992 89456089276535479198805 := by
  unfold tailWord_195992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574207752980965806903115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4765610337307954409204153 3574207752980965806903115)
  ·
    refine ⟨5361311629471448710354673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3574207752980965806903115 5361311629471448710354673)
    ·
      refine ⟨4020983722103586532766005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5361311629471448710354673 4020983722103586532766005)
      ·
        refine ⟨376967223947211237446813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4020983722103586532766005 376967223947211237446813)
        ·
          refine ⟨141362708980204214042555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376967223947211237446813 141362708980204214042555)
          ·
            refine ⟨212044063470306321063833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141362708980204214042555 212044063470306321063833)
            ·
              refine ⟨159033047602729740797875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212044063470306321063833 159033047602729740797875)
              ·
                refine ⟨238549571404094611196813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159033047602729740797875 238549571404094611196813)
                ·
                  refine ⟨89456089276535479198805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238549571404094611196813 89456089276535479198805)
                  ·
                    rfl

theorem cell20_195992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_195992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195992 prefixEnd_195992 := by exact prefixLift 195992
  have htrace : WordTrace (prefixWord ++ tailWord_195992) baseStart_195992 baseEnd_195992 := by
    simpa [prefixWord, tailWord_195992, baseEnd_195992] using wordTrace_append hprefix tailTrace_195992
  have hstable : (prefixWord ++ tailWord_195992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195992).length < 2 ^ (prefixWord ++ tailWord_195992).sum := by decide
  have hdescent : baseEnd_195992 < baseStart_195992 := by decide
  rcases family_descends (prefixWord ++ tailWord_195992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195993 : List Nat := [1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_195993 : Nat := 118140960795 + 195993 * 2 ^ 59
def prefixEnd_195993 : Nat := 4983230072969 + 3 ^ 40 * 195993 * 2
def baseEnd_195993 : Nat := 29818848567927973388489

theorem tailTrace_195993 : CollatzResearch.WordTrace tailWord_195993 prefixEnd_195993 29818848567927973388489 := by
  unfold tailWord_195993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148451978958308784592633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4765634652638872523061755 7148451978958308784592633)
  ·
    refine ⟨5361338984218731588444475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7148451978958308784592633 5361338984218731588444475)
    ·
      refine ⟨8042008476328097382666713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5361338984218731588444475 8042008476328097382666713)
      ·
        refine ⟨6031506357246073037000035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8042008476328097382666713 6031506357246073037000035)
        ·
          refine ⟨9047259535869109555500053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031506357246073037000035 9047259535869109555500053)
          ·
            refine ⟨424090290743864510414065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9047259535869109555500053 424090290743864510414065)
            ·
              refine ⟨318067718057898382810549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424090290743864510414065 318067718057898382810549)
              ·
                refine ⟨29818848567927973388489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318067718057898382810549 29818848567927973388489)
                ·
                  rfl

theorem cell20_195993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_195993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195993 prefixEnd_195993 := by exact prefixLift 195993
  have htrace : WordTrace (prefixWord ++ tailWord_195993) baseStart_195993 baseEnd_195993 := by
    simpa [prefixWord, tailWord_195993, baseEnd_195993] using wordTrace_append hprefix tailTrace_195993
  have hstable : (prefixWord ++ tailWord_195993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195993).length < 2 ^ (prefixWord ++ tailWord_195993).sum := by decide
  have hdescent : baseEnd_195993 < baseStart_195993 := by decide
  rcases family_descends (prefixWord ++ tailWord_195993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196090 : List Nat := [3, 1, 1, 1, 1, 2, 11]
def baseStart_196090 : Nat := 118140960795 + 196090 * 2 ^ 59
def prefixEnd_196090 : Nat := 4983230072969 + 3 ^ 40 * 196090 * 2
def baseEnd_196090 : Nat := 9944535460764743770193

theorem tailTrace_196090 : CollatzResearch.WordTrace tailWord_196090 prefixEnd_196090 9944535460764743770193 := by
  unfold tailWord_196090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787997464901723587718431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4767993239737929567249149 1787997464901723587718431)
  ·
    refine ⟨2681996197352585381577647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1787997464901723587718431 2681996197352585381577647)
    ·
      refine ⟨4022994296028878072366471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2681996197352585381577647 4022994296028878072366471)
      ·
        refine ⟨6034491444043317108549707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4022994296028878072366471 6034491444043317108549707)
        ·
          refine ⟨9051737166064975662824561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034491444043317108549707 9051737166064975662824561)
          ·
            refine ⟨6788802874548731747118421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9051737166064975662824561 6788802874548731747118421)
            ·
              refine ⟨9944535460764743770193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6788802874548731747118421 9944535460764743770193)
              ·
                rfl

theorem cell20_196090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_196090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196090 prefixEnd_196090 := by exact prefixLift 196090
  have htrace : WordTrace (prefixWord ++ tailWord_196090) baseStart_196090 baseEnd_196090 := by
    simpa [prefixWord, tailWord_196090, baseEnd_196090] using wordTrace_append hprefix tailTrace_196090
  have hstable : (prefixWord ++ tailWord_196090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196090).length < 2 ^ (prefixWord ++ tailWord_196090).sum := by decide
  have hdescent : baseEnd_196090 < baseStart_196090 := by decide
  rcases family_descends (prefixWord ++ tailWord_196090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196093 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_196093 : Nat := 118140960795 + 196093 * 2 ^ 59
def prefixEnd_196093 : Nat := 4983230072969 + 3 ^ 40 * 196093 * 2
def baseEnd_196093 : Nat := 89502188428628016831725

theorem tailTrace_196093 : CollatzResearch.WordTrace tailWord_196093 prefixEnd_196093 89502188428628016831725 := by
  unfold tailWord_196093
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152099278596025863232933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4768066185730683908821955 7152099278596025863232933)
  ·
    refine ⟨1341018614736754849356175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7152099278596025863232933 1341018614736754849356175)
    ·
      refine ⟨2011527922105132274034263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341018614736754849356175 2011527922105132274034263)
      ·
        refine ⟨3017291883157698411051395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011527922105132274034263 3017291883157698411051395)
        ·
          refine ⟨4525937824736547616577093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017291883157698411051395 4525937824736547616577093)
          ·
            refine ⟨848613342138102678108205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4525937824736547616577093 848613342138102678108205)
            ·
              refine ⟨318230003301788504290577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 848613342138102678108205 318230003301788504290577)
              ·
                refine ⟨238672502476341378217933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318230003301788504290577 238672502476341378217933)
                ·
                  refine ⟨89502188428628016831725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238672502476341378217933 89502188428628016831725)
                  ·
                    rfl

theorem cell20_196093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_196093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196093 prefixEnd_196093 := by exact prefixLift 196093
  have htrace : WordTrace (prefixWord ++ tailWord_196093) baseStart_196093 baseEnd_196093 := by
    simpa [prefixWord, tailWord_196093, baseEnd_196093] using wordTrace_append hprefix tailTrace_196093
  have hstable : (prefixWord ++ tailWord_196093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196093).length < 2 ^ (prefixWord ++ tailWord_196093).sum := by decide
  have hdescent : baseEnd_196093 < baseStart_196093 := by decide
  rcases family_descends (prefixWord ++ tailWord_196093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196126 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_196126 : Nat := 118140960795 + 196126 * 2 ^ 59
def prefixEnd_196126 : Nat := 4983230072969 + 3 ^ 40 * 196126 * 2
def baseEnd_196126 : Nat := 89517250527826568731591

theorem tailTrace_196126 : CollatzResearch.WordTrace tailWord_196126 prefixEnd_196126 89517250527826568731591 := by
  unfold tailWord_196126
  simp only [CollatzResearch.WordTrace]
  refine ⟨894162860934559062398029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4768868591650981666122821 894162860934559062398029)
  ·
    refine ⟨335311072850459648399261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 894162860934559062398029 335311072850459648399261)
    ·
      refine ⟨125741652318922368149723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335311072850459648399261 125741652318922368149723)
      ·
        refine ⟨188612478478383552224585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125741652318922368149723 188612478478383552224585)
        ·
          refine ⟨141459358858787664168439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188612478478383552224585 141459358858787664168439)
          ·
            refine ⟨212189038288181496252659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141459358858787664168439 212189038288181496252659)
            ·
              refine ⟨318283557432272244378989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212189038288181496252659 318283557432272244378989)
              ·
                refine ⟨119356334037102091642121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318283557432272244378989 119356334037102091642121)
                ·
                  refine ⟨89517250527826568731591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119356334037102091642121 89517250527826568731591)
                  ·
                    rfl

theorem cell20_196126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_196126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196126 prefixEnd_196126 := by exact prefixLift 196126
  have htrace : WordTrace (prefixWord ++ tailWord_196126) baseStart_196126 baseEnd_196126 := by
    simpa [prefixWord, tailWord_196126, baseEnd_196126] using wordTrace_append hprefix tailTrace_196126
  have hstable : (prefixWord ++ tailWord_196126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196126).length < 2 ^ (prefixWord ++ tailWord_196126).sum := by decide
  have hdescent : baseEnd_196126 < baseStart_196126 := by decide
  rcases family_descends (prefixWord ++ tailWord_196126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196152 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_196152 : Nat := 118140960795 + 196152 * 2 ^ 59
def prefixEnd_196152 : Nat := 4983230072969 + 3 ^ 40 * 196152 * 2
def baseEnd_196152 : Nat := 89529117636286033864817

theorem tailTrace_196152 : CollatzResearch.WordTrace tailWord_196152 prefixEnd_196152 89529117636286033864817 := by
  unfold tailWord_196152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577125592691139469815355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4769500790254852626420473 3577125592691139469815355)
  ·
    refine ⟨5365688389036709204723033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3577125592691139469815355 5365688389036709204723033)
    ·
      refine ⟨4024266291777531903542275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5365688389036709204723033 4024266291777531903542275)
      ·
        refine ⟨6036399437666297855313413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024266291777531903542275 6036399437666297855313413)
        ·
          refine ⟨1131824894562430847871265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6036399437666297855313413 1131824894562430847871265)
          ·
            refine ⟨848868670921823135903449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131824894562430847871265 848868670921823135903449)
            ·
              refine ⟨636651503191367351927587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848868670921823135903449 636651503191367351927587)
              ·
                refine ⟨954977254787051027891381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636651503191367351927587 954977254787051027891381)
                ·
                  refine ⟨89529117636286033864817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 954977254787051027891381 89529117636286033864817)
                  ·
                    rfl

theorem cell20_196152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_196152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196152 prefixEnd_196152 := by exact prefixLift 196152
  have htrace : WordTrace (prefixWord ++ tailWord_196152) baseStart_196152 baseEnd_196152 := by
    simpa [prefixWord, tailWord_196152, baseEnd_196152] using wordTrace_append hprefix tailTrace_196152
  have hstable : (prefixWord ++ tailWord_196152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196152).length < 2 ^ (prefixWord ++ tailWord_196152).sum := by decide
  have hdescent : baseEnd_196152 < baseStart_196152 := by decide
  rcases family_descends (prefixWord ++ tailWord_196152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196206 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_196206 : Nat := 118140960795 + 196206 * 2 ^ 59
def prefixEnd_196206 : Nat := 4983230072969 + 3 ^ 40 * 196206 * 2
def baseEnd_196206 : Nat := 89553764707701846064597

theorem tailTrace_196206 : CollatzResearch.WordTrace tailWord_196206 prefixEnd_196206 89553764707701846064597 := by
  unfold tailWord_196206
  simp only [CollatzResearch.WordTrace]
  refine ⟨894527590898330770262059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4770813818124430774730981 894527590898330770262059)
  ·
    refine ⟨1341791386347496155393089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 894527590898330770262059 1341791386347496155393089)
    ·
      refine ⟨1006343539760622116544817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1341791386347496155393089 1006343539760622116544817)
      ·
        refine ⟨754757654820466587408613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1006343539760622116544817 754757654820466587408613)
        ·
          refine ⟨141517060278837485139115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 754757654820466587408613 141517060278837485139115)
          ·
            refine ⟨212275590418256227708673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141517060278837485139115 212275590418256227708673)
            ·
              refine ⟨159206692813692170781505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212275590418256227708673 159206692813692170781505)
              ·
                refine ⟨119405019610269128086129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159206692813692170781505 119405019610269128086129)
                ·
                  refine ⟨89553764707701846064597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119405019610269128086129 89553764707701846064597)
                  ·
                    rfl

theorem cell20_196206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_196206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196206 prefixEnd_196206 := by exact prefixLift 196206
  have htrace : WordTrace (prefixWord ++ tailWord_196206) baseStart_196206 baseEnd_196206 := by
    simpa [prefixWord, tailWord_196206, baseEnd_196206] using wordTrace_append hprefix tailTrace_196206
  have hstable : (prefixWord ++ tailWord_196206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196206).length < 2 ^ (prefixWord ++ tailWord_196206).sum := by decide
  have hdescent : baseEnd_196206 < baseStart_196206 := by decide
  rcases family_descends (prefixWord ++ tailWord_196206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196210 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_196210 : Nat := 118140960795 + 196210 * 2 ^ 59
def prefixEnd_196210 : Nat := 4983230072969 + 3 ^ 40 * 196210 * 2
def baseEnd_196210 : Nat := 89555590416695609931247

theorem tailTrace_196210 : CollatzResearch.WordTrace tailWord_196210 prefixEnd_196210 89555590416695609931247 := by
  unfold tailWord_196210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789091654793038711310521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4770911079448103230161389 1789091654793038711310521)
  ·
    refine ⟨1341818741094779033482891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1789091654793038711310521 1341818741094779033482891)
    ·
      refine ⟨2012728111642168550224337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341818741094779033482891 2012728111642168550224337)
      ·
        refine ⟨1509546083731626412668253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2012728111642168550224337 1509546083731626412668253)
        ·
          refine ⟨566079781399359904750595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1509546083731626412668253 566079781399359904750595)
          ·
            refine ⟨849119672099039857125893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566079781399359904750595 849119672099039857125893)
            ·
              refine ⟨159209938518569973211105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 849119672099039857125893 159209938518569973211105)
              ·
                refine ⟨119407453888927479908329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159209938518569973211105 119407453888927479908329)
                ·
                  refine ⟨89555590416695609931247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119407453888927479908329 89555590416695609931247)
                  ·
                    rfl

theorem cell20_196210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_196210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196210 prefixEnd_196210 := by exact prefixLift 196210
  have htrace : WordTrace (prefixWord ++ tailWord_196210) baseStart_196210 baseEnd_196210 := by
    simpa [prefixWord, tailWord_196210, baseEnd_196210] using wordTrace_append hprefix tailTrace_196210
  have hstable : (prefixWord ++ tailWord_196210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196210).length < 2 ^ (prefixWord ++ tailWord_196210).sum := by decide
  have hdescent : baseEnd_196210 < baseStart_196210 := by decide
  rcases family_descends (prefixWord ++ tailWord_196210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196211 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_196211 : Nat := 118140960795 + 196211 * 2 ^ 59
def prefixEnd_196211 : Nat := 4983230072969 + 3 ^ 40 * 196211 * 2
def baseEnd_196211 : Nat := 89556046843944050897909

theorem tailTrace_196211 : CollatzResearch.WordTrace tailWord_196211 prefixEnd_196211 89556046843944050897909 := by
  unfold tailWord_196211
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156403092168532016028487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4770935394779021344018991 7156403092168532016028487)
  ·
    refine ⟨10734604638252798024042731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7156403092168532016028487 10734604638252798024042731)
    ·
      refine ⟨16101906957379197036064097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10734604638252798024042731 16101906957379197036064097)
      ·
        refine ⟨12076430218034397777048073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16101906957379197036064097 12076430218034397777048073)
        ·
          refine ⟨9057322663525798332786055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12076430218034397777048073 9057322663525798332786055)
          ·
            refine ⟨13585983995288697499179083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057322663525798332786055 13585983995288697499179083)
            ·
              refine ⟨20378975992933046248768625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13585983995288697499179083 20378975992933046248768625)
              ·
                refine ⟨15284231994699784686576469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20378975992933046248768625 15284231994699784686576469)
                ·
                  refine ⟨89556046843944050897909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15284231994699784686576469 89556046843944050897909)
                  ·
                    rfl

theorem cell20_196211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_196211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196211 prefixEnd_196211 := by exact prefixLift 196211
  have htrace : WordTrace (prefixWord ++ tailWord_196211) baseStart_196211 baseEnd_196211 := by
    simpa [prefixWord, tailWord_196211, baseEnd_196211] using wordTrace_append hprefix tailTrace_196211
  have hstable : (prefixWord ++ tailWord_196211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196211).length < 2 ^ (prefixWord ++ tailWord_196211).sum := by decide
  have hdescent : baseEnd_196211 < baseStart_196211 := by decide
  rcases family_descends (prefixWord ++ tailWord_196211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196221 : List Nat := [1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_196221 : Nat := 118140960795 + 196221 * 2 ^ 59
def prefixEnd_196221 : Nat := 4983230072969 + 3 ^ 40 * 196221 * 2
def baseEnd_196221 : Nat := 29853537038809486854845

theorem tailTrace_196221 : CollatzResearch.WordTrace tailWord_196221 prefixEnd_196221 29853537038809486854845 := by
  unfold tailWord_196221
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156767822132303723892517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4771178548088202482595011 7156767822132303723892517)
  ·
    refine ⟨1341893966649806948229847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7156767822132303723892517 1341893966649806948229847)
    ·
      refine ⟨2012840949974710422344771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341893966649806948229847 2012840949974710422344771)
      ·
        refine ⟨3019261424962065633517157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012840949974710422344771 3019261424962065633517157)
        ·
          refine ⟨566111517180387306284467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3019261424962065633517157 566111517180387306284467)
          ·
            refine ⟨849167275770580959426701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566111517180387306284467 849167275770580959426701)
            ·
              refine ⟨318437728413967859785013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849167275770580959426701 318437728413967859785013)
              ·
                refine ⟨29853537038809486854845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318437728413967859785013 29853537038809486854845)
                ·
                  rfl

theorem cell20_196221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_196221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196221 prefixEnd_196221 := by exact prefixLift 196221
  have htrace : WordTrace (prefixWord ++ tailWord_196221) baseStart_196221 baseEnd_196221 := by
    simpa [prefixWord, tailWord_196221, baseEnd_196221] using wordTrace_append hprefix tailTrace_196221
  have hstable : (prefixWord ++ tailWord_196221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196221).length < 2 ^ (prefixWord ++ tailWord_196221).sum := by decide
  have hdescent : baseEnd_196221 < baseStart_196221 := by decide
  rcases family_descends (prefixWord ++ tailWord_196221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196235 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_196235 : Nat := 118140960795 + 196235 * 2 ^ 59
def prefixEnd_196235 : Nat := 4983230072969 + 3 ^ 40 * 196235 * 2
def baseEnd_196235 : Nat := 89567001097906634097811

theorem tailTrace_196235 : CollatzResearch.WordTrace tailWord_196235 prefixEnd_196235 89567001097906634097811 := by
  unfold tailWord_196235
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157278444081584114902159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4771518962721056076601439 7157278444081584114902159)
  ·
    refine ⟨10735917666122376172353239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7157278444081584114902159 10735917666122376172353239)
    ·
      refine ⟨16103876499183564258529859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735917666122376172353239 16103876499183564258529859)
      ·
        refine ⟨24155814748775346387794789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16103876499183564258529859 24155814748775346387794789)
        ·
          refine ⟨4529215265395377447711523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24155814748775346387794789 4529215265395377447711523)
          ·
            refine ⟨6793822898093066171567285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529215265395377447711523 6793822898093066171567285)
            ·
              refine ⟨636920896696224953584433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6793822898093066171567285 636920896696224953584433)
              ·
                refine ⟨477690672522168715188325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636920896696224953584433 477690672522168715188325)
                ·
                  refine ⟨89567001097906634097811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477690672522168715188325 89567001097906634097811)
                  ·
                    rfl

theorem cell20_196235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_196235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196235 prefixEnd_196235 := by exact prefixLift 196235
  have htrace : WordTrace (prefixWord ++ tailWord_196235) baseStart_196235 baseEnd_196235 := by
    simpa [prefixWord, tailWord_196235, baseEnd_196235] using wordTrace_append hprefix tailTrace_196235
  have hstable : (prefixWord ++ tailWord_196235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196235).length < 2 ^ (prefixWord ++ tailWord_196235).sum := by decide
  have hdescent : baseEnd_196235 < baseStart_196235 := by decide
  rcases family_descends (prefixWord ++ tailWord_196235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196238 : List Nat := [4, 1, 1, 3, 1, 3, 3, 4]
def baseStart_196238 : Nat := 118140960795 + 196238 * 2 ^ 59
def prefixEnd_196238 : Nat := 4983230072969 + 3 ^ 40 * 196238 * 2
def baseEnd_196238 : Nat := 29856123459883985665933

theorem tailTrace_196238 : CollatzResearch.WordTrace tailWord_196238 prefixEnd_196238 29856123459883985665933 := by
  unfold tailWord_196238
  simp only [CollatzResearch.WordTrace]
  refine ⟨894673482883839453407671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4771591908713810418174245 894673482883839453407671)
  ·
    refine ⟨1342010224325759180111507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 894673482883839453407671 1342010224325759180111507)
    ·
      refine ⟨2013015336488638770167261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342010224325759180111507 2013015336488638770167261)
      ·
        refine ⟨754880751183239538812723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2013015336488638770167261 754880751183239538812723)
        ·
          refine ⟨1132321126774859308219085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754880751183239538812723 1132321126774859308219085)
          ·
            refine ⟨424620422540572240582157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1132321126774859308219085 424620422540572240582157)
            ·
              refine ⟨159232658452714590218309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424620422540572240582157 159232658452714590218309)
              ·
                refine ⟨29856123459883985665933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159232658452714590218309 29856123459883985665933)
                ·
                  rfl

theorem cell20_196238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_196238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196238 prefixEnd_196238 := by exact prefixLift 196238
  have htrace : WordTrace (prefixWord ++ tailWord_196238) baseStart_196238 baseEnd_196238 := by
    simpa [prefixWord, tailWord_196238, baseEnd_196238] using wordTrace_append hprefix tailTrace_196238
  have hstable : (prefixWord ++ tailWord_196238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196238).length < 2 ^ (prefixWord ++ tailWord_196238).sum := by decide
  have hdescent : baseEnd_196238 < baseStart_196238 := by decide
  rcases family_descends (prefixWord ++ tailWord_196238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196258 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_196258 : Nat := 118140960795 + 196258 * 2 ^ 59
def prefixEnd_196258 : Nat := 4983230072969 + 3 ^ 40 * 196258 * 2
def baseEnd_196258 : Nat := 89577498924620776331051

theorem tailTrace_196258 : CollatzResearch.WordTrace tailWord_196258 prefixEnd_196258 89577498924620776331051 := by
  unfold tailWord_196258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789529330749564760747357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4772078215332172695326285 1789529330749564760747357)
  ·
    refine ⟨671073499031086785280259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1789529330749564760747357 671073499031086785280259)
    ·
      refine ⟨1006610248546630177920389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671073499031086785280259 1006610248546630177920389)
      ·
        refine ⟨188739421602493158360073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1006610248546630177920389 188739421602493158360073)
        ·
          refine ⟨141554566201869868770055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188739421602493158360073 141554566201869868770055)
          ·
            refine ⟨212331849302804803155083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141554566201869868770055 212331849302804803155083)
            ·
              refine ⟨318497773954207204732625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212331849302804803155083 318497773954207204732625)
              ·
                refine ⟨238873330465655403549469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318497773954207204732625 238873330465655403549469)
                ·
                  refine ⟨89577498924620776331051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238873330465655403549469 89577498924620776331051)
                  ·
                    rfl

theorem cell20_196258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_196258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196258 prefixEnd_196258 := by exact prefixLift 196258
  have htrace : WordTrace (prefixWord ++ tailWord_196258) baseStart_196258 baseEnd_196258 := by
    simpa [prefixWord, tailWord_196258, baseEnd_196258] using wordTrace_append hprefix tailTrace_196258
  have hstable : (prefixWord ++ tailWord_196258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196258).length < 2 ^ (prefixWord ++ tailWord_196258).sum := by decide
  have hdescent : baseEnd_196258 < baseStart_196258 := by decide
  rcases family_descends (prefixWord ++ tailWord_196258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196269 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 2]
def baseStart_196269 : Nat := 118140960795 + 196269 * 2 ^ 59
def prefixEnd_196269 : Nat := 4983230072969 + 3 ^ 40 * 196269 * 2
def baseEnd_196269 : Nat := 89582519624353626964339

theorem tailTrace_196269 : CollatzResearch.WordTrace tailWord_196269 prefixEnd_196269 89582519624353626964339 := by
  unfold tailWord_196269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158518525958407921639861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4772345683972271947759907 7158518525958407921639861)
  ·
    refine ⟨671111111808600742653737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7158518525958407921639861 671111111808600742653737)
    ·
      refine ⟨503333333856450556990303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 671111111808600742653737 503333333856450556990303)
      ·
        refine ⟨755000000784675835485455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503333333856450556990303 755000000784675835485455)
        ·
          refine ⟨1132500001177013753228183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755000000784675835485455 1132500001177013753228183)
          ·
            refine ⟨1698750001765520629842275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132500001177013753228183 1698750001765520629842275)
            ·
              refine ⟨2548125002648280944763413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698750001765520629842275 2548125002648280944763413)
              ·
                refine ⟨119443359499138169285785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2548125002648280944763413 119443359499138169285785)
                ·
                  refine ⟨89582519624353626964339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119443359499138169285785 89582519624353626964339)
                  ·
                    rfl

theorem cell20_196269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_196269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196269 prefixEnd_196269 := by exact prefixLift 196269
  have htrace : WordTrace (prefixWord ++ tailWord_196269) baseStart_196269 baseEnd_196269 := by
    simpa [prefixWord, tailWord_196269, baseEnd_196269] using wordTrace_append hprefix tailTrace_196269
  have hstable : (prefixWord ++ tailWord_196269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196269).length < 2 ^ (prefixWord ++ tailWord_196269).sum := by decide
  have hdescent : baseEnd_196269 < baseStart_196269 := by decide
  rcases family_descends (prefixWord ++ tailWord_196269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196310 : List Nat := [5, 2, 1, 3, 2, 1, 6]
def baseStart_196310 : Nat := 118140960795 + 196310 * 2 ^ 59
def prefixEnd_196310 : Nat := 4983230072969 + 3 ^ 40 * 196310 * 2
def baseEnd_196310 : Nat := 9955692571282189621945

theorem tailTrace_196310 : CollatzResearch.WordTrace tailWord_196310 prefixEnd_196310 9955692571282189621945 := by
  unfold tailWord_196310
  simp only [CollatzResearch.WordTrace]
  refine ⟨447500869925616995242649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4773342612539914615921589 447500869925616995242649)
  ·
    refine ⟨335625652444212746431987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 447500869925616995242649 335625652444212746431987)
    ·
      refine ⟨503438478666319119647981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335625652444212746431987 503438478666319119647981)
      ·
        refine ⟨188789429499869669867993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 503438478666319119647981 188789429499869669867993)
        ·
          refine ⟨141592072124902252400995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188789429499869669867993 141592072124902252400995)
          ·
            refine ⟨212388108187353378601493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141592072124902252400995 212388108187353378601493)
            ·
              refine ⟨9955692571282189621945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212388108187353378601493 9955692571282189621945)
              ·
                rfl

theorem cell20_196310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 6].length) (baseStart_196310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196310 prefixEnd_196310 := by exact prefixLift 196310
  have htrace : WordTrace (prefixWord ++ tailWord_196310) baseStart_196310 baseEnd_196310 := by
    simpa [prefixWord, tailWord_196310, baseEnd_196310] using wordTrace_append hprefix tailTrace_196310
  have hstable : (prefixWord ++ tailWord_196310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196310).length < 2 ^ (prefixWord ++ tailWord_196310).sum := by decide
  have hdescent : baseEnd_196310 < baseStart_196310 := by decide
  rcases family_descends (prefixWord ++ tailWord_196310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196328 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_196328 : Nat := 118140960795 + 196328 * 2 ^ 59
def prefixEnd_196328 : Nat := 4983230072969 + 3 ^ 40 * 196328 * 2
def baseEnd_196328 : Nat := 89609448832011643997431

theorem tailTrace_196328 : CollatzResearch.WordTrace tailWord_196328 prefixEnd_196328 89609448832011643997431 := by
  unfold tailWord_196328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580335216372330499018819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4773780288496440665358425 3580335216372330499018819)
  ·
    refine ⟨5370502824558495748528229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3580335216372330499018819 5370502824558495748528229)
    ·
      refine ⟨1006969279604717952849043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5370502824558495748528229 1006969279604717952849043)
      ·
        refine ⟨1510453919407076929273565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006969279604717952849043 1510453919407076929273565)
        ·
          refine ⟨566420219777653848477587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1510453919407076929273565 566420219777653848477587)
          ·
            refine ⟨849630329666480772716381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566420219777653848477587 849630329666480772716381)
            ·
              refine ⟨318611373624930289768643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849630329666480772716381 318611373624930289768643)
              ·
                refine ⟨477917060437395434652965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318611373624930289768643 477917060437395434652965)
                ·
                  refine ⟨89609448832011643997431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477917060437395434652965 89609448832011643997431)
                  ·
                    rfl

theorem cell20_196328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_196328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196328 prefixEnd_196328 := by exact prefixLift 196328
  have htrace : WordTrace (prefixWord ++ tailWord_196328) baseStart_196328 baseEnd_196328 := by
    simpa [prefixWord, tailWord_196328, baseEnd_196328] using wordTrace_append hprefix tailTrace_196328
  have hstable : (prefixWord ++ tailWord_196328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196328).length < 2 ^ (prefixWord ++ tailWord_196328).sum := by decide
  have hdescent : baseEnd_196328 < baseStart_196328 := by decide
  rcases family_descends (prefixWord ++ tailWord_196328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196363 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_196363 : Nat := 118140960795 + 196363 * 2 ^ 59
def prefixEnd_196363 : Nat := 4983230072969 + 3 ^ 40 * 196363 * 2
def baseEnd_196363 : Nat := 89625423785707077830621

theorem tailTrace_196363 : CollatzResearch.WordTrace tailWord_196363 prefixEnd_196363 89625423785707077830621 := by
  unfold tailWord_196363
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161946987617861975561743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4774631325078574650374495 7161946987617861975561743)
  ·
    refine ⟨10742920481426792963342615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7161946987617861975561743 10742920481426792963342615)
    ·
      refine ⟨16114380722140189445013923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742920481426792963342615 16114380722140189445013923)
      ·
        refine ⟨24171571083210284167520885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16114380722140189445013923 24171571083210284167520885)
        ·
          refine ⟨2266084789050964140705083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24171571083210284167520885 2266084789050964140705083)
          ·
            refine ⟨3399127183576446211057625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266084789050964140705083 3399127183576446211057625)
            ·
              refine ⟨2549345387682334658293219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399127183576446211057625 2549345387682334658293219)
              ·
                refine ⟨3824018081523501987439829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549345387682334658293219 3824018081523501987439829)
                ·
                  refine ⟨89625423785707077830621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3824018081523501987439829 89625423785707077830621)
                  ·
                    rfl

theorem cell20_196363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_196363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196363 prefixEnd_196363 := by exact prefixLift 196363
  have htrace : WordTrace (prefixWord ++ tailWord_196363) baseStart_196363 baseEnd_196363 := by
    simpa [prefixWord, tailWord_196363, baseEnd_196363] using wordTrace_append hprefix tailTrace_196363
  have hstable : (prefixWord ++ tailWord_196363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196363).length < 2 ^ (prefixWord ++ tailWord_196363).sum := by decide
  have hdescent : baseEnd_196363 < baseStart_196363 := by decide
  rcases family_descends (prefixWord ++ tailWord_196363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196372 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 3]
def baseStart_196372 : Nat := 118140960795 + 196372 * 2 ^ 59
def prefixEnd_196372 : Nat := 4983230072969 + 3 ^ 40 * 196372 * 2
def baseEnd_196372 : Nat := 89629531630943046530585

theorem tailTrace_196372 : CollatzResearch.WordTrace tailWord_196372 prefixEnd_196372 89629531630943046530585 := by
  unfold tailWord_196372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581137622292628256319685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4774850163056837675092913 3581137622292628256319685)
  ·
    refine ⟨671463304179867798059941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3581137622292628256319685 671463304179867798059941)
    ·
      refine ⟨125899369533725212136239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 671463304179867798059941 125899369533725212136239)
      ·
        refine ⟨188849054300587818204359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125899369533725212136239 188849054300587818204359)
        ·
          refine ⟨283273581450881727306539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188849054300587818204359 283273581450881727306539)
          ·
            refine ⟨424910372176322590959809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283273581450881727306539 424910372176322590959809)
            ·
              refine ⟨318682779132241943219857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424910372176322590959809 318682779132241943219857)
              ·
                refine ⟨239012084349181457414893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318682779132241943219857 239012084349181457414893)
                ·
                  refine ⟨89629531630943046530585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239012084349181457414893 89629531630943046530585)
                  ·
                    rfl

theorem cell20_196372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_196372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196372 prefixEnd_196372 := by exact prefixLift 196372
  have htrace : WordTrace (prefixWord ++ tailWord_196372) baseStart_196372 baseEnd_196372 := by
    simpa [prefixWord, tailWord_196372, baseEnd_196372] using wordTrace_append hprefix tailTrace_196372
  have hstable : (prefixWord ++ tailWord_196372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196372).length < 2 ^ (prefixWord ++ tailWord_196372).sum := by decide
  have hdescent : baseEnd_196372 < baseStart_196372 := by decide
  rcases family_descends (prefixWord ++ tailWord_196372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196404 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_196404 : Nat := 118140960795 + 196404 * 2 ^ 59
def prefixEnd_196404 : Nat := 4983230072969 + 3 ^ 40 * 196404 * 2
def baseEnd_196404 : Nat := 89644137302893157463787

theorem tailTrace_196404 : CollatzResearch.WordTrace tailWord_196404 prefixEnd_196404 89644137302893157463787 := by
  unfold tailWord_196404
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581721190234662988902133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4775628253646217318536177 3581721190234662988902133)
  ·
    refine ⟨335786361584499655209575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3581721190234662988902133 335786361584499655209575)
    ·
      refine ⟨503679542376749482814363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335786361584499655209575 503679542376749482814363)
      ·
        refine ⟨755519313565124224221545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503679542376749482814363 755519313565124224221545)
        ·
          refine ⟨566639485173843168166159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755519313565124224221545 566639485173843168166159)
          ·
            refine ⟨849959227760764752249239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566639485173843168166159 849959227760764752249239)
            ·
              refine ⟨1274938841641147128373859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849959227760764752249239 1274938841641147128373859)
              ·
                refine ⟨1912408262461720692560789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274938841641147128373859 1912408262461720692560789)
                ·
                  refine ⟨89644137302893157463787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1912408262461720692560789 89644137302893157463787)
                  ·
                    rfl

theorem cell20_196404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_196404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196404 prefixEnd_196404 := by exact prefixLift 196404
  have htrace : WordTrace (prefixWord ++ tailWord_196404) baseStart_196404 baseEnd_196404 := by
    simpa [prefixWord, tailWord_196404, baseEnd_196404] using wordTrace_append hprefix tailTrace_196404
  have hstable : (prefixWord ++ tailWord_196404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196404).length < 2 ^ (prefixWord ++ tailWord_196404).sum := by decide
  have hdescent : baseEnd_196404 < baseStart_196404 := by decide
  rcases family_descends (prefixWord ++ tailWord_196404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196442 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_196442 : Nat := 118140960795 + 196442 * 2 ^ 59
def prefixEnd_196442 : Nat := 4983230072969 + 3 ^ 40 * 196442 * 2
def baseEnd_196442 : Nat := 89661481538333914196965

theorem tailTrace_196442 : CollatzResearch.WordTrace tailWord_196442 prefixEnd_196442 89661481538333914196965 := by
  unfold tailWord_196442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791207088582914616921895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4776552236221105645125053 1791207088582914616921895)
  ·
    refine ⟨2686810632874371925382843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791207088582914616921895 2686810632874371925382843)
    ·
      refine ⟨4030215949311557888074265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686810632874371925382843 4030215949311557888074265)
      ·
        refine ⟨3022661961983668416055699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4030215949311557888074265 3022661961983668416055699)
        ·
          refine ⟨4533992942975502624083549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022661961983668416055699 4533992942975502624083549)
          ·
            refine ⟨1700247353615813484031331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4533992942975502624083549 1700247353615813484031331)
            ·
              refine ⟨2550371030423720226046997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700247353615813484031331 2550371030423720226046997)
              ·
                refine ⟨119548642051111885595953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2550371030423720226046997 119548642051111885595953)
                ·
                  refine ⟨89661481538333914196965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119548642051111885595953 89661481538333914196965)
                  ·
                    rfl

theorem cell20_196442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_196442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196442 prefixEnd_196442 := by exact prefixLift 196442
  have htrace : WordTrace (prefixWord ++ tailWord_196442) baseStart_196442 baseEnd_196442 := by
    simpa [prefixWord, tailWord_196442, baseEnd_196442] using wordTrace_append hprefix tailTrace_196442
  have hstable : (prefixWord ++ tailWord_196442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196442).length < 2 ^ (prefixWord ++ tailWord_196442).sum := by decide
  have hdescent : baseEnd_196442 < baseStart_196442 := by decide
  rcases family_descends (prefixWord ++ tailWord_196442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196452 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_196452 : Nat := 118140960795 + 196452 * 2 ^ 59
def prefixEnd_196452 : Nat := 4983230072969 + 3 ^ 40 * 196452 * 2
def baseEnd_196452 : Nat := 89666045810818323863591

theorem tailTrace_196452 : CollatzResearch.WordTrace tailWord_196452 prefixEnd_196452 89666045810818323863591 := by
  unfold tailWord_196452
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582596542147715087775805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4776795389530286783701073 3582596542147715087775805)
  ·
    refine ⟨1343473703305393157915927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3582596542147715087775805 1343473703305393157915927)
    ·
      refine ⟨2015210554958089736873891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343473703305393157915927 2015210554958089736873891)
      ·
        refine ⟨3022815832437134605310837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015210554958089736873891 3022815832437134605310837)
        ·
          refine ⟨283388984290981369247891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3022815832437134605310837 283388984290981369247891)
          ·
            refine ⟨425083476436472053871837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283388984290981369247891 425083476436472053871837)
            ·
              refine ⟨159406303663677020201939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425083476436472053871837 159406303663677020201939)
              ·
                refine ⟨239109455495515530302909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159406303663677020201939 239109455495515530302909)
                ·
                  refine ⟨89666045810818323863591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239109455495515530302909 89666045810818323863591)
                  ·
                    rfl

theorem cell20_196452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_196452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196452 prefixEnd_196452 := by exact prefixLift 196452
  have htrace : WordTrace (prefixWord ++ tailWord_196452) baseStart_196452 baseEnd_196452 := by
    simpa [prefixWord, tailWord_196452, baseEnd_196452] using wordTrace_append hprefix tailTrace_196452
  have hstable : (prefixWord ++ tailWord_196452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196452).length < 2 ^ (prefixWord ++ tailWord_196452).sum := by decide
  have hdescent : baseEnd_196452 < baseStart_196452 := by decide
  rcases family_descends (prefixWord ++ tailWord_196452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196487 : List Nat := [1, 1, 4, 2, 4, 2, 6]
def baseStart_196487 : Nat := 118140960795 + 196487 * 2 ^ 59
def prefixEnd_196487 : Nat := 4983230072969 + 3 ^ 40 * 196487 * 2
def baseEnd_196487 : Nat := 9964668973834861966309

theorem tailTrace_196487 : CollatzResearch.WordTrace tailWord_196487 prefixEnd_196487 9964668973834861966309 := by
  unfold tailWord_196487
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166469639168631153075715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4777646426112420768717143 7166469639168631153075715)
  ·
    refine ⟨10749704458752946729613573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7166469639168631153075715 10749704458752946729613573)
    ·
      refine ⟨2015569586016177511802545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10749704458752946729613573 2015569586016177511802545)
      ·
        refine ⟨1511677189512133133851909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015569586016177511802545 1511677189512133133851909)
        ·
          refine ⟨283439473033524962597233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1511677189512133133851909 283439473033524962597233)
          ·
            refine ⟨212579604775143721947925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283439473033524962597233 212579604775143721947925)
            ·
              refine ⟨9964668973834861966309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212579604775143721947925 9964668973834861966309)
              ·
                rfl

theorem cell20_196487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_196487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196487 prefixEnd_196487 := by exact prefixLift 196487
  have htrace : WordTrace (prefixWord ++ tailWord_196487) baseStart_196487 baseEnd_196487 := by
    simpa [prefixWord, tailWord_196487, baseEnd_196487] using wordTrace_append hprefix tailTrace_196487
  have hstable : (prefixWord ++ tailWord_196487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196487).length < 2 ^ (prefixWord ++ tailWord_196487).sum := by decide
  have hdescent : baseEnd_196487 < baseStart_196487 := by decide
  rcases family_descends (prefixWord ++ tailWord_196487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196504 : List Nat := [2, 1, 2, 6, 1, 1, 2, 5]
def baseStart_196504 : Nat := 118140960795 + 196504 * 2 ^ 59
def prefixEnd_196504 : Nat := 4983230072969 + 3 ^ 40 * 196504 * 2
def baseEnd_196504 : Nat := 29896593342579084710015

theorem tailTrace_196504 : CollatzResearch.WordTrace tailWord_196504 prefixEnd_196504 29896593342579084710015 := by
  unfold tailWord_196504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583544840053521528222283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4778059786738028704296377 3583544840053521528222283)
  ·
    refine ⟨5375317260080282292333425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583544840053521528222283 5375317260080282292333425)
    ·
      refine ⟨4031487945060211719250069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5375317260080282292333425 4031487945060211719250069)
      ·
        refine ⟨188975997424697424339847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4031487945060211719250069 188975997424697424339847)
        ·
          refine ⟨283463996137046136509771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188975997424697424339847 283463996137046136509771)
          ·
            refine ⟨425195994205569204764657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283463996137046136509771 425195994205569204764657)
            ·
              refine ⟨318896995654176903573493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425195994205569204764657 318896995654176903573493)
              ·
                refine ⟨29896593342579084710015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318896995654176903573493 29896593342579084710015)
                ·
                  rfl

theorem cell20_196504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_196504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196504 prefixEnd_196504 := by exact prefixLift 196504
  have htrace : WordTrace (prefixWord ++ tailWord_196504) baseStart_196504 baseEnd_196504 := by
    simpa [prefixWord, tailWord_196504, baseEnd_196504] using wordTrace_append hprefix tailTrace_196504
  have hstable : (prefixWord ++ tailWord_196504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196504).length < 2 ^ (prefixWord ++ tailWord_196504).sum := by decide
  have hdescent : baseEnd_196504 < baseStart_196504 := by decide
  rcases family_descends (prefixWord ++ tailWord_196504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196511 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_196511 : Nat := 118140960795 + 196511 * 2 ^ 59
def prefixEnd_196511 : Nat := 4983230072969 + 3 ^ 40 * 196511 * 2
def baseEnd_196511 : Nat := 89692975018476340896683

theorem tailTrace_196511 : CollatzResearch.WordTrace tailWord_196511 prefixEnd_196511 89692975018476340896683 := by
  unfold tailWord_196511
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167344991081683251949387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4778229994054455501299591 7167344991081683251949387)
  ·
    refine ⟨10751017486622524877924081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7167344991081683251949387 10751017486622524877924081)
    ·
      refine ⟨8063263114966893658443061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10751017486622524877924081 8063263114966893658443061)
      ·
        refine ⟨755930917028146280479037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8063263114966893658443061 755930917028146280479037)
        ·
          refine ⟨283474093885554855179639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 755930917028146280479037 283474093885554855179639)
          ·
            refine ⟨425211140828332282769459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283474093885554855179639 425211140828332282769459)
            ·
              refine ⟨637816711242498424154189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425211140828332282769459 637816711242498424154189)
              ·
                refine ⟨239181266715936909057821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637816711242498424154189 239181266715936909057821)
                ·
                  refine ⟨89692975018476340896683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239181266715936909057821 89692975018476340896683)
                  ·
                    rfl

theorem cell20_196511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_196511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196511 prefixEnd_196511 := by exact prefixLift 196511
  have htrace : WordTrace (prefixWord ++ tailWord_196511) baseStart_196511 baseEnd_196511 := by
    simpa [prefixWord, tailWord_196511, baseEnd_196511] using wordTrace_append hprefix tailTrace_196511
  have hstable : (prefixWord ++ tailWord_196511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196511).length < 2 ^ (prefixWord ++ tailWord_196511).sum := by decide
  have hdescent : baseEnd_196511 < baseStart_196511 := by decide
  rcases family_descends (prefixWord ++ tailWord_196511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196552 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 2]
def baseStart_196552 : Nat := 118140960795 + 196552 * 2 ^ 59
def prefixEnd_196552 : Nat := 4983230072969 + 3 ^ 40 * 196552 * 2
def baseEnd_196552 : Nat := 89711688535662420529849

theorem tailTrace_196552 : CollatzResearch.WordTrace tailWord_196552 prefixEnd_196552 89711688535662420529849 := by
  unfold tailWord_196552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3584420191966573627095955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4779226922622098169461273 3584420191966573627095955)
  ·
    refine ⟨5376630287949860440643933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3584420191966573627095955 5376630287949860440643933)
    ·
      refine ⟨2016236357981197665241475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5376630287949860440643933 2016236357981197665241475)
      ·
        refine ⟨3024354536971796497862213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016236357981197665241475 3024354536971796497862213)
        ·
          refine ⟨567066475682211843349165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3024354536971796497862213 567066475682211843349165)
          ·
            refine ⟨212649928380829441255937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567066475682211843349165 212649928380829441255937)
            ·
              refine ⟨159487446285622080941953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212649928380829441255937 159487446285622080941953)
              ·
                refine ⟨119615584714216560706465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159487446285622080941953 119615584714216560706465)
                ·
                  refine ⟨89711688535662420529849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119615584714216560706465 89711688535662420529849)
                  ·
                    rfl

theorem cell20_196552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_196552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196552 prefixEnd_196552 := by exact prefixLift 196552
  have htrace : WordTrace (prefixWord ++ tailWord_196552) baseStart_196552 baseEnd_196552 := by
    simpa [prefixWord, tailWord_196552, baseEnd_196552] using wordTrace_append hprefix tailTrace_196552
  have hstable : (prefixWord ++ tailWord_196552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196552).length < 2 ^ (prefixWord ++ tailWord_196552).sum := by decide
  have hdescent : baseEnd_196552 < baseStart_196552 := by decide
  rcases family_descends (prefixWord ++ tailWord_196552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196591 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_196591 : Nat := 118140960795 + 196591 * 2 ^ 59
def prefixEnd_196591 : Nat := 4983230072969 + 3 ^ 40 * 196591 * 2
def baseEnd_196591 : Nat := 89729489198351618229689

theorem tailTrace_196591 : CollatzResearch.WordTrace tailWord_196591 prefixEnd_196591 89729489198351618229689 := by
  unfold tailWord_196591
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170262830791856914861627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4780175220527904609907751 7170262830791856914861627)
  ·
    refine ⟨10755394246187785372292441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7170262830791856914861627 10755394246187785372292441)
    ·
      refine ⟨8066545684640839029219331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10755394246187785372292441 8066545684640839029219331)
      ·
        refine ⟨12099818526961258543828997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066545684640839029219331 12099818526961258543828997)
        ·
          refine ⟨2268715973805235976967937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12099818526961258543828997 2268715973805235976967937)
          ·
            refine ⟨1701536980353926982725953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268715973805235976967937 1701536980353926982725953)
            ·
              refine ⟨1276152735265445237044465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701536980353926982725953 1276152735265445237044465)
              ·
                refine ⟨957114551449083927783349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276152735265445237044465 957114551449083927783349)
                ·
                  refine ⟨89729489198351618229689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 957114551449083927783349 89729489198351618229689)
                  ·
                    rfl

theorem cell20_196591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_196591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196591 prefixEnd_196591 := by exact prefixLift 196591
  have htrace : WordTrace (prefixWord ++ tailWord_196591) baseStart_196591 baseEnd_196591 := by
    simpa [prefixWord, tailWord_196591, baseEnd_196591] using wordTrace_append hprefix tailTrace_196591
  have hstable : (prefixWord ++ tailWord_196591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196591).length < 2 ^ (prefixWord ++ tailWord_196591).sum := by decide
  have hdescent : baseEnd_196591 < baseStart_196591 := by decide
  rcases family_descends (prefixWord ++ tailWord_196591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196615 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_196615 : Nat := 118140960795 + 196615 * 2 ^ 59
def prefixEnd_196615 : Nat := 4983230072969 + 3 ^ 40 * 196615 * 2
def baseEnd_196615 : Nat := 89740443452314201429591

theorem tailTrace_196615 : CollatzResearch.WordTrace tailWord_196615 prefixEnd_196615 89740443452314201429591 := by
  unfold tailWord_196615
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171138182704909013735299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4780758788469939342490199 7171138182704909013735299)
  ·
    refine ⟨10756707274057363520602949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7171138182704909013735299 10756707274057363520602949)
    ·
      refine ⟨2016882613885755660113053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10756707274057363520602949 2016882613885755660113053)
      ·
        refine ⟨756330980207158372542395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2016882613885755660113053 756330980207158372542395)
        ·
          refine ⟨1134496470310737558813593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756330980207158372542395 1134496470310737558813593)
          ·
            refine ⟨850872352733053169110195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1134496470310737558813593 850872352733053169110195)
            ·
              refine ⟨1276308529099579753665293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850872352733053169110195 1276308529099579753665293)
              ·
                refine ⟨478615698412342407624485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1276308529099579753665293 478615698412342407624485)
                ·
                  refine ⟨89740443452314201429591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478615698412342407624485 89740443452314201429591)
                  ·
                    rfl

theorem cell20_196615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_196615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196615 prefixEnd_196615 := by exact prefixLift 196615
  have htrace : WordTrace (prefixWord ++ tailWord_196615) baseStart_196615 baseEnd_196615 := by
    simpa [prefixWord, tailWord_196615, baseEnd_196615] using wordTrace_append hprefix tailTrace_196615
  have hstable : (prefixWord ++ tailWord_196615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196615).length < 2 ^ (prefixWord ++ tailWord_196615).sum := by decide
  have hdescent : baseEnd_196615 < baseStart_196615 := by decide
  rcases family_descends (prefixWord ++ tailWord_196615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196622 : List Nat := [4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_196622 : Nat := 118140960795 + 196622 * 2 ^ 59
def prefixEnd_196622 : Nat := 4983230072969 + 3 ^ 40 * 196622 * 2
def baseEnd_196622 : Nat := 29914546147684429398743

theorem tailTrace_196622 : CollatzResearch.WordTrace tailWord_196622 prefixEnd_196622 29914546147684429398743 := by
  unfold tailWord_196622
  simp only [CollatzResearch.WordTrace]
  refine ⟨896424186709943651155015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4780928995786366139493413 896424186709943651155015)
  ·
    refine ⟨1344636280064915476732523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 896424186709943651155015 1344636280064915476732523)
    ·
      refine ⟨2016954420097373215098785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344636280064915476732523 2016954420097373215098785)
      ·
        refine ⟨1512715815073029911324089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2016954420097373215098785 1512715815073029911324089)
        ·
          refine ⟨1134536861304772433493067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1512715815073029911324089 1134536861304772433493067)
          ·
            refine ⟨1701805291957158650239601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134536861304772433493067 1701805291957158650239601)
            ·
              refine ⟨1276353968967868987679701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701805291957158650239601 1276353968967868987679701)
              ·
                refine ⟨29914546147684429398743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1276353968967868987679701 29914546147684429398743)
                ·
                  rfl

theorem cell20_196622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_196622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196622 prefixEnd_196622 := by exact prefixLift 196622
  have htrace : WordTrace (prefixWord ++ tailWord_196622) baseStart_196622 baseEnd_196622 := by
    simpa [prefixWord, tailWord_196622, baseEnd_196622] using wordTrace_append hprefix tailTrace_196622
  have hstable : (prefixWord ++ tailWord_196622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196622).length < 2 ^ (prefixWord ++ tailWord_196622).sum := by decide
  have hdescent : baseEnd_196622 < baseStart_196622 := by decide
  rcases family_descends (prefixWord ++ tailWord_196622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196694 : List Nat := [5, 2, 2, 1, 1, 1, 2, 6]
def baseStart_196694 : Nat := 118140960795 + 196694 * 2 ^ 59
def prefixEnd_196694 : Nat := 4983230072969 + 3 ^ 40 * 196694 * 2
def baseEnd_196694 : Nat := 29925500401647012598645

theorem tailTrace_196694 : CollatzResearch.WordTrace tailWord_196694 prefixEnd_196694 29925500401647012598645 := by
  unfold tailWord_196694
  simp only [CollatzResearch.WordTrace]
  refine ⟨448376221838669094116321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4782679699612470337240757 448376221838669094116321)
  ·
    refine ⟨336282166379001820587241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 448376221838669094116321 336282166379001820587241)
    ·
      refine ⟨252211624784251365440431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336282166379001820587241 252211624784251365440431)
      ·
        refine ⟨378317437176377048160647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252211624784251365440431 378317437176377048160647)
        ·
          refine ⟨567476155764565572240971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378317437176377048160647 567476155764565572240971)
          ·
            refine ⟨851214233646848358361457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567476155764565572240971 851214233646848358361457)
            ·
              refine ⟨638410675235136268771093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851214233646848358361457 638410675235136268771093)
              ·
                refine ⟨29925500401647012598645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 638410675235136268771093 29925500401647012598645)
                ·
                  rfl

theorem cell20_196694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_196694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196694 prefixEnd_196694 := by exact prefixLift 196694
  have htrace : WordTrace (prefixWord ++ tailWord_196694) baseStart_196694 baseEnd_196694 := by
    simpa [prefixWord, tailWord_196694, baseEnd_196694] using wordTrace_append hprefix tailTrace_196694
  have hstable : (prefixWord ++ tailWord_196694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196694).length < 2 ^ (prefixWord ++ tailWord_196694).sum := by decide
  have hdescent : baseEnd_196694 < baseStart_196694 := by decide
  rcases family_descends (prefixWord ++ tailWord_196694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196719 : List Nat := [1, 1, 2, 1, 3, 12]
def baseStart_196719 : Nat := 118140960795 + 196719 * 2 ^ 59
def prefixEnd_196719 : Nat := 4983230072969 + 3 ^ 40 * 196719 * 2
def baseEnd_196719 : Nat := 3325478218005631924537

theorem tailTrace_196719 : CollatzResearch.WordTrace tailWord_196719 prefixEnd_196719 3325478218005631924537 := by
  unfold tailWord_196719
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174931374328134775521211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4783287582885423183680807 7174931374328134775521211)
  ·
    refine ⟨10762397061492202163281817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7174931374328134775521211 10762397061492202163281817)
    ·
      refine ⟨8071797796119151622461363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10762397061492202163281817 8071797796119151622461363)
      ·
        refine ⟨12107696694178727433692045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8071797796119151622461363 12107696694178727433692045)
        ·
          refine ⟨4540386260317022787634517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12107696694178727433692045 4540386260317022787634517)
          ·
            refine ⟨3325478218005631924537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4540386260317022787634517 3325478218005631924537)
            ·
              rfl

theorem cell20_196719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 12].length) (baseStart_196719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196719 prefixEnd_196719 := by exact prefixLift 196719
  have htrace : WordTrace (prefixWord ++ tailWord_196719) baseStart_196719 baseEnd_196719 := by
    simpa [prefixWord, tailWord_196719, baseEnd_196719] using wordTrace_append hprefix tailTrace_196719
  have hstable : (prefixWord ++ tailWord_196719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196719).length < 2 ^ (prefixWord ++ tailWord_196719).sum := by decide
  have hdescent : baseEnd_196719 < baseStart_196719 := by decide
  rcases family_descends (prefixWord ++ tailWord_196719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196722 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_196722 : Nat := 118140960795 + 196722 * 2 ^ 59
def prefixEnd_196722 : Nat := 4983230072969 + 3 ^ 40 * 196722 * 2
def baseEnd_196722 : Nat := 89789281167897384862487

theorem tailTrace_196722 : CollatzResearch.WordTrace tailWord_196722 prefixEnd_196722 89789281167897384862487 := by
  unfold tailWord_196722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793760198329316571970105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4783360528878177525253613 1793760198329316571970105)
  ·
    refine ⟨1345320148746987428977579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1793760198329316571970105 1345320148746987428977579)
    ·
      refine ⟨2017980223120481143466369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1345320148746987428977579 2017980223120481143466369)
      ·
        refine ⟨1513485167340360857599777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2017980223120481143466369 1513485167340360857599777)
        ·
          refine ⟨1135113875505270643199833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513485167340360857599777 1135113875505270643199833)
          ·
            refine ⟨851335406628952982399875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135113875505270643199833 851335406628952982399875)
            ·
              refine ⟨1277003109943429473599813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851335406628952982399875 1277003109943429473599813)
              ·
                refine ⟨239438083114393026299965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1277003109943429473599813 239438083114393026299965)
                ·
                  refine ⟨89789281167897384862487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239438083114393026299965 89789281167897384862487)
                  ·
                    rfl

theorem cell20_196722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_196722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196722 prefixEnd_196722 := by exact prefixLift 196722
  have htrace : WordTrace (prefixWord ++ tailWord_196722) baseStart_196722 baseEnd_196722 := by
    simpa [prefixWord, tailWord_196722, baseEnd_196722] using wordTrace_append hprefix tailTrace_196722
  have hstable : (prefixWord ++ tailWord_196722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196722).length < 2 ^ (prefixWord ++ tailWord_196722).sum := by decide
  have hdescent : baseEnd_196722 < baseStart_196722 := by decide
  rcases family_descends (prefixWord ++ tailWord_196722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196795 : List Nat := [1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_196795 : Nat := 118140960795 + 196795 * 2 ^ 59
def prefixEnd_196795 : Nat := 4983230072969 + 3 ^ 40 * 196795 * 2
def baseEnd_196795 : Nat := 29940866785677858476285

theorem tailTrace_196795 : CollatzResearch.WordTrace tailWord_196795 prefixEnd_196795 29940866785677858476285 := by
  unfold tailWord_196795
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177703322052799755287839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4785135548035199836858559 7177703322052799755287839)
  ·
    refine ⟨10766554983079199632931759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177703322052799755287839 10766554983079199632931759)
    ·
      refine ⟨16149832474618799449397639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766554983079199632931759 16149832474618799449397639)
      ·
        refine ⟨24224748711928199174096459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16149832474618799449397639 24224748711928199174096459)
        ·
          refine ⟨36337123067892298761144689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24224748711928199174096459 36337123067892298761144689)
          ·
            refine ⟨27252842300919224070858517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36337123067892298761144689 27252842300919224070858517)
            ·
              refine ⟨1277476982855588628321493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27252842300919224070858517 1277476982855588628321493)
              ·
                refine ⟨29940866785677858476285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1277476982855588628321493 29940866785677858476285)
                ·
                  rfl

theorem cell20_196795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_196795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196795 prefixEnd_196795 := by exact prefixLift 196795
  have htrace : WordTrace (prefixWord ++ tailWord_196795) baseStart_196795 baseEnd_196795 := by
    simpa [prefixWord, tailWord_196795, baseEnd_196795] using wordTrace_append hprefix tailTrace_196795
  have hstable : (prefixWord ++ tailWord_196795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196795).length < 2 ^ (prefixWord ++ tailWord_196795).sum := by decide
  have hdescent : baseEnd_196795 < baseStart_196795 := by decide
  rcases family_descends (prefixWord ++ tailWord_196795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196826 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_196826 : Nat := 118140960795 + 196826 * 2 ^ 59
def prefixEnd_196826 : Nat := 4983230072969 + 3 ^ 40 * 196826 * 2
def baseEnd_196826 : Nat := 89836749601735245395395

theorem tailTrace_196826 : CollatzResearch.WordTrace tailWord_196826 prefixEnd_196826 89836749601735245395395 := by
  unfold tailWord_196826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794708496235123012416583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4785889323293661366444221 1794708496235123012416583)
  ·
    refine ⟨2692062744352684518624875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1794708496235123012416583 2692062744352684518624875)
    ·
      refine ⟨4038094116529026777937313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692062744352684518624875 4038094116529026777937313)
      ·
        refine ⟨3028570587396770083452985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038094116529026777937313 3028570587396770083452985)
        ·
          refine ⟨2271427940547577562589739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3028570587396770083452985 2271427940547577562589739)
          ·
            refine ⟨3407141910821366343884609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271427940547577562589739 3407141910821366343884609)
            ·
              refine ⟨2555356433116024757913457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407141910821366343884609 2555356433116024757913457)
              ·
                refine ⟨1916517324837018568435093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555356433116024757913457 1916517324837018568435093)
                ·
                  refine ⟨89836749601735245395395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1916517324837018568435093 89836749601735245395395)
                  ·
                    rfl

theorem cell20_196826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_196826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196826 prefixEnd_196826 := by exact prefixLift 196826
  have htrace : WordTrace (prefixWord ++ tailWord_196826) baseStart_196826 baseEnd_196826 := by
    simpa [prefixWord, tailWord_196826, baseEnd_196826] using wordTrace_append hprefix tailTrace_196826
  have hstable : (prefixWord ++ tailWord_196826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196826).length < 2 ^ (prefixWord ++ tailWord_196826).sum := by decide
  have hdescent : baseEnd_196826 < baseStart_196826 := by decide
  rcases family_descends (prefixWord ++ tailWord_196826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196829 : List Nat := [1, 4, 3, 2, 1, 3, 6]
def baseStart_196829 : Nat := 118140960795 + 196829 * 2 ^ 59
def prefixEnd_196829 : Nat := 4983230072969 + 3 ^ 40 * 196829 * 2
def baseEnd_196829 : Nat := 9982013209275618699487

theorem tailTrace_196829 : CollatzResearch.WordTrace tailWord_196829 prefixEnd_196829 9982013209275618699487 := by
  unfold tailWord_196829
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178943403929623562025541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4785962269286415708017027 7178943403929623562025541)
  ·
    refine ⟨1346051888236804417879789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7178943403929623562025541 1346051888236804417879789)
    ·
      refine ⟨504769458088801656704921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1346051888236804417879789 504769458088801656704921)
      ·
        refine ⟨378577093566601242528691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504769458088801656704921 378577093566601242528691)
        ·
          refine ⟨567865640349901863793037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378577093566601242528691 567865640349901863793037)
          ·
            refine ⟨212949615131213198922389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567865640349901863793037 212949615131213198922389)
            ·
              refine ⟨9982013209275618699487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212949615131213198922389 9982013209275618699487)
              ·
                rfl

theorem cell20_196829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_196829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196829 prefixEnd_196829 := by exact prefixLift 196829
  have htrace : WordTrace (prefixWord ++ tailWord_196829) baseStart_196829 baseEnd_196829 := by
    simpa [prefixWord, tailWord_196829, baseEnd_196829] using wordTrace_append hprefix tailTrace_196829
  have hstable : (prefixWord ++ tailWord_196829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196829).length < 2 ^ (prefixWord ++ tailWord_196829).sum := by decide
  have hdescent : baseEnd_196829 < baseStart_196829 := by decide
  rcases family_descends (prefixWord ++ tailWord_196829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196850 : List Nat := [3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_196850 : Nat := 118140960795 + 196850 * 2 ^ 59
def prefixEnd_196850 : Nat := 4983230072969 + 3 ^ 40 * 196850 * 2
def baseEnd_196850 : Nat := 29949234618565942865099

theorem tailTrace_196850 : CollatzResearch.WordTrace tailWord_196850 prefixEnd_196850 29949234618565942865099 := by
  unfold tailWord_196850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794927334213386037135001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4786472891235696099026669 1794927334213386037135001)
  ·
    refine ⟨1346195500660039527851251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1794927334213386037135001 1346195500660039527851251)
    ·
      refine ⟨2019293250990059291776877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346195500660039527851251 2019293250990059291776877)
      ·
        refine ⟨757234969121272234416329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2019293250990059291776877 757234969121272234416329)
        ·
          refine ⟨567926226840954175812247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757234969121272234416329 567926226840954175812247)
          ·
            refine ⟨851889340261431263718371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567926226840954175812247 851889340261431263718371)
            ·
              refine ⟨1277834010392146895577557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851889340261431263718371 1277834010392146895577557)
              ·
                refine ⟨29949234618565942865099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1277834010392146895577557 29949234618565942865099)
                ·
                  rfl

theorem cell20_196850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_196850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196850 prefixEnd_196850 := by exact prefixLift 196850
  have htrace : WordTrace (prefixWord ++ tailWord_196850) baseStart_196850 baseEnd_196850 := by
    simpa [prefixWord, tailWord_196850, baseEnd_196850] using wordTrace_append hprefix tailTrace_196850
  have hstable : (prefixWord ++ tailWord_196850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196850).length < 2 ^ (prefixWord ++ tailWord_196850).sum := by decide
  have hdescent : baseEnd_196850 < baseStart_196850 := by decide
  rcases family_descends (prefixWord ++ tailWord_196850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196864 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_196864 : Nat := 118140960795 + 196864 * 2 ^ 59
def prefixEnd_196864 : Nat := 4983230072969 + 3 ^ 40 * 196864 * 2
def baseEnd_196864 : Nat := 89854093837176002128573

theorem tailTrace_196864 : CollatzResearch.WordTrace tailWord_196864 prefixEnd_196864 89854093837176002128573 := by
  unfold tailWord_196864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590109979401412269774823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4786813305868549693033097 3590109979401412269774823)
  ·
    refine ⟨5385164969102118404662235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3590109979401412269774823 5385164969102118404662235)
    ·
      refine ⟨8077747453653177606993353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5385164969102118404662235 8077747453653177606993353)
      ·
        refine ⟨6058310590239883205245015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8077747453653177606993353 6058310590239883205245015)
        ·
          refine ⟨9087465885359824807867523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058310590239883205245015 9087465885359824807867523)
          ·
            refine ⟨13631198828039737211801285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9087465885359824807867523 13631198828039737211801285)
            ·
              refine ⟨2555849780257450727212741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13631198828039737211801285 2555849780257450727212741)
              ·
                refine ⟨479221833798272011352389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2555849780257450727212741 479221833798272011352389)
                ·
                  refine ⟨89854093837176002128573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479221833798272011352389 89854093837176002128573)
                  ·
                    rfl

theorem cell20_196864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_196864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196864 prefixEnd_196864 := by exact prefixLift 196864
  have htrace : WordTrace (prefixWord ++ tailWord_196864) baseStart_196864 baseEnd_196864 := by
    simpa [prefixWord, tailWord_196864, baseEnd_196864] using wordTrace_append hprefix tailTrace_196864
  have hstable : (prefixWord ++ tailWord_196864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196864).length < 2 ^ (prefixWord ++ tailWord_196864).sum := by decide
  have hdescent : baseEnd_196864 < baseStart_196864 := by decide
  rcases family_descends (prefixWord ++ tailWord_196864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196894 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_196894 : Nat := 118140960795 + 196894 * 2 ^ 59
def prefixEnd_196894 : Nat := 4983230072969 + 3 ^ 40 * 196894 * 2
def baseEnd_196894 : Nat := 89867786654629231128451

theorem tailTrace_196894 : CollatzResearch.WordTrace tailWord_196894 prefixEnd_196894 89867786654629231128451 := by
  unfold tailWord_196894
  simp only [CollatzResearch.WordTrace]
  refine ⟨897664268586767457892717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4787542765796093108761157 897664268586767457892717)
  ·
    refine ⟨336624100720037796709769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 897664268586767457892717 336624100720037796709769)
    ·
      refine ⟨252468075540028347532327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336624100720037796709769 252468075540028347532327)
      ·
        refine ⟨378702113310042521298491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252468075540028347532327 378702113310042521298491)
        ·
          refine ⟨568053169965063781947737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378702113310042521298491 568053169965063781947737)
          ·
            refine ⟨426039877473797836460803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568053169965063781947737 426039877473797836460803)
            ·
              refine ⟨639059816210696754691205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426039877473797836460803 639059816210696754691205)
              ·
                refine ⟨119823715539505641504601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639059816210696754691205 119823715539505641504601)
                ·
                  refine ⟨89867786654629231128451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119823715539505641504601 89867786654629231128451)
                  ·
                    rfl

theorem cell20_196894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_196894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196894 prefixEnd_196894 := by exact prefixLift 196894
  have htrace : WordTrace (prefixWord ++ tailWord_196894) baseStart_196894 baseEnd_196894 := by
    simpa [prefixWord, tailWord_196894, baseEnd_196894] using wordTrace_append hprefix tailTrace_196894
  have hstable : (prefixWord ++ tailWord_196894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196894).length < 2 ^ (prefixWord ++ tailWord_196894).sum := by decide
  have hdescent : baseEnd_196894 < baseStart_196894 := by decide
  rcases family_descends (prefixWord ++ tailWord_196894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196932 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 2]
def baseStart_196932 : Nat := 118140960795 + 196932 * 2 ^ 59
def prefixEnd_196932 : Nat := 4983230072969 + 3 ^ 40 * 196932 * 2
def baseEnd_196932 : Nat := 89885130890069987861629

theorem tailTrace_196932 : CollatzResearch.WordTrace tailWord_196932 prefixEnd_196932 89885130890069987861629 := by
  unfold tailWord_196932
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591350061278236076512525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4788466748370981435350033 3591350061278236076512525)
  ·
    refine ⟨1346756272979338528692197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3591350061278236076512525 1346756272979338528692197)
    ·
      refine ⟨252516801183625974129787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1346756272979338528692197 252516801183625974129787)
      ·
        refine ⟨378775201775438961194681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252516801183625974129787 378775201775438961194681)
        ·
          refine ⟨284081401331579220896011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378775201775438961194681 284081401331579220896011)
          ·
            refine ⟨426122101997368831344017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284081401331579220896011 426122101997368831344017)
            ·
              refine ⟨319591576498026623508013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426122101997368831344017 319591576498026623508013)
              ·
                refine ⟨119846841186759983815505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319591576498026623508013 119846841186759983815505)
                ·
                  refine ⟨89885130890069987861629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119846841186759983815505 89885130890069987861629)
                  ·
                    rfl

theorem cell20_196932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_196932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196932 prefixEnd_196932 := by exact prefixLift 196932
  have htrace : WordTrace (prefixWord ++ tailWord_196932) baseStart_196932 baseEnd_196932 := by
    simpa [prefixWord, tailWord_196932, baseEnd_196932] using wordTrace_append hprefix tailTrace_196932
  have hstable : (prefixWord ++ tailWord_196932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196932).length < 2 ^ (prefixWord ++ tailWord_196932).sum := by decide
  have hdescent : baseEnd_196932 < baseStart_196932 := by decide
  rcases family_descends (prefixWord ++ tailWord_196932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196940 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_196940 : Nat := 118140960795 + 196940 * 2 ^ 59
def prefixEnd_196940 : Nat := 4983230072969 + 3 ^ 40 * 196940 * 2
def baseEnd_196940 : Nat := 89888782308057515594929

theorem tailTrace_196940 : CollatzResearch.WordTrace tailWord_196940 prefixEnd_196940 89888782308057515594929 := by
  unfold tailWord_196940
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591495953263744759658137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4788661271018326346210849 3591495953263744759658137)
  ·
    refine ⟨2693621964947808569743603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3591495953263744759658137 2693621964947808569743603)
    ·
      refine ⟨4040432947421712854615405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693621964947808569743603 4040432947421712854615405)
      ·
        refine ⟨1515162355283142320480777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4040432947421712854615405 1515162355283142320480777)
        ·
          refine ⟨1136371766462356740360583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1515162355283142320480777 1136371766462356740360583)
          ·
            refine ⟨1704557649693535110540875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136371766462356740360583 1704557649693535110540875)
            ·
              refine ⟨2556836474540302665811313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704557649693535110540875 2556836474540302665811313)
              ·
                refine ⟨1917627355905226999358485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556836474540302665811313 1917627355905226999358485)
                ·
                  refine ⟨89888782308057515594929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1917627355905226999358485 89888782308057515594929)
                  ·
                    rfl

theorem cell20_196940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_196940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196940 prefixEnd_196940 := by exact prefixLift 196940
  have htrace : WordTrace (prefixWord ++ tailWord_196940) baseStart_196940 baseEnd_196940 := by
    simpa [prefixWord, tailWord_196940, baseEnd_196940] using wordTrace_append hprefix tailTrace_196940
  have hstable : (prefixWord ++ tailWord_196940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196940).length < 2 ^ (prefixWord ++ tailWord_196940).sum := by decide
  have hdescent : baseEnd_196940 < baseStart_196940 := by decide
  rcases family_descends (prefixWord ++ tailWord_196940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196967 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 3]
def baseStart_196967 : Nat := 118140960795 + 196967 * 2 ^ 59
def prefixEnd_196967 : Nat := 4983230072969 + 3 ^ 40 * 196967 * 2
def baseEnd_196967 : Nat := 89901105843765421694819

theorem tailTrace_196967 : CollatzResearch.WordTrace tailWord_196967 prefixEnd_196967 89901105843765421694819 := by
  unfold tailWord_196967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7183976677429673130549155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4789317784953115420366103 7183976677429673130549155)
  ·
    refine ⟨10775965016144509695823733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7183976677429673130549155 10775965016144509695823733)
    ·
      refine ⟨1010246720263547783983475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10775965016144509695823733 1010246720263547783983475)
      ·
        refine ⟨1515370080395321675975213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010246720263547783983475 1515370080395321675975213)
        ·
          refine ⟨568263780148245628490705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1515370080395321675975213 568263780148245628490705)
          ·
            refine ⟨426197835111184221368029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568263780148245628490705 426197835111184221368029)
            ·
              refine ⟨159824188166694083013011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426197835111184221368029 159824188166694083013011)
              ·
                refine ⟨239736282250041124519517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159824188166694083013011 239736282250041124519517)
                ·
                  refine ⟨89901105843765421694819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239736282250041124519517 89901105843765421694819)
                  ·
                    rfl

theorem cell20_196967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_196967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196967 prefixEnd_196967 := by exact prefixLift 196967
  have htrace : WordTrace (prefixWord ++ tailWord_196967) baseStart_196967 baseEnd_196967 := by
    simpa [prefixWord, tailWord_196967, baseEnd_196967] using wordTrace_append hprefix tailTrace_196967
  have hstable : (prefixWord ++ tailWord_196967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196967).length < 2 ^ (prefixWord ++ tailWord_196967).sum := by decide
  have hdescent : baseEnd_196967 < baseStart_196967 := by decide
  rcases family_descends (prefixWord ++ tailWord_196967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196981 : List Nat := [1, 3, 4, 1, 2, 1, 4, 4]
def baseStart_196981 : Nat := 118140960795 + 196981 * 2 ^ 59
def prefixEnd_196981 : Nat := 4983230072969 + 3 ^ 40 * 196981 * 2
def baseEnd_196981 : Nat := 29969165275081198409365

theorem tailTrace_196981 : CollatzResearch.WordTrace tailWord_196981 prefixEnd_196981 29969165275081198409365 := by
  unfold tailWord_196981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184487299378953521558797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4789658199585969014372531 7184487299378953521558797)
  ·
    refine ⟨2694182737267107570584549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7184487299378953521558797 2694182737267107570584549)
    ·
      refine ⟨505159263237582669484603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2694182737267107570584549 505159263237582669484603)
      ·
        refine ⟨757738894856374004226905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505159263237582669484603 757738894856374004226905)
        ·
          refine ⟨568304171142280503170179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757738894856374004226905 568304171142280503170179)
          ·
            refine ⟨852456256713420754755269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568304171142280503170179 852456256713420754755269)
            ·
              refine ⟨159835548133766391516613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 852456256713420754755269 159835548133766391516613)
              ·
                refine ⟨29969165275081198409365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159835548133766391516613 29969165275081198409365)
                ·
                  rfl

theorem cell20_196981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_196981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_196981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_196981 prefixEnd_196981 := by exact prefixLift 196981
  have htrace : WordTrace (prefixWord ++ tailWord_196981) baseStart_196981 baseEnd_196981 := by
    simpa [prefixWord, tailWord_196981, baseEnd_196981] using wordTrace_append hprefix tailTrace_196981
  have hstable : (prefixWord ++ tailWord_196981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196981).length < 2 ^ (prefixWord ++ tailWord_196981).sum := by decide
  have hdescent : baseEnd_196981 < baseStart_196981 := by decide
  rcases family_descends (prefixWord ++ tailWord_196981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197022 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_197022 : Nat := 118140960795 + 197022 * 2 ^ 59
def prefixEnd_197022 : Nat := 4983230072969 + 3 ^ 40 * 197022 * 2
def baseEnd_197022 : Nat := 89926209342429674861261

theorem tailTrace_197022 : CollatzResearch.WordTrace tailWord_197022 prefixEnd_197022 89926209342429674861261 := by
  unfold tailWord_197022
  simp only [CollatzResearch.WordTrace]
  refine ⟨898247836528802190475165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4790655128153611682534213 898247836528802190475165)
  ·
    refine ⟨336842938698300821428187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 898247836528802190475165 336842938698300821428187)
    ·
      refine ⟨505264408047451232142281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336842938698300821428187 505264408047451232142281)
      ·
        refine ⟨378948306035588424106711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505264408047451232142281 378948306035588424106711)
        ·
          refine ⟨568422459053382636160067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378948306035588424106711 568422459053382636160067)
          ·
            refine ⟨852633688580073954240101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568422459053382636160067 852633688580073954240101)
            ·
              refine ⟨159868816608763866420019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 852633688580073954240101 159868816608763866420019)
              ·
                refine ⟨239803224913145799630029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159868816608763866420019 239803224913145799630029)
                ·
                  refine ⟨89926209342429674861261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239803224913145799630029 89926209342429674861261)
                  ·
                    rfl

theorem cell20_197022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_197022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197022 prefixEnd_197022 := by exact prefixLift 197022
  have htrace : WordTrace (prefixWord ++ tailWord_197022) baseStart_197022 baseEnd_197022 := by
    simpa [prefixWord, tailWord_197022, baseEnd_197022] using wordTrace_append hprefix tailTrace_197022
  have hstable : (prefixWord ++ tailWord_197022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197022).length < 2 ^ (prefixWord ++ tailWord_197022).sum := by decide
  have hdescent : baseEnd_197022 < baseStart_197022 := by decide
  rcases family_descends (prefixWord ++ tailWord_197022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197026 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_197026 : Nat := 118140960795 + 197026 * 2 ^ 59
def prefixEnd_197026 : Nat := 4983230072969 + 3 ^ 40 * 197026 * 2
def baseEnd_197026 : Nat := 89928035051423438727911

theorem tailTrace_197026 : CollatzResearch.WordTrace tailWord_197026 prefixEnd_197026 89928035051423438727911 := by
  unfold tailWord_197026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796532146053981551736733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4790752389477284137964621 1796532146053981551736733)
  ·
    refine ⟨673699554770243081901275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1796532146053981551736733 673699554770243081901275)
    ·
      refine ⟨1010549332155364622851913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673699554770243081901275 1010549332155364622851913)
      ·
        refine ⟨757911999116523467138935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1010549332155364622851913 757911999116523467138935)
        ·
          refine ⟨1136867998674785200708403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757911999116523467138935 1136867998674785200708403)
          ·
            refine ⟨1705301998012177801062605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136867998674785200708403 1705301998012177801062605)
            ·
              refine ⟨639488249254566675398477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1705301998012177801062605 639488249254566675398477)
              ·
                refine ⟨239808093470462503274429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 639488249254566675398477 239808093470462503274429)
                ·
                  refine ⟨89928035051423438727911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239808093470462503274429 89928035051423438727911)
                  ·
                    rfl

theorem cell20_197026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_197026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197026 prefixEnd_197026 := by exact prefixLift 197026
  have htrace : WordTrace (prefixWord ++ tailWord_197026) baseStart_197026 baseEnd_197026 := by
    simpa [prefixWord, tailWord_197026, baseEnd_197026] using wordTrace_append hprefix tailTrace_197026
  have hstable : (prefixWord ++ tailWord_197026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197026).length < 2 ^ (prefixWord ++ tailWord_197026).sum := by decide
  have hdescent : baseEnd_197026 < baseStart_197026 := by decide
  rcases family_descends (prefixWord ++ tailWord_197026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197057 : List Nat := [1, 2, 7, 1, 9]
def baseStart_197057 : Nat := 118140960795 + 197057 * 2 ^ 59
def prefixEnd_197057 : Nat := 4983230072969 + 3 ^ 40 * 197057 * 2
def baseEnd_197057 : Nat := 1110397336989198872771

theorem tailTrace_197057 : CollatzResearch.WordTrace tailWord_197057 prefixEnd_197057 1110397336989198872771 := by
  unfold tailWord_197057
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187259247103618501325425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4791506164735745667550283 7187259247103618501325425)
  ·
    refine ⟨5390444435327713875994069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7187259247103618501325425 5390444435327713875994069)
    ·
      refine ⟨126338541452993293968611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5390444435327713875994069 126338541452993293968611)
      ·
        refine ⟨189507812179489940952917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126338541452993293968611 189507812179489940952917)
        ·
          refine ⟨1110397336989198872771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 189507812179489940952917 1110397336989198872771)
          ·
            rfl

theorem cell20_197057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 9].length) (baseStart_197057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197057 prefixEnd_197057 := by exact prefixLift 197057
  have htrace : WordTrace (prefixWord ++ tailWord_197057) baseStart_197057 baseEnd_197057 := by
    simpa [prefixWord, tailWord_197057, baseEnd_197057] using wordTrace_append hprefix tailTrace_197057
  have hstable : (prefixWord ++ tailWord_197057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197057).length < 2 ^ (prefixWord ++ tailWord_197057).sum := by decide
  have hdescent : baseEnd_197057 < baseStart_197057 := by decide
  rcases family_descends (prefixWord ++ tailWord_197057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197064 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_197064 : Nat := 118140960795 + 197064 * 2 ^ 59
def prefixEnd_197064 : Nat := 4983230072969 + 3 ^ 40 * 197064 * 2
def baseEnd_197064 : Nat := 89945379286864195461089

theorem tailTrace_197064 : CollatzResearch.WordTrace tailWord_197064 prefixEnd_197064 89945379286864195461089 := by
  unfold tailWord_197064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593757279039129348415123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4791676372052172464553497 3593757279039129348415123)
  ·
    refine ⟨5390635918558694022622685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593757279039129348415123 5390635918558694022622685)
    ·
      refine ⟨2021488469459510258483507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5390635918558694022622685 2021488469459510258483507)
      ·
        refine ⟨3032232704189265387725261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021488469459510258483507 3032232704189265387725261)
        ·
          refine ⟨1137087264070974520396973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3032232704189265387725261 1137087264070974520396973)
          ·
            refine ⟨426407724026615445148865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1137087264070974520396973 426407724026615445148865)
            ·
              refine ⟨319805793019961583861649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426407724026615445148865 319805793019961583861649)
              ·
                refine ⟨239854344764971187896237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319805793019961583861649 239854344764971187896237)
                ·
                  refine ⟨89945379286864195461089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239854344764971187896237 89945379286864195461089)
                  ·
                    rfl

theorem cell20_197064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_197064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197064 prefixEnd_197064 := by exact prefixLift 197064
  have htrace : WordTrace (prefixWord ++ tailWord_197064) baseStart_197064 baseEnd_197064 := by
    simpa [prefixWord, tailWord_197064, baseEnd_197064] using wordTrace_append hprefix tailTrace_197064
  have hstable : (prefixWord ++ tailWord_197064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197064).length < 2 ^ (prefixWord ++ tailWord_197064).sum := by decide
  have hdescent : baseEnd_197064 < baseStart_197064 := by decide
  rcases family_descends (prefixWord ++ tailWord_197064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197074 : List Nat := [3, 2, 2, 4, 1, 2, 1, 5]
def baseStart_197074 : Nat := 118140960795 + 197074 * 2 ^ 59
def prefixEnd_197074 : Nat := 4983230072969 + 3 ^ 40 * 197074 * 2
def baseEnd_197074 : Nat := 29983314519782868375905

theorem tailTrace_197074 : CollatzResearch.WordTrace tailWord_197074 prefixEnd_197074 29983314519782868375905 := by
  unfold tailWord_197074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796969822010507601173569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4791919525361353603129517 1796969822010507601173569)
  ·
    refine ⟨1347727366507880700880177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1796969822010507601173569 1347727366507880700880177)
    ·
      refine ⟨1010795524880910525660133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1347727366507880700880177 1010795524880910525660133)
      ·
        refine ⟨189524160915170723561275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1010795524880910525660133 189524160915170723561275)
        ·
          refine ⟨284286241372756085341913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189524160915170723561275 284286241372756085341913)
          ·
            refine ⟨213214681029567064006435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284286241372756085341913 213214681029567064006435)
            ·
              refine ⟨319822021544350596009653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213214681029567064006435 319822021544350596009653)
              ·
                refine ⟨29983314519782868375905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319822021544350596009653 29983314519782868375905)
                ·
                  rfl

theorem cell20_197074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_197074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197074 prefixEnd_197074 := by exact prefixLift 197074
  have htrace : WordTrace (prefixWord ++ tailWord_197074) baseStart_197074 baseEnd_197074 := by
    simpa [prefixWord, tailWord_197074, baseEnd_197074] using wordTrace_append hprefix tailTrace_197074
  have hstable : (prefixWord ++ tailWord_197074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197074).length < 2 ^ (prefixWord ++ tailWord_197074).sum := by decide
  have hdescent : baseEnd_197074 < baseStart_197074 := by decide
  rcases family_descends (prefixWord ++ tailWord_197074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197181 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 2]
def baseStart_197181 : Nat := 118140960795 + 197181 * 2 ^ 59
def prefixEnd_197181 : Nat := 4983230072969 + 3 ^ 40 * 197181 * 2
def baseEnd_197181 : Nat := 89998781274931788560611

theorem tailTrace_197181 : CollatzResearch.WordTrace tailWord_197181 prefixEnd_197181 89998781274931788560611 := by
  unfold tailWord_197181
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191781898654387678839397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4794521265769591785892931 7191781898654387678839397)
  ·
    refine ⟨1348459105997697689782387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7191781898654387678839397 1348459105997697689782387)
    ·
      refine ⟨2022688658996546534673581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348459105997697689782387 2022688658996546534673581)
      ·
        refine ⟨758508247123704950502593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2022688658996546534673581 758508247123704950502593)
        ·
          refine ⟨568881185342778712876945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758508247123704950502593 568881185342778712876945)
          ·
            refine ⟨426660889007084034657709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568881185342778712876945 426660889007084034657709)
            ·
              refine ⟨159997833377656512996641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426660889007084034657709 159997833377656512996641)
              ·
                refine ⟨119998375033242384747481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159997833377656512996641 119998375033242384747481)
                ·
                  refine ⟨89998781274931788560611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119998375033242384747481 89998781274931788560611)
                  ·
                    rfl

theorem cell20_197181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_197181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197181 prefixEnd_197181 := by exact prefixLift 197181
  have htrace : WordTrace (prefixWord ++ tailWord_197181) baseStart_197181 baseEnd_197181 := by
    simpa [prefixWord, tailWord_197181, baseEnd_197181] using wordTrace_append hprefix tailTrace_197181
  have hstable : (prefixWord ++ tailWord_197181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197181).length < 2 ^ (prefixWord ++ tailWord_197181).sum := by decide
  have hdescent : baseEnd_197181 < baseStart_197181 := by decide
  rcases family_descends (prefixWord ++ tailWord_197181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197185 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_197185 : Nat := 118140960795 + 197185 * 2 ^ 59
def prefixEnd_197185 : Nat := 4983230072969 + 3 ^ 40 * 197185 * 2
def baseEnd_197185 : Nat := 90000606983925552427261

theorem tailTrace_197185 : CollatzResearch.WordTrace tailWord_197185 prefixEnd_197185 90000606983925552427261 := by
  unfold tailWord_197185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191927790639896361985009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4794618527093264241323339 7191927790639896361985009)
  ·
    refine ⟨5393945842979922271488757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7191927790639896361985009 5393945842979922271488757)
    ·
      refine ⟨505682422779367712952071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5393945842979922271488757 505682422779367712952071)
      ·
        refine ⟨758523634169051569428107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505682422779367712952071 758523634169051569428107)
        ·
          refine ⟨1137785451253577354142161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758523634169051569428107 1137785451253577354142161)
          ·
            refine ⟨853339088440183015606621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137785451253577354142161 853339088440183015606621)
            ·
              refine ⟨320002158165068630852483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853339088440183015606621 320002158165068630852483)
              ·
                refine ⟨480003237247602946278725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320002158165068630852483 480003237247602946278725)
                ·
                  refine ⟨90000606983925552427261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480003237247602946278725 90000606983925552427261)
                  ·
                    rfl

theorem cell20_197185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_197185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197185 prefixEnd_197185 := by exact prefixLift 197185
  have htrace : WordTrace (prefixWord ++ tailWord_197185) baseStart_197185 baseEnd_197185 := by
    simpa [prefixWord, tailWord_197185, baseEnd_197185] using wordTrace_append hprefix tailTrace_197185
  have hstable : (prefixWord ++ tailWord_197185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197185).length < 2 ^ (prefixWord ++ tailWord_197185).sum := by decide
  have hdescent : baseEnd_197185 < baseStart_197185 := by decide
  rcases family_descends (prefixWord ++ tailWord_197185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197223 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 2]
def baseStart_197223 : Nat := 118140960795 + 197223 * 2 ^ 59
def prefixEnd_197223 : Nat := 4983230072969 + 3 ^ 40 * 197223 * 2
def baseEnd_197223 : Nat := 90017951219366309160439

theorem tailTrace_197223 : CollatzResearch.WordTrace tailWord_197223 prefixEnd_197223 90017951219366309160439 := by
  unfold tailWord_197223
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193313764502228851868323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4795542509668152567912215 7193313764502228851868323)
  ·
    refine ⟨10789970646753343277802485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7193313764502228851868323 10789970646753343277802485)
    ·
      refine ⟨1011559748133125932293983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10789970646753343277802485 1011559748133125932293983)
      ·
        refine ⟨1517339622199688898440975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011559748133125932293983 1517339622199688898440975)
        ·
          refine ⟨2276009433299533347661463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517339622199688898440975 2276009433299533347661463)
          ·
            refine ⟨3414014149949300021492195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276009433299533347661463 3414014149949300021492195)
            ·
              refine ⟨5121021224923950032238293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414014149949300021492195 5121021224923950032238293)
              ·
                refine ⟨120023934959155078880585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5121021224923950032238293 120023934959155078880585)
                ·
                  refine ⟨90017951219366309160439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120023934959155078880585 90017951219366309160439)
                  ·
                    rfl

theorem cell20_197223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 2].length) (baseStart_197223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197223 prefixEnd_197223 := by exact prefixLift 197223
  have htrace : WordTrace (prefixWord ++ tailWord_197223) baseStart_197223 baseEnd_197223 := by
    simpa [prefixWord, tailWord_197223, baseEnd_197223] using wordTrace_append hprefix tailTrace_197223
  have hstable : (prefixWord ++ tailWord_197223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197223).length < 2 ^ (prefixWord ++ tailWord_197223).sum := by decide
  have hdescent : baseEnd_197223 < baseStart_197223 := by decide
  rcases family_descends (prefixWord ++ tailWord_197223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197227 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_197227 : Nat := 118140960795 + 197227 * 2 ^ 59
def prefixEnd_197227 : Nat := 4983230072969 + 3 ^ 40 * 197227 * 2
def baseEnd_197227 : Nat := 90019776928360073027089

theorem tailTrace_197227 : CollatzResearch.WordTrace tailWord_197227 prefixEnd_197227 90019776928360073027089 := by
  unfold tailWord_197227
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193459656487737535013935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4795639770991825023342623 7193459656487737535013935)
  ·
    refine ⟨10790189484731606302520903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7193459656487737535013935 10790189484731606302520903)
    ·
      refine ⟨16185284227097409453781355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10790189484731606302520903 16185284227097409453781355)
      ·
        refine ⟨24277926340646114180672033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16185284227097409453781355 24277926340646114180672033)
        ·
          refine ⟨18208444755484585635504025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24277926340646114180672033 18208444755484585635504025)
          ·
            refine ⟨13656333566613439226628019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18208444755484585635504025 13656333566613439226628019)
            ·
              refine ⟨20484500349920158839942029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13656333566613439226628019 20484500349920158839942029)
              ·
                refine ⟨7681687631220059564978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20484500349920158839942029 7681687631220059564978261)
                ·
                  refine ⟨90019776928360073027089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7681687631220059564978261 90019776928360073027089)
                  ·
                    rfl

theorem cell20_197227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_197227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197227 prefixEnd_197227 := by exact prefixLift 197227
  have htrace : WordTrace (prefixWord ++ tailWord_197227) baseStart_197227 baseEnd_197227 := by
    simpa [prefixWord, tailWord_197227, baseEnd_197227] using wordTrace_append hprefix tailTrace_197227
  have hstable : (prefixWord ++ tailWord_197227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197227).length < 2 ^ (prefixWord ++ tailWord_197227).sum := by decide
  have hdescent : baseEnd_197227 < baseStart_197227 := by decide
  rcases family_descends (prefixWord ++ tailWord_197227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197251 : List Nat := [1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_197251 : Nat := 118140960795 + 197251 * 2 ^ 59
def prefixEnd_197251 : Nat := 4983230072969 + 3 ^ 40 * 197251 * 2
def baseEnd_197251 : Nat := 30010243727440885408997

theorem tailTrace_197251 : CollatzResearch.WordTrace tailWord_197251 prefixEnd_197251 30010243727440885408997 := by
  unfold tailWord_197251
  simp only [CollatzResearch.WordTrace]
  refine ⟨7194335008400789633887607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4796223338933859755925071 7194335008400789633887607)
  ·
    refine ⟨10791502512601184450831411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7194335008400789633887607 10791502512601184450831411)
    ·
      refine ⟨16187253768901776676247117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10791502512601184450831411 16187253768901776676247117)
      ·
        refine ⟨6070220163338166253592669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16187253768901776676247117 6070220163338166253592669)
        ·
          refine ⟨2276332561251812345097251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6070220163338166253592669 2276332561251812345097251)
          ·
            refine ⟨3414498841877718517645877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276332561251812345097251 3414498841877718517645877)
            ·
              refine ⟨320109266426036111029301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3414498841877718517645877 320109266426036111029301)
              ·
                refine ⟨30010243727440885408997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320109266426036111029301 30010243727440885408997)
                ·
                  rfl

theorem cell20_197251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_197251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197251 prefixEnd_197251 := by exact prefixLift 197251
  have htrace : WordTrace (prefixWord ++ tailWord_197251) baseStart_197251 baseEnd_197251 := by
    simpa [prefixWord, tailWord_197251, baseEnd_197251] using wordTrace_append hprefix tailTrace_197251
  have hstable : (prefixWord ++ tailWord_197251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197251).length < 2 ^ (prefixWord ++ tailWord_197251).sum := by decide
  have hdescent : baseEnd_197251 < baseStart_197251 := by decide
  rcases family_descends (prefixWord ++ tailWord_197251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197299 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 2]
def baseStart_197299 : Nat := 118140960795 + 197299 * 2 ^ 59
def prefixEnd_197299 : Nat := 4983230072969 + 3 ^ 40 * 197299 * 2
def baseEnd_197299 : Nat := 90052639690247822626795

theorem tailTrace_197299 : CollatzResearch.WordTrace tailWord_197299 prefixEnd_197299 90052639690247822626795 := by
  unfold tailWord_197299
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196085712226893831634951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4797390474817929221089967 7196085712226893831634951)
  ·
    refine ⟨10794128568340340747452427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7196085712226893831634951 10794128568340340747452427)
    ·
      refine ⟨16191192852510511121178641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10794128568340340747452427 16191192852510511121178641)
      ·
        refine ⟨12143394639382883340883981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16191192852510511121178641 12143394639382883340883981)
        ·
          refine ⟨4553772989768581252831493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12143394639382883340883981 4553772989768581252831493)
          ·
            refine ⟨853832435581608984905905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4553772989768581252831493 853832435581608984905905)
            ·
              refine ⟨640374326686206738679429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853832435581608984905905 640374326686206738679429)
              ·
                refine ⟨120070186253663763502393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640374326686206738679429 120070186253663763502393)
                ·
                  refine ⟨90052639690247822626795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120070186253663763502393 90052639690247822626795)
                  ·
                    rfl

theorem cell20_197299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 2].length) (baseStart_197299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197299 prefixEnd_197299 := by exact prefixLift 197299
  have htrace : WordTrace (prefixWord ++ tailWord_197299) baseStart_197299 baseEnd_197299 := by
    simpa [prefixWord, tailWord_197299, baseEnd_197299] using wordTrace_append hprefix tailTrace_197299
  have hstable : (prefixWord ++ tailWord_197299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197299).length < 2 ^ (prefixWord ++ tailWord_197299).sum := by decide
  have hdescent : baseEnd_197299 < baseStart_197299 := by decide
  rcases family_descends (prefixWord ++ tailWord_197299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197320 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_197320 : Nat := 118140960795 + 197320 * 2 ^ 59
def prefixEnd_197320 : Nat := 4983230072969 + 3 ^ 40 * 197320 * 2
def baseEnd_197320 : Nat := 90062224662465082926709

theorem tailTrace_197320 : CollatzResearch.WordTrace tailWord_197320 prefixEnd_197320 90062224662465082926709 := by
  unfold tailWord_197320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598425822575407209074707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4797901096767209612099609 3598425822575407209074707)
  ·
    refine ⟨5397638733863110813612061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3598425822575407209074707 5397638733863110813612061)
    ·
      refine ⟨2024114525198666555104523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5397638733863110813612061 2024114525198666555104523)
      ·
        refine ⟨3036171787797999832656785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024114525198666555104523 3036171787797999832656785)
        ·
          refine ⟨2277128840848499874492589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3036171787797999832656785 2277128840848499874492589)
          ·
            refine ⟨853923315318187452934721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2277128840848499874492589 853923315318187452934721)
            ·
              refine ⟨640442486488640589701041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853923315318187452934721 640442486488640589701041)
              ·
                refine ⟨480331864866480442275781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640442486488640589701041 480331864866480442275781)
                ·
                  refine ⟨90062224662465082926709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480331864866480442275781 90062224662465082926709)
                  ·
                    rfl

theorem cell20_197320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_197320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197320 prefixEnd_197320 := by exact prefixLift 197320
  have htrace : WordTrace (prefixWord ++ tailWord_197320) baseStart_197320 baseEnd_197320 := by
    simpa [prefixWord, tailWord_197320, baseEnd_197320] using wordTrace_append hprefix tailTrace_197320
  have hstable : (prefixWord ++ tailWord_197320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197320).length < 2 ^ (prefixWord ++ tailWord_197320).sum := by decide
  have hdescent : baseEnd_197320 < baseStart_197320 := by decide
  rcases family_descends (prefixWord ++ tailWord_197320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197364 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_197364 : Nat := 118140960795 + 197364 * 2 ^ 59
def prefixEnd_197364 : Nat := 4983230072969 + 3 ^ 40 * 197364 * 2
def baseEnd_197364 : Nat := 90082307461396485459863

theorem tailTrace_197364 : CollatzResearch.WordTrace tailWord_197364 prefixEnd_197364 90082307461396485459863 := by
  unfold tailWord_197364
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599228228495704966375573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4798970971327606621834097 3599228228495704966375573)
  ·
    refine ⟨168713823210736170298855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3599228228495704966375573 168713823210736170298855)
    ·
      refine ⟨253070734816104255448283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168713823210736170298855 253070734816104255448283)
      ·
        refine ⟨379606102224156383172425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253070734816104255448283 379606102224156383172425)
        ·
          refine ⟨284704576668117287379319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379606102224156383172425 284704576668117287379319)
          ·
            refine ⟨427056865002175931068979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284704576668117287379319 427056865002175931068979)
            ·
              refine ⟨640585297503263896603469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427056865002175931068979 640585297503263896603469)
              ·
                refine ⟨240219486563723961226301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640585297503263896603469 240219486563723961226301)
                ·
                  refine ⟨90082307461396485459863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240219486563723961226301 90082307461396485459863)
                  ·
                    rfl

theorem cell20_197364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_197364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197364 prefixEnd_197364 := by exact prefixLift 197364
  have htrace : WordTrace (prefixWord ++ tailWord_197364) baseStart_197364 baseEnd_197364 := by
    simpa [prefixWord, tailWord_197364, baseEnd_197364] using wordTrace_append hprefix tailTrace_197364
  have hstable : (prefixWord ++ tailWord_197364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197364).length < 2 ^ (prefixWord ++ tailWord_197364).sum := by decide
  have hdescent : baseEnd_197364 < baseStart_197364 := by decide
  rcases family_descends (prefixWord ++ tailWord_197364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197379 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_197379 : Nat := 118140960795 + 197379 * 2 ^ 59
def prefixEnd_197379 : Nat := 4983230072969 + 3 ^ 40 * 197379 * 2
def baseEnd_197379 : Nat := 90089153870123099959801

theorem tailTrace_197379 : CollatzResearch.WordTrace tailWord_197379 prefixEnd_197379 90089153870123099959801 := by
  unfold tailWord_197379
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199003551937067494547191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4799335701291378329698127 7199003551937067494547191)
  ·
    refine ⟨10798505327905601241820787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199003551937067494547191 10798505327905601241820787)
    ·
      refine ⟨16197757991858401862731181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10798505327905601241820787 16197757991858401862731181)
      ·
        refine ⟨6074159246946900698524193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16197757991858401862731181 6074159246946900698524193)
        ·
          refine ⟨4555619435210175523893145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074159246946900698524193 4555619435210175523893145)
          ·
            refine ⟨3416714576407631642919859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555619435210175523893145 3416714576407631642919859)
            ·
              refine ⟨5125071864611447464379789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3416714576407631642919859 5125071864611447464379789)
              ·
                refine ⟨1921901949229292799142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125071864611447464379789 1921901949229292799142421)
                ·
                  refine ⟨90089153870123099959801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1921901949229292799142421 90089153870123099959801)
                  ·
                    rfl

theorem cell20_197379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_197379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197379 prefixEnd_197379 := by exact prefixLift 197379
  have htrace : WordTrace (prefixWord ++ tailWord_197379) baseStart_197379 baseEnd_197379 := by
    simpa [prefixWord, tailWord_197379, baseEnd_197379] using wordTrace_append hprefix tailTrace_197379
  have hstable : (prefixWord ++ tailWord_197379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197379).length < 2 ^ (prefixWord ++ tailWord_197379).sum := by decide
  have hdescent : baseEnd_197379 < baseStart_197379 := by decide
  rcases family_descends (prefixWord ++ tailWord_197379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197405 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 2]
def baseStart_197405 : Nat := 118140960795 + 197405 * 2 ^ 59
def prefixEnd_197405 : Nat := 4983230072969 + 3 ^ 40 * 197405 * 2
def baseEnd_197405 : Nat := 90101020978582565093029

theorem tailTrace_197405 : CollatzResearch.WordTrace tailWord_197405 prefixEnd_197405 90101020978582565093029 := by
  unfold tailWord_197405
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199951849842873934993669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4799967899895249289995779 7199951849842873934993669)
  ·
    refine ⟨1349990971845538862811313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7199951849842873934993669 1349990971845538862811313)
    ·
      refine ⟨1012493228884154147108485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1349990971845538862811313 1012493228884154147108485)
      ·
        refine ⟨189842480415778902582841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1012493228884154147108485 189842480415778902582841)
        ·
          refine ⟨142381860311834176937131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189842480415778902582841 142381860311834176937131)
          ·
            refine ⟨213572790467751265405697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142381860311834176937131 213572790467751265405697)
            ·
              refine ⟨160179592850813449054273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213572790467751265405697 160179592850813449054273)
              ·
                refine ⟨120134694638110086790705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160179592850813449054273 120134694638110086790705)
                ·
                  refine ⟨90101020978582565093029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120134694638110086790705 90101020978582565093029)
                  ·
                    rfl

theorem cell20_197405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_197405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197405 prefixEnd_197405 := by exact prefixLift 197405
  have htrace : WordTrace (prefixWord ++ tailWord_197405) baseStart_197405 baseEnd_197405 := by
    simpa [prefixWord, tailWord_197405, baseEnd_197405] using wordTrace_append hprefix tailTrace_197405
  have hstable : (prefixWord ++ tailWord_197405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197405).length < 2 ^ (prefixWord ++ tailWord_197405).sum := by decide
  have hdescent : baseEnd_197405 < baseStart_197405 := by decide
  rcases family_descends (prefixWord ++ tailWord_197405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197413 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 2]
def baseStart_197413 : Nat := 118140960795 + 197413 * 2 ^ 59
def prefixEnd_197413 : Nat := 4983230072969 + 3 ^ 40 * 197413 * 2
def baseEnd_197413 : Nat := 90104672396570092826329

theorem tailTrace_197413 : CollatzResearch.WordTrace tailWord_197413 prefixEnd_197413 90104672396570092826329 := by
  unfold tailWord_197413
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200243633813891301284893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800162422542594200856595 7200243633813891301284893)
  ·
    refine ⟨2700091362680209237981835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7200243633813891301284893 2700091362680209237981835)
    ·
      refine ⟨4050137044020313856972753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700091362680209237981835 4050137044020313856972753)
      ·
        refine ⟨3037602783015235392729565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4050137044020313856972753 3037602783015235392729565)
        ·
          refine ⟨1139101043630713272273587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3037602783015235392729565 1139101043630713272273587)
          ·
            refine ⟨1708651565446069908410381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139101043630713272273587 1708651565446069908410381)
            ·
              refine ⟨640744337042276215653893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1708651565446069908410381 640744337042276215653893)
              ·
                refine ⟨120139563195426790435105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640744337042276215653893 120139563195426790435105)
                ·
                  refine ⟨90104672396570092826329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120139563195426790435105 90104672396570092826329)
                  ·
                    rfl

theorem cell20_197413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_197413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197413 prefixEnd_197413 := by exact prefixLift 197413
  have htrace : WordTrace (prefixWord ++ tailWord_197413) baseStart_197413 baseEnd_197413 := by
    simpa [prefixWord, tailWord_197413, baseEnd_197413] using wordTrace_append hprefix tailTrace_197413
  have hstable : (prefixWord ++ tailWord_197413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197413).length < 2 ^ (prefixWord ++ tailWord_197413).sum := by decide
  have hdescent : baseEnd_197413 < baseStart_197413 := by decide
  rcases family_descends (prefixWord ++ tailWord_197413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197427 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_197427 : Nat := 118140960795 + 197427 * 2 ^ 59
def prefixEnd_197427 : Nat := 4983230072969 + 3 ^ 40 * 197427 * 2
def baseEnd_197427 : Nat := 90111062378048266359605

theorem tailTrace_197427 : CollatzResearch.WordTrace tailWord_197427 prefixEnd_197427 90111062378048266359605 := by
  unfold tailWord_197427
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200754255763171692294535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800502837175447794863023 7200754255763171692294535)
  ·
    refine ⟨10801131383644757538441803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7200754255763171692294535 10801131383644757538441803)
    ·
      refine ⟨16201697075467136307662705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10801131383644757538441803 16201697075467136307662705)
      ·
        refine ⟨12151272806600352230747029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16201697075467136307662705 12151272806600352230747029)
        ·
          refine ⟨569590912809391510816267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12151272806600352230747029 569590912809391510816267)
          ·
            refine ⟨854386369214087266224401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569590912809391510816267 854386369214087266224401)
            ·
              refine ⟨640789776910565449668301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854386369214087266224401 640789776910565449668301)
              ·
                refine ⟨240296166341462043625613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640789776910565449668301 240296166341462043625613)
                ·
                  refine ⟨90111062378048266359605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240296166341462043625613 90111062378048266359605)
                  ·
                    rfl

theorem cell20_197427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_197427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197427 prefixEnd_197427 := by exact prefixLift 197427
  have htrace : WordTrace (prefixWord ++ tailWord_197427) baseStart_197427 baseEnd_197427 := by
    simpa [prefixWord, tailWord_197427, baseEnd_197427] using wordTrace_append hprefix tailTrace_197427
  have hstable : (prefixWord ++ tailWord_197427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197427).length < 2 ^ (prefixWord ++ tailWord_197427).sum := by decide
  have hdescent : baseEnd_197427 < baseStart_197427 := by decide
  rcases family_descends (prefixWord ++ tailWord_197427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197430 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_197430 : Nat := 118140960795 + 197430 * 2 ^ 59
def prefixEnd_197430 : Nat := 4983230072969 + 3 ^ 40 * 197430 * 2
def baseEnd_197430 : Nat := 90112431659793589259593

theorem tailTrace_197430 : CollatzResearch.WordTrace tailWord_197430 prefixEnd_197430 90112431659793589259593 := by
  unfold tailWord_197430
  simp only [CollatzResearch.WordTrace]
  refine ⟨450053979672018950290859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4800575783168202136435829 450053979672018950290859)
  ·
    refine ⟨675080969508028425436289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450053979672018950290859 675080969508028425436289)
    ·
      refine ⟨506310727131021319077217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675080969508028425436289 506310727131021319077217)
      ·
        refine ⟨379733045348265989307913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506310727131021319077217 379733045348265989307913)
        ·
          refine ⟨284799784011199491980935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379733045348265989307913 284799784011199491980935)
          ·
            refine ⟨427199676016799237971403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284799784011199491980935 427199676016799237971403)
            ·
              refine ⟨640799514025198856957105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427199676016799237971403 640799514025198856957105)
              ·
                refine ⟨480599635518899142717829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640799514025198856957105 480599635518899142717829)
                ·
                  refine ⟨90112431659793589259593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480599635518899142717829 90112431659793589259593)
                  ·
                    rfl

theorem cell20_197430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_197430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197430 prefixEnd_197430 := by exact prefixLift 197430
  have htrace : WordTrace (prefixWord ++ tailWord_197430) baseStart_197430 baseEnd_197430 := by
    simpa [prefixWord, tailWord_197430, baseEnd_197430] using wordTrace_append hprefix tailTrace_197430
  have hstable : (prefixWord ++ tailWord_197430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197430).length < 2 ^ (prefixWord ++ tailWord_197430).sum := by decide
  have hdescent : baseEnd_197430 < baseStart_197430 := by decide
  rcases family_descends (prefixWord ++ tailWord_197430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197437 : List Nat := [1, 4, 1, 4, 2, 1, 3, 4]
def baseStart_197437 : Nat := 118140960795 + 197437 * 2 ^ 59
def prefixEnd_197437 : Nat := 4983230072969 + 3 ^ 40 * 197437 * 2
def baseEnd_197437 : Nat := 30038542216844225342077

theorem tailTrace_197437 : CollatzResearch.WordTrace tailWord_197437 prefixEnd_197437 30038542216844225342077 := by
  unfold tailWord_197437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201118985726943400158565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800745990484628933439043 7201118985726943400158565)
  ·
    refine ⟨1350209809823801887529731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7201118985726943400158565 1350209809823801887529731)
    ·
      refine ⟨2025314714735702831294597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1350209809823801887529731 2025314714735702831294597)
      ·
        refine ⟨379746509012944280867737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2025314714735702831294597 379746509012944280867737)
        ·
          refine ⟨284809881759708210650803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379746509012944280867737 284809881759708210650803)
          ·
            refine ⟨427214822639562315976205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284809881759708210650803 427214822639562315976205)
            ·
              refine ⟨160205558489835868491077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427214822639562315976205 160205558489835868491077)
              ·
                refine ⟨30038542216844225342077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160205558489835868491077 30038542216844225342077)
                ·
                  rfl

theorem cell20_197437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_197437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197437 prefixEnd_197437 := by exact prefixLift 197437
  have htrace : WordTrace (prefixWord ++ tailWord_197437) baseStart_197437 baseEnd_197437 := by
    simpa [prefixWord, tailWord_197437, baseEnd_197437] using wordTrace_append hprefix tailTrace_197437
  have hstable : (prefixWord ++ tailWord_197437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197437).length < 2 ^ (prefixWord ++ tailWord_197437).sum := by decide
  have hdescent : baseEnd_197437 < baseStart_197437 := by decide
  rcases family_descends (prefixWord ++ tailWord_197437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197448 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_197448 : Nat := 118140960795 + 197448 * 2 ^ 59
def prefixEnd_197448 : Nat := 4983230072969 + 3 ^ 40 * 197448 * 2
def baseEnd_197448 : Nat := 90120647350265526659519

theorem tailTrace_197448 : CollatzResearch.WordTrace tailWord_197448 prefixEnd_197448 90120647350265526659519 := by
  unfold tailWord_197448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600760094343546139404499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4801013459124728185872665 3600760094343546139404499)
  ·
    refine ⟨5401140141515319209106749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3600760094343546139404499 5401140141515319209106749)
    ·
      refine ⟨2025427553068244703415031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5401140141515319209106749 2025427553068244703415031)
      ·
        refine ⟨3038141329602367055122547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025427553068244703415031 3038141329602367055122547)
        ·
          refine ⟨4557211994403550582683821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038141329602367055122547 4557211994403550582683821)
          ·
            refine ⟨1708954497901331468506433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4557211994403550582683821 1708954497901331468506433)
            ·
              refine ⟨1281715873425998601379825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708954497901331468506433 1281715873425998601379825)
              ·
                refine ⟨961286905069498951034869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281715873425998601379825 961286905069498951034869)
                ·
                  refine ⟨90120647350265526659519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 961286905069498951034869 90120647350265526659519)
                  ·
                    rfl

theorem cell20_197448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_197448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197448 prefixEnd_197448 := by exact prefixLift 197448
  have htrace : WordTrace (prefixWord ++ tailWord_197448) baseStart_197448 baseEnd_197448 := by
    simpa [prefixWord, tailWord_197448, baseEnd_197448] using wordTrace_append hprefix tailTrace_197448
  have hstable : (prefixWord ++ tailWord_197448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197448).length < 2 ^ (prefixWord ++ tailWord_197448).sum := by decide
  have hdescent : baseEnd_197448 < baseStart_197448 := by decide
  rcases family_descends (prefixWord ++ tailWord_197448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197465 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_197465 : Nat := 118140960795 + 197465 * 2 ^ 59
def prefixEnd_197465 : Nat := 4983230072969 + 3 ^ 40 * 197465 * 2
def baseEnd_197465 : Nat := 90128406613489023092783

theorem tailTrace_197465 : CollatzResearch.WordTrace tailWord_197465 prefixEnd_197465 90128406613489023092783 := by
  unfold tailWord_197465
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202140229625504182177849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4801426819750336121451899 7202140229625504182177849)
  ·
    refine ⟨5401605172219128136633387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7202140229625504182177849 5401605172219128136633387)
    ·
      refine ⟨8102407758328692204950081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401605172219128136633387 8102407758328692204950081)
      ·
        refine ⟨6076805818746519153712561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8102407758328692204950081 6076805818746519153712561)
        ·
          refine ⟨4557604364059889365284421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6076805818746519153712561 4557604364059889365284421)
          ·
            refine ⟨854550818261229255990829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4557604364059889365284421 854550818261229255990829)
            ·
              refine ⟨320456556847960970996561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 854550818261229255990829 320456556847960970996561)
              ·
                refine ⟨240342417635970728247421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320456556847960970996561 240342417635970728247421)
                ·
                  refine ⟨90128406613489023092783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240342417635970728247421 90128406613489023092783)
                  ·
                    rfl

theorem cell20_197465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_197465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197465 prefixEnd_197465 := by exact prefixLift 197465
  have htrace : WordTrace (prefixWord ++ tailWord_197465) baseStart_197465 baseEnd_197465 := by
    simpa [prefixWord, tailWord_197465, baseEnd_197465] using wordTrace_append hprefix tailTrace_197465
  have hstable : (prefixWord ++ tailWord_197465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197465).length < 2 ^ (prefixWord ++ tailWord_197465).sum := by decide
  have hdescent : baseEnd_197465 < baseStart_197465 := by decide
  rcases family_descends (prefixWord ++ tailWord_197465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197468 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 2]
def baseStart_197468 : Nat := 118140960795 + 197468 * 2 ^ 59
def prefixEnd_197468 : Nat := 4983230072969 + 3 ^ 40 * 197468 * 2
def baseEnd_197468 : Nat := 90129775895234345992771

theorem tailTrace_197468 : CollatzResearch.WordTrace tailWord_197468 prefixEnd_197468 90129775895234345992771 := by
  unfold tailWord_197468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601124824307317847268529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4801499765743090463024705 3601124824307317847268529)
  ·
    refine ⟨2700843618230488385451397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3601124824307317847268529 2700843618230488385451397)
    ·
      refine ⟨506408178418216572272137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2700843618230488385451397 506408178418216572272137)
      ·
        refine ⟨379806133813662429204103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506408178418216572272137 379806133813662429204103)
        ·
          refine ⟨569709200720493643806155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379806133813662429204103 569709200720493643806155)
          ·
            refine ⟨854563801080740465709233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569709200720493643806155 854563801080740465709233)
            ·
              refine ⟨640922850810555349281925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854563801080740465709233 640922850810555349281925)
              ·
                refine ⟨120173034526979127990361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640922850810555349281925 120173034526979127990361)
                ·
                  refine ⟨90129775895234345992771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120173034526979127990361 90129775895234345992771)
                  ·
                    rfl

theorem cell20_197468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_197468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197468 prefixEnd_197468 := by exact prefixLift 197468
  have htrace : WordTrace (prefixWord ++ tailWord_197468) baseStart_197468 baseEnd_197468 := by
    simpa [prefixWord, tailWord_197468, baseEnd_197468] using wordTrace_append hprefix tailTrace_197468
  have hstable : (prefixWord ++ tailWord_197468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197468).length < 2 ^ (prefixWord ++ tailWord_197468).sum := by decide
  have hdescent : baseEnd_197468 < baseStart_197468 := by decide
  rcases family_descends (prefixWord ++ tailWord_197468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197472 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_197472 : Nat := 118140960795 + 197472 * 2 ^ 59
def prefixEnd_197472 : Nat := 4983230072969 + 3 ^ 40 * 197472 * 2
def baseEnd_197472 : Nat := 90131601604228109859421

theorem tailTrace_197472 : CollatzResearch.WordTrace tailWord_197472 prefixEnd_197472 90131601604228109859421 := by
  unfold tailWord_197472
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601197770300072188841335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4801597027066762918455113 3601197770300072188841335)
  ·
    refine ⟨5401796655450108283262003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3601197770300072188841335 5401796655450108283262003)
    ·
      refine ⟨8102694983175162424893005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401796655450108283262003 8102694983175162424893005)
      ·
        refine ⟨3038510618690685909334877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8102694983175162424893005 3038510618690685909334877)
        ·
          refine ⟨1139441482009007216000579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3038510618690685909334877 1139441482009007216000579)
          ·
            refine ⟨1709162223013510824000869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139441482009007216000579 1709162223013510824000869)
            ·
              refine ⟨320467916815033279500163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1709162223013510824000869 320467916815033279500163)
              ·
                refine ⟨480701875222549919250245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320467916815033279500163 480701875222549919250245)
                ·
                  refine ⟨90131601604228109859421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480701875222549919250245 90131601604228109859421)
                  ·
                    rfl

theorem cell20_197472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_197472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197472 prefixEnd_197472 := by exact prefixLift 197472
  have htrace : WordTrace (prefixWord ++ tailWord_197472) baseStart_197472 baseEnd_197472 := by
    simpa [prefixWord, tailWord_197472, baseEnd_197472] using wordTrace_append hprefix tailTrace_197472
  have hstable : (prefixWord ++ tailWord_197472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197472).length < 2 ^ (prefixWord ++ tailWord_197472).sum := by decide
  have hdescent : baseEnd_197472 < baseStart_197472 := by decide
  rcases family_descends (prefixWord ++ tailWord_197472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197502 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_197502 : Nat := 118140960795 + 197502 * 2 ^ 59
def prefixEnd_197502 : Nat := 4983230072969 + 3 ^ 40 * 197502 * 2
def baseEnd_197502 : Nat := 90145294421681338859299

theorem tailTrace_197502 : CollatzResearch.WordTrace tailWord_197502 prefixEnd_197502 90145294421681338859299 := by
  unfold tailWord_197502
  simp only [CollatzResearch.WordTrace]
  refine ⟨900436216311432437659345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4802326486994306334183173 900436216311432437659345)
  ·
    refine ⟨675327162233574328244509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 900436216311432437659345 675327162233574328244509)
    ·
      refine ⟨253247685837590373091691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 675327162233574328244509 253247685837590373091691)
      ·
        refine ⟨379871528756385559637537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253247685837590373091691 379871528756385559637537)
        ·
          refine ⟨284903646567289169728153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379871528756385559637537 284903646567289169728153)
          ·
            refine ⟨213677734925466877296115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284903646567289169728153 213677734925466877296115)
            ·
              refine ⟨320516602388200315944173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213677734925466877296115 320516602388200315944173)
              ·
                refine ⟨120193725895575118479065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320516602388200315944173 120193725895575118479065)
                ·
                  refine ⟨90145294421681338859299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120193725895575118479065 90145294421681338859299)
                  ·
                    rfl

theorem cell20_197502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_197502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197502 prefixEnd_197502 := by exact prefixLift 197502
  have htrace : WordTrace (prefixWord ++ tailWord_197502) baseStart_197502 baseEnd_197502 := by
    simpa [prefixWord, tailWord_197502, baseEnd_197502] using wordTrace_append hprefix tailTrace_197502
  have hstable : (prefixWord ++ tailWord_197502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197502).length < 2 ^ (prefixWord ++ tailWord_197502).sum := by decide
  have hdescent : baseEnd_197502 < baseStart_197502 := by decide
  rcases family_descends (prefixWord ++ tailWord_197502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197537 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 3]
def baseStart_197537 : Nat := 118140960795 + 197537 * 2 ^ 59
def prefixEnd_197537 : Nat := 4983230072969 + 3 ^ 40 * 197537 * 2
def baseEnd_197537 : Nat := 90161269375376772692489

theorem tailTrace_197537 : CollatzResearch.WordTrace tailWord_197537 prefixEnd_197537 90161269375376772692489 := by
  unfold tailWord_197537
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204766285364660478798865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4803177523576440319199243 7204766285364660478798865)
  ·
    refine ⟨5403574714023495359099149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7204766285364660478798865 5403574714023495359099149)
    ·
      refine ⟨2026340517758810759662181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5403574714023495359099149 2026340517758810759662181)
      ·
        refine ⟨379938847079777017436659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2026340517758810759662181 379938847079777017436659)
        ·
          refine ⟨569908270619665526154989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379938847079777017436659 569908270619665526154989)
          ·
            refine ⟨213715601482374572308121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 569908270619665526154989 213715601482374572308121)
            ·
              refine ⟨160286701111780929231091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213715601482374572308121 160286701111780929231091)
              ·
                refine ⟨240430051667671393846637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160286701111780929231091 240430051667671393846637)
                ·
                  refine ⟨90161269375376772692489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240430051667671393846637 90161269375376772692489)
                  ·
                    rfl

theorem cell20_197537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_197537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197537 prefixEnd_197537 := by exact prefixLift 197537
  have htrace : WordTrace (prefixWord ++ tailWord_197537) baseStart_197537 baseEnd_197537 := by
    simpa [prefixWord, tailWord_197537, baseEnd_197537] using wordTrace_append hprefix tailTrace_197537
  have hstable : (prefixWord ++ tailWord_197537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197537).length < 2 ^ (prefixWord ++ tailWord_197537).sum := by decide
  have hdescent : baseEnd_197537 < baseStart_197537 := by decide
  rcases family_descends (prefixWord ++ tailWord_197537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197572 : List Nat := [2, 3, 3, 3, 1, 8]
def baseStart_197572 : Nat := 118140960795 + 197572 * 2 ^ 59
def prefixEnd_197572 : Nat := 4983230072969 + 3 ^ 40 * 197572 * 2
def baseEnd_197572 : Nat := 3339897938113785426877

theorem tailTrace_197572 : CollatzResearch.WordTrace tailWord_197572 prefixEnd_197572 3339897938113785426877 := by
  unfold tailWord_197572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603021420118930728161485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4804028560158574304215313 3603021420118930728161485)
  ·
    refine ⟨1351133032544599023060557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3603021420118930728161485 1351133032544599023060557)
    ·
      refine ⟨506674887204224633647709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1351133032544599023060557 506674887204224633647709)
      ·
        refine ⟨190003082701584237617891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506674887204224633647709 190003082701584237617891)
        ·
          refine ⟨285004624052376356426837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190003082701584237617891 285004624052376356426837)
          ·
            refine ⟨3339897938113785426877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 285004624052376356426837 3339897938113785426877)
            ·
              rfl

theorem cell20_197572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 8].length) (baseStart_197572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197572 prefixEnd_197572 := by exact prefixLift 197572
  have htrace : WordTrace (prefixWord ++ tailWord_197572) baseStart_197572 baseEnd_197572 := by
    simpa [prefixWord, tailWord_197572, baseEnd_197572] using wordTrace_append hprefix tailTrace_197572
  have hstable : (prefixWord ++ tailWord_197572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197572).length < 2 ^ (prefixWord ++ tailWord_197572).sum := by decide
  have hdescent : baseEnd_197572 < baseStart_197572 := by decide
  rcases family_descends (prefixWord ++ tailWord_197572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197576 : List Nat := [2, 1, 3, 1, 13]
def baseStart_197576 : Nat := 118140960795 + 197576 * 2 ^ 59
def prefixEnd_197576 : Nat := 4983230072969 + 3 ^ 40 * 197576 * 2
def baseEnd_197576 : Nat := 1113321852321802103609

theorem tailTrace_197576 : CollatzResearch.WordTrace tailWord_197576 prefixEnd_197576 1113321852321802103609 := by
  unfold tailWord_197576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603094366111685069734291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4804125821482246759645721 3603094366111685069734291)
  ·
    refine ⟨5404641549167527604601437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603094366111685069734291 5404641549167527604601437)
    ·
      refine ⟨2026740580937822851725539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5404641549167527604601437 2026740580937822851725539)
      ·
        refine ⟨3040110871406734277588309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026740580937822851725539 3040110871406734277588309)
        ·
          refine ⟨1113321852321802103609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3040110871406734277588309 1113321852321802103609)
          ·
            rfl

theorem cell20_197576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 13].length) (baseStart_197576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197576 prefixEnd_197576 := by exact prefixLift 197576
  have htrace : WordTrace (prefixWord ++ tailWord_197576) baseStart_197576 baseEnd_197576 := by
    simpa [prefixWord, tailWord_197576, baseEnd_197576] using wordTrace_append hprefix tailTrace_197576
  have hstable : (prefixWord ++ tailWord_197576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197576).length < 2 ^ (prefixWord ++ tailWord_197576).sum := by decide
  have hdescent : baseEnd_197576 < baseStart_197576 := by decide
  rcases family_descends (prefixWord ++ tailWord_197576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197579 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_197579 : Nat := 118140960795 + 197579 * 2 ^ 59
def prefixEnd_197579 : Nat := 4983230072969 + 3 ^ 40 * 197579 * 2
def baseEnd_197579 : Nat := 90180439319811293292317

theorem tailTrace_197579 : CollatzResearch.WordTrace tailWord_197579 prefixEnd_197579 90180439319811293292317 := by
  unfold tailWord_197579
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206298151212501651827791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4804198767475001101218527 7206298151212501651827791)
  ·
    refine ⟨10809447226818752477741687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7206298151212501651827791 10809447226818752477741687)
    ·
      refine ⟨16214170840228128716612531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10809447226818752477741687 16214170840228128716612531)
      ·
        refine ⟨24321256260342193074918797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16214170840228128716612531 24321256260342193074918797)
        ·
          refine ⟨9120471097628322403094549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24321256260342193074918797 9120471097628322403094549)
          ·
            refine ⟨427522082701327612645057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9120471097628322403094549 427522082701327612645057)
            ·
              refine ⟨320641562025995709483793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427522082701327612645057 320641562025995709483793)
              ·
                refine ⟨240481171519496782112845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320641562025995709483793 240481171519496782112845)
                ·
                  refine ⟨90180439319811293292317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240481171519496782112845 90180439319811293292317)
                  ·
                    rfl

theorem cell20_197579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_197579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197579 prefixEnd_197579 := by exact prefixLift 197579
  have htrace : WordTrace (prefixWord ++ tailWord_197579) baseStart_197579 baseEnd_197579 := by
    simpa [prefixWord, tailWord_197579, baseEnd_197579] using wordTrace_append hprefix tailTrace_197579
  have hstable : (prefixWord ++ tailWord_197579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197579).length < 2 ^ (prefixWord ++ tailWord_197579).sum := by decide
  have hdescent : baseEnd_197579 < baseStart_197579 := by decide
  rcases family_descends (prefixWord ++ tailWord_197579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197582 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_197582 : Nat := 118140960795 + 197582 * 2 ^ 59
def prefixEnd_197582 : Nat := 4983230072969 + 3 ^ 40 * 197582 * 2
def baseEnd_197582 : Nat := 90181808601556616192305

theorem tailTrace_197582 : CollatzResearch.WordTrace tailWord_197582 prefixEnd_197582 90181808601556616192305 := by
  unfold tailWord_197582
  simp only [CollatzResearch.WordTrace]
  refine ⟨900800946275204145523375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4804271713467755442791333 900800946275204145523375)
  ·
    refine ⟨1351201419412806218285063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 900800946275204145523375 1351201419412806218285063)
    ·
      refine ⟨2026802129119209327427595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351201419412806218285063 2026802129119209327427595)
      ·
        refine ⟨3040203193678813991141393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026802129119209327427595 3040203193678813991141393)
        ·
          refine ⟨2280152395259110493356045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040203193678813991141393 2280152395259110493356045)
          ·
            refine ⟨855057148222166435008517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2280152395259110493356045 855057148222166435008517)
            ·
              refine ⟨160323215291656206564097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 855057148222166435008517 160323215291656206564097)
              ·
                refine ⟨120242411468742154923073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160323215291656206564097 120242411468742154923073)
                ·
                  refine ⟨90181808601556616192305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120242411468742154923073 90181808601556616192305)
                  ·
                    rfl

theorem cell20_197582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_197582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197582 prefixEnd_197582 := by exact prefixLift 197582
  have htrace : WordTrace (prefixWord ++ tailWord_197582) baseStart_197582 baseEnd_197582 := by
    simpa [prefixWord, tailWord_197582, baseEnd_197582] using wordTrace_append hprefix tailTrace_197582
  have hstable : (prefixWord ++ tailWord_197582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197582).length < 2 ^ (prefixWord ++ tailWord_197582).sum := by decide
  have hdescent : baseEnd_197582 < baseStart_197582 := by decide
  rcases family_descends (prefixWord ++ tailWord_197582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197589 : List Nat := [1, 3, 2, 3, 4, 1, 1, 5]
def baseStart_197589 : Nat := 118140960795 + 197589 * 2 ^ 59
def prefixEnd_197589 : Nat := 4983230072969 + 3 ^ 40 * 197589 * 2
def baseEnd_197589 : Nat := 30061667864098567652981

theorem tailTrace_197589 : CollatzResearch.WordTrace tailWord_197589 prefixEnd_197589 30061667864098567652981 := by
  unfold tailWord_197589
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206662881176273359691821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4804441920784182239794547 7206662881176273359691821)
  ·
    refine ⟨2702498580441102509884433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7206662881176273359691821 2702498580441102509884433)
    ·
      refine ⟨2026873935330826882413325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2702498580441102509884433 2026873935330826882413325)
      ·
        refine ⟨760077725749060080904997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2026873935330826882413325 760077725749060080904997)
        ·
          refine ⟨142514573577948765169687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 760077725749060080904997 142514573577948765169687)
          ·
            refine ⟨213771860366923147754531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142514573577948765169687 213771860366923147754531)
            ·
              refine ⟨320657790550384721631797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213771860366923147754531 320657790550384721631797)
              ·
                refine ⟨30061667864098567652981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320657790550384721631797 30061667864098567652981)
                ·
                  rfl

theorem cell20_197589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].length) (baseStart_197589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197589 prefixEnd_197589 := by exact prefixLift 197589
  have htrace : WordTrace (prefixWord ++ tailWord_197589) baseStart_197589 baseEnd_197589 := by
    simpa [prefixWord, tailWord_197589, baseEnd_197589] using wordTrace_append hprefix tailTrace_197589
  have hstable : (prefixWord ++ tailWord_197589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197589).length < 2 ^ (prefixWord ++ tailWord_197589).sum := by decide
  have hdescent : baseEnd_197589 < baseStart_197589 := by decide
  rcases family_descends (prefixWord ++ tailWord_197589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197593 : List Nat := [1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_197593 : Nat := 118140960795 + 197593 * 2 ^ 59
def prefixEnd_197593 : Nat := 4983230072969 + 3 ^ 40 * 197593 * 2
def baseEnd_197593 : Nat := 30062276433763155608531

theorem tailTrace_197593 : CollatzResearch.WordTrace tailWord_197593 prefixEnd_197593 30062276433763155608531 := by
  unfold tailWord_197593
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206808773161782042837433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4804539182107854695224955 7206808773161782042837433)
  ·
    refine ⟨5405106579871336532128075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7206808773161782042837433 5405106579871336532128075)
    ·
      refine ⟨8107659869807004798192113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405106579871336532128075 8107659869807004798192113)
      ·
        refine ⟨6080744902355253598644085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8107659869807004798192113 6080744902355253598644085)
        ·
          refine ⟨570069834595805024872883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6080744902355253598644085 570069834595805024872883)
          ·
            refine ⟨855104751893707537309325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570069834595805024872883 855104751893707537309325)
            ·
              refine ⟨320664281960140326490997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855104751893707537309325 320664281960140326490997)
              ·
                refine ⟨30062276433763155608531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320664281960140326490997 30062276433763155608531)
                ·
                  rfl

theorem cell20_197593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_197593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197593 prefixEnd_197593 := by exact prefixLift 197593
  have htrace : WordTrace (prefixWord ++ tailWord_197593) baseStart_197593 baseEnd_197593 := by
    simpa [prefixWord, tailWord_197593, baseEnd_197593] using wordTrace_append hprefix tailTrace_197593
  have hstable : (prefixWord ++ tailWord_197593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197593).length < 2 ^ (prefixWord ++ tailWord_197593).sum := by decide
  have hdescent : baseEnd_197593 < baseStart_197593 := by decide
  rcases family_descends (prefixWord ++ tailWord_197593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197610 : List Nat := [3, 1, 3, 1, 2, 3, 3, 4]
def baseStart_197610 : Nat := 118140960795 + 197610 * 2 ^ 59
def prefixEnd_197610 : Nat := 4983230072969 + 3 ^ 40 * 197610 * 2
def baseEnd_197610 : Nat := 30064862854837654419619

theorem tailTrace_197610 : CollatzResearch.WordTrace tailWord_197610 prefixEnd_197610 30064862854837654419619 := by
  unfold tailWord_197610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801857203525048486551571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4804952542733462630804189 1801857203525048486551571)
  ·
    refine ⟨2702785805287572729827357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801857203525048486551571 2702785805287572729827357)
    ·
      refine ⟨1013544676982839773685259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2702785805287572729827357 1013544676982839773685259)
      ·
        refine ⟨1520317015474259660527889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013544676982839773685259 1520317015474259660527889)
        ·
          refine ⟨1140237761605694745395917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520317015474259660527889 1140237761605694745395917)
          ·
            refine ⟨427589160602135529523469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1140237761605694745395917 427589160602135529523469)
            ·
              refine ⟨160345935225800823571301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427589160602135529523469 160345935225800823571301)
              ·
                refine ⟨30064862854837654419619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160345935225800823571301 30064862854837654419619)
                ·
                  rfl

theorem cell20_197610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_197610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197610 prefixEnd_197610 := by exact prefixLift 197610
  have htrace : WordTrace (prefixWord ++ tailWord_197610) baseStart_197610 baseEnd_197610 := by
    simpa [prefixWord, tailWord_197610, baseEnd_197610] using wordTrace_append hprefix tailTrace_197610
  have hstable : (prefixWord ++ tailWord_197610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197610).length < 2 ^ (prefixWord ++ tailWord_197610).sum := by decide
  have hdescent : baseEnd_197610 < baseStart_197610 := by decide
  rcases family_descends (prefixWord ++ tailWord_197610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197630 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_197630 : Nat := 118140960795 + 197630 * 2 ^ 59
def prefixEnd_197630 : Nat := 4983230072969 + 3 ^ 40 * 197630 * 2
def baseEnd_197630 : Nat := 90203717109481782592109

theorem tailTrace_197630 : CollatzResearch.WordTrace tailWord_197630 prefixEnd_197630 90203717109481782592109 := by
  unfold tailWord_197630
  simp only [CollatzResearch.WordTrace]
  refine ⟨901019784253467170241793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4805438849351824907956229 901019784253467170241793)
  ·
    refine ⟨675764838190100377681345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 901019784253467170241793 675764838190100377681345)
    ·
      refine ⟨506823628642575283261009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675764838190100377681345 506823628642575283261009)
      ·
        refine ⟨380117721481931462445757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506823628642575283261009 380117721481931462445757)
        ·
          refine ⟨142544145555724298417159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380117721481931462445757 142544145555724298417159)
          ·
            refine ⟨213816218333586447625739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142544145555724298417159 213816218333586447625739)
            ·
              refine ⟨320724327500379671438609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213816218333586447625739 320724327500379671438609)
              ·
                refine ⟨240543245625284753578957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320724327500379671438609 240543245625284753578957)
                ·
                  refine ⟨90203717109481782592109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240543245625284753578957 90203717109481782592109)
                  ·
                    rfl

theorem cell20_197630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_197630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197630 prefixEnd_197630 := by exact prefixLift 197630
  have htrace : WordTrace (prefixWord ++ tailWord_197630) baseStart_197630 baseEnd_197630 := by
    simpa [prefixWord, tailWord_197630, baseEnd_197630] using wordTrace_append hprefix tailTrace_197630
  have hstable : (prefixWord ++ tailWord_197630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197630).length < 2 ^ (prefixWord ++ tailWord_197630).sum := by decide
  have hdescent : baseEnd_197630 < baseStart_197630 := by decide
  rcases family_descends (prefixWord ++ tailWord_197630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197686 : List Nat := [5, 1, 2, 1, 1, 4, 6]
def baseStart_197686 : Nat := 118140960795 + 197686 * 2 ^ 59
def prefixEnd_197686 : Nat := 4983230072969 + 3 ^ 40 * 197686 * 2
def baseEnd_197686 : Nat := 10025475226154941858357

theorem tailTrace_197686 : CollatzResearch.WordTrace tailWord_197686 prefixEnd_197686 10025475226154941858357 := by
  unfold tailWord_197686
  simp only [CollatzResearch.WordTrace]
  refine ⟨450637547614053682873307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4806800507883239283981941 450637547614053682873307)
  ·
    refine ⟨675956321421080524309961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450637547614053682873307 675956321421080524309961)
    ·
      refine ⟨506967241065810393232471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675956321421080524309961 506967241065810393232471)
      ·
        refine ⟨760450861598715589848707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506967241065810393232471 760450861598715589848707)
        ·
          refine ⟨1140676292398073384773061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760450861598715589848707 1140676292398073384773061)
          ·
            refine ⟨213876804824638759644949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1140676292398073384773061 213876804824638759644949)
            ·
              refine ⟨10025475226154941858357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213876804824638759644949 10025475226154941858357)
              ·
                rfl

theorem cell20_197686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 6].length) (baseStart_197686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197686 prefixEnd_197686 := by exact prefixLift 197686
  have htrace : WordTrace (prefixWord ++ tailWord_197686) baseStart_197686 baseEnd_197686 := by
    simpa [prefixWord, tailWord_197686, baseEnd_197686] using wordTrace_append hprefix tailTrace_197686
  have hstable : (prefixWord ++ tailWord_197686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197686).length < 2 ^ (prefixWord ++ tailWord_197686).sum := by decide
  have hdescent : baseEnd_197686 < baseStart_197686 := by decide
  rcases family_descends (prefixWord ++ tailWord_197686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197690 : List Nat := [3, 1, 1, 1, 3, 1, 10]
def baseStart_197690 : Nat := 118140960795 + 197690 * 2 ^ 59
def prefixEnd_197690 : Nat := 4983230072969 + 3 ^ 40 * 197690 * 2
def baseEnd_197690 : Nat := 10025678082709804510207

theorem tailTrace_197690 : CollatzResearch.WordTrace tailWord_197690 prefixEnd_197690 10025678082709804510207 := by
  unfold tailWord_197690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802586663452591902279631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4806897769206911739412349 1802586663452591902279631)
  ·
    refine ⟨2703879995178887853419447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802586663452591902279631 2703879995178887853419447)
    ·
      refine ⟨4055819992768331780129171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703879995178887853419447 4055819992768331780129171)
      ·
        refine ⟨6083729989152497670193757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055819992768331780129171 6083729989152497670193757)
        ·
          refine ⟨2281398745932186626322659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6083729989152497670193757 2281398745932186626322659)
          ·
            refine ⟨3422098118898279939483989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281398745932186626322659 3422098118898279939483989)
            ·
              refine ⟨10025678082709804510207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3422098118898279939483989 10025678082709804510207)
              ·
                rfl

theorem cell20_197690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_197690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197690 prefixEnd_197690 := by exact prefixLift 197690
  have htrace : WordTrace (prefixWord ++ tailWord_197690) baseStart_197690 baseEnd_197690 := by
    simpa [prefixWord, tailWord_197690, baseEnd_197690] using wordTrace_append hprefix tailTrace_197690
  have hstable : (prefixWord ++ tailWord_197690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197690).length < 2 ^ (prefixWord ++ tailWord_197690).sum := by decide
  have hdescent : baseEnd_197690 < baseStart_197690 := by decide
  rcases family_descends (prefixWord ++ tailWord_197690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197728 : List Nat := [2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_197728 : Nat := 118140960795 + 197728 * 2 ^ 59
def prefixEnd_197728 : Nat := 4983230072969 + 3 ^ 40 * 197728 * 2
def baseEnd_197728 : Nat := 30082815659942999108347

theorem tailTrace_197728 : CollatzResearch.WordTrace tailWord_197728 prefixEnd_197728 30082815659942999108347 := by
  unfold tailWord_197728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605866313836350049500919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4807821751781800066001225 3605866313836350049500919)
  ·
    refine ⟨5408799470754525074251379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605866313836350049500919 5408799470754525074251379)
    ·
      refine ⟨8113199206131787611377069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408799470754525074251379 8113199206131787611377069)
      ·
        refine ⟨3042449702299420354266401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8113199206131787611377069 3042449702299420354266401)
        ·
          refine ⟨2281837276724565265699801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3042449702299420354266401 2281837276724565265699801)
          ·
            refine ⟨1711377957543423949274851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281837276724565265699801 1711377957543423949274851)
            ·
              refine ⟨2567066936315135923912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711377957543423949274851 2567066936315135923912277)
              ·
                refine ⟨30082815659942999108347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2567066936315135923912277 30082815659942999108347)
                ·
                  rfl

theorem cell20_197728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_197728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197728 prefixEnd_197728 := by exact prefixLift 197728
  have htrace : WordTrace (prefixWord ++ tailWord_197728) baseStart_197728 baseEnd_197728 := by
    simpa [prefixWord, tailWord_197728, baseEnd_197728] using wordTrace_append hprefix tailTrace_197728
  have hstable : (prefixWord ++ tailWord_197728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197728).length < 2 ^ (prefixWord ++ tailWord_197728).sum := by decide
  have hdescent : baseEnd_197728 < baseStart_197728 := by decide
  rcases family_descends (prefixWord ++ tailWord_197728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197752 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_197752 : Nat := 118140960795 + 197752 * 2 ^ 59
def prefixEnd_197752 : Nat := 4983230072969 + 3 ^ 40 * 197752 * 2
def baseEnd_197752 : Nat := 90259401233791580524943

theorem tailTrace_197752 : CollatzResearch.WordTrace tailWord_197752 prefixEnd_197752 90259401233791580524943 := by
  unfold tailWord_197752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606303989792876098937755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4808405319723834798583673 3606303989792876098937755)
  ·
    refine ⟨5409455984689314148406633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606303989792876098937755 5409455984689314148406633)
    ·
      refine ⟨4057091988516985611304975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409455984689314148406633 4057091988516985611304975)
      ·
        refine ⟨6085637982775478416957463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057091988516985611304975 6085637982775478416957463)
        ·
          refine ⟨9128456974163217625436195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6085637982775478416957463 9128456974163217625436195)
          ·
            refine ⟨13692685461244826438154293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128456974163217625436195 13692685461244826438154293)
            ·
              refine ⟨1283689261991702478576965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13692685461244826438154293 1283689261991702478576965)
              ·
                refine ⟨240691736623444214733181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1283689261991702478576965 240691736623444214733181)
                ·
                  refine ⟨90259401233791580524943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240691736623444214733181 90259401233791580524943)
                  ·
                    rfl

theorem cell20_197752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_197752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197752 prefixEnd_197752 := by exact prefixLift 197752
  have htrace : WordTrace (prefixWord ++ tailWord_197752) baseStart_197752 baseEnd_197752 := by
    simpa [prefixWord, tailWord_197752, baseEnd_197752] using wordTrace_append hprefix tailTrace_197752
  have hstable : (prefixWord ++ tailWord_197752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197752).length < 2 ^ (prefixWord ++ tailWord_197752).sum := by decide
  have hdescent : baseEnd_197752 < baseStart_197752 := by decide
  rcases family_descends (prefixWord ++ tailWord_197752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197793 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 2]
def baseStart_197793 : Nat := 118140960795 + 197793 * 2 ^ 59
def prefixEnd_197793 : Nat := 4983230072969 + 3 ^ 40 * 197793 * 2
def baseEnd_197793 : Nat := 90278114750977660158109

theorem tailTrace_197793 : CollatzResearch.WordTrace tailWord_197793 prefixEnd_197793 90278114750977660158109 := by
  unfold tailWord_197793
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214103372437216200118033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4809402248291477466745355 7214103372437216200118033)
  ·
    refine ⟨5410577529327912150088525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7214103372437216200118033 5410577529327912150088525)
    ·
      refine ⟨2028966573497967056283197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5410577529327912150088525 2028966573497967056283197)
      ·
        refine ⟨760862465061737646106199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2028966573497967056283197 760862465061737646106199)
        ·
          refine ⟨1141293697592606469159299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760862465061737646106199 1141293697592606469159299)
          ·
            refine ⟨1711940546388909703738949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141293697592606469159299 1711940546388909703738949)
            ·
              refine ⟨320988852447920569451053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1711940546388909703738949 320988852447920569451053)
              ·
                refine ⟨120370819667970213544145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320988852447920569451053 120370819667970213544145)
                ·
                  refine ⟨90278114750977660158109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120370819667970213544145 90278114750977660158109)
                  ·
                    rfl

theorem cell20_197793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_197793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197793 prefixEnd_197793 := by exact prefixLift 197793
  have htrace : WordTrace (prefixWord ++ tailWord_197793) baseStart_197793 baseEnd_197793 := by
    simpa [prefixWord, tailWord_197793, baseEnd_197793] using wordTrace_append hprefix tailTrace_197793
  have hstable : (prefixWord ++ tailWord_197793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197793).length < 2 ^ (prefixWord ++ tailWord_197793).sum := by decide
  have hdescent : baseEnd_197793 < baseStart_197793 := by decide
  rcases family_descends (prefixWord ++ tailWord_197793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197824 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_197824 : Nat := 118140960795 + 197824 * 2 ^ 59
def prefixEnd_197824 : Nat := 4983230072969 + 3 ^ 40 * 197824 * 2
def baseEnd_197824 : Nat := 90292263995679330124649

theorem tailTrace_197824 : CollatzResearch.WordTrace tailWord_197824 prefixEnd_197824 90292263995679330124649 := by
  unfold tailWord_197824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607617017662454247248263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4810156023549938996331017 3607617017662454247248263)
  ·
    refine ⟨5411425526493681370872395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3607617017662454247248263 5411425526493681370872395)
    ·
      refine ⟨8117138289740522056308593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5411425526493681370872395 8117138289740522056308593)
      ·
        refine ⟨6087853717305391542231445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8117138289740522056308593 6087853717305391542231445)
        ·
          refine ⟨285368142998690228542099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6087853717305391542231445 285368142998690228542099)
          ·
            refine ⟨428052214498035342813149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285368142998690228542099 428052214498035342813149)
            ·
              refine ⟨160519580436763253554931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428052214498035342813149 160519580436763253554931)
              ·
                refine ⟨240779370655144880332397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160519580436763253554931 240779370655144880332397)
                ·
                  refine ⟨90292263995679330124649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240779370655144880332397 90292263995679330124649)
                  ·
                    rfl

theorem cell20_197824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_197824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197824 prefixEnd_197824 := by exact prefixLift 197824
  have htrace : WordTrace (prefixWord ++ tailWord_197824) baseStart_197824 baseEnd_197824 := by
    simpa [prefixWord, tailWord_197824, baseEnd_197824] using wordTrace_append hprefix tailTrace_197824
  have hstable : (prefixWord ++ tailWord_197824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197824).length < 2 ^ (prefixWord ++ tailWord_197824).sum := by decide
  have hdescent : baseEnd_197824 < baseStart_197824 := by decide
  rcases family_descends (prefixWord ++ tailWord_197824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197830 : List Nat := [6, 1, 2, 2, 2, 1, 2, 4]
def baseStart_197830 : Nat := 118140960795 + 197830 * 2 ^ 59
def prefixEnd_197830 : Nat := 4983230072969 + 3 ^ 40 * 197830 * 2
def baseEnd_197830 : Nat := 30098334186389991974875

theorem tailTrace_197830 : CollatzResearch.WordTrace tailWord_197830 prefixEnd_197830 30098334186389991974875 := by
  unfold tailWord_197830
  simp only [CollatzResearch.WordTrace]
  refine ⟨225482902290724109975467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4810301915535447679476629 225482902290724109975467)
  ·
    refine ⟨338224353436086164963201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225482902290724109975467 338224353436086164963201)
    ·
      refine ⟨253668265077064623722401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338224353436086164963201 253668265077064623722401)
      ·
        refine ⟨190251198807798467791801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253668265077064623722401 190251198807798467791801)
        ·
          refine ⟨142688399105848850843851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190251198807798467791801 142688399105848850843851)
          ·
            refine ⟨214032598658773276265777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142688399105848850843851 214032598658773276265777)
            ·
              refine ⟨160524448994079957199333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214032598658773276265777 160524448994079957199333)
              ·
                refine ⟨30098334186389991974875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160524448994079957199333 30098334186389991974875)
                ·
                  rfl

theorem cell20_197830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_197830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197830 prefixEnd_197830 := by exact prefixLift 197830
  have htrace : WordTrace (prefixWord ++ tailWord_197830) baseStart_197830 baseEnd_197830 := by
    simpa [prefixWord, tailWord_197830, baseEnd_197830] using wordTrace_append hprefix tailTrace_197830
  have hstable : (prefixWord ++ tailWord_197830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197830).length < 2 ^ (prefixWord ++ tailWord_197830).sum := by decide
  have hdescent : baseEnd_197830 < baseStart_197830 := by decide
  rcases family_descends (prefixWord ++ tailWord_197830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197844 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 2]
def baseStart_197844 : Nat := 118140960795 + 197844 * 2 ^ 59
def prefixEnd_197844 : Nat := 4983230072969 + 3 ^ 40 * 197844 * 2
def baseEnd_197844 : Nat := 90301392540648149457901

theorem tailTrace_197844 : CollatzResearch.WordTrace tailWord_197844 prefixEnd_197844 90301392540648149457901 := by
  unfold tailWord_197844
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607981747626225955112293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4810642330168301273483057 3607981747626225955112293)
  ·
    refine ⟨676496577679917366583555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3607981747626225955112293 676496577679917366583555)
    ·
      refine ⟨1014744866519876049875333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676496577679917366583555 1014744866519876049875333)
      ·
        refine ⟨190264662472476759351625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1014744866519876049875333 190264662472476759351625)
        ·
          refine ⟨142698496854357569513719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190264662472476759351625 142698496854357569513719)
          ·
            refine ⟨214047745281536354270579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142698496854357569513719 214047745281536354270579)
            ·
              refine ⟨321071617922304531405869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214047745281536354270579 321071617922304531405869)
              ·
                refine ⟨120401856720864199277201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321071617922304531405869 120401856720864199277201)
                ·
                  refine ⟨90301392540648149457901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120401856720864199277201 90301392540648149457901)
                  ·
                    rfl

theorem cell20_197844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_197844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197844 prefixEnd_197844 := by exact prefixLift 197844
  have htrace : WordTrace (prefixWord ++ tailWord_197844) baseStart_197844 baseEnd_197844 := by
    simpa [prefixWord, tailWord_197844, baseEnd_197844] using wordTrace_append hprefix tailTrace_197844
  have hstable : (prefixWord ++ tailWord_197844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197844).length < 2 ^ (prefixWord ++ tailWord_197844).sum := by decide
  have hdescent : baseEnd_197844 < baseStart_197844 := by decide
  rcases family_descends (prefixWord ++ tailWord_197844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197848 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 2]
def baseStart_197848 : Nat := 118140960795 + 197848 * 2 ^ 59
def prefixEnd_197848 : Nat := 4983230072969 + 3 ^ 40 * 197848 * 2
def baseEnd_197848 : Nat := 90303218249641913324551

theorem tailTrace_197848 : CollatzResearch.WordTrace tailWord_197848 prefixEnd_197848 90303218249641913324551 := by
  unfold tailWord_197848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608054693618980296685099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4810739591491973728913465 3608054693618980296685099)
  ·
    refine ⟨5412082040428470445027649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608054693618980296685099 5412082040428470445027649)
    ·
      refine ⟨4059061530321352833770737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5412082040428470445027649 4059061530321352833770737)
      ·
        refine ⟨3044296147741014625328053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4059061530321352833770737 3044296147741014625328053)
        ·
          refine ⟨285402763850720121124505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3044296147741014625328053 285402763850720121124505)
          ·
            refine ⟨214052072888040090843379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285402763850720121124505 214052072888040090843379)
            ·
              refine ⟨321078109332060136265069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214052072888040090843379 321078109332060136265069)
              ·
                refine ⟨120404290999522551099401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321078109332060136265069 120404290999522551099401)
                ·
                  refine ⟨90303218249641913324551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120404290999522551099401 90303218249641913324551)
                  ·
                    rfl

theorem cell20_197848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_197848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197848 prefixEnd_197848 := by exact prefixLift 197848
  have htrace : WordTrace (prefixWord ++ tailWord_197848) baseStart_197848 baseEnd_197848 := by
    simpa [prefixWord, tailWord_197848, baseEnd_197848] using wordTrace_append hprefix tailTrace_197848
  have hstable : (prefixWord ++ tailWord_197848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197848).length < 2 ^ (prefixWord ++ tailWord_197848).sum := by decide
  have hdescent : baseEnd_197848 < baseStart_197848 := by decide
  rcases family_descends (prefixWord ++ tailWord_197848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197866 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_197866 : Nat := 118140960795 + 197866 * 2 ^ 59
def prefixEnd_197866 : Nat := 4983230072969 + 3 ^ 40 * 197866 * 2
def baseEnd_197866 : Nat := 90311433940113850724477

theorem tailTrace_197866 : CollatzResearch.WordTrace tailWord_197866 prefixEnd_197866 90311433940113850724477 := by
  unfold tailWord_197866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804191475293187416881363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4811177267448499778350301 1804191475293187416881363)
  ·
    refine ⟨2706287212939781125322045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1804191475293187416881363 2706287212939781125322045)
    ·
      refine ⟨1014857704852417921995767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2706287212939781125322045 1014857704852417921995767)
      ·
        refine ⟨1522286557278626882993651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014857704852417921995767 1522286557278626882993651)
        ·
          refine ⟨2283429835917940324490477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522286557278626882993651 2283429835917940324490477)
          ·
            refine ⟨856286188469227621683929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2283429835917940324490477 856286188469227621683929)
            ·
              refine ⟨642214641351920716262947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856286188469227621683929 642214641351920716262947)
              ·
                refine ⟨963321962027881074394421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642214641351920716262947 963321962027881074394421)
                ·
                  refine ⟨90311433940113850724477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 963321962027881074394421 90311433940113850724477)
                  ·
                    rfl

theorem cell20_197866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_197866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197866 prefixEnd_197866 := by exact prefixLift 197866
  have htrace : WordTrace (prefixWord ++ tailWord_197866) baseStart_197866 baseEnd_197866 := by
    simpa [prefixWord, tailWord_197866, baseEnd_197866] using wordTrace_append hprefix tailTrace_197866
  have hstable : (prefixWord ++ tailWord_197866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197866).length < 2 ^ (prefixWord ++ tailWord_197866).sum := by decide
  have hdescent : baseEnd_197866 < baseStart_197866 := by decide
  rcases family_descends (prefixWord ++ tailWord_197866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197869 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 4]
def baseStart_197869 : Nat := 118140960795 + 197869 * 2 ^ 59
def prefixEnd_197869 : Nat := 4983230072969 + 3 ^ 40 * 197869 * 2
def baseEnd_197869 : Nat := 90312803221859173624465

theorem tailTrace_197869 : CollatzResearch.WordTrace tailWord_197869 prefixEnd_197869 90312803221859173624465 := by
  unfold tailWord_197869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7216875320161881179884661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4811250213441254119923107 7216875320161881179884661)
  ·
    refine ⟨676582061265176360614187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7216875320161881179884661 676582061265176360614187)
    ·
      refine ⟨1014873091897764540921281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676582061265176360614187 1014873091897764540921281)
      ·
        refine ⟨761154818923323405690961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1014873091897764540921281 761154818923323405690961)
        ·
          refine ⟨570866114192492554268221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761154818923323405690961 570866114192492554268221)
          ·
            refine ⟨214074792822184707850583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 570866114192492554268221 214074792822184707850583)
            ·
              refine ⟨321112189233277061775875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214074792822184707850583 321112189233277061775875)
              ·
                refine ⟨481668283849915592663813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321112189233277061775875 481668283849915592663813)
                ·
                  refine ⟨90312803221859173624465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481668283849915592663813 90312803221859173624465)
                  ·
                    rfl

theorem cell20_197869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_197869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197869 prefixEnd_197869 := by exact prefixLift 197869
  have htrace : WordTrace (prefixWord ++ tailWord_197869) baseStart_197869 baseEnd_197869 := by
    simpa [prefixWord, tailWord_197869, baseEnd_197869] using wordTrace_append hprefix tailTrace_197869
  have hstable : (prefixWord ++ tailWord_197869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197869).length < 2 ^ (prefixWord ++ tailWord_197869).sum := by decide
  have hdescent : baseEnd_197869 < baseStart_197869 := by decide
  rcases family_descends (prefixWord ++ tailWord_197869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197958 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_197958 : Nat := 118140960795 + 197958 * 2 ^ 59
def prefixEnd_197958 : Nat := 4983230072969 + 3 ^ 40 * 197958 * 2
def baseEnd_197958 : Nat := 90353425246970419657435

theorem tailTrace_197958 : CollatzResearch.WordTrace tailWord_197958 prefixEnd_197958 90353425246970419657435 := by
  unfold tailWord_197958
  simp only [CollatzResearch.WordTrace]
  refine ⟨225628794276232793121079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4813414277892966253249685 225628794276232793121079)
  ·
    refine ⟨338443191414349189681619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225628794276232793121079 338443191414349189681619)
    ·
      refine ⟨507664787121523784522429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338443191414349189681619 507664787121523784522429)
      ·
        refine ⟨190374295170571419195911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507664787121523784522429 190374295170571419195911)
        ·
          refine ⟨285561442755857128793867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190374295170571419195911 285561442755857128793867)
          ·
            refine ⟨428342164133785693190801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285561442755857128793867 428342164133785693190801)
            ·
              refine ⟨321256623100339269893101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428342164133785693190801 321256623100339269893101)
              ·
                refine ⟨120471233662627226209913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321256623100339269893101 120471233662627226209913)
                ·
                  refine ⟨90353425246970419657435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120471233662627226209913 90353425246970419657435)
                  ·
                    rfl

theorem cell20_197958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_197958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197958 prefixEnd_197958 := by exact prefixLift 197958
  have htrace : WordTrace (prefixWord ++ tailWord_197958) baseStart_197958 baseEnd_197958 := by
    simpa [prefixWord, tailWord_197958, baseEnd_197958] using wordTrace_append hprefix tailTrace_197958
  have hstable : (prefixWord ++ tailWord_197958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197958).length < 2 ^ (prefixWord ++ tailWord_197958).sum := by decide
  have hdescent : baseEnd_197958 < baseStart_197958 := by decide
  rcases family_descends (prefixWord ++ tailWord_197958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197987 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_197987 : Nat := 118140960795 + 197987 * 2 ^ 59
def prefixEnd_197987 : Nat := 4983230072969 + 3 ^ 40 * 197987 * 2
def baseEnd_197987 : Nat := 90366661637175207690649

theorem tailTrace_197987 : CollatzResearch.WordTrace tailWord_197987 prefixEnd_197987 90366661637175207690649 := by
  unfold tailWord_197987
  simp only [CollatzResearch.WordTrace]
  refine ⟨7221179133734387332680215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4814119422489591555120143 7221179133734387332680215)
  ·
    refine ⟨10831768700601580999020323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7221179133734387332680215 10831768700601580999020323)
    ·
      refine ⟨16247653050902371498530485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10831768700601580999020323 16247653050902371498530485)
      ·
        refine ⟨1523217473522097327987233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16247653050902371498530485 1523217473522097327987233)
        ·
          refine ⟨1142413105141572995990425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523217473522097327987233 1142413105141572995990425)
          ·
            refine ⟨856809828856179746992819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142413105141572995990425 856809828856179746992819)
            ·
              refine ⟨1285214743284269620489229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856809828856179746992819 1285214743284269620489229)
              ·
                refine ⟨481955528731601107683461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285214743284269620489229 481955528731601107683461)
                ·
                  refine ⟨90366661637175207690649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481955528731601107683461 90366661637175207690649)
                  ·
                    rfl

theorem cell20_197987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_197987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_197987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_197987 prefixEnd_197987 := by exact prefixLift 197987
  have htrace : WordTrace (prefixWord ++ tailWord_197987) baseStart_197987 baseEnd_197987 := by
    simpa [prefixWord, tailWord_197987, baseEnd_197987] using wordTrace_append hprefix tailTrace_197987
  have hstable : (prefixWord ++ tailWord_197987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197987).length < 2 ^ (prefixWord ++ tailWord_197987).sum := by decide
  have hdescent : baseEnd_197987 < baseStart_197987 := by decide
  rcases family_descends (prefixWord ++ tailWord_197987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198017 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 2]
def baseStart_198017 : Nat := 118140960795 + 198017 * 2 ^ 59
def prefixEnd_198017 : Nat := 4983230072969 + 3 ^ 40 * 198017 * 2
def baseEnd_198017 : Nat := 90380354454628436690527

theorem tailTrace_198017 : CollatzResearch.WordTrace tailWord_198017 prefixEnd_198017 90380354454628436690527 := by
  unfold tailWord_198017
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222273323625702456272305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4814848882417134970848203 7222273323625702456272305)
  ·
    refine ⟨5416704992719276842204229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7222273323625702456272305 5416704992719276842204229)
    ·
      refine ⟨1015632186134864407913293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5416704992719276842204229 1015632186134864407913293)
      ·
        refine ⟨380862069800574152967485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1015632186134864407913293 380862069800574152967485)
        ·
          refine ⟨142823276175215307362807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380862069800574152967485 142823276175215307362807)
          ·
            refine ⟨214234914262822961044211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142823276175215307362807 214234914262822961044211)
            ·
              refine ⟨321352371394234441566317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214234914262822961044211 321352371394234441566317)
              ·
                refine ⟨120507139272837915587369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321352371394234441566317 120507139272837915587369)
                ·
                  refine ⟨90380354454628436690527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120507139272837915587369 90380354454628436690527)
                  ·
                    rfl

theorem cell20_198017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_198017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198017 prefixEnd_198017 := by exact prefixLift 198017
  have htrace : WordTrace (prefixWord ++ tailWord_198017) baseStart_198017 baseEnd_198017 := by
    simpa [prefixWord, tailWord_198017, baseEnd_198017] using wordTrace_append hprefix tailTrace_198017
  have hstable : (prefixWord ++ tailWord_198017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198017).length < 2 ^ (prefixWord ++ tailWord_198017).sum := by decide
  have hdescent : baseEnd_198017 < baseStart_198017 := by decide
  rcases family_descends (prefixWord ++ tailWord_198017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198094 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_198094 : Nat := 118140960795 + 198094 * 2 ^ 59
def prefixEnd_198094 : Nat := 4983230072969 + 3 ^ 40 * 198094 * 2
def baseEnd_198094 : Nat := 90415499352758391123545

theorem tailTrace_198094 : CollatzResearch.WordTrace tailWord_198094 prefixEnd_198094 90415499352758391123545 := by
  unfold tailWord_198094
  simp only [CollatzResearch.WordTrace]
  refine ⟨903135218043343075853167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4816721162897829737883557 903135218043343075853167)
  ·
    refine ⟨1354702827065014613779751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 903135218043343075853167 1354702827065014613779751)
    ·
      refine ⟨2032054240597521920669627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354702827065014613779751 2032054240597521920669627)
      ·
        refine ⟨3048081360896282881004441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032054240597521920669627 3048081360896282881004441)
        ·
          refine ⟨2286061020672212160753331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048081360896282881004441 2286061020672212160753331)
          ·
            refine ⟨3429091531008318241129997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286061020672212160753331 3429091531008318241129997)
            ·
              refine ⟨1285909324128119340423749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3429091531008318241129997 1285909324128119340423749)
              ·
                refine ⟨241107998274022376329453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1285909324128119340423749 241107998274022376329453)
                ·
                  refine ⟨90415499352758391123545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241107998274022376329453 90415499352758391123545)
                  ·
                    rfl

theorem cell20_198094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_198094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198094 prefixEnd_198094 := by exact prefixLift 198094
  have htrace : WordTrace (prefixWord ++ tailWord_198094) baseStart_198094 baseEnd_198094 := by
    simpa [prefixWord, tailWord_198094, baseEnd_198094] using wordTrace_append hprefix tailTrace_198094
  have hstable : (prefixWord ++ tailWord_198094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198094).length < 2 ^ (prefixWord ++ tailWord_198094).sum := by decide
  have hdescent : baseEnd_198094 < baseStart_198094 := by decide
  rcases family_descends (prefixWord ++ tailWord_198094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198101 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_198101 : Nat := 118140960795 + 198101 * 2 ^ 59
def prefixEnd_198101 : Nat := 4983230072969 + 3 ^ 40 * 198101 * 2
def baseEnd_198101 : Nat := 90418694343497477890183

theorem tailTrace_198101 : CollatzResearch.WordTrace tailWord_198101 prefixEnd_198101 90418694343497477890183 := by
  unfold tailWord_198101
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225337055321384802330157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4816891370214256534886771 7225337055321384802330157)
  ·
    refine ⟨2709501395745519300873809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7225337055321384802330157 2709501395745519300873809)
    ·
      refine ⟨2032126046809139475655357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2709501395745519300873809 2032126046809139475655357)
      ·
        refine ⟨762047267553427303370759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2032126046809139475655357 762047267553427303370759)
        ·
          refine ⟨1143070901330140955056139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762047267553427303370759 1143070901330140955056139)
          ·
            refine ⟨1714606351995211432584209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143070901330140955056139 1714606351995211432584209)
            ·
              refine ⟨1285954763996408574438157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714606351995211432584209 1285954763996408574438157)
              ·
                refine ⟨482233036498653215414309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285954763996408574438157 482233036498653215414309)
                ·
                  refine ⟨90418694343497477890183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482233036498653215414309 90418694343497477890183)
                  ·
                    rfl

theorem cell20_198101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_198101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198101 prefixEnd_198101 := by exact prefixLift 198101
  have htrace : WordTrace (prefixWord ++ tailWord_198101) baseStart_198101 baseEnd_198101 := by
    simpa [prefixWord, tailWord_198101, baseEnd_198101] using wordTrace_append hprefix tailTrace_198101
  have hstable : (prefixWord ++ tailWord_198101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198101).length < 2 ^ (prefixWord ++ tailWord_198101).sum := by decide
  have hdescent : baseEnd_198101 < baseStart_198101 := by decide
  rcases family_descends (prefixWord ++ tailWord_198101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198142 : List Nat := [4, 2, 2, 3, 1, 1, 7]
def baseStart_198142 : Nat := 118140960795 + 198142 * 2 ^ 59
def prefixEnd_198142 : Nat := 4983230072969 + 3 ^ 40 * 198142 * 2
def baseEnd_198142 : Nat := 10048600873409284169261

theorem tailTrace_198142 : CollatzResearch.WordTrace tailWord_198142 prefixEnd_198142 10048600873409284169261 := by
  unfold tailWord_198142
  simp only [CollatzResearch.WordTrace]
  refine ⟨903354056021606100571585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4817888298781899203048453 903354056021606100571585)
  ·
    refine ⟨677515542016204575428689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 903354056021606100571585 677515542016204575428689)
    ·
      refine ⟨508136656512153431571517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677515542016204575428689 508136656512153431571517)
      ·
        refine ⟨190551246192057536839319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508136656512153431571517 190551246192057536839319)
        ·
          refine ⟨285826869288086305258979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190551246192057536839319 285826869288086305258979)
          ·
            refine ⟨428740303932129457888469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285826869288086305258979 428740303932129457888469)
            ·
              refine ⟨10048600873409284169261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 428740303932129457888469 10048600873409284169261)
              ·
                rfl

theorem cell20_198142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 7].length) (baseStart_198142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198142 prefixEnd_198142 := by exact prefixLift 198142
  have htrace : WordTrace (prefixWord ++ tailWord_198142) baseStart_198142 baseEnd_198142 := by
    simpa [prefixWord, tailWord_198142, baseEnd_198142] using wordTrace_append hprefix tailTrace_198142
  have hstable : (prefixWord ++ tailWord_198142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198142).length < 2 ^ (prefixWord ++ tailWord_198142).sum := by decide
  have hdescent : baseEnd_198142 < baseStart_198142 := by decide
  rcases family_descends (prefixWord ++ tailWord_198142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198153 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_198153 : Nat := 118140960795 + 198153 * 2 ^ 59
def prefixEnd_198153 : Nat := 4983230072969 + 3 ^ 40 * 198153 * 2
def baseEnd_198153 : Nat := 90442428560416408156637

theorem tailTrace_198153 : CollatzResearch.WordTrace tailWord_198153 prefixEnd_198153 90442428560416408156637 := by
  unfold tailWord_198153
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227233651132997683223113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4818155767421998455482075 7227233651132997683223113)
  ·
    refine ⟨5420425238349748262417335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7227233651132997683223113 5420425238349748262417335)
    ·
      refine ⟨8130637857524622393626003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420425238349748262417335 8130637857524622393626003)
      ·
        refine ⟨12195956786286933590439005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130637857524622393626003 12195956786286933590439005)
        ·
          refine ⟨4573483794857600096414627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12195956786286933590439005 4573483794857600096414627)
          ·
            refine ⟨6860225692286400144621941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573483794857600096414627 6860225692286400144621941)
            ·
              refine ⟨643146158651850013558307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6860225692286400144621941 643146158651850013558307)
              ·
                refine ⟨964719237977775020337461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643146158651850013558307 964719237977775020337461)
                ·
                  refine ⟨90442428560416408156637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 964719237977775020337461 90442428560416408156637)
                  ·
                    rfl

theorem cell20_198153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_198153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198153 prefixEnd_198153 := by exact prefixLift 198153
  have htrace : WordTrace (prefixWord ++ tailWord_198153) baseStart_198153 baseEnd_198153 := by
    simpa [prefixWord, tailWord_198153, baseEnd_198153] using wordTrace_append hprefix tailTrace_198153
  have hstable : (prefixWord ++ tailWord_198153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198153).length < 2 ^ (prefixWord ++ tailWord_198153).sum := by decide
  have hdescent : baseEnd_198153 < baseStart_198153 := by decide
  rcases family_descends (prefixWord ++ tailWord_198153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198156 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_198156 : Nat := 118140960795 + 198156 * 2 ^ 59
def prefixEnd_198156 : Nat := 4983230072969 + 3 ^ 40 * 198156 * 2
def baseEnd_198156 : Nat := 90443797842161731056625

theorem tailTrace_198156 : CollatzResearch.WordTrace tailWord_198156 prefixEnd_198156 90443797842161731056625 := by
  unfold tailWord_198156
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613671535061064597791161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4818228713414752797054881 3613671535061064597791161)
  ·
    refine ⟨2710253651295798448343371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3613671535061064597791161 2710253651295798448343371)
    ·
      refine ⟨4065380476943697672515057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710253651295798448343371 4065380476943697672515057)
      ·
        refine ⟨3049035357707773254386293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065380476943697672515057 3049035357707773254386293)
        ·
          refine ⟨285847064785103742598715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3049035357707773254386293 285847064785103742598715)
          ·
            refine ⟨428770597177655613898073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285847064785103742598715 428770597177655613898073)
            ·
              refine ⟨321577947883241710423555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428770597177655613898073 321577947883241710423555)
              ·
                refine ⟨482366921824862565635333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321577947883241710423555 482366921824862565635333)
                ·
                  refine ⟨90443797842161731056625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482366921824862565635333 90443797842161731056625)
                  ·
                    rfl

theorem cell20_198156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_198156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198156 prefixEnd_198156 := by exact prefixLift 198156
  have htrace : WordTrace (prefixWord ++ tailWord_198156) baseStart_198156 baseEnd_198156 := by
    simpa [prefixWord, tailWord_198156, baseEnd_198156] using wordTrace_append hprefix tailTrace_198156
  have hstable : (prefixWord ++ tailWord_198156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198156).length < 2 ^ (prefixWord ++ tailWord_198156).sum := by decide
  have hdescent : baseEnd_198156 < baseStart_198156 := by decide
  rcases family_descends (prefixWord ++ tailWord_198156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198177 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_198177 : Nat := 118140960795 + 198177 * 2 ^ 59
def prefixEnd_198177 : Nat := 4983230072969 + 3 ^ 40 * 198177 * 2
def baseEnd_198177 : Nat := 90453382814378991356539

theorem tailTrace_198177 : CollatzResearch.WordTrace tailWord_198177 prefixEnd_198177 90453382814378991356539 := by
  unfold tailWord_198177
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228109003046049782096785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4818739335364033188064523 7228109003046049782096785)
  ·
    refine ⟨5421081752284537336572589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7228109003046049782096785 5421081752284537336572589)
    ·
      refine ⟨2032905657106701501214721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5421081752284537336572589 2032905657106701501214721)
      ·
        refine ⟨1524679242830026125911041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032905657106701501214721 1524679242830026125911041)
        ·
          refine ⟨1143509432122519594433281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1524679242830026125911041 1143509432122519594433281)
          ·
            refine ⟨857632074091889695824961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143509432122519594433281 857632074091889695824961)
            ·
              refine ⟨643224055568917271868721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857632074091889695824961 643224055568917271868721)
              ·
                refine ⟨482418041676687953901541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643224055568917271868721 482418041676687953901541)
                ·
                  refine ⟨90453382814378991356539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482418041676687953901541 90453382814378991356539)
                  ·
                    rfl

theorem cell20_198177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_198177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198177 prefixEnd_198177 := by exact prefixLift 198177
  have htrace : WordTrace (prefixWord ++ tailWord_198177) baseStart_198177 baseEnd_198177 := by
    simpa [prefixWord, tailWord_198177, baseEnd_198177] using wordTrace_append hprefix tailTrace_198177
  have hstable : (prefixWord ++ tailWord_198177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198177).length < 2 ^ (prefixWord ++ tailWord_198177).sum := by decide
  have hdescent : baseEnd_198177 < baseStart_198177 := by decide
  rcases family_descends (prefixWord ++ tailWord_198177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198190 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_198190 : Nat := 118140960795 + 198190 * 2 ^ 59
def prefixEnd_198190 : Nat := 4983230072969 + 3 ^ 40 * 198190 * 2
def baseEnd_198190 : Nat := 90459316368608723923153

theorem tailTrace_198190 : CollatzResearch.WordTrace tailWord_198190 prefixEnd_198190 90459316368608723923153 := by
  unfold tailWord_198190
  simp only [CollatzResearch.WordTrace]
  refine ⟨903572893999869125290003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4819055434665968668213349 903572893999869125290003)
  ·
    refine ⟨1355359340999803687935005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 903572893999869125290003 1355359340999803687935005)
    ·
      refine ⟨508259752874926382975627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1355359340999803687935005 508259752874926382975627)
      ·
        refine ⟨762389629312389574463441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508259752874926382975627 762389629312389574463441)
        ·
          refine ⟨571792221984292180847581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762389629312389574463441 571792221984292180847581)
          ·
            refine ⟨214422083244109567817843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 571792221984292180847581 214422083244109567817843)
            ·
              refine ⟨321633124866164351726765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214422083244109567817843 321633124866164351726765)
              ·
                refine ⟨120612421824811631897537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321633124866164351726765 120612421824811631897537)
                ·
                  refine ⟨90459316368608723923153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120612421824811631897537 90459316368608723923153)
                  ·
                    rfl

theorem cell20_198190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_198190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198190 prefixEnd_198190 := by exact prefixLift 198190
  have htrace : WordTrace (prefixWord ++ tailWord_198190) baseStart_198190 baseEnd_198190 := by
    simpa [prefixWord, tailWord_198190, baseEnd_198190] using wordTrace_append hprefix tailTrace_198190
  have hstable : (prefixWord ++ tailWord_198190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198190).length < 2 ^ (prefixWord ++ tailWord_198190).sum := by decide
  have hdescent : baseEnd_198190 < baseStart_198190 := by decide
  rcases family_descends (prefixWord ++ tailWord_198190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198221 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 3]
def baseStart_198221 : Nat := 118140960795 + 198221 * 2 ^ 59
def prefixEnd_198221 : Nat := 4983230072969 + 3 ^ 40 * 198221 * 2
def baseEnd_198221 : Nat := 90473465613310393889693

theorem tailTrace_198221 : CollatzResearch.WordTrace tailWord_198221 prefixEnd_198221 90473465613310393889693 := by
  unfold tailWord_198221
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229713814886645296698517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4819809209924430197799011 7229713814886645296698517)
  ·
    refine ⟨338892835072811498282743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7229713814886645296698517 338892835072811498282743)
    ·
      refine ⟨508339252609217247424115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338892835072811498282743 508339252609217247424115)
      ·
        refine ⟨762508878913825871136173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508339252609217247424115 762508878913825871136173)
        ·
          refine ⟨285940829592684701676065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 762508878913825871136173 285940829592684701676065)
          ·
            refine ⟨214455622194513526257049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285940829592684701676065 214455622194513526257049)
            ·
              refine ⟨160841716645885144692787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214455622194513526257049 160841716645885144692787)
              ·
                refine ⟨241262574968827717039181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160841716645885144692787 241262574968827717039181)
                ·
                  refine ⟨90473465613310393889693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241262574968827717039181 90473465613310393889693)
                  ·
                    rfl

theorem cell20_198221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_198221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198221 prefixEnd_198221 := by exact prefixLift 198221
  have htrace : WordTrace (prefixWord ++ tailWord_198221) baseStart_198221 baseEnd_198221 := by
    simpa [prefixWord, tailWord_198221, baseEnd_198221] using wordTrace_append hprefix tailTrace_198221
  have hstable : (prefixWord ++ tailWord_198221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198221).length < 2 ^ (prefixWord ++ tailWord_198221).sum := by decide
  have hdescent : baseEnd_198221 < baseStart_198221 := by decide
  rcases family_descends (prefixWord ++ tailWord_198221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198308 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 2]
def baseStart_198308 : Nat := 118140960795 + 198308 * 2 ^ 59
def prefixEnd_198308 : Nat := 4983230072969 + 3 ^ 40 * 198308 * 2
def baseEnd_198308 : Nat := 90513174783924757989337

theorem tailTrace_198308 : CollatzResearch.WordTrace tailWord_198308 prefixEnd_198308 90513174783924757989337 := by
  unfold tailWord_198308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616443482785729577557789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4821924643714306103410385 3616443482785729577557789)
  ·
    refine ⟨1356166306044648591584171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3616443482785729577557789 1356166306044648591584171)
    ·
      refine ⟨2034249459066972887376257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356166306044648591584171 2034249459066972887376257)
      ·
        refine ⟨1525687094300229665532193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2034249459066972887376257 1525687094300229665532193)
        ·
          refine ⟨1144265320725172249149145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525687094300229665532193 1144265320725172249149145)
          ·
            refine ⟨858198990543879186861859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144265320725172249149145 858198990543879186861859)
            ·
              refine ⟨1287298485815818780292789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858198990543879186861859 1287298485815818780292789)
              ·
                refine ⟨120684233045233010652449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1287298485815818780292789 120684233045233010652449)
                ·
                  refine ⟨90513174783924757989337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120684233045233010652449 90513174783924757989337)
                  ·
                    rfl

theorem cell20_198308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_198308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198308 prefixEnd_198308 := by exact prefixLift 198308
  have htrace : WordTrace (prefixWord ++ tailWord_198308) baseStart_198308 baseEnd_198308 := by
    simpa [prefixWord, tailWord_198308, baseEnd_198308] using wordTrace_append hprefix tailTrace_198308
  have hstable : (prefixWord ++ tailWord_198308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198308).length < 2 ^ (prefixWord ++ tailWord_198308).sum := by decide
  have hdescent : baseEnd_198308 < baseStart_198308 := by decide
  rcases family_descends (prefixWord ++ tailWord_198308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198319 : List Nat := [1, 1, 2, 1, 2, 4, 9]
def baseStart_198319 : Nat := 118140960795 + 198319 * 2 ^ 59
def prefixEnd_198319 : Nat := 4983230072969 + 3 ^ 40 * 198319 * 2
def baseEnd_198319 : Nat := 10057577275961956513625

theorem tailTrace_198319 : CollatzResearch.WordTrace tailWord_198319 prefixEnd_198319 10057577275961956513625 := by
  unfold tailWord_198319
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233288168531608033766011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4822192112354405355844007 7233288168531608033766011)
  ·
    refine ⟨10849932252797412050649017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7233288168531608033766011 10849932252797412050649017)
    ·
      refine ⟨8137449189598059037986763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10849932252797412050649017 8137449189598059037986763)
      ·
        refine ⟨12206173784397088556980145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137449189598059037986763 12206173784397088556980145)
        ·
          refine ⟨9154630338297816417735109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12206173784397088556980145 9154630338297816417735109)
          ·
            refine ⟨1716493188430840578325333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9154630338297816417735109 1716493188430840578325333)
            ·
              refine ⟨10057577275961956513625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1716493188430840578325333 10057577275961956513625)
              ·
                rfl

theorem cell20_198319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_198319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198319 prefixEnd_198319 := by exact prefixLift 198319
  have htrace : WordTrace (prefixWord ++ tailWord_198319) baseStart_198319 baseEnd_198319 := by
    simpa [prefixWord, tailWord_198319, baseEnd_198319] using wordTrace_append hprefix tailTrace_198319
  have hstable : (prefixWord ++ tailWord_198319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198319).length < 2 ^ (prefixWord ++ tailWord_198319).sum := by decide
  have hdescent : baseEnd_198319 < baseStart_198319 := by decide
  rcases family_descends (prefixWord ++ tailWord_198319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198322 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_198322 : Nat := 118140960795 + 198322 * 2 ^ 59
def prefixEnd_198322 : Nat := 4983230072969 + 3 ^ 40 * 198322 * 2
def baseEnd_198322 : Nat := 90519564765402931522613

theorem tailTrace_198322 : CollatzResearch.WordTrace tailWord_198322 prefixEnd_198322 90519564765402931522613 := by
  unfold tailWord_198322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808349396880184886531305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4822265058347159697416813 1808349396880184886531305)
  ·
    refine ⟨1356262047660138664898479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1808349396880184886531305 1356262047660138664898479)
    ·
      refine ⟨2034393071490207997347719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356262047660138664898479 2034393071490207997347719)
      ·
        refine ⟨3051589607235311996021579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034393071490207997347719 3051589607235311996021579)
        ·
          refine ⟨4577384410852967994032369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051589607235311996021579 4577384410852967994032369)
          ·
            refine ⟨3433038308139725995524277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4577384410852967994032369 3433038308139725995524277)
            ·
              refine ⟨321847341388099312080401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3433038308139725995524277 321847341388099312080401)
              ·
                refine ⟨241385506041074484060301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321847341388099312080401 241385506041074484060301)
                ·
                  refine ⟨90519564765402931522613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241385506041074484060301 90519564765402931522613)
                  ·
                    rfl

theorem cell20_198322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_198322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198322 prefixEnd_198322 := by exact prefixLift 198322
  have htrace : WordTrace (prefixWord ++ tailWord_198322) baseStart_198322 baseEnd_198322 := by
    simpa [prefixWord, tailWord_198322, baseEnd_198322] using wordTrace_append hprefix tailTrace_198322
  have hstable : (prefixWord ++ tailWord_198322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198322).length < 2 ^ (prefixWord ++ tailWord_198322).sum := by decide
  have hdescent : baseEnd_198322 < baseStart_198322 := by decide
  rcases family_descends (prefixWord ++ tailWord_198322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198349 : List Nat := [1, 6, 2, 1, 1, 3, 2, 4]
def baseStart_198349 : Nat := 118140960795 + 198349 * 2 ^ 59
def prefixEnd_198349 : Nat := 4983230072969 + 3 ^ 40 * 198349 * 2
def baseEnd_198349 : Nat := 30177296100370279207501

theorem tailTrace_198349 : CollatzResearch.WordTrace tailWord_198349 prefixEnd_198349 30177296100370279207501 := by
  unfold tailWord_198349
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234382358422923157358101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4822921572281948771572067 7234382358422923157358101)
  ·
    refine ⟨339111673051074523001161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7234382358422923157358101 339111673051074523001161)
    ·
      refine ⟨254333754788305892250871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339111673051074523001161 254333754788305892250871)
      ·
        refine ⟨381500632182458838376307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254333754788305892250871 381500632182458838376307)
        ·
          refine ⟨572250948273688257564461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381500632182458838376307 572250948273688257564461)
          ·
            refine ⟨214594105602633096586673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572250948273688257564461 214594105602633096586673)
            ·
              refine ⟨160945579201974822440005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214594105602633096586673 160945579201974822440005)
              ·
                refine ⟨30177296100370279207501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160945579201974822440005 30177296100370279207501)
                ·
                  rfl

theorem cell20_198349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_198349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198349 prefixEnd_198349 := by exact prefixLift 198349
  have htrace : WordTrace (prefixWord ++ tailWord_198349) baseStart_198349 baseEnd_198349 := by
    simpa [prefixWord, tailWord_198349, baseEnd_198349] using wordTrace_append hprefix tailTrace_198349
  have hstable : (prefixWord ++ tailWord_198349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198349).length < 2 ^ (prefixWord ++ tailWord_198349).sum := by decide
  have hdescent : baseEnd_198349 < baseStart_198349 := by decide
  rcases family_descends (prefixWord ++ tailWord_198349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198353 : List Nat := [1, 2, 2, 1, 2, 6, 2, 4]
def baseStart_198353 : Nat := 118140960795 + 198353 * 2 ^ 59
def prefixEnd_198353 : Nat := 4983230072969 + 3 ^ 40 * 198353 * 2
def baseEnd_198353 : Nat := 30177904670034867163051

theorem tailTrace_198353 : CollatzResearch.WordTrace tailWord_198353 prefixEnd_198353 30177904670034867163051 := by
  unfold tailWord_198353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234528250408431840503713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4823018833605621227002475 7234528250408431840503713)
  ·
    refine ⟨5425896187806323880377785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7234528250408431840503713 5425896187806323880377785)
    ·
      refine ⟨4069422140854742910283339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5425896187806323880377785 4069422140854742910283339)
      ·
        refine ⟨6104133211282114365425009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069422140854742910283339 6104133211282114365425009)
        ·
          refine ⟨4578099908461585774068757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104133211282114365425009 4578099908461585774068757)
          ·
            refine ⟨214598433209136833159473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4578099908461585774068757 214598433209136833159473)
            ·
              refine ⟨160948824906852624869605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214598433209136833159473 160948824906852624869605)
              ·
                refine ⟨30177904670034867163051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160948824906852624869605 30177904670034867163051)
                ·
                  rfl

theorem cell20_198353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_198353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198353 prefixEnd_198353 := by exact prefixLift 198353
  have htrace : WordTrace (prefixWord ++ tailWord_198353) baseStart_198353 baseEnd_198353 := by
    simpa [prefixWord, tailWord_198353, baseEnd_198353] using wordTrace_append hprefix tailTrace_198353
  have hstable : (prefixWord ++ tailWord_198353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198353).length < 2 ^ (prefixWord ++ tailWord_198353).sum := by decide
  have hdescent : baseEnd_198353 < baseStart_198353 := by decide
  rcases family_descends (prefixWord ++ tailWord_198353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198433 : List Nat := [1, 2, 3, 2, 1, 11]
def baseStart_198433 : Nat := 118140960795 + 198433 * 2 ^ 59
def prefixEnd_198433 : Nat := 4983230072969 + 3 ^ 40 * 198433 * 2
def baseEnd_198433 : Nat := 3354452895925180697117

theorem tailTrace_198433 : CollatzResearch.WordTrace tailWord_198433 prefixEnd_198433 3354452895925180697117 := by
  unfold tailWord_198433
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237446090118605503415953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4824964060079070335610635 7237446090118605503415953)
  ·
    refine ⟨5428084567588954127561965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7237446090118605503415953 5428084567588954127561965)
    ·
      refine ⟨2035531712845857797835737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5428084567588954127561965 2035531712845857797835737)
      ·
        refine ⟨1526648784634393348376803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035531712845857797835737 1526648784634393348376803)
        ·
          refine ⟨2289973176951590022565205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526648784634393348376803 2289973176951590022565205)
          ·
            refine ⟨3354452895925180697117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2289973176951590022565205 3354452895925180697117)
            ·
              rfl

theorem cell20_198433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 11].length) (baseStart_198433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198433 prefixEnd_198433 := by exact prefixLift 198433
  have htrace : WordTrace (prefixWord ++ tailWord_198433) baseStart_198433 baseEnd_198433 := by
    simpa [prefixWord, tailWord_198433, baseEnd_198433] using wordTrace_append hprefix tailTrace_198433
  have hstable : (prefixWord ++ tailWord_198433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198433).length < 2 ^ (prefixWord ++ tailWord_198433).sum := by decide
  have hdescent : baseEnd_198433 < baseStart_198433 := by decide
  rcases family_descends (prefixWord ++ tailWord_198433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198436 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_198436 : Nat := 118140960795 + 198436 * 2 ^ 59
def prefixEnd_198436 : Nat := 4983230072969 + 3 ^ 40 * 198436 * 2
def baseEnd_198436 : Nat := 90571597471725201722147

theorem tailTrace_198436 : CollatzResearch.WordTrace tailWord_198436 prefixEnd_198436 90571597471725201722147 := by
  unfold tailWord_198436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618777754553868507887581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4825037006071824677183441 3618777754553868507887581)
  ·
    refine ⟨1357041657957700690457843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3618777754553868507887581 1357041657957700690457843)
    ·
      refine ⟨2035562486936551035686765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357041657957700690457843 2035562486936551035686765)
      ·
        refine ⟨763335932601206638382537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2035562486936551035686765 763335932601206638382537)
        ·
          refine ⟨572501949450904978786903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763335932601206638382537 572501949450904978786903)
          ·
            refine ⟨858752924176357468180355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572501949450904978786903 858752924176357468180355)
            ·
              refine ⟨1288129386264536202270533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858752924176357468180355 1288129386264536202270533)
              ·
                refine ⟨241524259924600537925725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1288129386264536202270533 241524259924600537925725)
                ·
                  refine ⟨90571597471725201722147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241524259924600537925725 90571597471725201722147)
                  ·
                    rfl

theorem cell20_198436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_198436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198436 prefixEnd_198436 := by exact prefixLift 198436
  have htrace : WordTrace (prefixWord ++ tailWord_198436) baseStart_198436 baseEnd_198436 := by
    simpa [prefixWord, tailWord_198436, baseEnd_198436] using wordTrace_append hprefix tailTrace_198436
  have hstable : (prefixWord ++ tailWord_198436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198436).length < 2 ^ (prefixWord ++ tailWord_198436).sum := by decide
  have hdescent : baseEnd_198436 < baseStart_198436 := by decide
  rcases family_descends (prefixWord ++ tailWord_198436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198446 : List Nat := [4, 1, 3, 2, 2, 2, 1, 5]
def baseStart_198446 : Nat := 118140960795 + 198446 * 2 ^ 59
def prefixEnd_198446 : Nat := 4983230072969 + 3 ^ 40 * 198446 * 2
def baseEnd_198446 : Nat := 30192053914736537129591

theorem tailTrace_198446 : CollatzResearch.WordTrace tailWord_198446 prefixEnd_198446 30192053914736537129591 := by
  unfold tailWord_198446
  simp only [CollatzResearch.WordTrace]
  refine ⟨904740029883938590454899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4825280159381005815759461 904740029883938590454899)
  ·
    refine ⟨1357110044825907885682349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 904740029883938590454899 1357110044825907885682349)
    ·
      refine ⟨508916266809715457130881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1357110044825907885682349 508916266809715457130881)
      ·
        refine ⟨381687200107286592848161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508916266809715457130881 381687200107286592848161)
        ·
          refine ⟨286265400080464944636121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381687200107286592848161 286265400080464944636121)
          ·
            refine ⟨214699050060348708477091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286265400080464944636121 214699050060348708477091)
            ·
              refine ⟨322048575090523062715637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214699050060348708477091 322048575090523062715637)
              ·
                refine ⟨30192053914736537129591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322048575090523062715637 30192053914736537129591)
                ·
                  rfl

theorem cell20_198446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_198446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198446 prefixEnd_198446 := by exact prefixLift 198446
  have htrace : WordTrace (prefixWord ++ tailWord_198446) baseStart_198446 baseEnd_198446 := by
    simpa [prefixWord, tailWord_198446, baseEnd_198446] using wordTrace_append hprefix tailTrace_198446
  have hstable : (prefixWord ++ tailWord_198446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198446).length < 2 ^ (prefixWord ++ tailWord_198446).sum := by decide
  have hdescent : baseEnd_198446 < baseStart_198446 := by decide
  rcases family_descends (prefixWord ++ tailWord_198446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198450 : List Nat := [3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_198450 : Nat := 118140960795 + 198450 * 2 ^ 59
def prefixEnd_198450 : Nat := 4983230072969 + 3 ^ 40 * 198450 * 2
def baseEnd_198450 : Nat := 30192662484401125085141

theorem tailTrace_198450 : CollatzResearch.WordTrace tailWord_198450 prefixEnd_198450 30192662484401125085141 := by
  unfold tailWord_198450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809516532764254351696201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4825377420704678271189869 1809516532764254351696201)
  ·
    refine ⟨1357137399573190763772151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1809516532764254351696201 1357137399573190763772151)
    ·
      refine ⟨2035706099359786145658227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357137399573190763772151 2035706099359786145658227)
      ·
        refine ⟨3053559149039679218487341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035706099359786145658227 3053559149039679218487341)
        ·
          refine ⟨1145084680889879706932753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3053559149039679218487341 1145084680889879706932753)
          ·
            refine ⟨858813510667409780199565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145084680889879706932753 858813510667409780199565)
            ·
              refine ⟨322055066500278667574837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858813510667409780199565 322055066500278667574837)
              ·
                refine ⟨30192662484401125085141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322055066500278667574837 30192662484401125085141)
                ·
                  rfl

theorem cell20_198450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_198450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198450 prefixEnd_198450 := by exact prefixLift 198450
  have htrace : WordTrace (prefixWord ++ tailWord_198450) baseStart_198450 baseEnd_198450 := by
    simpa [prefixWord, tailWord_198450, baseEnd_198450] using wordTrace_append hprefix tailTrace_198450
  have hstable : (prefixWord ++ tailWord_198450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198450).length < 2 ^ (prefixWord ++ tailWord_198450).sum := by decide
  have hdescent : baseEnd_198450 < baseStart_198450 := by decide
  rcases family_descends (prefixWord ++ tailWord_198450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198471 : List Nat := [1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_198471 : Nat := 118140960795 + 198471 * 2 ^ 59
def prefixEnd_198471 : Nat := 4983230072969 + 3 ^ 40 * 198471 * 2
def baseEnd_198471 : Nat := 30195857475140211851779

theorem tailTrace_198471 : CollatzResearch.WordTrace tailWord_198471 prefixEnd_198471 30195857475140211851779 := by
  unfold tailWord_198471
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238832063980937993299267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4825888042653958662199511 7238832063980937993299267)
  ·
    refine ⟨10858248095971406989948901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7238832063980937993299267 10858248095971406989948901)
    ·
      refine ⟨2035921517994638810615419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10858248095971406989948901 2035921517994638810615419)
      ·
        refine ⟨3053882276991958215923129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035921517994638810615419 3053882276991958215923129)
        ·
          refine ⟨2290411707743968661942347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3053882276991958215923129 2290411707743968661942347)
          ·
            refine ⟨3435617561615952992913521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290411707743968661942347 3435617561615952992913521)
            ·
              refine ⟨2576713171211964744685141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3435617561615952992913521 2576713171211964744685141)
              ·
                refine ⟨30195857475140211851779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2576713171211964744685141 30195857475140211851779)
                ·
                  rfl

theorem cell20_198471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_198471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198471 prefixEnd_198471 := by exact prefixLift 198471
  have htrace : WordTrace (prefixWord ++ tailWord_198471) baseStart_198471 baseEnd_198471 := by
    simpa [prefixWord, tailWord_198471, baseEnd_198471] using wordTrace_append hprefix tailTrace_198471
  have hstable : (prefixWord ++ tailWord_198471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198471).length < 2 ^ (prefixWord ++ tailWord_198471).sum := by decide
  have hdescent : baseEnd_198471 < baseStart_198471 := by decide
  rcases family_descends (prefixWord ++ tailWord_198471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198477 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 2]
def baseStart_198477 : Nat := 118140960795 + 198477 * 2 ^ 59
def prefixEnd_198477 : Nat := 4983230072969 + 3 ^ 40 * 198477 * 2
def baseEnd_198477 : Nat := 90590310988911281355313

theorem tailTrace_198477 : CollatzResearch.WordTrace tailWord_198477 prefixEnd_198477 90590310988911281355313 := by
  unfold tailWord_198477
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239050901959201018017685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4826033934639467345345123 7239050901959201018017685)
  ·
    refine ⟨339330511029337547719579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7239050901959201018017685 339330511029337547719579)
    ·
      refine ⟨508995766544006321579369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339330511029337547719579 508995766544006321579369)
      ·
        refine ⟨381746824908004741184527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508995766544006321579369 381746824908004741184527)
        ·
          refine ⟨572620237362007111776791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381746824908004741184527 572620237362007111776791)
          ·
            refine ⟨858930356043010667665187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572620237362007111776791 858930356043010667665187)
            ·
              refine ⟨1288395534064516001497781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858930356043010667665187 1288395534064516001497781)
              ·
                refine ⟨120787081318548375140417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1288395534064516001497781 120787081318548375140417)
                ·
                  refine ⟨90590310988911281355313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120787081318548375140417 90590310988911281355313)
                  ·
                    rfl

theorem cell20_198477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_198477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198477 prefixEnd_198477 := by exact prefixLift 198477
  have htrace : WordTrace (prefixWord ++ tailWord_198477) baseStart_198477 baseEnd_198477 := by
    simpa [prefixWord, tailWord_198477, baseEnd_198477] using wordTrace_append hprefix tailTrace_198477
  have hstable : (prefixWord ++ tailWord_198477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198477).length < 2 ^ (prefixWord ++ tailWord_198477).sum := by decide
  have hdescent : baseEnd_198477 < baseStart_198477 := by decide
  rcases family_descends (prefixWord ++ tailWord_198477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198495 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_198495 : Nat := 118140960795 + 198495 * 2 ^ 59
def prefixEnd_198495 : Nat := 4983230072969 + 3 ^ 40 * 198495 * 2
def baseEnd_198495 : Nat := 90598526679383218755239

theorem tailTrace_198495 : CollatzResearch.WordTrace tailWord_198495 prefixEnd_198495 90598526679383218755239 := by
  unfold tailWord_198495
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239707415893990092172939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4826471610595993394781959 7239707415893990092172939)
  ·
    refine ⟨10859561123840985138259409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239707415893990092172939 10859561123840985138259409)
    ·
      refine ⟨8144670842880738853694557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10859561123840985138259409 8144670842880738853694557)
      ·
        refine ⟨3054251566080277070135459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8144670842880738853694557 3054251566080277070135459)
        ·
          refine ⟨4581377349120415605203189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054251566080277070135459 4581377349120415605203189)
          ·
            refine ⟨429504126480038962987799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4581377349120415605203189 429504126480038962987799)
            ·
              refine ⟨644256189720058444481699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429504126480038962987799 644256189720058444481699)
              ·
                refine ⟨966384284580087666722549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644256189720058444481699 966384284580087666722549)
                ·
                  refine ⟨90598526679383218755239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 966384284580087666722549 90598526679383218755239)
                  ·
                    rfl

theorem cell20_198495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_198495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198495 prefixEnd_198495 := by exact prefixLift 198495
  have htrace : WordTrace (prefixWord ++ tailWord_198495) baseStart_198495 baseEnd_198495 := by
    simpa [prefixWord, tailWord_198495, baseEnd_198495] using wordTrace_append hprefix tailTrace_198495
  have hstable : (prefixWord ++ tailWord_198495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198495).length < 2 ^ (prefixWord ++ tailWord_198495).sum := by decide
  have hdescent : baseEnd_198495 < baseStart_198495 := by decide
  rcases family_descends (prefixWord ++ tailWord_198495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198498 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_198498 : Nat := 118140960795 + 198498 * 2 ^ 59
def prefixEnd_198498 : Nat := 4983230072969 + 3 ^ 40 * 198498 * 2
def baseEnd_198498 : Nat := 90599895961128541655227

theorem tailTrace_198498 : CollatzResearch.WordTrace tailWord_198498 prefixEnd_198498 90599895961128541655227 := by
  unfold tailWord_198498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809954208720780401133037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4826544556588747736354765 1809954208720780401133037)
  ·
    refine ⟨678732828270292650424889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1809954208720780401133037 678732828270292650424889)
    ·
      refine ⟨509049621202719487818667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678732828270292650424889 509049621202719487818667)
      ·
        refine ⟨763574431804079231728001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509049621202719487818667 763574431804079231728001)
        ·
          refine ⟨572680823853059423796001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763574431804079231728001 572680823853059423796001)
          ·
            refine ⟨429510617889794567847001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572680823853059423796001 429510617889794567847001)
            ·
              refine ⟨322132963417345925885251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429510617889794567847001 322132963417345925885251)
              ·
                refine ⟨483199445126018888827877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322132963417345925885251 483199445126018888827877)
                ·
                  refine ⟨90599895961128541655227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483199445126018888827877 90599895961128541655227)
                  ·
                    rfl

theorem cell20_198498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_198498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198498 prefixEnd_198498 := by exact prefixLift 198498
  have htrace : WordTrace (prefixWord ++ tailWord_198498) baseStart_198498 baseEnd_198498 := by
    simpa [prefixWord, tailWord_198498, baseEnd_198498] using wordTrace_append hprefix tailTrace_198498
  have hstable : (prefixWord ++ tailWord_198498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198498).length < 2 ^ (prefixWord ++ tailWord_198498).sum := by decide
  have hdescent : baseEnd_198498 < baseStart_198498 := by decide
  rcases family_descends (prefixWord ++ tailWord_198498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198557 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_198557 : Nat := 118140960795 + 198557 * 2 ^ 59
def prefixEnd_198557 : Nat := 4983230072969 + 3 ^ 40 * 198557 * 2
def baseEnd_198557 : Nat := 90626825168786558688319

theorem tailTrace_198557 : CollatzResearch.WordTrace tailWord_198557 prefixEnd_198557 90626825168786558688319 := by
  unfold tailWord_198557
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241968741669374680929925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4827979161112916453953283 7241968741669374680929925)
  ·
    refine ⟨1357869139063007752674361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7241968741669374680929925 1357869139063007752674361)
    ·
      refine ⟨1018401854297255814505771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1357869139063007752674361 1018401854297255814505771)
      ·
        refine ⟨1527602781445883721758657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018401854297255814505771 1527602781445883721758657)
        ·
          refine ⟨1145702086084412791318993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1527602781445883721758657 1145702086084412791318993)
          ·
            refine ⟨859276564563309593489245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145702086084412791318993 859276564563309593489245)
            ·
              refine ⟨322228711711241097558467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 859276564563309593489245 322228711711241097558467)
              ·
                refine ⟨483343067566861646337701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322228711711241097558467 483343067566861646337701)
                ·
                  refine ⟨90626825168786558688319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483343067566861646337701 90626825168786558688319)
                  ·
                    rfl

theorem cell20_198557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_198557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198557 prefixEnd_198557 := by exact prefixLift 198557
  have htrace : WordTrace (prefixWord ++ tailWord_198557) baseStart_198557 baseEnd_198557 := by
    simpa [prefixWord, tailWord_198557, baseEnd_198557] using wordTrace_append hprefix tailTrace_198557
  have hstable : (prefixWord ++ tailWord_198557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198557).length < 2 ^ (prefixWord ++ tailWord_198557).sum := by decide
  have hdescent : baseEnd_198557 < baseStart_198557 := by decide
  rcases family_descends (prefixWord ++ tailWord_198557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198564 : List Nat := [2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_198564 : Nat := 118140960795 + 198564 * 2 ^ 59
def prefixEnd_198564 : Nat := 4983230072969 + 3 ^ 40 * 198564 * 2
def baseEnd_198564 : Nat := 30210006719841881818319

theorem tailTrace_198564 : CollatzResearch.WordTrace tailWord_198564 prefixEnd_198564 30210006719841881818319 := by
  unfold tailWord_198564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621112026322007438217373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4828149368429343250956497 3621112026322007438217373)
  ·
    refine ⟨1357917009870752789331515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3621112026322007438217373 1357917009870752789331515)
    ·
      refine ⟨2036875514806129183997273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357917009870752789331515 2036875514806129183997273)
      ·
        refine ⟨1527656636104596887997955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036875514806129183997273 1527656636104596887997955)
        ·
          refine ⟨2291484954156895331996933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527656636104596887997955 2291484954156895331996933)
          ·
            refine ⟨429653428904417874749425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2291484954156895331996933 429653428904417874749425)
            ·
              refine ⟨322240071678313406062069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429653428904417874749425 322240071678313406062069)
              ·
                refine ⟨30210006719841881818319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322240071678313406062069 30210006719841881818319)
                ·
                  rfl

theorem cell20_198564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_198564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198564 prefixEnd_198564 := by exact prefixLift 198564
  have htrace : WordTrace (prefixWord ++ tailWord_198564) baseStart_198564 baseEnd_198564 := by
    simpa [prefixWord, tailWord_198564, baseEnd_198564] using wordTrace_append hprefix tailTrace_198564
  have hstable : (prefixWord ++ tailWord_198564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198564).length < 2 ^ (prefixWord ++ tailWord_198564).sum := by decide
  have hdescent : baseEnd_198564 < baseStart_198564 := by decide
  rcases family_descends (prefixWord ++ tailWord_198564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198567 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 3]
def baseStart_198567 : Nat := 118140960795 + 198567 * 2 ^ 59
def prefixEnd_198567 : Nat := 4983230072969 + 3 ^ 40 * 198567 * 2
def baseEnd_198567 : Nat := 90631389441270968354945

theorem tailTrace_198567 : CollatzResearch.WordTrace tailWord_198567 prefixEnd_198567 90631389441270968354945 := by
  unfold tailWord_198567
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242333471633146388793955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4828222314422097592529303 7242333471633146388793955)
  ·
    refine ⟨10863500207449719583190933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7242333471633146388793955 10863500207449719583190933)
    ·
      refine ⟨509226572224205605462075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10863500207449719583190933 509226572224205605462075)
      ·
        refine ⟨763839858336308408193113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509226572224205605462075 763839858336308408193113)
        ·
          refine ⟨572879893752231306144835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763839858336308408193113 572879893752231306144835)
          ·
            refine ⟨859319840628346959217253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572879893752231306144835 859319840628346959217253)
            ·
              refine ⟨161122470117815054853235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 859319840628346959217253 161122470117815054853235)
              ·
                refine ⟨241683705176722582279853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161122470117815054853235 241683705176722582279853)
                ·
                  refine ⟨90631389441270968354945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241683705176722582279853 90631389441270968354945)
                  ·
                    rfl

theorem cell20_198567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_198567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198567 prefixEnd_198567 := by exact prefixLift 198567
  have htrace : WordTrace (prefixWord ++ tailWord_198567) baseStart_198567 baseEnd_198567 := by
    simpa [prefixWord, tailWord_198567, baseEnd_198567] using wordTrace_append hprefix tailTrace_198567
  have hstable : (prefixWord ++ tailWord_198567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198567).length < 2 ^ (prefixWord ++ tailWord_198567).sum := by decide
  have hdescent : baseEnd_198567 < baseStart_198567 := by decide
  rcases family_descends (prefixWord ++ tailWord_198567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198578 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_198578 : Nat := 118140960795 + 198578 * 2 ^ 59
def prefixEnd_198578 : Nat := 4983230072969 + 3 ^ 40 * 198578 * 2
def baseEnd_198578 : Nat := 90636410141003818988233

theorem tailTrace_198578 : CollatzResearch.WordTrace tailWord_198578 prefixEnd_198578 90636410141003818988233 := by
  unfold tailWord_198578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810683668648323816861097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4828489783062196844962925 1810683668648323816861097)
  ·
    refine ⟨1358012751486242862645823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1810683668648323816861097 1358012751486242862645823)
    ·
      refine ⟨2037019127229364293968735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358012751486242862645823 2037019127229364293968735)
      ·
        refine ⟨3055528690844046440953103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037019127229364293968735 3055528690844046440953103)
        ·
          refine ⟨4583293036266069661429655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055528690844046440953103 4583293036266069661429655)
          ·
            refine ⟨6874939554399104492144483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583293036266069661429655 6874939554399104492144483)
            ·
              refine ⟨10312409331598656738216725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874939554399104492144483 10312409331598656738216725)
              ·
                refine ⟨483394187418687034603909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10312409331598656738216725 483394187418687034603909)
                ·
                  refine ⟨90636410141003818988233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483394187418687034603909 90636410141003818988233)
                  ·
                    rfl

theorem cell20_198578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_198578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198578 prefixEnd_198578 := by exact prefixLift 198578
  have htrace : WordTrace (prefixWord ++ tailWord_198578) baseStart_198578 baseEnd_198578 := by
    simpa [prefixWord, tailWord_198578, baseEnd_198578] using wordTrace_append hprefix tailTrace_198578
  have hstable : (prefixWord ++ tailWord_198578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198578).length < 2 ^ (prefixWord ++ tailWord_198578).sum := by decide
  have hdescent : baseEnd_198578 < baseStart_198578 := by decide
  rcases family_descends (prefixWord ++ tailWord_198578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198585 : List Nat := [1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_198585 : Nat := 118140960795 + 198585 * 2 ^ 59
def prefixEnd_198585 : Nat := 4983230072969 + 3 ^ 40 * 198585 * 2
def baseEnd_198585 : Nat := 30213201710580968584957

theorem tailTrace_198585 : CollatzResearch.WordTrace tailWord_198585 prefixEnd_198585 30213201710580968584957 := by
  unfold tailWord_198585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242989985567935462949209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4828659990378623641966139 7242989985567935462949209)
  ·
    refine ⟨5432242489175951597211907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7242989985567935462949209 5432242489175951597211907)
    ·
      refine ⟨8148363733763927395817861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5432242489175951597211907 8148363733763927395817861)
      ·
        refine ⟨1527818200080736386715849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8148363733763927395817861 1527818200080736386715849)
        ·
          refine ⟨1145863650060552290036887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1527818200080736386715849 1145863650060552290036887)
          ·
            refine ⟨1718795475090828435055331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145863650060552290036887 1718795475090828435055331)
            ·
              refine ⟨2578193212636242652582997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718795475090828435055331 2578193212636242652582997)
              ·
                refine ⟨30213201710580968584957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2578193212636242652582997 30213201710580968584957)
                ·
                  rfl

theorem cell20_198585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_198585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198585 prefixEnd_198585 := by exact prefixLift 198585
  have htrace : WordTrace (prefixWord ++ tailWord_198585) baseStart_198585 baseEnd_198585 := by
    simpa [prefixWord, tailWord_198585, baseEnd_198585] using wordTrace_append hprefix tailTrace_198585
  have hstable : (prefixWord ++ tailWord_198585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198585).length < 2 ^ (prefixWord ++ tailWord_198585).sum := by decide
  have hdescent : baseEnd_198585 < baseStart_198585 := by decide
  rcases family_descends (prefixWord ++ tailWord_198585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198612 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 2]
def baseStart_198612 : Nat := 118140960795 + 198612 * 2 ^ 59
def prefixEnd_198612 : Nat := 4983230072969 + 3 ^ 40 * 198612 * 2
def baseEnd_198612 : Nat := 90651928667450811854761

theorem tailTrace_198612 : CollatzResearch.WordTrace tailWord_198612 prefixEnd_198612 90651928667450811854761 := by
  unfold tailWord_198612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621987378235059537091045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4829316504313412716121393 3621987378235059537091045)
  ·
    refine ⟨679122633419073663204571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3621987378235059537091045 679122633419073663204571)
    ·
      refine ⟨1018683950128610494806857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679122633419073663204571 1018683950128610494806857)
      ·
        refine ⟨764012962596457871105143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1018683950128610494806857 764012962596457871105143)
        ·
          refine ⟨1146019443894686806657715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764012962596457871105143 1146019443894686806657715)
          ·
            refine ⟨1719029165842030209986573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146019443894686806657715 1719029165842030209986573)
            ·
              refine ⟨644635937190761328744965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1719029165842030209986573 644635937190761328744965)
              ·
                refine ⟨120869238223267749139681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644635937190761328744965 120869238223267749139681)
                ·
                  refine ⟨90651928667450811854761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120869238223267749139681 90651928667450811854761)
                  ·
                    rfl

theorem cell20_198612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_198612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198612 prefixEnd_198612 := by exact prefixLift 198612
  have htrace : WordTrace (prefixWord ++ tailWord_198612) baseStart_198612 baseEnd_198612 := by
    simpa [prefixWord, tailWord_198612, baseEnd_198612] using wordTrace_append hprefix tailTrace_198612
  have hstable : (prefixWord ++ tailWord_198612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198612).length < 2 ^ (prefixWord ++ tailWord_198612).sum := by decide
  have hdescent : baseEnd_198612 < baseStart_198612 := by decide
  rcases family_descends (prefixWord ++ tailWord_198612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198616 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_198616 : Nat := 118140960795 + 198616 * 2 ^ 59
def prefixEnd_198616 : Nat := 4983230072969 + 3 ^ 40 * 198616 * 2
def baseEnd_198616 : Nat := 90653754376444575721411

theorem tailTrace_198616 : CollatzResearch.WordTrace tailWord_198616 prefixEnd_198616 90653754376444575721411 := by
  unfold tailWord_198616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622060324227813878663851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4829413765637085171551801 3622060324227813878663851)
  ·
    refine ⟨5433090486341720817995777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3622060324227813878663851 5433090486341720817995777)
    ·
      refine ⟨4074817864756290613496833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5433090486341720817995777 4074817864756290613496833)
      ·
        refine ⟨3056113398567217960122625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4074817864756290613496833 3056113398567217960122625)
        ·
          refine ⟨2292085048925413470091969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056113398567217960122625 2292085048925413470091969)
          ·
            refine ⟨1719063786694060102568977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292085048925413470091969 1719063786694060102568977)
            ·
              refine ⟨1289297840020545076926733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719063786694060102568977 1289297840020545076926733)
              ·
                refine ⟨483486690007704403847525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289297840020545076926733 483486690007704403847525)
                ·
                  refine ⟨90653754376444575721411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483486690007704403847525 90653754376444575721411)
                  ·
                    rfl

theorem cell20_198616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_198616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198616 prefixEnd_198616 := by exact prefixLift 198616
  have htrace : WordTrace (prefixWord ++ tailWord_198616) baseStart_198616 baseEnd_198616 := by
    simpa [prefixWord, tailWord_198616, baseEnd_198616] using wordTrace_append hprefix tailTrace_198616
  have hstable : (prefixWord ++ tailWord_198616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198616).length < 2 ^ (prefixWord ++ tailWord_198616).sum := by decide
  have hdescent : baseEnd_198616 < baseStart_198616 := by decide
  rcases family_descends (prefixWord ++ tailWord_198616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198660 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_198660 : Nat := 118140960795 + 198660 * 2 ^ 59
def prefixEnd_198660 : Nat := 4983230072969 + 3 ^ 40 * 198660 * 2
def baseEnd_198660 : Nat := 90673837175375978254565

theorem tailTrace_198660 : CollatzResearch.WordTrace tailWord_198660 prefixEnd_198660 90673837175375978254565 := by
  unfold tailWord_198660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622862730148111635964717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4830483640197482181286289 3622862730148111635964717)
  ·
    refine ⟨1358573523805541863486769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3622862730148111635964717 1358573523805541863486769)
    ·
      refine ⟨1018930142854156397615077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358573523805541863486769 1018930142854156397615077)
      ·
        refine ⟨191049401785154324552827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1018930142854156397615077 191049401785154324552827)
        ·
          refine ⟨286574102677731486829241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191049401785154324552827 286574102677731486829241)
          ·
            refine ⟨214930577008298615121931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286574102677731486829241 214930577008298615121931)
            ·
              refine ⟨322395865512447922682897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214930577008298615121931 322395865512447922682897)
              ·
                refine ⟨241796899134335942012173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322395865512447922682897 241796899134335942012173)
                ·
                  refine ⟨90673837175375978254565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241796899134335942012173 90673837175375978254565)
                  ·
                    rfl

theorem cell20_198660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_198660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198660 prefixEnd_198660 := by exact prefixLift 198660
  have htrace : WordTrace (prefixWord ++ tailWord_198660) baseStart_198660 baseEnd_198660 := by
    simpa [prefixWord, tailWord_198660, baseEnd_198660] using wordTrace_append hprefix tailTrace_198660
  have hstable : (prefixWord ++ tailWord_198660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198660).length < 2 ^ (prefixWord ++ tailWord_198660).sum := by decide
  have hdescent : baseEnd_198660 < baseStart_198660 := by decide
  rcases family_descends (prefixWord ++ tailWord_198660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198661 : List Nat := [1, 3, 1, 1, 2, 5, 7]
def baseStart_198661 : Nat := 118140960795 + 198661 * 2 ^ 59
def prefixEnd_198661 : Nat := 4983230072969 + 3 ^ 40 * 198661 * 2
def baseEnd_198661 : Nat := 10074921511402713246803

theorem tailTrace_198661 : CollatzResearch.WordTrace tailWord_198661 prefixEnd_198661 10074921511402713246803 := by
  unfold tailWord_198661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245761933292600442715837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4830507955528400295143891 7245761933292600442715837)
  ·
    refine ⟨2717160724984725166018439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7245761933292600442715837 2717160724984725166018439)
    ·
      refine ⟨4075741087477087749027659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717160724984725166018439 4075741087477087749027659)
      ·
        refine ⟨6113611631215631623541489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075741087477087749027659 6113611631215631623541489)
        ·
          refine ⟨4585208723411723717656117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6113611631215631623541489 4585208723411723717656117)
          ·
            refine ⟨429863317819849098530261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4585208723411723717656117 429863317819849098530261)
            ·
              refine ⟨10074921511402713246803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 429863317819849098530261 10074921511402713246803)
              ·
                rfl

theorem cell20_198661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_198661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198661 prefixEnd_198661 := by exact prefixLift 198661
  have htrace : WordTrace (prefixWord ++ tailWord_198661) baseStart_198661 baseEnd_198661 := by
    simpa [prefixWord, tailWord_198661, baseEnd_198661] using wordTrace_append hprefix tailTrace_198661
  have hstable : (prefixWord ++ tailWord_198661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198661).length < 2 ^ (prefixWord ++ tailWord_198661).sum := by decide
  have hdescent : baseEnd_198661 < baseStart_198661 := by decide
  rcases family_descends (prefixWord ++ tailWord_198661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198695 : List Nat := [1, 1, 7, 1, 2, 1, 1, 6]
def baseStart_198695 : Nat := 118140960795 + 198695 * 2 ^ 59
def prefixEnd_198695 : Nat := 4983230072969 + 3 ^ 40 * 198695 * 2
def baseEnd_198695 : Nat := 30229937376357137362585

theorem tailTrace_198695 : CollatzResearch.WordTrace tailWord_198695 prefixEnd_198695 30229937376357137362585 := by
  unfold tailWord_198695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247002015169424249453539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4831334676779616166302359 7247002015169424249453539)
  ·
    refine ⟨10870503022754136374180309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7247002015169424249453539 10870503022754136374180309)
    ·
      refine ⟨254777414595800071269851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10870503022754136374180309 254777414595800071269851)
      ·
        refine ⟨382166121893700106904777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254777414595800071269851 382166121893700106904777)
        ·
          refine ⟨286624591420275080178583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382166121893700106904777 286624591420275080178583)
          ·
            refine ⟨429936887130412620267875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286624591420275080178583 429936887130412620267875)
            ·
              refine ⟨644905330695618930401813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429936887130412620267875 644905330695618930401813)
              ·
                refine ⟨30229937376357137362585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 644905330695618930401813 30229937376357137362585)
                ·
                  rfl

theorem cell20_198695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_198695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198695 prefixEnd_198695 := by exact prefixLift 198695
  have htrace : WordTrace (prefixWord ++ tailWord_198695) baseStart_198695 baseEnd_198695 := by
    simpa [prefixWord, tailWord_198695, baseEnd_198695] using wordTrace_append hprefix tailTrace_198695
  have hstable : (prefixWord ++ tailWord_198695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198695).length < 2 ^ (prefixWord ++ tailWord_198695).sum := by decide
  have hdescent : baseEnd_198695 < baseStart_198695 := by decide
  rcases family_descends (prefixWord ++ tailWord_198695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198781 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 2]
def baseStart_198781 : Nat := 118140960795 + 198781 * 2 ^ 59
def prefixEnd_198781 : Nat := 4983230072969 + 3 ^ 40 * 198781 * 2
def baseEnd_198781 : Nat := 90729064872437335220737

theorem tailTrace_198781 : CollatzResearch.WordTrace tailWord_198781 prefixEnd_198781 90729064872437335220737 := by
  unfold tailWord_198781
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250138692857860937084197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4833425795238573958056131 7250138692857860937084197)
  ·
    refine ⟨1359401004910848925703287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7250138692857860937084197 1359401004910848925703287)
    ·
      refine ⟨2039101507366273388554931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359401004910848925703287 2039101507366273388554931)
      ·
        refine ⟨3058652261049410082832397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039101507366273388554931 3058652261049410082832397)
        ·
          refine ⟨1146994597893528781062149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3058652261049410082832397 1146994597893528781062149)
          ·
            refine ⟨215061487105036646449153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1146994597893528781062149 215061487105036646449153)
            ·
              refine ⟨161296115328777484836865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215061487105036646449153 161296115328777484836865)
              ·
                refine ⟨120972086496583113627649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161296115328777484836865 120972086496583113627649)
                ·
                  refine ⟨90729064872437335220737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120972086496583113627649 90729064872437335220737)
                  ·
                    rfl

theorem cell20_198781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_198781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198781 prefixEnd_198781 := by exact prefixLift 198781
  have htrace : WordTrace (prefixWord ++ tailWord_198781) baseStart_198781 baseEnd_198781 := by
    simpa [prefixWord, tailWord_198781, baseEnd_198781] using wordTrace_append hprefix tailTrace_198781
  have hstable : (prefixWord ++ tailWord_198781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198781).length < 2 ^ (prefixWord ++ tailWord_198781).sum := by decide
  have hdescent : baseEnd_198781 < baseStart_198781 := by decide
  rcases family_descends (prefixWord ++ tailWord_198781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198792 : List Nat := [2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_198792 : Nat := 118140960795 + 198792 * 2 ^ 59
def prefixEnd_198792 : Nat := 4983230072969 + 3 ^ 40 * 198792 * 2
def baseEnd_198792 : Nat := 30244695190723395284675

theorem tailTrace_198792 : CollatzResearch.WordTrace tailWord_198792 prefixEnd_198792 30244695190723395284675 := by
  unfold tailWord_198792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625269947909004907867315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4833693263878673210489753 3625269947909004907867315)
  ·
    refine ⟨5437904921863507361800973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3625269947909004907867315 5437904921863507361800973)
    ·
      refine ⟨2039214345698815260675365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5437904921863507361800973 2039214345698815260675365)
      ·
        refine ⟨382352689818527861376631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2039214345698815260675365 382352689818527861376631)
        ·
          refine ⟨573529034727791792064947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382352689818527861376631 573529034727791792064947)
          ·
            refine ⟨860293552091687688097421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573529034727791792064947 860293552091687688097421)
            ·
              refine ⟨322610082034382883036533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860293552091687688097421 322610082034382883036533)
              ·
                refine ⟨30244695190723395284675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322610082034382883036533 30244695190723395284675)
                ·
                  rfl

theorem cell20_198792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_198792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198792 prefixEnd_198792 := by exact prefixLift 198792
  have htrace : WordTrace (prefixWord ++ tailWord_198792) baseStart_198792 baseEnd_198792 := by
    simpa [prefixWord, tailWord_198792, baseEnd_198792] using wordTrace_append hprefix tailTrace_198792
  have hstable : (prefixWord ++ tailWord_198792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198792).length < 2 ^ (prefixWord ++ tailWord_198792).sum := by decide
  have hdescent : baseEnd_198792 < baseStart_198792 := by decide
  rcases family_descends (prefixWord ++ tailWord_198792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198833 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 3]
def baseStart_198833 : Nat := 118140960795 + 198833 * 2 ^ 59
def prefixEnd_198833 : Nat := 4983230072969 + 3 ^ 40 * 198833 * 2
def baseEnd_198833 : Nat := 90752799089356265487191

theorem tailTrace_198833 : CollatzResearch.WordTrace tailWord_198833 prefixEnd_198833 90752799089356265487191 := by
  unfold tailWord_198833
  simp only [CollatzResearch.WordTrace]
  refine ⟨7252035288669473817977153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4834690192446315878651435 7252035288669473817977153)
  ·
    refine ⟨5439026466502105363482865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7252035288669473817977153 5439026466502105363482865)
    ·
      refine ⟨4079269849876579022612149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5439026466502105363482865 4079269849876579022612149)
      ·
        refine ⟨382431548425929283369889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4079269849876579022612149 382431548425929283369889)
        ·
          refine ⟨286823661319446962527417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382431548425929283369889 286823661319446962527417)
          ·
            refine ⟨215117745989585221895563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286823661319446962527417 215117745989585221895563)
            ·
              refine ⟨322676618984377832843345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215117745989585221895563 322676618984377832843345)
              ·
                refine ⟨242007464238283374632509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322676618984377832843345 242007464238283374632509)
                ·
                  refine ⟨90752799089356265487191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242007464238283374632509 90752799089356265487191)
                  ·
                    rfl

theorem cell20_198833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_198833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198833 prefixEnd_198833 := by exact prefixLift 198833
  have htrace : WordTrace (prefixWord ++ tailWord_198833) baseStart_198833 baseEnd_198833 := by
    simpa [prefixWord, tailWord_198833, baseEnd_198833] using wordTrace_append hprefix tailTrace_198833
  have hstable : (prefixWord ++ tailWord_198833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198833).length < 2 ^ (prefixWord ++ tailWord_198833).sum := by decide
  have hdescent : baseEnd_198833 < baseStart_198833 := by decide
  rcases family_descends (prefixWord ++ tailWord_198833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198836 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 4]
def baseStart_198836 : Nat := 118140960795 + 198836 * 2 ^ 59
def prefixEnd_198836 : Nat := 4983230072969 + 3 ^ 40 * 198836 * 2
def baseEnd_198836 : Nat := 90754168371101588387179

theorem tailTrace_198836 : CollatzResearch.WordTrace tailWord_198836 prefixEnd_198836 90754168371101588387179 := by
  unfold tailWord_198836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626072353829302665168181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4834763138439070220224241 3626072353829302665168181)
  ·
    refine ⟨339944283171497124859517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3626072353829302665168181 339944283171497124859517)
    ·
      refine ⟨127479106189311421822319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339944283171497124859517 127479106189311421822319)
      ·
        refine ⟨191218659283967132733479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127479106189311421822319 191218659283967132733479)
        ·
          refine ⟨286827988925950699100219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191218659283967132733479 286827988925950699100219)
          ·
            refine ⟨430241983388926048650329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286827988925950699100219 430241983388926048650329)
            ·
              refine ⟨322681487541694536487747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430241983388926048650329 322681487541694536487747)
              ·
                refine ⟨484022231312541804731621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322681487541694536487747 484022231312541804731621)
                ·
                  refine ⟨90754168371101588387179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484022231312541804731621 90754168371101588387179)
                  ·
                    rfl

theorem cell20_198836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_198836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198836 prefixEnd_198836 := by exact prefixLift 198836
  have htrace : WordTrace (prefixWord ++ tailWord_198836) baseStart_198836 baseEnd_198836 := by
    simpa [prefixWord, tailWord_198836, baseEnd_198836] using wordTrace_append hprefix tailTrace_198836
  have hstable : (prefixWord ++ tailWord_198836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198836).length < 2 ^ (prefixWord ++ tailWord_198836).sum := by decide
  have hdescent : baseEnd_198836 < baseStart_198836 := by decide
  rcases family_descends (prefixWord ++ tailWord_198836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198913 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_198913 : Nat := 118140960795 + 198913 * 2 ^ 59
def prefixEnd_198913 : Nat := 4983230072969 + 3 ^ 40 * 198913 * 2
def baseEnd_198913 : Nat := 90789313269231542820197

theorem tailTrace_198913 : CollatzResearch.WordTrace tailWord_198913 prefixEnd_198913 90789313269231542820197 := by
  unfold tailWord_198913
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254953128379647480889393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4836635418919764987259595 7254953128379647480889393)
  ·
    refine ⟨5441214846284735610667045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7254953128379647480889393 5441214846284735610667045)
    ·
      refine ⟨1020227783678387927000071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5441214846284735610667045 1020227783678387927000071)
      ·
        refine ⟨1530341675517581890500107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020227783678387927000071 1530341675517581890500107)
        ·
          refine ⟨2295512513276372835750161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530341675517581890500107 2295512513276372835750161)
          ·
            refine ⟨1721634384957279626812621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295512513276372835750161 1721634384957279626812621)
            ·
              refine ⟨645612894358979860054733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1721634384957279626812621 645612894358979860054733)
              ·
                refine ⟨242104835384617447520525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645612894358979860054733 242104835384617447520525)
                ·
                  refine ⟨90789313269231542820197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242104835384617447520525 90789313269231542820197)
                  ·
                    rfl

theorem cell20_198913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_198913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198913 prefixEnd_198913 := by exact prefixLift 198913
  have htrace : WordTrace (prefixWord ++ tailWord_198913) baseStart_198913 baseEnd_198913 := by
    simpa [prefixWord, tailWord_198913, baseEnd_198913] using wordTrace_append hprefix tailTrace_198913
  have hstable : (prefixWord ++ tailWord_198913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198913).length < 2 ^ (prefixWord ++ tailWord_198913).sum := by decide
  have hdescent : baseEnd_198913 < baseStart_198913 := by decide
  rcases family_descends (prefixWord ++ tailWord_198913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198961 : List Nat := [1, 2, 2, 3, 5, 1, 1, 5]
def baseStart_198961 : Nat := 118140960795 + 198961 * 2 ^ 59
def prefixEnd_198961 : Nat := 4983230072969 + 3 ^ 40 * 198961 * 2
def baseEnd_198961 : Nat := 30270407259052236406667

theorem tailTrace_198961 : CollatzResearch.WordTrace tailWord_198961 prefixEnd_198961 30270407259052236406667 := by
  unfold tailWord_198961
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256703832205751678636737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4837802554803834452424491 7256703832205751678636737)
  ·
    refine ⟨5442527874154313758977553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7256703832205751678636737 5442527874154313758977553)
    ·
      refine ⟨4081895905615735319233165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5442527874154313758977553 4081895905615735319233165)
      ·
        refine ⟨1530710964605900744712437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4081895905615735319233165 1530710964605900744712437)
        ·
          refine ⟨143504152931803194816791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1530710964605900744712437 143504152931803194816791)
          ·
            refine ⟨215256229397704792225187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143504152931803194816791 215256229397704792225187)
            ·
              refine ⟨322884344096557188337781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215256229397704792225187 322884344096557188337781)
              ·
                refine ⟨30270407259052236406667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322884344096557188337781 30270407259052236406667)
                ·
                  rfl

theorem cell20_198961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].length) (baseStart_198961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198961 prefixEnd_198961 := by exact prefixLift 198961
  have htrace : WordTrace (prefixWord ++ tailWord_198961) baseStart_198961 baseEnd_198961 := by
    simpa [prefixWord, tailWord_198961, baseEnd_198961] using wordTrace_append hprefix tailTrace_198961
  have hstable : (prefixWord ++ tailWord_198961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198961).length < 2 ^ (prefixWord ++ tailWord_198961).sum := by decide
  have hdescent : baseEnd_198961 < baseStart_198961 := by decide
  rcases family_descends (prefixWord ++ tailWord_198961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198979 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_198979 : Nat := 118140960795 + 198979 * 2 ^ 59
def prefixEnd_198979 : Nat := 4983230072969 + 3 ^ 40 * 198979 * 2
def baseEnd_198979 : Nat := 90819437467628646619927

theorem tailTrace_198979 : CollatzResearch.WordTrace tailWord_198979 prefixEnd_198979 90819437467628646619927 := by
  unfold tailWord_198979
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257360346140540752791991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4838240230760360501861327 7257360346140540752791991)
  ·
    refine ⟨10886040519210811129187987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257360346140540752791991 10886040519210811129187987)
    ·
      refine ⟨16329060778816216693781981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10886040519210811129187987 16329060778816216693781981)
      ·
        refine ⟨6123397792056081260168243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16329060778816216693781981 6123397792056081260168243)
        ·
          refine ⟨9185096688084121890252365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123397792056081260168243 9185096688084121890252365)
          ·
            refine ⟨3444411258031545708844637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9185096688084121890252365 3444411258031545708844637)
            ·
              refine ⟨1291654221761829640816739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444411258031545708844637 1291654221761829640816739)
              ·
                refine ⟨1937481332642744461225109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291654221761829640816739 1937481332642744461225109)
                ·
                  refine ⟨90819437467628646619927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1937481332642744461225109 90819437467628646619927)
                  ·
                    rfl

theorem cell20_198979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_198979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_198979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_198979 prefixEnd_198979 := by exact prefixLift 198979
  have htrace : WordTrace (prefixWord ++ tailWord_198979) baseStart_198979 baseEnd_198979 := by
    simpa [prefixWord, tailWord_198979, baseEnd_198979] using wordTrace_append hprefix tailTrace_198979
  have hstable : (prefixWord ++ tailWord_198979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198979).length < 2 ^ (prefixWord ++ tailWord_198979).sum := by decide
  have hdescent : baseEnd_198979 < baseStart_198979 := by decide
  rcases family_descends (prefixWord ++ tailWord_198979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199013 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 2]
def baseStart_199013 : Nat := 118140960795 + 199013 * 2 ^ 59
def prefixEnd_199013 : Nat := 4983230072969 + 3 ^ 40 * 199013 * 2
def baseEnd_199013 : Nat := 90834955994075639486455

theorem tailTrace_199013 : CollatzResearch.WordTrace tailWord_199013 prefixEnd_199013 90834955994075639486455 := by
  unfold tailWord_199013
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258600428017364559529693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4839066952011576373019795 7258600428017364559529693)
  ·
    refine ⟨2721975160506511709823635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7258600428017364559529693 2721975160506511709823635)
    ·
      refine ⟨4082962740759767564735453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721975160506511709823635 4082962740759767564735453)
      ·
        refine ⟨1531111027784912836775795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4082962740759767564735453 1531111027784912836775795)
        ·
          refine ⟨2296666541677369255163693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531111027784912836775795 2296666541677369255163693)
          ·
            refine ⟨861249953129013470686385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2296666541677369255163693 861249953129013470686385)
            ·
              refine ⟨645937464846760103014789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861249953129013470686385 645937464846760103014789)
              ·
                refine ⟨121113274658767519315273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645937464846760103014789 121113274658767519315273)
                ·
                  refine ⟨90834955994075639486455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121113274658767519315273 90834955994075639486455)
                  ·
                    rfl

theorem cell20_199013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_199013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199013 prefixEnd_199013 := by exact prefixLift 199013
  have htrace : WordTrace (prefixWord ++ tailWord_199013) baseStart_199013 baseEnd_199013 := by
    simpa [prefixWord, tailWord_199013, baseEnd_199013] using wordTrace_append hprefix tailTrace_199013
  have hstable : (prefixWord ++ tailWord_199013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199013).length < 2 ^ (prefixWord ++ tailWord_199013).sum := by decide
  have hdescent : baseEnd_199013 < baseStart_199013 := by decide
  rcases family_descends (prefixWord ++ tailWord_199013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199048 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_199048 : Nat := 118140960795 + 199048 * 2 ^ 59
def prefixEnd_199048 : Nat := 4983230072969 + 3 ^ 40 * 199048 * 2
def baseEnd_199048 : Nat := 90850930947771073319645

theorem tailTrace_199048 : CollatzResearch.WordTrace tailWord_199048 prefixEnd_199048 90850930947771073319645 := by
  unfold tailWord_199048
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629938491445282768526899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4839917988593710358035865 3629938491445282768526899)
  ·
    refine ⟨5444907737167924152790349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629938491445282768526899 5444907737167924152790349)
    ·
      refine ⟨2041840401437971557296381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5444907737167924152790349 2041840401437971557296381)
      ·
        refine ⟨765690150539239333986143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2041840401437971557296381 765690150539239333986143)
        ·
          refine ⟨1148535225808859000979215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765690150539239333986143 1148535225808859000979215)
          ·
            refine ⟨1722802838713288501468823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148535225808859000979215 1722802838713288501468823)
            ·
              refine ⟨2584204258069932752203235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722802838713288501468823 2584204258069932752203235)
              ·
                refine ⟨3876306387104899128304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584204258069932752203235 3876306387104899128304853)
                ·
                  refine ⟨90850930947771073319645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3876306387104899128304853 90850930947771073319645)
                  ·
                    rfl

theorem cell20_199048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_199048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199048 prefixEnd_199048 := by exact prefixLift 199048
  have htrace : WordTrace (prefixWord ++ tailWord_199048) baseStart_199048 baseEnd_199048 := by
    simpa [prefixWord, tailWord_199048, baseEnd_199048] using wordTrace_append hprefix tailTrace_199048
  have hstable : (prefixWord ++ tailWord_199048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199048).length < 2 ^ (prefixWord ++ tailWord_199048).sum := by decide
  have hdescent : baseEnd_199048 < baseStart_199048 := by decide
  rcases family_descends (prefixWord ++ tailWord_199048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199051 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 2]
def baseStart_199051 : Nat := 118140960795 + 199051 * 2 ^ 59
def prefixEnd_199051 : Nat := 4983230072969 + 3 ^ 40 * 199051 * 2
def baseEnd_199051 : Nat := 90852300229516396219633

theorem tailTrace_199051 : CollatzResearch.WordTrace tailWord_199051 prefixEnd_199051 90852300229516396219633 := by
  unfold tailWord_199051
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259986401879697049413007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4839990934586464699608671 7259986401879697049413007)
  ·
    refine ⟨10889979602819545574119511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259986401879697049413007 10889979602819545574119511)
    ·
      refine ⟨16334969404229318361179267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10889979602819545574119511 16334969404229318361179267)
      ·
        refine ⟨24502454106343977541768901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16334969404229318361179267 24502454106343977541768901)
        ·
          refine ⟨4594210144939495789081669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24502454106343977541768901 4594210144939495789081669)
          ·
            refine ⟨861414402176155460452813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4594210144939495789081669 861414402176155460452813)
            ·
              refine ⟨323030400816058297669805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 861414402176155460452813 323030400816058297669805)
              ·
                refine ⟨121136400306021861626177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323030400816058297669805 121136400306021861626177)
                ·
                  refine ⟨90852300229516396219633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121136400306021861626177 90852300229516396219633)
                  ·
                    rfl

theorem cell20_199051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 2].length) (baseStart_199051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199051 prefixEnd_199051 := by exact prefixLift 199051
  have htrace : WordTrace (prefixWord ++ tailWord_199051) baseStart_199051 baseEnd_199051 := by
    simpa [prefixWord, tailWord_199051, baseEnd_199051] using wordTrace_append hprefix tailTrace_199051
  have hstable : (prefixWord ++ tailWord_199051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199051).length < 2 ^ (prefixWord ++ tailWord_199051).sum := by decide
  have hdescent : baseEnd_199051 < baseStart_199051 := by decide
  rcases family_descends (prefixWord ++ tailWord_199051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199072 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_199072 : Nat := 118140960795 + 199072 * 2 ^ 59
def prefixEnd_199072 : Nat := 4983230072969 + 3 ^ 40 * 199072 * 2
def baseEnd_199072 : Nat := 90861885201733656519547

theorem tailTrace_199072 : CollatzResearch.WordTrace tailWord_199072 prefixEnd_199072 90861885201733656519547 := by
  unfold tailWord_199072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630376167401808817963735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4840501556535745090618313 3630376167401808817963735)
  ·
    refine ⟨5445564251102713226945603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3630376167401808817963735 5445564251102713226945603)
    ·
      refine ⟨8168346376654069840418405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445564251102713226945603 8168346376654069840418405)
      ·
        refine ⟨1531564945622638095078451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8168346376654069840418405 1531564945622638095078451)
        ·
          refine ⟨2297347418433957142617677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531564945622638095078451 2297347418433957142617677)
          ·
            refine ⟨861505281912733928481629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2297347418433957142617677 861505281912733928481629)
            ·
              refine ⟨323064480717275223180611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 861505281912733928481629 323064480717275223180611)
              ·
                refine ⟨484596721075912834770917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323064480717275223180611 484596721075912834770917)
                ·
                  refine ⟨90861885201733656519547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484596721075912834770917 90861885201733656519547)
                  ·
                    rfl

theorem cell20_199072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_199072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199072 prefixEnd_199072 := by exact prefixLift 199072
  have htrace : WordTrace (prefixWord ++ tailWord_199072) baseStart_199072 baseEnd_199072 := by
    simpa [prefixWord, tailWord_199072, baseEnd_199072] using wordTrace_append hprefix tailTrace_199072
  have hstable : (prefixWord ++ tailWord_199072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199072).length < 2 ^ (prefixWord ++ tailWord_199072).sum := by decide
  have hdescent : baseEnd_199072 < baseStart_199072 := by decide
  rcases family_descends (prefixWord ++ tailWord_199072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199079 : List Nat := [1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_199079 : Nat := 118140960795 + 199079 * 2 ^ 59
def prefixEnd_199079 : Nat := 4983230072969 + 3 ^ 40 * 199079 * 2
def baseEnd_199079 : Nat := 30288360064157581095395

theorem tailTrace_199079 : CollatzResearch.WordTrace tailWord_199079 prefixEnd_199079 30288360064157581095395 := by
  unfold tailWord_199079
  simp only [CollatzResearch.WordTrace]
  refine ⟨7261007645778257831432291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4840671763852171887621527 7261007645778257831432291)
  ·
    refine ⟨10891511468667386747148437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7261007645778257831432291 10891511468667386747148437)
    ·
      refine ⟨510539600093783753772583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10891511468667386747148437 510539600093783753772583)
      ·
        refine ⟨765809400140675630658875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510539600093783753772583 765809400140675630658875)
        ·
          refine ⟨1148714100211013445988313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765809400140675630658875 1148714100211013445988313)
          ·
            refine ⟨861535575158260084491235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148714100211013445988313 861535575158260084491235)
            ·
              refine ⟨1292303362737390126736853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861535575158260084491235 1292303362737390126736853)
              ·
                refine ⟨30288360064157581095395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1292303362737390126736853 30288360064157581095395)
                ·
                  rfl

theorem cell20_199079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_199079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199079 prefixEnd_199079 := by exact prefixLift 199079
  have htrace : WordTrace (prefixWord ++ tailWord_199079) baseStart_199079 baseEnd_199079 := by
    simpa [prefixWord, tailWord_199079, baseEnd_199079] using wordTrace_append hprefix tailTrace_199079
  have hstable : (prefixWord ++ tailWord_199079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199079).length < 2 ^ (prefixWord ++ tailWord_199079).sum := by decide
  have hdescent : baseEnd_199079 < baseStart_199079 := by decide
  rcases family_descends (prefixWord ++ tailWord_199079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199155 : List Nat := [1, 1, 1, 2, 2, 2, 7, 4]
def baseStart_199155 : Nat := 118140960795 + 199155 * 2 ^ 59
def prefixEnd_199155 : Nat := 4983230072969 + 3 ^ 40 * 199155 * 2
def baseEnd_199155 : Nat := 30299922887784752250847

theorem tailTrace_199155 : CollatzResearch.WordTrace tailWord_199155 prefixEnd_199155 30299922887784752250847 := by
  unfold tailWord_199155
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263779593502922811198919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4842519729001948540799279 7263779593502922811198919)
  ·
    refine ⟨10895669390254384216798379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7263779593502922811198919 10895669390254384216798379)
    ·
      refine ⟨16343504085381576325197569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10895669390254384216798379 16343504085381576325197569)
      ·
        refine ⟨12257628064036182243898177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16343504085381576325197569 12257628064036182243898177)
        ·
          refine ⟨9193221048027136682923633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12257628064036182243898177 9193221048027136682923633)
          ·
            refine ⟨6894915786020352512192725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9193221048027136682923633 6894915786020352512192725)
            ·
              refine ⟨161599588734852012004517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6894915786020352512192725 161599588734852012004517)
              ·
                refine ⟨30299922887784752250847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161599588734852012004517 30299922887784752250847)
                ·
                  rfl

theorem cell20_199155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_199155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199155 prefixEnd_199155 := by exact prefixLift 199155
  have htrace : WordTrace (prefixWord ++ tailWord_199155) baseStart_199155 baseEnd_199155 := by
    simpa [prefixWord, tailWord_199155, baseEnd_199155] using wordTrace_append hprefix tailTrace_199155
  have hstable : (prefixWord ++ tailWord_199155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199155).length < 2 ^ (prefixWord ++ tailWord_199155).sum := by decide
  have hdescent : baseEnd_199155 < baseStart_199155 := by decide
  rcases family_descends (prefixWord ++ tailWord_199155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199165 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 2]
def baseStart_199165 : Nat := 118140960795 + 199165 * 2 ^ 59
def prefixEnd_199165 : Nat := 4983230072969 + 3 ^ 40 * 199165 * 2
def baseEnd_199165 : Nat := 90904332935838666419167

theorem tailTrace_199165 : CollatzResearch.WordTrace tailWord_199165 prefixEnd_199165 90904332935838666419167 := by
  unfold tailWord_199165
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264144323466694519062949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4842762882311129679375299 7264144323466694519062949)
  ·
    refine ⟨1362027060650005222324303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7264144323466694519062949 1362027060650005222324303)
    ·
      refine ⟨2043040590975007833486455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362027060650005222324303 2043040590975007833486455)
      ·
        refine ⟨3064560886462511750229683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043040590975007833486455 3064560886462511750229683)
        ·
          refine ⟨4596841329693767625344525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064560886462511750229683 4596841329693767625344525)
          ·
            refine ⟨1723815498635162859504197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4596841329693767625344525 1723815498635162859504197)
            ·
              refine ⟨323215405994093036157037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1723815498635162859504197 323215405994093036157037)
              ·
                refine ⟨121205777247784888558889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323215405994093036157037 121205777247784888558889)
                ·
                  refine ⟨90904332935838666419167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121205777247784888558889 90904332935838666419167)
                  ·
                    rfl

theorem cell20_199165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_199165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199165 prefixEnd_199165 := by exact prefixLift 199165
  have htrace : WordTrace (prefixWord ++ tailWord_199165) baseStart_199165 baseEnd_199165 := by
    simpa [prefixWord, tailWord_199165, baseEnd_199165] using wordTrace_append hprefix tailTrace_199165
  have hstable : (prefixWord ++ tailWord_199165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199165).length < 2 ^ (prefixWord ++ tailWord_199165).sum := by decide
  have hdescent : baseEnd_199165 < baseStart_199165 := by decide
  rcases family_descends (prefixWord ++ tailWord_199165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199175 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 3]
def baseStart_199175 : Nat := 118140960795 + 199175 * 2 ^ 59
def prefixEnd_199175 : Nat := 4983230072969 + 3 ^ 40 * 199175 * 2
def baseEnd_199175 : Nat := 90908897208323076085793

theorem tailTrace_199175 : CollatzResearch.WordTrace tailWord_199175 prefixEnd_199175 90908897208323076085793 := by
  unfold tailWord_199175
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264509053430466226926979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4843006035620310817951319 7264509053430466226926979)
  ·
    refine ⟨10896763580145699340390469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264509053430466226926979 10896763580145699340390469)
    ·
      refine ⟨2043143171277318626323213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10896763580145699340390469 2043143171277318626323213)
      ·
        refine ⟨766178689228994484871205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2043143171277318626323213 766178689228994484871205)
        ·
          refine ⟨143658504230436465913351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 766178689228994484871205 143658504230436465913351)
          ·
            refine ⟨215487756345654698870027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143658504230436465913351 215487756345654698870027)
            ·
              refine ⟨323231634518482048305041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215487756345654698870027 323231634518482048305041)
              ·
                refine ⟨242423725888861536228781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323231634518482048305041 242423725888861536228781)
                ·
                  refine ⟨90908897208323076085793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242423725888861536228781 90908897208323076085793)
                  ·
                    rfl

theorem cell20_199175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 3].length) (baseStart_199175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199175 prefixEnd_199175 := by exact prefixLift 199175
  have htrace : WordTrace (prefixWord ++ tailWord_199175) baseStart_199175 baseEnd_199175 := by
    simpa [prefixWord, tailWord_199175, baseEnd_199175] using wordTrace_append hprefix tailTrace_199175
  have hstable : (prefixWord ++ tailWord_199175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199175).length < 2 ^ (prefixWord ++ tailWord_199175).sum := by decide
  have hdescent : baseEnd_199175 < baseStart_199175 := by decide
  rcases family_descends (prefixWord ++ tailWord_199175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199179 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_199179 : Nat := 118140960795 + 199179 * 2 ^ 59
def prefixEnd_199179 : Nat := 4983230072969 + 3 ^ 40 * 199179 * 2
def baseEnd_199179 : Nat := 90910722917316839952443

theorem tailTrace_199179 : CollatzResearch.WordTrace tailWord_199179 prefixEnd_199179 90910722917316839952443 := by
  unfold tailWord_199179
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264654945415974910072591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4843103296943983273381727 7264654945415974910072591)
  ·
    refine ⟨10896982418123962365108887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264654945415974910072591 10896982418123962365108887)
    ·
      refine ⟨16345473627185943547663331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896982418123962365108887 16345473627185943547663331)
      ·
        refine ⟨24518210440778915321494997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16345473627185943547663331 24518210440778915321494997)
        ·
          refine ⟨574645557205755827847539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24518210440778915321494997 574645557205755827847539)
          ·
            refine ⟨861968335808633741771309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574645557205755827847539 861968335808633741771309)
            ·
              refine ⟨323238125928237653164241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 861968335808633741771309 323238125928237653164241)
              ·
                refine ⟨242428594446178239873181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323238125928237653164241 242428594446178239873181)
                ·
                  refine ⟨90910722917316839952443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242428594446178239873181 90910722917316839952443)
                  ·
                    rfl

theorem cell20_199179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_199179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199179 prefixEnd_199179 := by exact prefixLift 199179
  have htrace : WordTrace (prefixWord ++ tailWord_199179) baseStart_199179 baseEnd_199179 := by
    simpa [prefixWord, tailWord_199179, baseEnd_199179] using wordTrace_append hprefix tailTrace_199179
  have hstable : (prefixWord ++ tailWord_199179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199179).length < 2 ^ (prefixWord ++ tailWord_199179).sum := by decide
  have hdescent : baseEnd_199179 < baseStart_199179 := by decide
  rcases family_descends (prefixWord ++ tailWord_199179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199196 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_199196 : Nat := 118140960795 + 199196 * 2 ^ 59
def prefixEnd_199196 : Nat := 4983230072969 + 3 ^ 40 * 199196 * 2
def baseEnd_199196 : Nat := 90918482180540336385707

theorem tailTrace_199196 : CollatzResearch.WordTrace tailWord_199196 prefixEnd_199196 90918482180540336385707 := by
  unfold tailWord_199196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632637493177193406720721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4843516657569591208960961 3632637493177193406720721)
  ·
    refine ⟨2724478119882895055040541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3632637493177193406720721 2724478119882895055040541)
    ·
      refine ⟨1021679294956085645640203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2724478119882895055040541 1021679294956085645640203)
      ·
        refine ⟨1532518942434128468460305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021679294956085645640203 1532518942434128468460305)
        ·
          refine ⟨1149389206825596351345229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532518942434128468460305 1149389206825596351345229)
          ·
            refine ⟨431020952559598631754461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1149389206825596351345229 431020952559598631754461)
            ·
              refine ⟨161632857209849486907923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431020952559598631754461 161632857209849486907923)
              ·
                refine ⟨242449285814774230361885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161632857209849486907923 242449285814774230361885)
                ·
                  refine ⟨90918482180540336385707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242449285814774230361885 90918482180540336385707)
                  ·
                    rfl

theorem cell20_199196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_199196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199196 prefixEnd_199196 := by exact prefixLift 199196
  have htrace : WordTrace (prefixWord ++ tailWord_199196) baseStart_199196 baseEnd_199196 := by
    simpa [prefixWord, tailWord_199196, baseEnd_199196] using wordTrace_append hprefix tailTrace_199196
  have hstable : (prefixWord ++ tailWord_199196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199196).length < 2 ^ (prefixWord ++ tailWord_199196).sum := by decide
  have hdescent : baseEnd_199196 < baseStart_199196 := by decide
  rcases family_descends (prefixWord ++ tailWord_199196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199210 : List Nat := [3, 1, 4, 1, 1, 2, 4, 4]
def baseStart_199210 : Nat := 118140960795 + 199210 * 2 ^ 59
def prefixEnd_199210 : Nat := 4983230072969 + 3 ^ 40 * 199210 * 2
def baseEnd_199210 : Nat := 30308290720672836639661

theorem tailTrace_199210 : CollatzResearch.WordTrace tailWord_199210 prefixEnd_199210 30308290720672836639661 := by
  unfold tailWord_199210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816446402075916801112771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4843857072202444802967389 1816446402075916801112771)
  ·
    refine ⟨2724669603113875201669157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816446402075916801112771 2724669603113875201669157)
    ·
      refine ⟨510875550583851600312967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2724669603113875201669157 510875550583851600312967)
      ·
        refine ⟨766313325875777400469451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510875550583851600312967 766313325875777400469451)
        ·
          refine ⟨1149469988813666100704177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766313325875777400469451 1149469988813666100704177)
          ·
            refine ⟨862102491610249575528133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149469988813666100704177 862102491610249575528133)
            ·
              refine ⟨161644217176921795411525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 862102491610249575528133 161644217176921795411525)
              ·
                refine ⟨30308290720672836639661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161644217176921795411525 30308290720672836639661)
                ·
                  rfl

theorem cell20_199210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_199210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199210 prefixEnd_199210 := by exact prefixLift 199210
  have htrace : WordTrace (prefixWord ++ tailWord_199210) baseStart_199210 baseEnd_199210 := by
    simpa [prefixWord, tailWord_199210, baseEnd_199210] using wordTrace_append hprefix tailTrace_199210
  have hstable : (prefixWord ++ tailWord_199210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199210).length < 2 ^ (prefixWord ++ tailWord_199210).sum := by decide
  have hdescent : baseEnd_199210 < baseStart_199210 := by decide
  rcases family_descends (prefixWord ++ tailWord_199210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199286 : List Nat := [5, 1, 1, 2, 4, 7]
def baseStart_199286 : Nat := 118140960795 + 199286 * 2 ^ 59
def prefixEnd_199286 : Nat := 4983230072969 + 3 ^ 40 * 199286 * 2
def baseEnd_199286 : Nat := 3368872616033334199457

theorem tailTrace_199286 : CollatzResearch.WordTrace tailWord_199286 prefixEnd_199286 3368872616033334199457 := by
  unfold tailWord_199286
  simp only [CollatzResearch.WordTrace]
  refine ⟨454284847251770761513607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4845705037352221456145141 454284847251770761513607)
  ·
    refine ⟨681427270877656142270411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454284847251770761513607 681427270877656142270411)
    ·
      refine ⟨1022140906316484213405617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681427270877656142270411 1022140906316484213405617)
      ·
        refine ⟨766605679737363160054213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022140906316484213405617 766605679737363160054213)
        ·
          refine ⟨143738564950755592510165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 766605679737363160054213 143738564950755592510165)
          ·
            refine ⟨3368872616033334199457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 143738564950755592510165 3368872616033334199457)
            ·
              rfl

theorem cell20_199286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 7].length) (baseStart_199286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199286 prefixEnd_199286 := by exact prefixLift 199286
  have htrace : WordTrace (prefixWord ++ tailWord_199286) baseStart_199286 baseEnd_199286 := by
    simpa [prefixWord, tailWord_199286, baseEnd_199286] using wordTrace_append hprefix tailTrace_199286
  have hstable : (prefixWord ++ tailWord_199286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199286).length < 2 ^ (prefixWord ++ tailWord_199286).sum := by decide
  have hdescent : baseEnd_199286 < baseStart_199286 := by decide
  rcases family_descends (prefixWord ++ tailWord_199286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199296 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 2]
def baseStart_199296 : Nat := 118140960795 + 199296 * 2 ^ 59
def prefixEnd_199296 : Nat := 4983230072969 + 3 ^ 40 * 199296 * 2
def baseEnd_199296 : Nat := 90964124905384433051965

theorem tailTrace_199296 : CollatzResearch.WordTrace tailWord_199296 prefixEnd_199296 90964124905384433051965 := by
  unfold tailWord_199296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634461142996051946040871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4845948190661402594721161 3634461142996051946040871)
  ·
    refine ⟨5451691714494077919061307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3634461142996051946040871 5451691714494077919061307)
    ·
      refine ⟨8177537571741116878591961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5451691714494077919061307 8177537571741116878591961)
      ·
        refine ⟨6133153178805837658943971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8177537571741116878591961 6133153178805837658943971)
        ·
          refine ⟨9199729768208756488415957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133153178805837658943971 9199729768208756488415957)
          ·
            refine ⟨215618666442392730197249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9199729768208756488415957 215618666442392730197249)
            ·
              refine ⟨161713999831794547647937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215618666442392730197249 161713999831794547647937)
              ·
                refine ⟨121285499873845910735953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161713999831794547647937 121285499873845910735953)
                ·
                  refine ⟨90964124905384433051965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121285499873845910735953 90964124905384433051965)
                  ·
                    rfl

theorem cell20_199296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_199296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199296 prefixEnd_199296 := by exact prefixLift 199296
  have htrace : WordTrace (prefixWord ++ tailWord_199296) baseStart_199296 baseEnd_199296 := by
    simpa [prefixWord, tailWord_199296, baseEnd_199296] using wordTrace_append hprefix tailTrace_199296
  have hstable : (prefixWord ++ tailWord_199296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199296).length < 2 ^ (prefixWord ++ tailWord_199296).sum := by decide
  have hdescent : baseEnd_199296 < baseStart_199296 := by decide
  rcases family_descends (prefixWord ++ tailWord_199296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199321 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_199321 : Nat := 118140960795 + 199321 * 2 ^ 59
def prefixEnd_199321 : Nat := 4983230072969 + 3 ^ 40 * 199321 * 2
def baseEnd_199321 : Nat := 90975535586595457218529

theorem tailTrace_199321 : CollatzResearch.WordTrace tailWord_199321 prefixEnd_199321 90975535586595457218529 := by
  unfold tailWord_199321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269834110901533161741817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4846556073934355441161211 7269834110901533161741817)
  ·
    refine ⟨5452375583176149871306363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7269834110901533161741817 5452375583176149871306363)
    ·
      refine ⟨8178563374764224806959545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452375583176149871306363 8178563374764224806959545)
      ·
        refine ⟨6133922531073168605219659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8178563374764224806959545 6133922531073168605219659)
        ·
          refine ⟨9200883796609752907829489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133922531073168605219659 9200883796609752907829489)
          ·
            refine ⟨6900662847457314680872117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9200883796609752907829489 6900662847457314680872117)
            ·
              refine ⟨646937141949123251331761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6900662847457314680872117 646937141949123251331761)
              ·
                refine ⟨485202856461842438498821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646937141949123251331761 485202856461842438498821)
                ·
                  refine ⟨90975535586595457218529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485202856461842438498821 90975535586595457218529)
                  ·
                    rfl

theorem cell20_199321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_199321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199321 prefixEnd_199321 := by exact prefixLift 199321
  have htrace : WordTrace (prefixWord ++ tailWord_199321) baseStart_199321 baseEnd_199321 := by
    simpa [prefixWord, tailWord_199321, baseEnd_199321] using wordTrace_append hprefix tailTrace_199321
  have hstable : (prefixWord ++ tailWord_199321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199321).length < 2 ^ (prefixWord ++ tailWord_199321).sum := by decide
  have hdescent : baseEnd_199321 < baseStart_199321 := by decide
  rcases family_descends (prefixWord ++ tailWord_199321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199324 : List Nat := [2, 2, 3, 2, 2, 2, 3, 4]
def baseStart_199324 : Nat := 118140960795 + 199324 * 2 ^ 59
def prefixEnd_199324 : Nat := 4983230072969 + 3 ^ 40 * 199324 * 2
def baseEnd_199324 : Nat := 30325634956113593372839

theorem tailTrace_199324 : CollatzResearch.WordTrace tailWord_199324 prefixEnd_199324 30325634956113593372839 := by
  unfold tailWord_199324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634971764945332337050513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4846629019927109782734017 3634971764945332337050513)
  ·
    refine ⟨2726228823708999252787885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3634971764945332337050513 2726228823708999252787885)
    ·
      refine ⟨1022335808890874719795457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2726228823708999252787885 1022335808890874719795457)
      ·
        refine ⟨766751856668156039846593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022335808890874719795457 766751856668156039846593)
        ·
          refine ⟨575063892501117029884945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766751856668156039846593 575063892501117029884945)
          ·
            refine ⟨431297919375837772413709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575063892501117029884945 431297919375837772413709)
            ·
              refine ⟨161736719765939164655141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431297919375837772413709 161736719765939164655141)
              ·
                refine ⟨30325634956113593372839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161736719765939164655141 30325634956113593372839)
                ·
                  rfl

theorem cell20_199324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_199324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199324 prefixEnd_199324 := by exact prefixLift 199324
  have htrace : WordTrace (prefixWord ++ tailWord_199324) baseStart_199324 baseEnd_199324 := by
    simpa [prefixWord, tailWord_199324, baseEnd_199324] using wordTrace_append hprefix tailTrace_199324
  have hstable : (prefixWord ++ tailWord_199324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199324).length < 2 ^ (prefixWord ++ tailWord_199324).sum := by decide
  have hdescent : baseEnd_199324 < baseStart_199324 := by decide
  rcases family_descends (prefixWord ++ tailWord_199324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199359 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_199359 : Nat := 118140960795 + 199359 * 2 ^ 59
def prefixEnd_199359 : Nat := 4983230072969 + 3 ^ 40 * 199359 * 2
def baseEnd_199359 : Nat := 90992879822036213951707

theorem tailTrace_199359 : CollatzResearch.WordTrace tailWord_199359 prefixEnd_199359 90992879822036213951707 := by
  unfold tailWord_199359
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271220084763865651625131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4847480056509243767750087 7271220084763865651625131)
  ·
    refine ⟨10906830127145798477437697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7271220084763865651625131 10906830127145798477437697)
    ·
      refine ⟨8180122595359348858078273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10906830127145798477437697 8180122595359348858078273)
      ·
        refine ⟨6135091946519511643558705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8180122595359348858078273 6135091946519511643558705)
        ·
          refine ⟨4601318959889633732669029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6135091946519511643558705 4601318959889633732669029)
          ·
            refine ⟨862747304979306324875443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4601318959889633732669029 862747304979306324875443)
            ·
              refine ⟨1294120957468959487313165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862747304979306324875443 1294120957468959487313165)
              ·
                refine ⟨485295359050859807742437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1294120957468959487313165 485295359050859807742437)
                ·
                  refine ⟨90992879822036213951707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485295359050859807742437 90992879822036213951707)
                  ·
                    rfl

theorem cell20_199359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_199359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199359 prefixEnd_199359 := by exact prefixLift 199359
  have htrace : WordTrace (prefixWord ++ tailWord_199359) baseStart_199359 baseEnd_199359 := by
    simpa [prefixWord, tailWord_199359, baseEnd_199359] using wordTrace_append hprefix tailTrace_199359
  have hstable : (prefixWord ++ tailWord_199359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199359).length < 2 ^ (prefixWord ++ tailWord_199359).sum := by decide
  have hdescent : baseEnd_199359 < baseStart_199359 := by decide
  rcases family_descends (prefixWord ++ tailWord_199359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199383 : List Nat := [1, 1, 3, 2, 1, 4, 4, 4]
def baseStart_199383 : Nat := 118140960795 + 199383 * 2 ^ 59
def prefixEnd_199383 : Nat := 4983230072969 + 3 ^ 40 * 199383 * 2
def baseEnd_199383 : Nat := 30334611358666265717203

theorem tailTrace_199383 : CollatzResearch.WordTrace tailWord_199383 prefixEnd_199383 30334611358666265717203 := by
  unfold tailWord_199383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272095436676917750498803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4848063624451278500332535 7272095436676917750498803)
  ·
    refine ⟨10908143155015376625748205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7272095436676917750498803 10908143155015376625748205)
    ·
      refine ⟨4090553683130766234655577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10908143155015376625748205 4090553683130766234655577)
      ·
        refine ⟨3067915262348074675991683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4090553683130766234655577 3067915262348074675991683)
        ·
          refine ⟨4601872893522112013987525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067915262348074675991683 4601872893522112013987525)
          ·
            refine ⟨862851167535396002622661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4601872893522112013987525 862851167535396002622661)
            ·
              refine ⟨161784593912886750491749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 862851167535396002622661 161784593912886750491749)
              ·
                refine ⟨30334611358666265717203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161784593912886750491749 30334611358666265717203)
                ·
                  rfl

theorem cell20_199383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_199383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199383 prefixEnd_199383 := by exact prefixLift 199383
  have htrace : WordTrace (prefixWord ++ tailWord_199383) baseStart_199383 baseEnd_199383 := by
    simpa [prefixWord, tailWord_199383, baseEnd_199383] using wordTrace_append hprefix tailTrace_199383
  have hstable : (prefixWord ++ tailWord_199383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199383).length < 2 ^ (prefixWord ++ tailWord_199383).sum := by decide
  have hdescent : baseEnd_199383 < baseStart_199383 := by decide
  rcases family_descends (prefixWord ++ tailWord_199383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199393 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 2]
def baseStart_199393 : Nat := 118140960795 + 199393 * 2 ^ 59
def prefixEnd_199393 : Nat := 4983230072969 + 3 ^ 40 * 199393 * 2
def baseEnd_199393 : Nat := 91008398348483206818235

theorem tailTrace_199393 : CollatzResearch.WordTrace tailWord_199393 prefixEnd_199393 91008398348483206818235 := by
  unfold tailWord_199393
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272460166640689458362833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4848306777760459638908555 7272460166640689458362833)
  ·
    refine ⟨5454345124980517093772125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7272460166640689458362833 5454345124980517093772125)
    ·
      refine ⟨2045379421867693910164547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5454345124980517093772125 2045379421867693910164547)
      ·
        refine ⟨3068069132801540865246821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045379421867693910164547 3068069132801540865246821)
        ·
          refine ⟨575262962400288912233779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3068069132801540865246821 575262962400288912233779)
          ·
            refine ⟨862894443600433368350669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575262962400288912233779 862894443600433368350669)
            ·
              refine ⟨323585416350162513131501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 862894443600433368350669 323585416350162513131501)
              ·
                refine ⟨121344531131310942424313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323585416350162513131501 121344531131310942424313)
                ·
                  refine ⟨91008398348483206818235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121344531131310942424313 91008398348483206818235)
                  ·
                    rfl

theorem cell20_199393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_199393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199393 prefixEnd_199393 := by exact prefixLift 199393
  have htrace : WordTrace (prefixWord ++ tailWord_199393) baseStart_199393 baseEnd_199393 := by
    simpa [prefixWord, tailWord_199393, baseEnd_199393] using wordTrace_append hprefix tailTrace_199393
  have hstable : (prefixWord ++ tailWord_199393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199393).length < 2 ^ (prefixWord ++ tailWord_199393).sum := by decide
  have hdescent : baseEnd_199393 < baseStart_199393 := by decide
  rcases family_descends (prefixWord ++ tailWord_199393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199400 : List Nat := [2, 1, 4, 1, 5, 1, 6]
def baseStart_199400 : Nat := 118140960795 + 199400 * 2 ^ 59
def prefixEnd_199400 : Nat := 4983230072969 + 3 ^ 40 * 199400 * 2
def baseEnd_199400 : Nat := 10112399259913588176097

theorem tailTrace_199400 : CollatzResearch.WordTrace tailWord_199400 prefixEnd_199400 10112399259913588176097 := by
  unfold tailWord_199400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636357738807664826933827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4848476985076886435911769 3636357738807664826933827)
  ·
    refine ⟨5454536608211497240400741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636357738807664826933827 5454536608211497240400741)
    ·
      refine ⟨1022725614039655732575139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5454536608211497240400741 1022725614039655732575139)
      ·
        refine ⟨1534088421059483598862709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022725614039655732575139 1534088421059483598862709)
        ·
          refine ⟨143820789474326587393379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1534088421059483598862709 143820789474326587393379)
          ·
            refine ⟨215731184211489881090069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143820789474326587393379 215731184211489881090069)
            ·
              refine ⟨10112399259913588176097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215731184211489881090069 10112399259913588176097)
              ·
                rfl

theorem cell20_199400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 6].length) (baseStart_199400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199400 prefixEnd_199400 := by exact prefixLift 199400
  have htrace : WordTrace (prefixWord ++ tailWord_199400) baseStart_199400 baseEnd_199400 := by
    simpa [prefixWord, tailWord_199400, baseEnd_199400] using wordTrace_append hprefix tailTrace_199400
  have hstable : (prefixWord ++ tailWord_199400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199400).length < 2 ^ (prefixWord ++ tailWord_199400).sum := by decide
  have hdescent : baseEnd_199400 < baseStart_199400 := by decide
  rcases family_descends (prefixWord ++ tailWord_199400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199410 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_199410 : Nat := 118140960795 + 199410 * 2 ^ 59
def prefixEnd_199410 : Nat := 4983230072969 + 3 ^ 40 * 199410 * 2
def baseEnd_199410 : Nat := 91016157611706703251499

theorem tailTrace_199410 : CollatzResearch.WordTrace tailWord_199410 prefixEnd_199410 91016157611706703251499 := by
  unfold tailWord_199410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818270051894775340432921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4848720138386067574487789 1818270051894775340432921)
  ·
    refine ⟨1363702538921081505324691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1818270051894775340432921 1363702538921081505324691)
    ·
      refine ⟨2045553808381622257987037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363702538921081505324691 2045553808381622257987037)
      ·
        refine ⟨767082678143108346745139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2045553808381622257987037 767082678143108346745139)
        ·
          refine ⟨1150624017214662520117709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767082678143108346745139 1150624017214662520117709)
          ·
            refine ⟨431484006455498445044141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1150624017214662520117709 431484006455498445044141)
            ·
              refine ⟨161806502420811916891553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431484006455498445044141 161806502420811916891553)
              ·
                refine ⟨121354876815608937668665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161806502420811916891553 121354876815608937668665)
                ·
                  refine ⟨91016157611706703251499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121354876815608937668665 91016157611706703251499)
                  ·
                    rfl

theorem cell20_199410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_199410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199410 prefixEnd_199410 := by exact prefixLift 199410
  have htrace : WordTrace (prefixWord ++ tailWord_199410) baseStart_199410 baseEnd_199410 := by
    simpa [prefixWord, tailWord_199410, baseEnd_199410] using wordTrace_append hprefix tailTrace_199410
  have hstable : (prefixWord ++ tailWord_199410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199410).length < 2 ^ (prefixWord ++ tailWord_199410).sum := by decide
  have hdescent : baseEnd_199410 < baseStart_199410 := by decide
  rcases family_descends (prefixWord ++ tailWord_199410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199449 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_199449 : Nat := 118140960795 + 199449 * 2 ^ 59
def prefixEnd_199449 : Nat := 4983230072969 + 3 ^ 40 * 199449 * 2
def baseEnd_199449 : Nat := 91033958274395900951339

theorem tailTrace_199449 : CollatzResearch.WordTrace tailWord_199449 prefixEnd_199449 91033958274395900951339 := by
  unfold tailWord_199449
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274502654437811022401401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4849668436291874014934267 7274502654437811022401401)
  ·
    refine ⟨5455876990828358266801051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7274502654437811022401401 5455876990828358266801051)
    ·
      refine ⟨8183815486242537400201577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5455876990828358266801051 8183815486242537400201577)
      ·
        refine ⟨6137861614681903050151183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8183815486242537400201577 6137861614681903050151183)
        ·
          refine ⟨9206792422022854575226775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137861614681903050151183 9206792422022854575226775)
          ·
            refine ⟨13810188633034281862840163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9206792422022854575226775 13810188633034281862840163)
            ·
              refine ⟨20715282949551422794260245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13810188633034281862840163 20715282949551422794260245)
              ·
                refine ⟨971028888260222943480949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20715282949551422794260245 971028888260222943480949)
                ·
                  refine ⟨91033958274395900951339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 971028888260222943480949 91033958274395900951339)
                  ·
                    rfl

theorem cell20_199449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_199449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199449 prefixEnd_199449 := by exact prefixLift 199449
  have htrace : WordTrace (prefixWord ++ tailWord_199449) baseStart_199449 baseEnd_199449 := by
    simpa [prefixWord, tailWord_199449, baseEnd_199449] using wordTrace_append hprefix tailTrace_199449
  have hstable : (prefixWord ++ tailWord_199449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199449).length < 2 ^ (prefixWord ++ tailWord_199449).sum := by decide
  have hdescent : baseEnd_199449 < baseStart_199449 := by decide
  rcases family_descends (prefixWord ++ tailWord_199449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199473 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_199473 : Nat := 118140960795 + 199473 * 2 ^ 59
def prefixEnd_199473 : Nat := 4983230072969 + 3 ^ 40 * 199473 * 2
def baseEnd_199473 : Nat := 91044912528358484151241

theorem tailTrace_199473 : CollatzResearch.WordTrace tailWord_199473 prefixEnd_199473 91044912528358484151241 := by
  unfold tailWord_199473
  simp only [CollatzResearch.WordTrace]
  refine ⟨7275378006350863121275073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4850252004233908747516715 7275378006350863121275073)
  ·
    refine ⟨5456533504763147340956305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7275378006350863121275073 5456533504763147340956305)
    ·
      refine ⟨4092400128572360505717229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5456533504763147340956305 4092400128572360505717229)
      ·
        refine ⟨1534650048214635189643961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4092400128572360505717229 1534650048214635189643961)
        ·
          refine ⟨1150987536160976392232971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534650048214635189643961 1150987536160976392232971)
          ·
            refine ⟨1726481304241464588349457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150987536160976392232971 1726481304241464588349457)
            ·
              refine ⟨1294860978181098441262093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726481304241464588349457 1294860978181098441262093)
              ·
                refine ⟨485572866817911915473285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1294860978181098441262093 485572866817911915473285)
                ·
                  refine ⟨91044912528358484151241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485572866817911915473285 91044912528358484151241)
                  ·
                    rfl

theorem cell20_199473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_199473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199473 prefixEnd_199473 := by exact prefixLift 199473
  have htrace : WordTrace (prefixWord ++ tailWord_199473) baseStart_199473 baseEnd_199473 := by
    simpa [prefixWord, tailWord_199473, baseEnd_199473] using wordTrace_append hprefix tailTrace_199473
  have hstable : (prefixWord ++ tailWord_199473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199473).length < 2 ^ (prefixWord ++ tailWord_199473).sum := by decide
  have hdescent : baseEnd_199473 < baseStart_199473 := by decide
  rcases family_descends (prefixWord ++ tailWord_199473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199497 : List Nat := [1, 2, 1, 1, 2, 6, 3, 4]
def baseStart_199497 : Nat := 118140960795 + 199497 * 2 ^ 59
def prefixEnd_199497 : Nat := 4983230072969 + 3 ^ 40 * 199497 * 2
def baseEnd_199497 : Nat := 30351955594107022450381

theorem tailTrace_199497 : CollatzResearch.WordTrace tailWord_199497 prefixEnd_199497 30351955594107022450381 := by
  unfold tailWord_199497
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276253358263915220148745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4850835572175943480099163 7276253358263915220148745)
  ·
    refine ⟨5457190018697936415111559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7276253358263915220148745 5457190018697936415111559)
    ·
      refine ⟨8185785028046904622667339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457190018697936415111559 8185785028046904622667339)
      ·
        refine ⟨12278677542070356934001009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8185785028046904622667339 12278677542070356934001009)
        ·
          refine ⟨9209008156552767700500757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12278677542070356934001009 9209008156552767700500757)
          ·
            refine ⟨431672257338410985960973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9209008156552767700500757 431672257338410985960973)
            ·
              refine ⟨161877096501904119735365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431672257338410985960973 161877096501904119735365)
              ·
                refine ⟨30351955594107022450381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161877096501904119735365 30351955594107022450381)
                ·
                  rfl

theorem cell20_199497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_199497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199497 prefixEnd_199497 := by exact prefixLift 199497
  have htrace : WordTrace (prefixWord ++ tailWord_199497) baseStart_199497 baseEnd_199497 := by
    simpa [prefixWord, tailWord_199497, baseEnd_199497] using wordTrace_append hprefix tailTrace_199497
  have hstable : (prefixWord ++ tailWord_199497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199497).length < 2 ^ (prefixWord ++ tailWord_199497).sum := by decide
  have hdescent : baseEnd_199497 < baseStart_199497 := by decide
  rcases family_descends (prefixWord ++ tailWord_199497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199528 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_199528 : Nat := 118140960795 + 199528 * 2 ^ 59
def prefixEnd_199528 : Nat := 4983230072969 + 3 ^ 40 * 199528 * 2
def baseEnd_199528 : Nat := 91070016027022737317683

theorem tailTrace_199528 : CollatzResearch.WordTrace tailWord_199528 prefixEnd_199528 91070016027022737317683 := by
  unfold tailWord_199528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638692010575803757263619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4851589347434405009684825 3638692010575803757263619)
  ·
    refine ⟨5458038015863705635895429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3638692010575803757263619 5458038015863705635895429)
    ·
      refine ⟨1023382127974444806730393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5458038015863705635895429 1023382127974444806730393)
      ·
        refine ⟨767536595980833605047795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023382127974444806730393 767536595980833605047795)
        ·
          refine ⟨1151304893971250407571693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767536595980833605047795 1151304893971250407571693)
          ·
            refine ⟨431739335239218902839385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1151304893971250407571693 431739335239218902839385)
            ·
              refine ⟨323804501429414177129539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431739335239218902839385 323804501429414177129539)
              ·
                refine ⟨485706752144121265694309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323804501429414177129539 485706752144121265694309)
                ·
                  refine ⟨91070016027022737317683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485706752144121265694309 91070016027022737317683)
                  ·
                    rfl

theorem cell20_199528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_199528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199528 prefixEnd_199528 := by exact prefixLift 199528
  have htrace : WordTrace (prefixWord ++ tailWord_199528) baseStart_199528 baseEnd_199528 := by
    simpa [prefixWord, tailWord_199528, baseEnd_199528] using wordTrace_append hprefix tailTrace_199528
  have hstable : (prefixWord ++ tailWord_199528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199528).length < 2 ^ (prefixWord ++ tailWord_199528).sum := by decide
  have hdescent : baseEnd_199528 < baseStart_199528 := by decide
  rcases family_descends (prefixWord ++ tailWord_199528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199549 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_199549 : Nat := 118140960795 + 199549 * 2 ^ 59
def prefixEnd_199549 : Nat := 4983230072969 + 3 ^ 40 * 199549 * 2
def baseEnd_199549 : Nat := 91079600999239997617597

theorem tailTrace_199549 : CollatzResearch.WordTrace tailWord_199549 prefixEnd_199549 91079600999239997617597 := by
  unfold tailWord_199549
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278149954075528101041701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4852099969383685400694467 7278149954075528101041701)
  ·
    refine ⟨1364653116389161518945319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7278149954075528101041701 1364653116389161518945319)
    ·
      refine ⟨2046979674583742278417979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1364653116389161518945319 2046979674583742278417979)
      ·
        refine ⟨3070469511875613417626969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046979674583742278417979 3070469511875613417626969)
        ·
          refine ⟨2302852133906710063220227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3070469511875613417626969 2302852133906710063220227)
          ·
            refine ⟨3454278200860065094830341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302852133906710063220227 3454278200860065094830341)
            ·
              refine ⟨647677162661262205280689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3454278200860065094830341 647677162661262205280689)
              ·
                refine ⟨485757871995946653960517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647677162661262205280689 485757871995946653960517)
                ·
                  refine ⟨91079600999239997617597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485757871995946653960517 91079600999239997617597)
                  ·
                    rfl

theorem cell20_199549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_199549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199549 prefixEnd_199549 := by exact prefixLift 199549
  have htrace : WordTrace (prefixWord ++ tailWord_199549) baseStart_199549 baseEnd_199549 := by
    simpa [prefixWord, tailWord_199549, baseEnd_199549] using wordTrace_append hprefix tailTrace_199549
  have hstable : (prefixWord ++ tailWord_199549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199549).length < 2 ^ (prefixWord ++ tailWord_199549).sum := by decide
  have hdescent : baseEnd_199549 < baseStart_199549 := by decide
  rcases family_descends (prefixWord ++ tailWord_199549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199562 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_199562 : Nat := 118140960795 + 199562 * 2 ^ 59
def prefixEnd_199562 : Nat := 4983230072969 + 3 ^ 40 * 199562 * 2
def baseEnd_199562 : Nat := 91085534553469730184211

theorem tailTrace_199562 : CollatzResearch.WordTrace tailWord_199562 prefixEnd_199562 91085534553469730184211 := by
  unfold tailWord_199562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819656025757107830316235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4852416068685620880843293 1819656025757107830316235)
  ·
    refine ⟨2729484038635661745474353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1819656025757107830316235 2729484038635661745474353)
    ·
      refine ⟨2047113028976746309105765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2729484038635661745474353 2047113028976746309105765)
      ·
        refine ⟨383833692933139932957331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2047113028976746309105765 383833692933139932957331)
        ·
          refine ⟨575750539399709899435997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383833692933139932957331 575750539399709899435997)
          ·
            refine ⟨215906452274891212288499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575750539399709899435997 215906452274891212288499)
            ·
              refine ⟨323859678412336818432749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215906452274891212288499 323859678412336818432749)
              ·
                refine ⟨121447379404626306912281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323859678412336818432749 121447379404626306912281)
                ·
                  refine ⟨91085534553469730184211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121447379404626306912281 91085534553469730184211)
                  ·
                    rfl

theorem cell20_199562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_199562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199562 prefixEnd_199562 := by exact prefixLift 199562
  have htrace : WordTrace (prefixWord ++ tailWord_199562) baseStart_199562 baseEnd_199562 := by
    simpa [prefixWord, tailWord_199562, baseEnd_199562] using wordTrace_append hprefix tailTrace_199562
  have hstable : (prefixWord ++ tailWord_199562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199562).length < 2 ^ (prefixWord ++ tailWord_199562).sum := by decide
  have hdescent : baseEnd_199562 < baseStart_199562 := by decide
  rcases family_descends (prefixWord ++ tailWord_199562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199563 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_199563 : Nat := 118140960795 + 199563 * 2 ^ 59
def prefixEnd_199563 : Nat := 4983230072969 + 3 ^ 40 * 199563 * 2
def baseEnd_199563 : Nat := 91085990980718171150873

theorem tailTrace_199563 : CollatzResearch.WordTrace tailWord_199563 prefixEnd_199563 91085990980718171150873 := by
  unfold tailWord_199563
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278660576024808492051343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4852440384016538994700895 7278660576024808492051343)
  ·
    refine ⟨10917990864037212738077015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7278660576024808492051343 10917990864037212738077015)
    ·
      refine ⟨16376986296055819107115523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10917990864037212738077015 16376986296055819107115523)
      ·
        refine ⟨24565479444083728660673285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376986296055819107115523 24565479444083728660673285)
        ·
          refine ⟨4606027395765699123876241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24565479444083728660673285 4606027395765699123876241)
          ·
            refine ⟨3454520546824274342907181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4606027395765699123876241 3454520546824274342907181)
            ·
              refine ⟨1295445205059102878590193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3454520546824274342907181 1295445205059102878590193)
              ·
                refine ⟨971583903794327158942645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295445205059102878590193 971583903794327158942645)
                ·
                  refine ⟨91085990980718171150873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 971583903794327158942645 91085990980718171150873)
                  ·
                    rfl

theorem cell20_199563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_199563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199563 prefixEnd_199563 := by exact prefixLift 199563
  have htrace : WordTrace (prefixWord ++ tailWord_199563) baseStart_199563 baseEnd_199563 := by
    simpa [prefixWord, tailWord_199563, baseEnd_199563] using wordTrace_append hprefix tailTrace_199563
  have hstable : (prefixWord ++ tailWord_199563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199563).length < 2 ^ (prefixWord ++ tailWord_199563).sum := by decide
  have hdescent : baseEnd_199563 < baseStart_199563 := by decide
  rcases family_descends (prefixWord ++ tailWord_199563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199587 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_199587 : Nat := 118140960795 + 199587 * 2 ^ 59
def prefixEnd_199587 : Nat := 4983230072969 + 3 ^ 40 * 199587 * 2
def baseEnd_199587 : Nat := 91096945234680754350775

theorem tailTrace_199587 : CollatzResearch.WordTrace tailWord_199587 prefixEnd_199587 91096945234680754350775 := by
  unfold tailWord_199587
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279535927937860590925015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4853023951958573727283343 7279535927937860590925015)
  ·
    refine ⟨10919303891906790886387523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7279535927937860590925015 10919303891906790886387523)
    ·
      refine ⟨16378955837860186329581285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10919303891906790886387523 16378955837860186329581285)
      ·
        refine ⟨3071054219598784936796491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16378955837860186329581285 3071054219598784936796491)
        ·
          refine ⟨4606581329398177405194737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071054219598784936796491 4606581329398177405194737)
          ·
            refine ⟨3454935997048633053896053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4606581329398177405194737 3454935997048633053896053)
            ·
              refine ⟨323900249723309348802755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3454935997048633053896053 323900249723309348802755)
              ·
                refine ⟨485850374584964023204133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323900249723309348802755 485850374584964023204133)
                ·
                  refine ⟨91096945234680754350775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485850374584964023204133 91096945234680754350775)
                  ·
                    rfl

theorem cell20_199587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_199587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199587 prefixEnd_199587 := by exact prefixLift 199587
  have htrace : WordTrace (prefixWord ++ tailWord_199587) baseStart_199587 baseEnd_199587 := by
    simpa [prefixWord, tailWord_199587, baseEnd_199587] using wordTrace_append hprefix tailTrace_199587
  have hstable : (prefixWord ++ tailWord_199587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199587).length < 2 ^ (prefixWord ++ tailWord_199587).sum := by decide
  have hdescent : baseEnd_199587 < baseStart_199587 := by decide
  rcases family_descends (prefixWord ++ tailWord_199587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199638 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_199638 : Nat := 118140960795 + 199638 * 2 ^ 59
def prefixEnd_199638 : Nat := 4983230072969 + 3 ^ 40 * 199638 * 2
def baseEnd_199638 : Nat := 91120223024351243650567

theorem tailTrace_199638 : CollatzResearch.WordTrace tailWord_199638 prefixEnd_199638 91120223024351243650567 := by
  unfold tailWord_199638
  simp only [CollatzResearch.WordTrace]
  refine ⟨455087253172068518814473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4854264033835397534021045 455087253172068518814473)
  ·
    refine ⟨341315439879051389110855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 455087253172068518814473 341315439879051389110855)
    ·
      refine ⟨511973159818577083666283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341315439879051389110855 511973159818577083666283)
      ·
        refine ⟨767959739727865625499425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511973159818577083666283 767959739727865625499425)
        ·
          refine ⟨575969804795899219124569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767959739727865625499425 575969804795899219124569)
          ·
            refine ⟨431977353596924414343427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575969804795899219124569 431977353596924414343427)
            ·
              refine ⟨647966030395386621515141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431977353596924414343427 647966030395386621515141)
              ·
                refine ⟨121493630699134991534089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647966030395386621515141 121493630699134991534089)
                ·
                  refine ⟨91120223024351243650567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121493630699134991534089 91120223024351243650567)
                  ·
                    rfl

theorem cell20_199638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_199638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199638 prefixEnd_199638 := by exact prefixLift 199638
  have htrace : WordTrace (prefixWord ++ tailWord_199638) baseStart_199638 baseEnd_199638 := by
    simpa [prefixWord, tailWord_199638, baseEnd_199638] using wordTrace_append hprefix tailTrace_199638
  have hstable : (prefixWord ++ tailWord_199638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199638).length < 2 ^ (prefixWord ++ tailWord_199638).sum := by decide
  have hdescent : baseEnd_199638 < baseStart_199638 := by decide
  rcases family_descends (prefixWord ++ tailWord_199638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199656 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_199656 : Nat := 118140960795 + 199656 * 2 ^ 59
def prefixEnd_199656 : Nat := 4983230072969 + 3 ^ 40 * 199656 * 2
def baseEnd_199656 : Nat := 91128438714823181050493

theorem tailTrace_199656 : CollatzResearch.WordTrace tailWord_199656 prefixEnd_199656 91128438714823181050493 := by
  unfold tailWord_199656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641026282343942687593411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4854701709791923583457881 3641026282343942687593411)
  ·
    refine ⟨5461539423515914031390117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3641026282343942687593411 5461539423515914031390117)
    ·
      refine ⟨1024038641909233880885647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5461539423515914031390117 1024038641909233880885647)
      ·
        refine ⟨1536057962863850821328471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024038641909233880885647 1536057962863850821328471)
        ·
          refine ⟨2304086944295776231992707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536057962863850821328471 2304086944295776231992707)
          ·
            refine ⟨3456130416443664347989061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304086944295776231992707 3456130416443664347989061)
            ·
              refine ⟨648024453083187065247949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3456130416443664347989061 648024453083187065247949)
              ·
                refine ⟨243009169906195149467981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648024453083187065247949 243009169906195149467981)
                ·
                  refine ⟨91128438714823181050493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243009169906195149467981 91128438714823181050493)
                  ·
                    rfl

theorem cell20_199656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_199656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199656 prefixEnd_199656 := by exact prefixLift 199656
  have htrace : WordTrace (prefixWord ++ tailWord_199656) baseStart_199656 baseEnd_199656 := by
    simpa [prefixWord, tailWord_199656, baseEnd_199656] using wordTrace_append hprefix tailTrace_199656
  have hstable : (prefixWord ++ tailWord_199656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199656).length < 2 ^ (prefixWord ++ tailWord_199656).sum := by decide
  have hdescent : baseEnd_199656 < baseStart_199656 := by decide
  rcases family_descends (prefixWord ++ tailWord_199656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199663 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_199663 : Nat := 118140960795 + 199663 * 2 ^ 59
def prefixEnd_199663 : Nat := 4983230072969 + 3 ^ 40 * 199663 * 2
def baseEnd_199663 : Nat := 91131633705562267817131

theorem tailTrace_199663 : CollatzResearch.WordTrace tailWord_199663 prefixEnd_199663 91131633705562267817131 := by
  unfold tailWord_199663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282307875662525570691643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4854871917108350380461095 7282307875662525570691643)
  ·
    refine ⟨10923461813493788356037465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7282307875662525570691643 10923461813493788356037465)
    ·
      refine ⟨8192596360120341267028099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10923461813493788356037465 8192596360120341267028099)
      ·
        refine ⟨12288894540180511900542149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8192596360120341267028099 12288894540180511900542149)
        ·
          refine ⟨2304167726283845981351653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12288894540180511900542149 2304167726283845981351653)
          ·
            refine ⟨432031448678221121503435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2304167726283845981351653 432031448678221121503435)
            ·
              refine ⟨648047173017331682255153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432031448678221121503435 648047173017331682255153)
              ·
                refine ⟨486035379762998761691365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648047173017331682255153 486035379762998761691365)
                ·
                  refine ⟨91131633705562267817131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486035379762998761691365 91131633705562267817131)
                  ·
                    rfl

theorem cell20_199663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_199663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199663 prefixEnd_199663 := by exact prefixLift 199663
  have htrace : WordTrace (prefixWord ++ tailWord_199663) baseStart_199663 baseEnd_199663 := by
    simpa [prefixWord, tailWord_199663, baseEnd_199663] using wordTrace_append hprefix tailTrace_199663
  have hstable : (prefixWord ++ tailWord_199663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199663).length < 2 ^ (prefixWord ++ tailWord_199663).sum := by decide
  have hdescent : baseEnd_199663 < baseStart_199663 := by decide
  rcases family_descends (prefixWord ++ tailWord_199663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199677 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_199677 : Nat := 118140960795 + 199677 * 2 ^ 59
def prefixEnd_199677 : Nat := 4983230072969 + 3 ^ 40 * 199677 * 2
def baseEnd_199677 : Nat := 91138023687040441350407

theorem tailTrace_199677 : CollatzResearch.WordTrace tailWord_199677 prefixEnd_199677 91138023687040441350407 := by
  unfold tailWord_199677
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282818497611805961701285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4855212331741203974467523 7282818497611805961701285)
  ·
    refine ⟨1365528468302213617818991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7282818497611805961701285 1365528468302213617818991)
    ·
      refine ⟨2048292702453320426728487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365528468302213617818991 2048292702453320426728487)
      ·
        refine ⟨3072439053679980640092731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048292702453320426728487 3072439053679980640092731)
        ·
          refine ⟨4608658580519970960139097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072439053679980640092731 4608658580519970960139097)
          ·
            refine ⟨3456493935389978220104323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608658580519970960139097 3456493935389978220104323)
            ·
              refine ⟨5184740903084967330156485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456493935389978220104323 5184740903084967330156485)
              ·
                refine ⟨972138919328431374404341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5184740903084967330156485 972138919328431374404341)
                ·
                  refine ⟨91138023687040441350407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 972138919328431374404341 91138023687040441350407)
                  ·
                    rfl

theorem cell20_199677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_199677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199677 prefixEnd_199677 := by exact prefixLift 199677
  have htrace : WordTrace (prefixWord ++ tailWord_199677) baseStart_199677 baseEnd_199677 := by
    simpa [prefixWord, tailWord_199677, baseEnd_199677] using wordTrace_append hprefix tailTrace_199677
  have hstable : (prefixWord ++ tailWord_199677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199677).length < 2 ^ (prefixWord ++ tailWord_199677).sum := by decide
  have hdescent : baseEnd_199677 < baseStart_199677 := by decide
  rcases family_descends (prefixWord ++ tailWord_199677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199694 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_199694 : Nat := 118140960795 + 199694 * 2 ^ 59
def prefixEnd_199694 : Nat := 4983230072969 + 3 ^ 40 * 199694 * 2
def baseEnd_199694 : Nat := 91145782950263937783671

theorem tailTrace_199694 : CollatzResearch.WordTrace tailWord_199694 prefixEnd_199694 91145782950263937783671 := by
  unfold tailWord_199694
  simp only [CollatzResearch.WordTrace]
  refine ⟨910429817318777233133767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4855625692366811910046757 910429817318777233133767)
  ·
    refine ⟨1365644725978165849700651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910429817318777233133767 1365644725978165849700651)
    ·
      refine ⟨2048467088967248774550977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365644725978165849700651 2048467088967248774550977)
      ·
        refine ⟨1536350316725436580913233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2048467088967248774550977 1536350316725436580913233)
        ·
          refine ⟨1152262737544077435684925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536350316725436580913233 1152262737544077435684925)
          ·
            refine ⟨432098526579029038381847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1152262737544077435684925 432098526579029038381847)
            ·
              refine ⟨648147789868543557572771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432098526579029038381847 648147789868543557572771)
              ·
                refine ⟨972221684802815336359157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648147789868543557572771 972221684802815336359157)
                ·
                  refine ⟨91145782950263937783671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 972221684802815336359157 91145782950263937783671)
                  ·
                    rfl

theorem cell20_199694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_199694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199694 prefixEnd_199694 := by exact prefixLift 199694
  have htrace : WordTrace (prefixWord ++ tailWord_199694) baseStart_199694 baseEnd_199694 := by
    simpa [prefixWord, tailWord_199694, baseEnd_199694] using wordTrace_append hprefix tailTrace_199694
  have hstable : (prefixWord ++ tailWord_199694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199694).length < 2 ^ (prefixWord ++ tailWord_199694).sum := by decide
  have hdescent : baseEnd_199694 < baseStart_199694 := by decide
  rcases family_descends (prefixWord ++ tailWord_199694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199701 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_199701 : Nat := 118140960795 + 199701 * 2 ^ 59
def prefixEnd_199701 : Nat := 4983230072969 + 3 ^ 40 * 199701 * 2
def baseEnd_199701 : Nat := 91148977941003024550309

theorem tailTrace_199701 : CollatzResearch.WordTrace tailWord_199701 prefixEnd_199701 91148977941003024550309 := by
  unfold tailWord_199701
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283693849524858060574957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4855795899683238707049971 7283693849524858060574957)
  ·
    refine ⟨2731385193571821772715609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7283693849524858060574957 2731385193571821772715609)
    ·
      refine ⟨2048538895178866329536707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2731385193571821772715609 2048538895178866329536707)
      ·
        refine ⟨3072808342768299494305061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048538895178866329536707 3072808342768299494305061)
        ·
          refine ⟨576151564269056155182199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3072808342768299494305061 576151564269056155182199)
          ·
            refine ⟨864227346403584232773299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576151564269056155182199 864227346403584232773299)
            ·
              refine ⟨1296341019605376349159949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864227346403584232773299 1296341019605376349159949)
              ·
                refine ⟨486127882352016130934981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296341019605376349159949 486127882352016130934981)
                ·
                  refine ⟨91148977941003024550309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486127882352016130934981 91148977941003024550309)
                  ·
                    rfl

theorem cell20_199701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_199701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199701 prefixEnd_199701 := by exact prefixLift 199701
  have htrace : WordTrace (prefixWord ++ tailWord_199701) baseStart_199701 baseEnd_199701 := by
    simpa [prefixWord, tailWord_199701, baseEnd_199701] using wordTrace_append hprefix tailTrace_199701
  have hstable : (prefixWord ++ tailWord_199701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199701).length < 2 ^ (prefixWord ++ tailWord_199701).sum := by decide
  have hdescent : baseEnd_199701 < baseStart_199701 := by decide
  rcases family_descends (prefixWord ++ tailWord_199701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199711 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 3]
def baseStart_199711 : Nat := 118140960795 + 199711 * 2 ^ 59
def prefixEnd_199711 : Nat := 4983230072969 + 3 ^ 40 * 199711 * 2
def baseEnd_199711 : Nat := 91153542213487434216935

theorem tailTrace_199711 : CollatzResearch.WordTrace tailWord_199711 prefixEnd_199711 91153542213487434216935 := by
  unfold tailWord_199711
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284058579488629768438987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4856039052992419845625991 7284058579488629768438987)
  ·
    refine ⟨10926087869232944652658481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7284058579488629768438987 10926087869232944652658481)
    ·
      refine ⟨8194565901924708489493861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10926087869232944652658481 8194565901924708489493861)
      ·
        refine ⟨1536481106610882841780099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8194565901924708489493861 1536481106610882841780099)
        ·
          refine ⟨2304721659916324262670149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536481106610882841780099 2304721659916324262670149)
          ·
            refine ⟨432135311234310799250653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2304721659916324262670149 432135311234310799250653)
            ·
              refine ⟨162050741712866549718995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432135311234310799250653 162050741712866549718995)
              ·
                refine ⟨243076112569299824578493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162050741712866549718995 243076112569299824578493)
                ·
                  refine ⟨91153542213487434216935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243076112569299824578493 91153542213487434216935)
                  ·
                    rfl

theorem cell20_199711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_199711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199711 prefixEnd_199711 := by exact prefixLift 199711
  have htrace : WordTrace (prefixWord ++ tailWord_199711) baseStart_199711 baseEnd_199711 := by
    simpa [prefixWord, tailWord_199711, baseEnd_199711] using wordTrace_append hprefix tailTrace_199711
  have hstable : (prefixWord ++ tailWord_199711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199711).length < 2 ^ (prefixWord ++ tailWord_199711).sum := by decide
  have hdescent : baseEnd_199711 < baseStart_199711 := by decide
  rcases family_descends (prefixWord ++ tailWord_199711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199794 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_199794 : Nat := 118140960795 + 199794 * 2 ^ 59
def prefixEnd_199794 : Nat := 4983230072969 + 3 ^ 40 * 199794 * 2
def baseEnd_199794 : Nat := 91191425675108034449929

theorem tailTrace_199794 : CollatzResearch.WordTrace tailWord_199794 prefixEnd_199794 91191425675108034449929 := by
  unfold tailWord_199794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821771459546983735927609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4858057225458623295806957 1821771459546983735927609)
  ·
    refine ⟨1366328594660237801945707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1821771459546983735927609 1366328594660237801945707)
    ·
      refine ⟨2049492891990356702918561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366328594660237801945707 2049492891990356702918561)
      ·
        refine ⟨1537119668992767527188921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2049492891990356702918561 1537119668992767527188921)
        ·
          refine ⟨1152839751744575645391691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537119668992767527188921 1152839751744575645391691)
          ·
            refine ⟨1729259627616863468087537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152839751744575645391691 1729259627616863468087537)
            ·
              refine ⟨1296944720712647601065653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729259627616863468087537 1296944720712647601065653)
              ·
                refine ⟨121588567566810712599905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1296944720712647601065653 121588567566810712599905)
                ·
                  refine ⟨91191425675108034449929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121588567566810712599905 91191425675108034449929)
                  ·
                    rfl

theorem cell20_199794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_199794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199794 prefixEnd_199794 := by exact prefixLift 199794
  have htrace : WordTrace (prefixWord ++ tailWord_199794) baseStart_199794 baseEnd_199794 := by
    simpa [prefixWord, tailWord_199794, baseEnd_199794] using wordTrace_append hprefix tailTrace_199794
  have hstable : (prefixWord ++ tailWord_199794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199794).length < 2 ^ (prefixWord ++ tailWord_199794).sum := by decide
  have hdescent : baseEnd_199794 < baseStart_199794 := by decide
  rcases family_descends (prefixWord ++ tailWord_199794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199843 : List Nat := [1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_199843 : Nat := 118140960795 + 199843 * 2 ^ 59
def prefixEnd_199843 : Nat := 4983230072969 + 3 ^ 40 * 199843 * 2
def baseEnd_199843 : Nat := 30404596870093880605465

theorem tailTrace_199843 : CollatzResearch.WordTrace tailWord_199843 prefixEnd_199843 30404596870093880605465 := by
  unfold tailWord_199843
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288873015010416312244183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4859248676673610874829455 7288873015010416312244183)
  ·
    refine ⟨10933309522515624468366275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288873015010416312244183 10933309522515624468366275)
    ·
      refine ⟨16399964283773436702549413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10933309522515624468366275 16399964283773436702549413)
      ·
        refine ⟨3074993303207519381728015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16399964283773436702549413 3074993303207519381728015)
        ·
          refine ⟨4612489954811279072592023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074993303207519381728015 4612489954811279072592023)
          ·
            refine ⟨6918734932216918608888035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612489954811279072592023 6918734932216918608888035)
            ·
              refine ⟨10378102398325377913332053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918734932216918608888035 10378102398325377913332053)
              ·
                refine ⟨30404596870093880605465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10378102398325377913332053 30404596870093880605465)
                ·
                  rfl

theorem cell20_199843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_199843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199843 prefixEnd_199843 := by exact prefixLift 199843
  have htrace : WordTrace (prefixWord ++ tailWord_199843) baseStart_199843 baseEnd_199843 := by
    simpa [prefixWord, tailWord_199843, baseEnd_199843] using wordTrace_append hprefix tailTrace_199843
  have hstable : (prefixWord ++ tailWord_199843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199843).length < 2 ^ (prefixWord ++ tailWord_199843).sum := by decide
  have hdescent : baseEnd_199843 < baseStart_199843 := by decide
  rcases family_descends (prefixWord ++ tailWord_199843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199867 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_199867 : Nat := 118140960795 + 199867 * 2 ^ 59
def prefixEnd_199867 : Nat := 4983230072969 + 3 ^ 40 * 199867 * 2
def baseEnd_199867 : Nat := 91224744864244225016297

theorem tailTrace_199867 : CollatzResearch.WordTrace tailWord_199867 prefixEnd_199867 91224744864244225016297 := by
  unfold tailWord_199867
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289748366923468411117855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4859832244615645607411903 7289748366923468411117855)
  ·
    refine ⟨10934622550385202616676783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7289748366923468411117855 10934622550385202616676783)
    ·
      refine ⟨16401933825577803925015175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10934622550385202616676783 16401933825577803925015175)
      ·
        refine ⟨24602900738366705887522763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16401933825577803925015175 24602900738366705887522763)
        ·
          refine ⟨36904351107550058831284145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24602900738366705887522763 36904351107550058831284145)
          ·
            refine ⟨27678263330662544123463109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36904351107550058831284145 27678263330662544123463109)
            ·
              refine ⟨5189674374499227023149333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27678263330662544123463109 5189674374499227023149333)
              ·
                refine ⟨243265986304651266710125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5189674374499227023149333 243265986304651266710125)
                ·
                  refine ⟨91224744864244225016297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243265986304651266710125 91224744864244225016297)
                  ·
                    rfl

theorem cell20_199867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_199867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199867 prefixEnd_199867 := by exact prefixLift 199867
  have htrace : WordTrace (prefixWord ++ tailWord_199867) baseStart_199867 baseEnd_199867 := by
    simpa [prefixWord, tailWord_199867, baseEnd_199867] using wordTrace_append hprefix tailTrace_199867
  have hstable : (prefixWord ++ tailWord_199867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199867).length < 2 ^ (prefixWord ++ tailWord_199867).sum := by decide
  have hdescent : baseEnd_199867 < baseStart_199867 := by decide
  rcases family_descends (prefixWord ++ tailWord_199867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199870 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_199870 : Nat := 118140960795 + 199870 * 2 ^ 59
def prefixEnd_199870 : Nat := 4983230072969 + 3 ^ 40 * 199870 * 2
def baseEnd_199870 : Nat := 91226114145989547916285

theorem tailTrace_199870 : CollatzResearch.WordTrace tailWord_199870 prefixEnd_199870 91226114145989547916285 := by
  unfold tailWord_199870
  simp only [CollatzResearch.WordTrace]
  refine ⟨911232223239074990434633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4859905190608399948984709 911232223239074990434633)
  ·
    refine ⟨683424167429306242825975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 911232223239074990434633 683424167429306242825975)
    ·
      refine ⟨1025136251143959364238963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683424167429306242825975 1025136251143959364238963)
      ·
        refine ⟨1537704376715939046358445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025136251143959364238963 1537704376715939046358445)
        ·
          refine ⟨576639141268477142384417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1537704376715939046358445 576639141268477142384417)
          ·
            refine ⟨432479355951357856788313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576639141268477142384417 432479355951357856788313)
            ·
              refine ⟨324359516963518392591235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432479355951357856788313 324359516963518392591235)
              ·
                refine ⟨486539275445277588886853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324359516963518392591235 486539275445277588886853)
                ·
                  refine ⟨91226114145989547916285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486539275445277588886853 91226114145989547916285)
                  ·
                    rfl

theorem cell20_199870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_199870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199870 prefixEnd_199870 := by exact prefixLift 199870
  have htrace : WordTrace (prefixWord ++ tailWord_199870) baseStart_199870 baseEnd_199870 := by
    simpa [prefixWord, tailWord_199870, baseEnd_199870] using wordTrace_append hprefix tailTrace_199870
  have hstable : (prefixWord ++ tailWord_199870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199870).length < 2 ^ (prefixWord ++ tailWord_199870).sum := by decide
  have hdescent : baseEnd_199870 < baseStart_199870 := by decide
  rcases family_descends (prefixWord ++ tailWord_199870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199894 : List Nat := [5, 2, 1, 2, 2, 1, 1, 6]
def baseStart_199894 : Nat := 118140960795 + 199894 * 2 ^ 59
def prefixEnd_199894 : Nat := 4983230072969 + 3 ^ 40 * 199894 * 2
def baseEnd_199894 : Nat := 30412356133317377038729

theorem tailTrace_199894 : CollatzResearch.WordTrace tailWord_199894 prefixEnd_199894 30412356133317377038729 := by
  unfold tailWord_199894
  simp only [CollatzResearch.WordTrace]
  refine ⟨455670821114103251396921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4860488758550434681567157 455670821114103251396921)
  ·
    refine ⟨341753115835577438547691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 455670821114103251396921 341753115835577438547691)
    ·
      refine ⟨512629673753366157821537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341753115835577438547691 512629673753366157821537)
      ·
        refine ⟨384472255315024618366153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512629673753366157821537 384472255315024618366153)
        ·
          refine ⟨288354191486268463774615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384472255315024618366153 288354191486268463774615)
          ·
            refine ⟨432531287229402695661923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288354191486268463774615 432531287229402695661923)
            ·
              refine ⟨648796930844104043492885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432531287229402695661923 648796930844104043492885)
              ·
                refine ⟨30412356133317377038729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 648796930844104043492885 30412356133317377038729)
                ·
                  rfl

theorem cell20_199894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_199894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199894 prefixEnd_199894 := by exact prefixLift 199894
  have htrace : WordTrace (prefixWord ++ tailWord_199894) baseStart_199894 baseEnd_199894 := by
    simpa [prefixWord, tailWord_199894, baseEnd_199894] using wordTrace_append hprefix tailTrace_199894
  have hstable : (prefixWord ++ tailWord_199894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199894).length < 2 ^ (prefixWord ++ tailWord_199894).sum := by decide
  have hdescent : baseEnd_199894 < baseStart_199894 := by decide
  rcases family_descends (prefixWord ++ tailWord_199894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199905 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_199905 : Nat := 118140960795 + 199905 * 2 ^ 59
def prefixEnd_199905 : Nat := 4983230072969 + 3 ^ 40 * 199905 * 2
def baseEnd_199905 : Nat := 91242089099684981749475

theorem tailTrace_199905 : CollatzResearch.WordTrace tailWord_199905 prefixEnd_199905 91242089099684981749475 := by
  unfold tailWord_199905
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291134340785800901001169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4860756227190533934000779 7291134340785800901001169)
  ·
    refine ⟨5468350755589350675750877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7291134340785800901001169 5468350755589350675750877)
    ·
      refine ⟨2050631533346006503406579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5468350755589350675750877 2050631533346006503406579)
      ·
        refine ⟨3075947300019009755109869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050631533346006503406579 3075947300019009755109869)
        ·
          refine ⟨1153480237507128658166201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3075947300019009755109869 1153480237507128658166201)
          ·
            refine ⟨865110178130346493624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153480237507128658166201 865110178130346493624651)
            ·
              refine ⟨1297665267195519740436977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865110178130346493624651 1297665267195519740436977)
              ·
                refine ⟨973248950396639805327733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297665267195519740436977 973248950396639805327733)
                ·
                  refine ⟨91242089099684981749475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 973248950396639805327733 91242089099684981749475)
                  ·
                    rfl

theorem cell20_199905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_199905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199905 prefixEnd_199905 := by exact prefixLift 199905
  have htrace : WordTrace (prefixWord ++ tailWord_199905) baseStart_199905 baseEnd_199905 := by
    simpa [prefixWord, tailWord_199905, baseEnd_199905] using wordTrace_append hprefix tailTrace_199905
  have hstable : (prefixWord ++ tailWord_199905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199905).length < 2 ^ (prefixWord ++ tailWord_199905).sum := by decide
  have hdescent : baseEnd_199905 < baseStart_199905 := by decide
  rcases family_descends (prefixWord ++ tailWord_199905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199908 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 2]
def baseStart_199908 : Nat := 118140960795 + 199908 * 2 ^ 59
def prefixEnd_199908 : Nat := 4983230072969 + 3 ^ 40 * 199908 * 2
def baseEnd_199908 : Nat := 91243458381430304649463

theorem tailTrace_199908 : CollatzResearch.WordTrace tailWord_199908 prefixEnd_199908 91243458381430304649463 := by
  unfold tailWord_199908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645621879887466206680189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4860829173183288275573585 3645621879887466206680189)
  ·
    refine ⟨1367108204957799827505071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3645621879887466206680189 1367108204957799827505071)
    ·
      refine ⟨2050662307436699741257607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367108204957799827505071 2050662307436699741257607)
      ·
        refine ⟨3075993461155049611886411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050662307436699741257607 3075993461155049611886411)
        ·
          refine ⟨4613990191732574417829617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075993461155049611886411 4613990191732574417829617)
          ·
            refine ⟨3460492643799430813372213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613990191732574417829617 3460492643799430813372213)
            ·
              refine ⟨324421185356196638753645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3460492643799430813372213 324421185356196638753645)
              ·
                refine ⟨121657944508573739532617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324421185356196638753645 121657944508573739532617)
                ·
                  refine ⟨91243458381430304649463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121657944508573739532617 91243458381430304649463)
                  ·
                    rfl

theorem cell20_199908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_199908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199908 prefixEnd_199908 := by exact prefixLift 199908
  have htrace : WordTrace (prefixWord ++ tailWord_199908) baseStart_199908 baseEnd_199908 := by
    simpa [prefixWord, tailWord_199908, baseEnd_199908] using wordTrace_append hprefix tailTrace_199908
  have hstable : (prefixWord ++ tailWord_199908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199908).length < 2 ^ (prefixWord ++ tailWord_199908).sum := by decide
  have hdescent : baseEnd_199908 < baseStart_199908 := by decide
  rcases family_descends (prefixWord ++ tailWord_199908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199939 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 3]
def baseStart_199939 : Nat := 118140960795 + 199939 * 2 ^ 59
def prefixEnd_199939 : Nat := 4983230072969 + 3 ^ 40 * 199939 * 2
def baseEnd_199939 : Nat := 91257607626131974616003

theorem tailTrace_199939 : CollatzResearch.WordTrace tailWord_199939 prefixEnd_199939 91257607626131974616003 := by
  unfold tailWord_199939
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292374422662624707738871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4861582948441749805159247 7292374422662624707738871)
  ·
    refine ⟨10938561633993937061608307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7292374422662624707738871 10938561633993937061608307)
    ·
      refine ⟨16407842450990905592412461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10938561633993937061608307 16407842450990905592412461)
      ·
        refine ⟨6152940919121589597154673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16407842450990905592412461 6152940919121589597154673)
        ·
          refine ⟨4614705689341192197866005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6152940919121589597154673 4614705689341192197866005)
          ·
            refine ⟨216314329187868384274969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4614705689341192197866005 216314329187868384274969)
            ·
              refine ⟨162235746890901288206227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216314329187868384274969 162235746890901288206227)
              ·
                refine ⟨243353620336351932309341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162235746890901288206227 243353620336351932309341)
                ·
                  refine ⟨91257607626131974616003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243353620336351932309341 91257607626131974616003)
                  ·
                    rfl

theorem cell20_199939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_199939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199939 prefixEnd_199939 := by exact prefixLift 199939
  have htrace : WordTrace (prefixWord ++ tailWord_199939) baseStart_199939 baseEnd_199939 := by
    simpa [prefixWord, tailWord_199939, baseEnd_199939] using wordTrace_append hprefix tailTrace_199939
  have hstable : (prefixWord ++ tailWord_199939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199939).length < 2 ^ (prefixWord ++ tailWord_199939).sum := by decide
  have hdescent : baseEnd_199939 < baseStart_199939 := by decide
  rcases family_descends (prefixWord ++ tailWord_199939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199998 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_199998 : Nat := 118140960795 + 199998 * 2 ^ 59
def prefixEnd_199998 : Nat := 4983230072969 + 3 ^ 40 * 199998 * 2
def baseEnd_199998 : Nat := 91284536833789991649095

theorem tailTrace_199998 : CollatzResearch.WordTrace tailWord_199998 prefixEnd_199998 91284536833789991649095 := by
  unfold tailWord_199998
  simp only [CollatzResearch.WordTrace]
  refine ⟨911815791181109723017081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4863017552965918522757765 911815791181109723017081)
  ·
    refine ⟨683861843385832292262811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 911815791181109723017081 683861843385832292262811)
    ·
      refine ⟨1025792765078748438394217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683861843385832292262811 1025792765078748438394217)
      ·
        refine ⟨769344573809061328795663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1025792765078748438394217 769344573809061328795663)
        ·
          refine ⟨1154016860713591993193495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769344573809061328795663 1154016860713591993193495)
          ·
            refine ⟨1731025291070387989790243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154016860713591993193495 1731025291070387989790243)
            ·
              refine ⟨2596537936605581984685365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731025291070387989790243 2596537936605581984685365)
              ·
                refine ⟨243425431556773311064253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2596537936605581984685365 243425431556773311064253)
                ·
                  refine ⟨91284536833789991649095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243425431556773311064253 91284536833789991649095)
                  ·
                    rfl

theorem cell20_199998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_199998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_199998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_199998 prefixEnd_199998 := by exact prefixLift 199998
  have htrace : WordTrace (prefixWord ++ tailWord_199998) baseStart_199998 baseEnd_199998 := by
    simpa [prefixWord, tailWord_199998, baseEnd_199998] using wordTrace_append hprefix tailTrace_199998
  have hstable : (prefixWord ++ tailWord_199998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199998).length < 2 ^ (prefixWord ++ tailWord_199998).sum := by decide
  have hdescent : baseEnd_199998 < baseStart_199998 := by decide
  rcases family_descends (prefixWord ++ tailWord_199998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200036 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_200036 : Nat := 118140960795 + 200036 * 2 ^ 59
def prefixEnd_200036 : Nat := 4983230072969 + 3 ^ 40 * 200036 * 2
def baseEnd_200036 : Nat := 91301881069230748382273

theorem tailTrace_200036 : CollatzResearch.WordTrace tailWord_200036 prefixEnd_200036 91301881069230748382273 := by
  unfold tailWord_200036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647956151655605137009981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4863941535540806849346641 3647956151655605137009981)
  ·
    refine ⟨1367983556870851926378743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3647956151655605137009981 1367983556870851926378743)
    ·
      refine ⟨2051975335306277889568115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367983556870851926378743 2051975335306277889568115)
      ·
        refine ⟨3077963002959416834352173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051975335306277889568115 3077963002959416834352173)
        ·
          refine ⟨1154236126109781312882065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3077963002959416834352173 1154236126109781312882065)
          ·
            refine ⟨865677094582335984661549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154236126109781312882065 865677094582335984661549)
            ·
              refine ⟨324628910468375994248081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 865677094582335984661549 324628910468375994248081)
              ·
                refine ⟨243471682851281995686061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324628910468375994248081 243471682851281995686061)
                ·
                  refine ⟨91301881069230748382273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243471682851281995686061 91301881069230748382273)
                  ·
                    rfl

theorem cell20_200036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_200036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200036 prefixEnd_200036 := by exact prefixLift 200036
  have htrace : WordTrace (prefixWord ++ tailWord_200036) baseStart_200036 baseEnd_200036 := by
    simpa [prefixWord, tailWord_200036, baseEnd_200036] using wordTrace_append hprefix tailTrace_200036
  have hstable : (prefixWord ++ tailWord_200036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200036).length < 2 ^ (prefixWord ++ tailWord_200036).sum := by decide
  have hdescent : baseEnd_200036 < baseStart_200036 := by decide
  rcases family_descends (prefixWord ++ tailWord_200036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200057 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_200057 : Nat := 118140960795 + 200057 * 2 ^ 59
def prefixEnd_200057 : Nat := 4983230072969 + 3 ^ 40 * 200057 * 2
def baseEnd_200057 : Nat := 91311466041448008682187

theorem tailTrace_200057 : CollatzResearch.WordTrace tailWord_200057 prefixEnd_200057 91311466041448008682187 := by
  unfold tailWord_200057
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296678236235130860534425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4864452157490087240356283 7296678236235130860534425)
  ·
    refine ⟨5472508677176348145400819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7296678236235130860534425 5472508677176348145400819)
    ·
      refine ⟨8208763015764522218101229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472508677176348145400819 8208763015764522218101229)
      ·
        refine ⟨3078286130911695831787961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8208763015764522218101229 3078286130911695831787961)
        ·
          refine ⟨2308714598183771873840971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078286130911695831787961 2308714598183771873840971)
          ·
            refine ⟨3463071897275657810761457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308714598183771873840971 3463071897275657810761457)
            ·
              refine ⟨2597303922956743358071093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3463071897275657810761457 2597303922956743358071093)
              ·
                refine ⟨243497242777194689819165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2597303922956743358071093 243497242777194689819165)
                ·
                  refine ⟨91311466041448008682187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243497242777194689819165 91311466041448008682187)
                  ·
                    rfl

theorem cell20_200057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_200057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200057 prefixEnd_200057 := by exact prefixLift 200057
  have htrace : WordTrace (prefixWord ++ tailWord_200057) baseStart_200057 baseEnd_200057 := by
    simpa [prefixWord, tailWord_200057, baseEnd_200057] using wordTrace_append hprefix tailTrace_200057
  have hstable : (prefixWord ++ tailWord_200057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200057).length < 2 ^ (prefixWord ++ tailWord_200057).sum := by decide
  have hdescent : baseEnd_200057 < baseStart_200057 := by decide
  rcases family_descends (prefixWord ++ tailWord_200057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200067 : List Nat := [1, 1, 1, 3, 5, 3, 2, 4]
def baseStart_200067 : Nat := 118140960795 + 200067 * 2 ^ 59
def prefixEnd_200067 : Nat := 4983230072969 + 3 ^ 40 * 200067 * 2
def baseEnd_200067 : Nat := 30438676771310806116271

theorem tailTrace_200067 : CollatzResearch.WordTrace tailWord_200067 prefixEnd_200067 30438676771310806116271 := by
  unfold tailWord_200067
  simp only [CollatzResearch.WordTrace]
  refine ⟨7297042966198902568398455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4864695310799268378932303 7297042966198902568398455)
  ·
    refine ⟨10945564449298353852597683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7297042966198902568398455 10945564449298353852597683)
    ·
      refine ⟨16418346673947530778896525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10945564449298353852597683 16418346673947530778896525)
      ·
        refine ⟨6156880002730324042086197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16418346673947530778896525 6156880002730324042086197)
        ·
          refine ⟨577207500255967878945581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6156880002730324042086197 577207500255967878945581)
          ·
            refine ⟨216452812595987954604593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577207500255967878945581 216452812595987954604593)
            ·
              refine ⟨162339609446990965953445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216452812595987954604593 162339609446990965953445)
              ·
                refine ⟨30438676771310806116271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162339609446990965953445 30438676771310806116271)
                ·
                  rfl

theorem cell20_200067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_200067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200067 prefixEnd_200067 := by exact prefixLift 200067
  have htrace : WordTrace (prefixWord ++ tailWord_200067) baseStart_200067 baseEnd_200067 := by
    simpa [prefixWord, tailWord_200067, baseEnd_200067] using wordTrace_append hprefix tailTrace_200067
  have hstable : (prefixWord ++ tailWord_200067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200067).length < 2 ^ (prefixWord ++ tailWord_200067).sum := by decide
  have hdescent : baseEnd_200067 < baseStart_200067 := by decide
  rcases family_descends (prefixWord ++ tailWord_200067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200094 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_200094 : Nat := 118140960795 + 200094 * 2 ^ 59
def prefixEnd_200094 : Nat := 4983230072969 + 3 ^ 40 * 200094 * 2
def baseEnd_200094 : Nat := 91328353849640324448703

theorem tailTrace_200094 : CollatzResearch.WordTrace tailWord_200094 prefixEnd_200094 91328353849640324448703 := by
  unfold tailWord_200094
  simp only [CollatzResearch.WordTrace]
  refine ⟨912253467137635772453917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4865351824734057453087557 912253467137635772453917)
  ·
    refine ⟨342095050176613414670219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 912253467137635772453917 342095050176613414670219)
    ·
      refine ⟨513142575264920122005329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342095050176613414670219 513142575264920122005329)
      ·
        refine ⟨384856931448690091503997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513142575264920122005329 384856931448690091503997)
        ·
          refine ⟨144321349293258784313999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384856931448690091503997 144321349293258784313999)
          ·
            refine ⟨216482023939888176470999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144321349293258784313999 216482023939888176470999)
            ·
              refine ⟨324723035909832264706499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216482023939888176470999 324723035909832264706499)
              ·
                refine ⟨487084553864748397059749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324723035909832264706499 487084553864748397059749)
                ·
                  refine ⟨91328353849640324448703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 487084553864748397059749 91328353849640324448703)
                  ·
                    rfl

theorem cell20_200094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_200094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200094 prefixEnd_200094 := by exact prefixLift 200094
  have htrace : WordTrace (prefixWord ++ tailWord_200094) baseStart_200094 baseEnd_200094 := by
    simpa [prefixWord, tailWord_200094, baseEnd_200094] using wordTrace_append hprefix tailTrace_200094
  have hstable : (prefixWord ++ tailWord_200094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200094).length < 2 ^ (prefixWord ++ tailWord_200094).sum := by decide
  have hdescent : baseEnd_200094 < baseStart_200094 := by decide
  rcases family_descends (prefixWord ++ tailWord_200094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200095 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_200095 : Nat := 118140960795 + 200095 * 2 ^ 59
def prefixEnd_200095 : Nat := 4983230072969 + 3 ^ 40 * 200095 * 2
def baseEnd_200095 : Nat := 91328810276888765415365

theorem tailTrace_200095 : CollatzResearch.WordTrace tailWord_200095 prefixEnd_200095 91328810276888765415365 := by
  unfold tailWord_200095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298064210097463350417739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4865376140064975566945159 7298064210097463350417739)
  ·
    refine ⟨10947096315146195025626609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7298064210097463350417739 10947096315146195025626609)
    ·
      refine ⟨8210322236359646269219957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10947096315146195025626609 8210322236359646269219957)
      ·
        refine ⟨769717709658716837739371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8210322236359646269219957 769717709658716837739371)
        ·
          refine ⟨1154576564488075256609057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769717709658716837739371 1154576564488075256609057)
          ·
            refine ⟨865932423366056442456793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154576564488075256609057 865932423366056442456793)
            ·
              refine ⟨649449317524542331842595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865932423366056442456793 649449317524542331842595)
              ·
                refine ⟨974173976286813497763893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649449317524542331842595 974173976286813497763893)
                ·
                  refine ⟨91328810276888765415365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974173976286813497763893 91328810276888765415365)
                  ·
                    rfl

theorem cell20_200095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_200095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200095 prefixEnd_200095 := by exact prefixLift 200095
  have htrace : WordTrace (prefixWord ++ tailWord_200095) baseStart_200095 baseEnd_200095 := by
    simpa [prefixWord, tailWord_200095, baseEnd_200095] using wordTrace_append hprefix tailTrace_200095
  have hstable : (prefixWord ++ tailWord_200095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200095).length < 2 ^ (prefixWord ++ tailWord_200095).sum := by decide
  have hdescent : baseEnd_200095 < baseStart_200095 := by decide
  rcases family_descends (prefixWord ++ tailWord_200095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200098 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_200098 : Nat := 118140960795 + 200098 * 2 ^ 59
def prefixEnd_200098 : Nat := 4983230072969 + 3 ^ 40 * 200098 * 2
def baseEnd_200098 : Nat := 91330179558634088315353

theorem tailTrace_200098 : CollatzResearch.WordTrace tailWord_200098 prefixEnd_200098 91330179558634088315353 := by
  unfold tailWord_200098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1824543407271648715694237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4865449086057729908517965 1824543407271648715694237)
  ·
    refine ⟨684203777726868268385339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1824543407271648715694237 684203777726868268385339)
    ·
      refine ⟨1026305666590302402578009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684203777726868268385339 1026305666590302402578009)
      ·
        refine ⟨769729249942726801933507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1026305666590302402578009 769729249942726801933507)
        ·
          refine ⟨1154593874914090202900261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769729249942726801933507 1154593874914090202900261)
          ·
            refine ⟨216486351546391913043799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1154593874914090202900261 216486351546391913043799)
            ·
              refine ⟨324729527319587869565699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216486351546391913043799 324729527319587869565699)
              ·
                refine ⟨487094290979381804348549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324729527319587869565699 487094290979381804348549)
                ·
                  refine ⟨91330179558634088315353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 487094290979381804348549 91330179558634088315353)
                  ·
                    rfl

theorem cell20_200098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_200098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200098 prefixEnd_200098 := by exact prefixLift 200098
  have htrace : WordTrace (prefixWord ++ tailWord_200098) baseStart_200098 baseEnd_200098 := by
    simpa [prefixWord, tailWord_200098, baseEnd_200098] using wordTrace_append hprefix tailTrace_200098
  have hstable : (prefixWord ++ tailWord_200098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200098).length < 2 ^ (prefixWord ++ tailWord_200098).sum := by decide
  have hdescent : baseEnd_200098 < baseStart_200098 := by decide
  rcases family_descends (prefixWord ++ tailWord_200098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200153 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 2]
def baseStart_200153 : Nat := 118140960795 + 200153 * 2 ^ 59
def prefixEnd_200153 : Nat := 4983230072969 + 3 ^ 40 * 200153 * 2
def baseEnd_200153 : Nat := 91355283057298341481795

theorem tailTrace_200153 : CollatzResearch.WordTrace tailWord_200153 prefixEnd_200153 91355283057298341481795 := by
  unfold tailWord_200153
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300179643887339256029113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4866786429258226170686075 7300179643887339256029113)
  ·
    refine ⟨5475134732915504442021835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7300179643887339256029113 5475134732915504442021835)
    ·
      refine ⟨8212702099373256663032753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5475134732915504442021835 8212702099373256663032753)
      ·
        refine ⟨6159526574529942497274565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8212702099373256663032753 6159526574529942497274565)
        ·
          refine ⟨1154911232724364218238981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6159526574529942497274565 1154911232724364218238981)
          ·
            refine ⟨216545856135818290919809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1154911232724364218238981 216545856135818290919809)
            ·
              refine ⟨162409392101863718189857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216545856135818290919809 162409392101863718189857)
              ·
                refine ⟨121807044076397788642393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162409392101863718189857 121807044076397788642393)
                ·
                  refine ⟨91355283057298341481795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121807044076397788642393 91355283057298341481795)
                  ·
                    rfl

theorem cell20_200153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_200153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200153 prefixEnd_200153 := by exact prefixLift 200153
  have htrace : WordTrace (prefixWord ++ tailWord_200153) baseStart_200153 baseEnd_200153 := by
    simpa [prefixWord, tailWord_200153, baseEnd_200153] using wordTrace_append hprefix tailTrace_200153
  have hstable : (prefixWord ++ tailWord_200153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200153).length < 2 ^ (prefixWord ++ tailWord_200153).sum := by decide
  have hdescent : baseEnd_200153 < baseStart_200153 := by decide
  rcases family_descends (prefixWord ++ tailWord_200153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200246 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_200246 : Nat := 118140960795 + 200246 * 2 ^ 59
def prefixEnd_200246 : Nat := 4983230072969 + 3 ^ 40 * 200246 * 2
def baseEnd_200246 : Nat := 91397730791403351381415

theorem tailTrace_200246 : CollatzResearch.WordTrace tailWord_200246 prefixEnd_200246 91397730791403351381415 := by
  unfold tailWord_200246
  simp only [CollatzResearch.WordTrace]
  refine ⟨456473227034401008697787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4869047755033610759443061 456473227034401008697787)
  ·
    refine ⟨684709840551601513046681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 456473227034401008697787 684709840551601513046681)
    ·
      refine ⟨513532380413701134785011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 684709840551601513046681 513532380413701134785011)
      ·
        refine ⟨770298570620551702177517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513532380413701134785011 770298570620551702177517)
        ·
          refine ⟨288861963982706888316569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 770298570620551702177517 288861963982706888316569)
          ·
            refine ⟨216646472987030166237427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288861963982706888316569 216646472987030166237427)
            ·
              refine ⟨324969709480545249356141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216646472987030166237427 324969709480545249356141)
              ·
                refine ⟨121863641055204468508553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324969709480545249356141 121863641055204468508553)
                ·
                  refine ⟨91397730791403351381415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121863641055204468508553 91397730791403351381415)
                  ·
                    rfl

theorem cell20_200246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_200246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200246 prefixEnd_200246 := by exact prefixLift 200246
  have htrace : WordTrace (prefixWord ++ tailWord_200246) baseStart_200246 baseEnd_200246 := by
    simpa [prefixWord, tailWord_200246, baseEnd_200246] using wordTrace_append hprefix tailTrace_200246
  have hstable : (prefixWord ++ tailWord_200246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200246).length < 2 ^ (prefixWord ++ tailWord_200246).sum := by decide
  have hdescent : baseEnd_200246 < baseStart_200246 := by decide
  rcases family_descends (prefixWord ++ tailWord_200246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200275 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_200275 : Nat := 118140960795 + 200275 * 2 ^ 59
def prefixEnd_200275 : Nat := 4983230072969 + 3 ^ 40 * 200275 * 2
def baseEnd_200275 : Nat := 91410967181608139414629

theorem tailTrace_200275 : CollatzResearch.WordTrace tailWord_200275 prefixEnd_200275 91410967181608139414629 := by
  unfold tailWord_200275
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304629349445354091970279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4869752899630236061313519 7304629349445354091970279)
  ·
    refine ⟨10956944024168031137955419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304629349445354091970279 10956944024168031137955419)
    ·
      refine ⟨16435416036252046706933129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10956944024168031137955419 16435416036252046706933129)
      ·
        refine ⟨12326562027189035030199847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16435416036252046706933129 12326562027189035030199847)
        ·
          refine ⟨18489843040783552545299771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12326562027189035030199847 18489843040783552545299771)
          ·
            refine ⟨27734764561175328817949657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489843040783552545299771 27734764561175328817949657)
            ·
              refine ⟨20801073420881496613462243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27734764561175328817949657 20801073420881496613462243)
              ·
                refine ⟨31201610131322244920193365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20801073420881496613462243 31201610131322244920193365)
                ·
                  refine ⟨91410967181608139414629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31201610131322244920193365 91410967181608139414629)
                  ·
                    rfl

theorem cell20_200275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_200275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200275 prefixEnd_200275 := by exact prefixLift 200275
  have htrace : WordTrace (prefixWord ++ tailWord_200275) baseStart_200275 baseEnd_200275 := by
    simpa [prefixWord, tailWord_200275, baseEnd_200275] using wordTrace_append hprefix tailTrace_200275
  have hstable : (prefixWord ++ tailWord_200275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200275).length < 2 ^ (prefixWord ++ tailWord_200275).sum := by decide
  have hdescent : baseEnd_200275 < baseStart_200275 := by decide
  rcases family_descends (prefixWord ++ tailWord_200275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200374 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_200374 : Nat := 118140960795 + 200374 * 2 ^ 59
def prefixEnd_200374 : Nat := 4983230072969 + 3 ^ 40 * 200374 * 2
def baseEnd_200374 : Nat := 91456153479203795114225

theorem tailTrace_200374 : CollatzResearch.WordTrace tailWord_200374 prefixEnd_200374 91456153479203795114225 := by
  unfold tailWord_200374
  simp only [CollatzResearch.WordTrace]
  refine ⟨456765011005418374989011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4872160117391129333216117 456765011005418374989011)
  ·
    refine ⟨685147516508127562483517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 456765011005418374989011 685147516508127562483517)
    ·
      refine ⟨256930318690547835931319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 685147516508127562483517 256930318690547835931319)
      ·
        refine ⟨385395478035821753896979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256930318690547835931319 385395478035821753896979)
        ·
          refine ⟨578093217053732630845469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385395478035821753896979 578093217053732630845469)
          ·
            refine ⟨216784956395149736567051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578093217053732630845469 216784956395149736567051)
            ·
              refine ⟨325177434592724604850577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216784956395149736567051 325177434592724604850577)
              ·
                refine ⟨243883075944543453637933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325177434592724604850577 243883075944543453637933)
                ·
                  refine ⟨91456153479203795114225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243883075944543453637933 91456153479203795114225)
                  ·
                    rfl

theorem cell20_200374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_200374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200374 prefixEnd_200374 := by exact prefixLift 200374
  have htrace : WordTrace (prefixWord ++ tailWord_200374) baseStart_200374 baseEnd_200374 := by
    simpa [prefixWord, tailWord_200374, baseEnd_200374] using wordTrace_append hprefix tailTrace_200374
  have hstable : (prefixWord ++ tailWord_200374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200374).length < 2 ^ (prefixWord ++ tailWord_200374).sum := by decide
  have hdescent : baseEnd_200374 < baseStart_200374 := by decide
  rcases family_descends (prefixWord ++ tailWord_200374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200375 : List Nat := [1, 1, 3, 1, 5, 2, 7]
def baseStart_200375 : Nat := 118140960795 + 200375 * 2 ^ 59
def prefixEnd_200375 : Nat := 4983230072969 + 3 ^ 40 * 200375 * 2
def baseEnd_200375 : Nat := 10161845545161359564543

theorem tailTrace_200375 : CollatzResearch.WordTrace tailWord_200375 prefixEnd_200375 10161845545161359564543 := by
  unfold tailWord_200375
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308276649083071170610579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872184432722047447073719 7308276649083071170610579)
  ·
    refine ⟨10962414973624606755915869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7308276649083071170610579 10962414973624606755915869)
    ·
      refine ⟨4110905615109227533468451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10962414973624606755915869 4110905615109227533468451)
      ·
        refine ⟨6166358422663841300202677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110905615109227533468451 6166358422663841300202677)
        ·
          refine ⟨578096102124735121894001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6166358422663841300202677 578096102124735121894001)
          ·
            refine ⟨433572076593551341420501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578096102124735121894001 433572076593551341420501)
            ·
              refine ⟨10161845545161359564543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 433572076593551341420501 10161845545161359564543)
              ·
                rfl

theorem cell20_200375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_200375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200375 prefixEnd_200375 := by exact prefixLift 200375
  have htrace : WordTrace (prefixWord ++ tailWord_200375) baseStart_200375 baseEnd_200375 := by
    simpa [prefixWord, tailWord_200375, baseEnd_200375] using wordTrace_append hprefix tailTrace_200375
  have hstable : (prefixWord ++ tailWord_200375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200375).length < 2 ^ (prefixWord ++ tailWord_200375).sum := by decide
  have hdescent : baseEnd_200375 < baseStart_200375 := by decide
  rcases family_descends (prefixWord ++ tailWord_200375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200378 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_200378 : Nat := 118140960795 + 200378 * 2 ^ 59
def prefixEnd_200378 : Nat := 4983230072969 + 3 ^ 40 * 200378 * 2
def baseEnd_200378 : Nat := 91457979188197558980875

theorem tailTrace_200378 : CollatzResearch.WordTrace tailWord_200378 prefixEnd_200378 91457979188197558980875 := by
  unfold tailWord_200378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827096517018050670742447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4872257378714801788646525 1827096517018050670742447)
  ·
    refine ⟨2740644775527076006113671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1827096517018050670742447 2740644775527076006113671)
    ·
      refine ⟨4110967163290614009170507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740644775527076006113671 4110967163290614009170507)
      ·
        refine ⟨6166450744935921013755761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110967163290614009170507 6166450744935921013755761)
        ·
          refine ⟨4624838058701940760316821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6166450744935921013755761 4624838058701940760316821)
          ·
            refine ⟨216789284001653473139851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4624838058701940760316821 216789284001653473139851)
            ·
              refine ⟨325183926002480209709777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216789284001653473139851 325183926002480209709777)
              ·
                refine ⟨243887944501860157282333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325183926002480209709777 243887944501860157282333)
                ·
                  refine ⟨91457979188197558980875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243887944501860157282333 91457979188197558980875)
                  ·
                    rfl

theorem cell20_200378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_200378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200378 prefixEnd_200378 := by exact prefixLift 200378
  have htrace : WordTrace (prefixWord ++ tailWord_200378) baseStart_200378 baseEnd_200378 := by
    simpa [prefixWord, tailWord_200378, baseEnd_200378] using wordTrace_append hprefix tailTrace_200378
  have hstable : (prefixWord ++ tailWord_200378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200378).length < 2 ^ (prefixWord ++ tailWord_200378).sum := by decide
  have hdescent : baseEnd_200378 < baseStart_200378 := by decide
  rcases family_descends (prefixWord ++ tailWord_200378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200389 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_200389 : Nat := 118140960795 + 200389 * 2 ^ 59
def prefixEnd_200389 : Nat := 4983230072969 + 3 ^ 40 * 200389 * 2
def baseEnd_200389 : Nat := 91462999887930409614163

theorem tailTrace_200389 : CollatzResearch.WordTrace tailWord_200389 prefixEnd_200389 91462999887930409614163 := by
  unfold tailWord_200389
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308787271032351561620221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872524847354901041080147 7308787271032351561620221)
  ·
    refine ⟨2740795226637131835607583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7308787271032351561620221 2740795226637131835607583)
    ·
      refine ⟨4111192839955697753411375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740795226637131835607583 4111192839955697753411375)
      ·
        refine ⟨6166789259933546630117063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4111192839955697753411375 6166789259933546630117063)
        ·
          refine ⟨9250183889900319945175595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166789259933546630117063 9250183889900319945175595)
          ·
            refine ⟨13875275834850479917763393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250183889900319945175595 13875275834850479917763393)
            ·
              refine ⟨10406456876137859938322545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13875275834850479917763393 10406456876137859938322545)
              ·
                refine ⟨7804842657103394953741909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10406456876137859938322545 7804842657103394953741909)
                ·
                  refine ⟨91462999887930409614163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7804842657103394953741909 91462999887930409614163)
                  ·
                    rfl

theorem cell20_200389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_200389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200389 prefixEnd_200389 := by exact prefixLift 200389
  have htrace : WordTrace (prefixWord ++ tailWord_200389) baseStart_200389 baseEnd_200389 := by
    simpa [prefixWord, tailWord_200389, baseEnd_200389] using wordTrace_append hprefix tailTrace_200389
  have hstable : (prefixWord ++ tailWord_200389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200389).length < 2 ^ (prefixWord ++ tailWord_200389).sum := by decide
  have hdescent : baseEnd_200389 < baseStart_200389 := by decide
  rcases family_descends (prefixWord ++ tailWord_200389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200419 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 2]
def baseStart_200419 : Nat := 118140960795 + 200419 * 2 ^ 59
def prefixEnd_200419 : Nat := 4983230072969 + 3 ^ 40 * 200419 * 2
def baseEnd_200419 : Nat := 91476692705383638614041

theorem tailTrace_200419 : CollatzResearch.WordTrace tailWord_200419 prefixEnd_200419 91476692705383638614041 := by
  unfold tailWord_200419
  simp only [CollatzResearch.WordTrace]
  refine ⟨7309881460923666685212311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4873254307282444456808207 7309881460923666685212311)
  ·
    refine ⟨10964822191385500027818467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7309881460923666685212311 10964822191385500027818467)
    ·
      refine ⟨16447233287078250041727701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10964822191385500027818467 16447233287078250041727701)
      ·
        refine ⟨385482030165896485352993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16447233287078250041727701 385482030165896485352993)
        ·
          refine ⟨289111522624422364014745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385482030165896485352993 289111522624422364014745)
          ·
            refine ⟨216833641968316773011059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289111522624422364014745 216833641968316773011059)
            ·
              refine ⟨325250462952475159516589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216833641968316773011059 325250462952475159516589)
              ·
                refine ⟨121968923607178184818721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325250462952475159516589 121968923607178184818721)
                ·
                  refine ⟨91476692705383638614041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121968923607178184818721 91476692705383638614041)
                  ·
                    rfl

theorem cell20_200419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 2].length) (baseStart_200419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200419 prefixEnd_200419 := by exact prefixLift 200419
  have htrace : WordTrace (prefixWord ++ tailWord_200419) baseStart_200419 baseEnd_200419 := by
    simpa [prefixWord, tailWord_200419, baseEnd_200419] using wordTrace_append hprefix tailTrace_200419
  have hstable : (prefixWord ++ tailWord_200419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200419).length < 2 ^ (prefixWord ++ tailWord_200419).sum := by decide
  have hdescent : baseEnd_200419 < baseStart_200419 := by decide
  rcases family_descends (prefixWord ++ tailWord_200419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200420 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_200420 : Nat := 118140960795 + 200420 * 2 ^ 59
def prefixEnd_200420 : Nat := 4983230072969 + 3 ^ 40 * 200420 * 2
def baseEnd_200420 : Nat := 91477149132632079580703

theorem tailTrace_200420 : CollatzResearch.WordTrace tailWord_200420 prefixEnd_200420 91477149132632079580703 := by
  unfold tailWord_200420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654958966960021927999357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4873278622613362570665809 3654958966960021927999357)
  ·
    refine ⟨1370609612610008222999759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3654958966960021927999357 1370609612610008222999759)
    ·
      refine ⟨2055914418915012334499639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370609612610008222999759 2055914418915012334499639)
      ·
        refine ⟨3083871628372518501749459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055914418915012334499639 3083871628372518501749459)
        ·
          refine ⟨4625807442558777752624189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083871628372518501749459 4625807442558777752624189)
          ·
            refine ⟨1734677790959541657234071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4625807442558777752624189 1734677790959541657234071)
            ·
              refine ⟨2602016686439312485851107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734677790959541657234071 2602016686439312485851107)
              ·
                refine ⟨3903025029658968728776661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602016686439312485851107 3903025029658968728776661)
                ·
                  refine ⟨91477149132632079580703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3903025029658968728776661 91477149132632079580703)
                  ·
                    rfl

theorem cell20_200420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_200420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200420 prefixEnd_200420 := by exact prefixLift 200420
  have htrace : WordTrace (prefixWord ++ tailWord_200420) baseStart_200420 baseEnd_200420 := by
    simpa [prefixWord, tailWord_200420, baseEnd_200420] using wordTrace_append hprefix tailTrace_200420
  have hstable : (prefixWord ++ tailWord_200420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200420).length < 2 ^ (prefixWord ++ tailWord_200420).sum := by decide
  have hdescent : baseEnd_200420 < baseStart_200420 := by decide
  rcases family_descends (prefixWord ++ tailWord_200420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200427 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_200427 : Nat := 118140960795 + 200427 * 2 ^ 59
def prefixEnd_200427 : Nat := 4983230072969 + 3 ^ 40 * 200427 * 2
def baseEnd_200427 : Nat := 91480344123371166347341

theorem tailTrace_200427 : CollatzResearch.WordTrace tailWord_200427 prefixEnd_200427 91480344123371166347341 := by
  unfold tailWord_200427
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310173244894684051503535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4873448829929789367669023 7310173244894684051503535)
  ·
    refine ⟨10965259867342026077255303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7310173244894684051503535 10965259867342026077255303)
    ·
      refine ⟨16447889801013039115882955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10965259867342026077255303 16447889801013039115882955)
      ·
        refine ⟨24671834701519558673824433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16447889801013039115882955 24671834701519558673824433)
        ·
          refine ⟨18503876026139669005368325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24671834701519558673824433 18503876026139669005368325)
          ·
            refine ⟨3469476754901187938506561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18503876026139669005368325 3469476754901187938506561)
            ·
              refine ⟨2602107566175890953879921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3469476754901187938506561 2602107566175890953879921)
              ·
                refine ⟨1951580674631918215409941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602107566175890953879921 1951580674631918215409941)
                ·
                  refine ⟨91480344123371166347341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1951580674631918215409941 91480344123371166347341)
                  ·
                    rfl

theorem cell20_200427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_200427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200427 prefixEnd_200427 := by exact prefixLift 200427
  have htrace : WordTrace (prefixWord ++ tailWord_200427) baseStart_200427 baseEnd_200427 := by
    simpa [prefixWord, tailWord_200427, baseEnd_200427] using wordTrace_append hprefix tailTrace_200427
  have hstable : (prefixWord ++ tailWord_200427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200427).length < 2 ^ (prefixWord ++ tailWord_200427).sum := by decide
  have hdescent : baseEnd_200427 < baseStart_200427 := by decide
  rcases family_descends (prefixWord ++ tailWord_200427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200465 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_200465 : Nat := 118140960795 + 200465 * 2 ^ 59
def prefixEnd_200465 : Nat := 4983230072969 + 3 ^ 40 * 200465 * 2
def baseEnd_200465 : Nat := 91497688358811923080519

theorem tailTrace_200465 : CollatzResearch.WordTrace tailWord_200465 prefixEnd_200465 91497688358811923080519 := by
  unfold tailWord_200465
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311559218757016541386849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4874372812504677694257899 7311559218757016541386849)
  ·
    refine ⟨5483669414067762406040137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7311559218757016541386849 5483669414067762406040137)
    ·
      refine ⟨4112752060550821804530103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5483669414067762406040137 4112752060550821804530103)
      ·
        refine ⟨6169128090826232706795155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112752060550821804530103 6169128090826232706795155)
        ·
          refine ⟨9253692136239349060192733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169128090826232706795155 9253692136239349060192733)
          ·
            refine ⟨3470134551089755897572275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9253692136239349060192733 3470134551089755897572275)
            ·
              refine ⟨5205201826634633846358413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470134551089755897572275 5205201826634633846358413)
              ·
                refine ⟨1951950684987987692384405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5205201826634633846358413 1951950684987987692384405)
                ·
                  refine ⟨91497688358811923080519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1951950684987987692384405 91497688358811923080519)
                  ·
                    rfl

theorem cell20_200465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_200465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200465 prefixEnd_200465 := by exact prefixLift 200465
  have htrace : WordTrace (prefixWord ++ tailWord_200465) baseStart_200465 baseEnd_200465 := by
    simpa [prefixWord, tailWord_200465, baseEnd_200465] using wordTrace_append hprefix tailTrace_200465
  have hstable : (prefixWord ++ tailWord_200465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200465).length < 2 ^ (prefixWord ++ tailWord_200465).sum := by decide
  have hdescent : baseEnd_200465 < baseStart_200465 := by decide
  rcases family_descends (prefixWord ++ tailWord_200465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200506 : List Nat := [3, 1, 1, 1, 5, 3, 1, 5]
def baseStart_200506 : Nat := 118140960795 + 200506 * 2 ^ 59
def prefixEnd_200506 : Nat := 4983230072969 + 3 ^ 40 * 200506 * 2
def baseEnd_200506 : Nat := 30505467291999334237895

theorem tailTrace_200506 : CollatzResearch.WordTrace tailWord_200506 prefixEnd_200506 30505467291999334237895 := by
  unfold tailWord_200506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828263652902120135907343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4875369741072320362419581 1828263652902120135907343)
  ·
    refine ⟨2742395479353180203861015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1828263652902120135907343 2742395479353180203861015)
    ·
      refine ⟨4113593219029770305791523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742395479353180203861015 4113593219029770305791523)
      ·
        refine ⟨6170389828544655458687285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4113593219029770305791523 6170389828544655458687285)
        ·
          refine ⟨578474046426061449251933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6170389828544655458687285 578474046426061449251933)
          ·
            refine ⟨216927767409773043469475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578474046426061449251933 216927767409773043469475)
            ·
              refine ⟨325391651114659565204213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216927767409773043469475 325391651114659565204213)
              ·
                refine ⟨30505467291999334237895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325391651114659565204213 30505467291999334237895)
                ·
                  rfl

theorem cell20_200506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_200506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200506 prefixEnd_200506 := by exact prefixLift 200506
  have htrace : WordTrace (prefixWord ++ tailWord_200506) baseStart_200506 baseEnd_200506 := by
    simpa [prefixWord, tailWord_200506, baseEnd_200506] using wordTrace_append hprefix tailTrace_200506
  have hstable : (prefixWord ++ tailWord_200506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200506).length < 2 ^ (prefixWord ++ tailWord_200506).sum := by decide
  have hdescent : baseEnd_200506 < baseStart_200506 := by decide
  rcases family_descends (prefixWord ++ tailWord_200506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200520 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_200520 : Nat := 118140960795 + 200520 * 2 ^ 59
def prefixEnd_200520 : Nat := 4983230072969 + 3 ^ 40 * 200520 * 2
def baseEnd_200520 : Nat := 91522791857476176246961

theorem tailTrace_200520 : CollatzResearch.WordTrace tailWord_200520 prefixEnd_200520 91522791857476176246961 := by
  unfold tailWord_200520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656782616778880467319507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4875710155705173956426009 3656782616778880467319507)
  ·
    refine ⟨5485173925168320700979261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3656782616778880467319507 5485173925168320700979261)
    ·
      refine ⟨2056940221938120262867223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5485173925168320700979261 2056940221938120262867223)
      ·
        refine ⟨3085410332907180394300835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056940221938120262867223 3085410332907180394300835)
        ·
          refine ⟨4628115499360770591451253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085410332907180394300835 4628115499360770591451253)
          ·
            refine ⟨433885828065072242948555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4628115499360770591451253 433885828065072242948555)
            ·
              refine ⟨650828742097608364422833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433885828065072242948555 650828742097608364422833)
              ·
                refine ⟨488121556573206273317125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650828742097608364422833 488121556573206273317125)
                ·
                  refine ⟨91522791857476176246961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488121556573206273317125 91522791857476176246961)
                  ·
                    rfl

theorem cell20_200520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_200520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200520 prefixEnd_200520 := by exact prefixLift 200520
  have htrace : WordTrace (prefixWord ++ tailWord_200520) baseStart_200520 baseEnd_200520 := by
    simpa [prefixWord, tailWord_200520, baseEnd_200520] using wordTrace_append hprefix tailTrace_200520
  have hstable : (prefixWord ++ tailWord_200520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200520).length < 2 ^ (prefixWord ++ tailWord_200520).sum := by decide
  have hdescent : baseEnd_200520 < baseStart_200520 := by decide
  rcases family_descends (prefixWord ++ tailWord_200520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200537 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 2]
def baseStart_200537 : Nat := 118140960795 + 200537 * 2 ^ 59
def prefixEnd_200537 : Nat := 4983230072969 + 3 ^ 40 * 200537 * 2
def baseEnd_200537 : Nat := 91530551120699672680225

theorem tailTrace_200537 : CollatzResearch.WordTrace tailWord_200537 prefixEnd_200537 91530551120699672680225 := by
  unfold tailWord_200537
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314185274496172838007865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4876123516330781892005243 7314185274496172838007865)
  ·
    refine ⟨5485638955872129628505899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7314185274496172838007865 5485638955872129628505899)
    ·
      refine ⟨8228458433808194442758849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5485638955872129628505899 8228458433808194442758849)
      ·
        refine ⟨6171343825356145832069137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8228458433808194442758849 6171343825356145832069137)
        ·
          refine ⟨4628507869017109374051853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6171343825356145832069137 4628507869017109374051853)
          ·
            refine ⟨1735690450881416015269445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4628507869017109374051853 1735690450881416015269445)
            ·
              refine ⟨325441959540265502863021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1735690450881416015269445 325441959540265502863021)
              ·
                refine ⟨122040734827599563573633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325441959540265502863021 122040734827599563573633)
                ·
                  refine ⟨91530551120699672680225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122040734827599563573633 91530551120699672680225)
                  ·
                    rfl

theorem cell20_200537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_200537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200537 prefixEnd_200537 := by exact prefixLift 200537
  have htrace : WordTrace (prefixWord ++ tailWord_200537) baseStart_200537 baseEnd_200537 := by
    simpa [prefixWord, tailWord_200537, baseEnd_200537] using wordTrace_append hprefix tailTrace_200537
  have hstable : (prefixWord ++ tailWord_200537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200537).length < 2 ^ (prefixWord ++ tailWord_200537).sum := by decide
  have hdescent : baseEnd_200537 < baseStart_200537 := by decide
  rcases family_descends (prefixWord ++ tailWord_200537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200547 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 3]
def baseStart_200547 : Nat := 118140960795 + 200547 * 2 ^ 59
def prefixEnd_200547 : Nat := 4983230072969 + 3 ^ 40 * 200547 * 2
def baseEnd_200547 : Nat := 91535115393184082346851

theorem tailTrace_200547 : CollatzResearch.WordTrace tailWord_200547 prefixEnd_200547 91535115393184082346851 := by
  unfold tailWord_200547
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314550004459944545871895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4876366669639963030581263 7314550004459944545871895)
  ·
    refine ⟨10971825006689916818807843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314550004459944545871895 10971825006689916818807843)
    ·
      refine ⟨16457737510034875228211765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10971825006689916818807843 16457737510034875228211765)
      ·
        refine ⟨1542912891565769552644853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16457737510034875228211765 1542912891565769552644853)
        ·
          refine ⟨144648083584290895560455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1542912891565769552644853 144648083584290895560455)
          ·
            refine ⟨216972125376436343340683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144648083584290895560455 216972125376436343340683)
            ·
              refine ⟨325458188064654515011025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216972125376436343340683 325458188064654515011025)
              ·
                refine ⟨244093641048490886258269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325458188064654515011025 244093641048490886258269)
                ·
                  refine ⟨91535115393184082346851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244093641048490886258269 91535115393184082346851)
                  ·
                    rfl

theorem cell20_200547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 3].length) (baseStart_200547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200547 prefixEnd_200547 := by exact prefixLift 200547
  have htrace : WordTrace (prefixWord ++ tailWord_200547) baseStart_200547 baseEnd_200547 := by
    simpa [prefixWord, tailWord_200547, baseEnd_200547] using wordTrace_append hprefix tailTrace_200547
  have hstable : (prefixWord ++ tailWord_200547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200547).length < 2 ^ (prefixWord ++ tailWord_200547).sum := by decide
  have hdescent : baseEnd_200547 < baseStart_200547 := by decide
  rcases family_descends (prefixWord ++ tailWord_200547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200554 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_200554 : Nat := 118140960795 + 200554 * 2 ^ 59
def prefixEnd_200554 : Nat := 4983230072969 + 3 ^ 40 * 200554 * 2
def baseEnd_200554 : Nat := 91538310383923169113489

theorem tailTrace_200554 : CollatzResearch.WordTrace tailWord_200554 prefixEnd_200554 91538310383923169113489 := by
  unfold tailWord_200554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828701328858646185344179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4876536876956389827584477 1828701328858646185344179)
  ·
    refine ⟨2743051993287969278016269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1828701328858646185344179 2743051993287969278016269)
    ·
      refine ⟨1028644497482988479256101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2743051993287969278016269 1028644497482988479256101)
      ·
        refine ⟨192870843278060339860519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1028644497482988479256101 192870843278060339860519)
        ·
          refine ⟨289306264917090509790779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192870843278060339860519 289306264917090509790779)
          ·
            refine ⟨433959397375635764686169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289306264917090509790779 433959397375635764686169)
            ·
              refine ⟨325469548031726823514627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433959397375635764686169 325469548031726823514627)
              ·
                refine ⟨488204322047590235271941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325469548031726823514627 488204322047590235271941)
                ·
                  refine ⟨91538310383923169113489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488204322047590235271941 91538310383923169113489)
                  ·
                    rfl

theorem cell20_200554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_200554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200554 prefixEnd_200554 := by exact prefixLift 200554
  have htrace : WordTrace (prefixWord ++ tailWord_200554) baseStart_200554 baseEnd_200554 := by
    simpa [prefixWord, tailWord_200554, baseEnd_200554] using wordTrace_append hprefix tailTrace_200554
  have hstable : (prefixWord ++ tailWord_200554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200554).length < 2 ^ (prefixWord ++ tailWord_200554).sum := by decide
  have hdescent : baseEnd_200554 < baseStart_200554 := by decide
  rcases family_descends (prefixWord ++ tailWord_200554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200565 : List Nat := [1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_200565 : Nat := 118140960795 + 200565 * 2 ^ 59
def prefixEnd_200565 : Nat := 4983230072969 + 3 ^ 40 * 200565 * 2
def baseEnd_200565 : Nat := 30514443694552006582259

theorem tailTrace_200565 : CollatzResearch.WordTrace tailWord_200565 prefixEnd_200565 30514443694552006582259 := by
  unfold tailWord_200565
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315206518394733620027149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4876804345596489080018099 7315206518394733620027149)
  ·
    refine ⟨2743202444398025107510181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7315206518394733620027149 2743202444398025107510181)
    ·
      refine ⟨514350458324629707658159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2743202444398025107510181 514350458324629707658159)
      ·
        refine ⟨771525687486944561487239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514350458324629707658159 771525687486944561487239)
        ·
          refine ⟨1157288531230416842230859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771525687486944561487239 1157288531230416842230859)
          ·
            refine ⟨1735932796845625263346289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157288531230416842230859 1735932796845625263346289)
            ·
              refine ⟨1301949597634218947509717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735932796845625263346289 1301949597634218947509717)
              ·
                refine ⟨30514443694552006582259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1301949597634218947509717 30514443694552006582259)
                ·
                  rfl

theorem cell20_200565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_200565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200565 prefixEnd_200565 := by exact prefixLift 200565
  have htrace : WordTrace (prefixWord ++ tailWord_200565) baseStart_200565 baseEnd_200565 := by
    simpa [prefixWord, tailWord_200565, baseEnd_200565] using wordTrace_append hprefix tailTrace_200565
  have hstable : (prefixWord ++ tailWord_200565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200565).length < 2 ^ (prefixWord ++ tailWord_200565).sum := by decide
  have hdescent : baseEnd_200565 < baseStart_200565 := by decide
  rcases family_descends (prefixWord ++ tailWord_200565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200609 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 2]
def baseStart_200609 : Nat := 118140960795 + 200609 * 2 ^ 59
def prefixEnd_200609 : Nat := 4983230072969 + 3 ^ 40 * 200609 * 2
def baseEnd_200609 : Nat := 91563413882587422279931

theorem tailTrace_200609 : CollatzResearch.WordTrace tailWord_200609 prefixEnd_200609 91563413882587422279931 := by
  unfold tailWord_200609
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316811330235329134628881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4877874220156886089752587 7316811330235329134628881)
  ·
    refine ⟨5487608497676496850971661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7316811330235329134628881 5487608497676496850971661)
    ·
      refine ⟨2057853186628686319114373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5487608497676496850971661 2057853186628686319114373)
      ·
        refine ⟨385847472492878684833945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2057853186628686319114373 385847472492878684833945)
        ·
          refine ⟨289385604369659013625459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385847472492878684833945 289385604369659013625459)
          ·
            refine ⟨434078406554488520438189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289385604369659013625459 434078406554488520438189)
            ·
              refine ⟨162779402457933195164321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434078406554488520438189 162779402457933195164321)
              ·
                refine ⟨122084551843449896373241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162779402457933195164321 122084551843449896373241)
                ·
                  refine ⟨91563413882587422279931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122084551843449896373241 91563413882587422279931)
                  ·
                    rfl

theorem cell20_200609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_200609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200609 prefixEnd_200609 := by exact prefixLift 200609
  have htrace : WordTrace (prefixWord ++ tailWord_200609) baseStart_200609 baseEnd_200609 := by
    simpa [prefixWord, tailWord_200609, baseEnd_200609] using wordTrace_append hprefix tailTrace_200609
  have hstable : (prefixWord ++ tailWord_200609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200609).length < 2 ^ (prefixWord ++ tailWord_200609).sum := by decide
  have hdescent : baseEnd_200609 < baseStart_200609 := by decide
  rcases family_descends (prefixWord ++ tailWord_200609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200617 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_200617 : Nat := 118140960795 + 200617 * 2 ^ 59
def prefixEnd_200617 : Nat := 4983230072969 + 3 ^ 40 * 200617 * 2
def baseEnd_200617 : Nat := 91567065300574950013231

theorem tailTrace_200617 : CollatzResearch.WordTrace tailWord_200617 prefixEnd_200617 91567065300574950013231 := by
  unfold tailWord_200617
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317103114206346500920105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4878068742804231000613403 7317103114206346500920105)
  ·
    refine ⟨5487827335654759875690079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7317103114206346500920105 5487827335654759875690079)
    ·
      refine ⟨8231741003482139813535119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487827335654759875690079 8231741003482139813535119)
      ·
        refine ⟨12347611505223209720302679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231741003482139813535119 12347611505223209720302679)
        ·
          refine ⟨18521417257834814580454019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347611505223209720302679 18521417257834814580454019)
          ·
            refine ⟨27782125886752221870681029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18521417257834814580454019 27782125886752221870681029)
            ·
              refine ⟨5209148603766041600752693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27782125886752221870681029 5209148603766041600752693)
              ·
                refine ⟨488357681603066400070565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5209148603766041600752693 488357681603066400070565)
                ·
                  refine ⟨91567065300574950013231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488357681603066400070565 91567065300574950013231)
                  ·
                    rfl

theorem cell20_200617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_200617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200617 prefixEnd_200617 := by exact prefixLift 200617
  have htrace : WordTrace (prefixWord ++ tailWord_200617) baseStart_200617 baseEnd_200617 := by
    simpa [prefixWord, tailWord_200617, baseEnd_200617] using wordTrace_append hprefix tailTrace_200617
  have hstable : (prefixWord ++ tailWord_200617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200617).length < 2 ^ (prefixWord ++ tailWord_200617).sum := by decide
  have hdescent : baseEnd_200617 < baseStart_200617 := by decide
  rcases family_descends (prefixWord ++ tailWord_200617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200658 : List Nat := [3, 2, 2, 3, 3, 7]
def baseStart_200658 : Nat := 118140960795 + 200658 * 2 ^ 59
def prefixEnd_200658 : Nat := 4983230072969 + 3 ^ 40 * 200658 * 2
def baseEnd_200658 : Nat := 3392065882139297394311

theorem tailTrace_200658 : CollatzResearch.WordTrace tailWord_200658 prefixEnd_200658 3392065882139297394311 := by
  unfold tailWord_200658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829649626764452625790657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4879065671371873668775085 1829649626764452625790657)
  ·
    refine ⟨1372237220073339469342993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1829649626764452625790657 1372237220073339469342993)
    ·
      refine ⟨1029177915055004602007245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1372237220073339469342993 1029177915055004602007245)
      ·
        refine ⟨385941718145626725752717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1029177915055004602007245 385941718145626725752717)
        ·
          refine ⟨144728144304610022157269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385941718145626725752717 144728144304610022157269)
          ·
            refine ⟨3392065882139297394311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 144728144304610022157269 3392065882139297394311)
            ·
              rfl

theorem cell20_200658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 7].length) (baseStart_200658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200658 prefixEnd_200658 := by exact prefixLift 200658
  have htrace : WordTrace (prefixWord ++ tailWord_200658) baseStart_200658 baseEnd_200658 := by
    simpa [prefixWord, tailWord_200658, baseEnd_200658] using wordTrace_append hprefix tailTrace_200658
  have hstable : (prefixWord ++ tailWord_200658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200658).length < 2 ^ (prefixWord ++ tailWord_200658).sum := by decide
  have hdescent : baseEnd_200658 < baseStart_200658 := by decide
  rcases family_descends (prefixWord ++ tailWord_200658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200727 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_200727 : Nat := 118140960795 + 200727 * 2 ^ 59
def prefixEnd_200727 : Nat := 4983230072969 + 3 ^ 40 * 200727 * 2
def baseEnd_200727 : Nat := 91617272297903456346115

theorem tailTrace_200727 : CollatzResearch.WordTrace tailWord_200727 prefixEnd_200727 91617272297903456346115 := by
  unfold tailWord_200727
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321115143807835287424435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4880743429205223524949623 7321115143807835287424435)
  ·
    refine ⟨10981672715711752931136653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321115143807835287424435 10981672715711752931136653)
    ·
      refine ⟨4118127268391907349176245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10981672715711752931136653 4118127268391907349176245)
      ·
        refine ⟨386074431411741313985273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4118127268391907349176245 386074431411741313985273)
        ·
          refine ⟨289555823558805985488955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386074431411741313985273 289555823558805985488955)
          ·
            refine ⟨434333735338208978233433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289555823558805985488955 434333735338208978233433)
            ·
              refine ⟨325750301503656733675075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434333735338208978233433 325750301503656733675075)
              ·
                refine ⟨488625452255485100512613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325750301503656733675075 488625452255485100512613)
                ·
                  refine ⟨91617272297903456346115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488625452255485100512613 91617272297903456346115)
                  ·
                    rfl

theorem cell20_200727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_200727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200727 prefixEnd_200727 := by exact prefixLift 200727
  have htrace : WordTrace (prefixWord ++ tailWord_200727) baseStart_200727 baseEnd_200727 := by
    simpa [prefixWord, tailWord_200727, baseEnd_200727] using wordTrace_append hprefix tailTrace_200727
  have hstable : (prefixWord ++ tailWord_200727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200727).length < 2 ^ (prefixWord ++ tailWord_200727).sum := by decide
  have hdescent : baseEnd_200727 < baseStart_200727 := by decide
  rcases family_descends (prefixWord ++ tailWord_200727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200755 : List Nat := [1, 1, 1, 2, 4, 1, 6, 4]
def baseStart_200755 : Nat := 118140960795 + 200755 * 2 ^ 59
def prefixEnd_200755 : Nat := 4983230072969 + 3 ^ 40 * 200755 * 2
def baseEnd_200755 : Nat := 30543350753619934470889

theorem tailTrace_200755 : CollatzResearch.WordTrace tailWord_200755 prefixEnd_200755 30543350753619934470889 := by
  unfold tailWord_200755
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322136387706396069443719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4881424258470930712962479 7322136387706396069443719)
  ·
    refine ⟨10983204581559594104165579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7322136387706396069443719 10983204581559594104165579)
    ·
      refine ⟨16474806872339391156248369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10983204581559594104165579 16474806872339391156248369)
      ·
        refine ⟨12356105154254543367186277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16474806872339391156248369 12356105154254543367186277)
        ·
          refine ⟨2316769716422726881347427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12356105154254543367186277 2316769716422726881347427)
          ·
            refine ⟨3475154574634090322021141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316769716422726881347427 3475154574634090322021141)
            ·
              refine ⟨162897870685972983844741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3475154574634090322021141 162897870685972983844741)
              ·
                refine ⟨30543350753619934470889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162897870685972983844741 30543350753619934470889)
                ·
                  rfl

theorem cell20_200755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_200755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200755 prefixEnd_200755 := by exact prefixLift 200755
  have htrace : WordTrace (prefixWord ++ tailWord_200755) baseStart_200755 baseEnd_200755 := by
    simpa [prefixWord, tailWord_200755, baseEnd_200755] using wordTrace_append hprefix tailTrace_200755
  have hstable : (prefixWord ++ tailWord_200755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200755).length < 2 ^ (prefixWord ++ tailWord_200755).sum := by decide
  have hdescent : baseEnd_200755 < baseStart_200755 := by decide
  rcases family_descends (prefixWord ++ tailWord_200755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200761 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 2]
def baseStart_200761 : Nat := 118140960795 + 200761 * 2 ^ 59
def prefixEnd_200761 : Nat := 4983230072969 + 3 ^ 40 * 200761 * 2
def baseEnd_200761 : Nat := 91632790824350449212643

theorem tailTrace_200761 : CollatzResearch.WordTrace tailWord_200761 prefixEnd_200761 91632790824350449212643 := by
  unfold tailWord_200761
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322355225684659094162137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4881570150456439396108091 7322355225684659094162137)
  ·
    refine ⟨5491766419263494320621603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7322355225684659094162137 5491766419263494320621603)
    ·
      refine ⟨8237649628895241480932405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5491766419263494320621603 8237649628895241480932405)
      ·
        refine ⟨772279652708928888837413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8237649628895241480932405 772279652708928888837413)
        ·
          refine ⟨144802434882924166657015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 772279652708928888837413 144802434882924166657015)
          ·
            refine ⟨217203652324386249985523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144802434882924166657015 217203652324386249985523)
            ·
              refine ⟨325805478486579374978285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217203652324386249985523 325805478486579374978285)
              ·
                refine ⟨122177054432467265616857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325805478486579374978285 122177054432467265616857)
                ·
                  refine ⟨91632790824350449212643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122177054432467265616857 91632790824350449212643)
                  ·
                    rfl

theorem cell20_200761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_200761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200761 prefixEnd_200761 := by exact prefixLift 200761
  have htrace : WordTrace (prefixWord ++ tailWord_200761) baseStart_200761 baseEnd_200761 := by
    simpa [prefixWord, tailWord_200761, baseEnd_200761] using wordTrace_append hprefix tailTrace_200761
  have hstable : (prefixWord ++ tailWord_200761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200761).length < 2 ^ (prefixWord ++ tailWord_200761).sum := by decide
  have hdescent : baseEnd_200761 < baseStart_200761 := by decide
  rcases family_descends (prefixWord ++ tailWord_200761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200782 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_200782 : Nat := 118140960795 + 200782 * 2 ^ 59
def prefixEnd_200782 : Nat := 4983230072969 + 3 ^ 40 * 200782 * 2
def baseEnd_200782 : Nat := 91642375796567709512557

theorem tailTrace_200782 : CollatzResearch.WordTrace tailWord_200782 prefixEnd_200782 91642375796567709512557 := by
  unfold tailWord_200782
  simp only [CollatzResearch.WordTrace]
  refine ⟨915390144826072460084575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4882080772405719787117733 915390144826072460084575)
  ·
    refine ⟨1373085217239108690126863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915390144826072460084575 1373085217239108690126863)
    ·
      refine ⟨2059627825858663035190295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373085217239108690126863 2059627825858663035190295)
      ·
        refine ⟨3089441738787994552785443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059627825858663035190295 3089441738787994552785443)
        ·
          refine ⟨4634162608181991829178165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089441738787994552785443 4634162608181991829178165)
          ·
            refine ⟨434452744517061733985453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4634162608181991829178165 434452744517061733985453)
            ·
              refine ⟨162919779193898150244545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434452744517061733985453 162919779193898150244545)
              ·
                refine ⟨122189834395423612683409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162919779193898150244545 122189834395423612683409)
                ·
                  refine ⟨91642375796567709512557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122189834395423612683409 91642375796567709512557)
                  ·
                    rfl

theorem cell20_200782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_200782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200782 prefixEnd_200782 := by exact prefixLift 200782
  have htrace : WordTrace (prefixWord ++ tailWord_200782) baseStart_200782 baseEnd_200782 := by
    simpa [prefixWord, tailWord_200782, baseEnd_200782] using wordTrace_append hprefix tailTrace_200782
  have hstable : (prefixWord ++ tailWord_200782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200782).length < 2 ^ (prefixWord ++ tailWord_200782).sum := by decide
  have hdescent : baseEnd_200782 < baseStart_200782 := by decide
  rcases family_descends (prefixWord ++ tailWord_200782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200796 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_200796 : Nat := 118140960795 + 200796 * 2 ^ 59
def prefixEnd_200796 : Nat := 4983230072969 + 3 ^ 40 * 200796 * 2
def baseEnd_200796 : Nat := 91648765778045883045833

theorem tailTrace_200796 : CollatzResearch.WordTrace tailWord_200796 prefixEnd_200796 91648765778045883045833 := by
  unfold tailWord_200796
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661815890278930035843121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4882421187038573381124161 3661815890278930035843121)
  ·
    refine ⟨2746361917709197526882341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3661815890278930035843121 2746361917709197526882341)
    ·
      refine ⟨514942859570474536290439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2746361917709197526882341 514942859570474536290439)
      ·
        refine ⟨772414289355711804435659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514942859570474536290439 772414289355711804435659)
        ·
          refine ⟨1158621434033567706653489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772414289355711804435659 1158621434033567706653489)
          ·
            refine ⟨868966075525175779990117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158621434033567706653489 868966075525175779990117)
            ·
              refine ⟨162931139160970458748147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 868966075525175779990117 162931139160970458748147)
              ·
                refine ⟨244396708741455688122221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162931139160970458748147 244396708741455688122221)
                ·
                  refine ⟨91648765778045883045833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244396708741455688122221 91648765778045883045833)
                  ·
                    rfl

theorem cell20_200796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_200796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200796 prefixEnd_200796 := by exact prefixLift 200796
  have htrace : WordTrace (prefixWord ++ tailWord_200796) baseStart_200796 baseEnd_200796 := by
    simpa [prefixWord, tailWord_200796, baseEnd_200796] using wordTrace_append hprefix tailTrace_200796
  have hstable : (prefixWord ++ tailWord_200796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200796).length < 2 ^ (prefixWord ++ tailWord_200796).sum := by decide
  have hdescent : baseEnd_200796 < baseStart_200796 := by decide
  rcases family_descends (prefixWord ++ tailWord_200796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200807 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_200807 : Nat := 118140960795 + 200807 * 2 ^ 59
def prefixEnd_200807 : Nat := 4983230072969 + 3 ^ 40 * 200807 * 2
def baseEnd_200807 : Nat := 91653786477778733679121

theorem tailTrace_200807 : CollatzResearch.WordTrace tailWord_200807 prefixEnd_200807 91653786477778733679121 := by
  unfold tailWord_200807
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324032983518008950336675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4882688655678672633557783 7324032983518008950336675)
  ·
    refine ⟨10986049475277013425505013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7324032983518008950336675 10986049475277013425505013)
    ·
      refine ⟨1029942138307220008641095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10986049475277013425505013 1029942138307220008641095)
      ·
        refine ⟨1544913207460830012961643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029942138307220008641095 1544913207460830012961643)
        ·
          refine ⟨2317369811191245019442465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544913207460830012961643 2317369811191245019442465)
          ·
            refine ⟨1738027358393433764581849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2317369811191245019442465 1738027358393433764581849)
            ·
              refine ⟨1303520518795075323436387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738027358393433764581849 1303520518795075323436387)
              ·
                refine ⟨1955280778192612985154581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303520518795075323436387 1955280778192612985154581)
                ·
                  refine ⟨91653786477778733679121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1955280778192612985154581 91653786477778733679121)
                  ·
                    rfl

theorem cell20_200807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_200807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200807 prefixEnd_200807 := by exact prefixLift 200807
  have htrace : WordTrace (prefixWord ++ tailWord_200807) baseStart_200807 baseEnd_200807 := by
    simpa [prefixWord, tailWord_200807, baseEnd_200807] using wordTrace_append hprefix tailTrace_200807
  have hstable : (prefixWord ++ tailWord_200807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200807).length < 2 ^ (prefixWord ++ tailWord_200807).sum := by decide
  have hdescent : baseEnd_200807 < baseStart_200807 := by decide
  rcases family_descends (prefixWord ++ tailWord_200807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200824 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 2]
def baseStart_200824 : Nat := 118140960795 + 200824 * 2 ^ 59
def prefixEnd_200824 : Nat := 4983230072969 + 3 ^ 40 * 200824 * 2
def baseEnd_200824 : Nat := 91661545741002230112385

theorem tailTrace_200824 : CollatzResearch.WordTrace tailWord_200824 prefixEnd_200824 91661545741002230112385 := by
  unfold tailWord_200824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662326512228210426852763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4883102016304280569137017 3662326512228210426852763)
  ·
    refine ⟨5493489768342315640279145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3662326512228210426852763 5493489768342315640279145)
    ·
      refine ⟨4120117326256736730209359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5493489768342315640279145 4120117326256736730209359)
      ·
        refine ⟨6180175989385105095314039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120117326256736730209359 6180175989385105095314039)
        ·
          refine ⟨9270263984077657642971059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6180175989385105095314039 9270263984077657642971059)
          ·
            refine ⟨13905395976116486464456589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9270263984077657642971059 13905395976116486464456589)
            ·
              refine ⟨5214523491043682424171221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13905395976116486464456589 5214523491043682424171221)
              ·
                refine ⟨122215394321336306816513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5214523491043682424171221 122215394321336306816513)
                ·
                  refine ⟨91661545741002230112385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122215394321336306816513 91661545741002230112385)
                  ·
                    rfl

theorem cell20_200824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_200824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200824 prefixEnd_200824 := by exact prefixLift 200824
  have htrace : WordTrace (prefixWord ++ tailWord_200824) baseStart_200824 baseEnd_200824 := by
    simpa [prefixWord, tailWord_200824, baseEnd_200824] using wordTrace_append hprefix tailTrace_200824
  have hstable : (prefixWord ++ tailWord_200824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200824).length < 2 ^ (prefixWord ++ tailWord_200824).sum := by decide
  have hdescent : baseEnd_200824 < baseStart_200824 := by decide
  rcases family_descends (prefixWord ++ tailWord_200824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200854 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_200854 : Nat := 118140960795 + 200854 * 2 ^ 59
def prefixEnd_200854 : Nat := 4983230072969 + 3 ^ 40 * 200854 * 2
def baseEnd_200854 : Nat := 91675238558455459112263

theorem tailTrace_200854 : CollatzResearch.WordTrace tailWord_200854 prefixEnd_200854 91675238558455459112263 := by
  unfold tailWord_200854
  simp only [CollatzResearch.WordTrace]
  refine ⟨457859200896733498581101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4883831476231823984865077 457859200896733498581101)
  ·
    refine ⟨171697200336275061967913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 457859200896733498581101 171697200336275061967913)
    ·
      refine ⟨128772900252206296475935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171697200336275061967913 128772900252206296475935)
      ·
        refine ⟨193159350378309444713903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128772900252206296475935 193159350378309444713903)
        ·
          refine ⟨289739025567464167070855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193159350378309444713903 289739025567464167070855)
          ·
            refine ⟨434608538351196250606283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289739025567464167070855 434608538351196250606283)
            ·
              refine ⟨651912807526794375909425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434608538351196250606283 651912807526794375909425)
              ·
                refine ⟨488934605645095781932069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651912807526794375909425 488934605645095781932069)
                ·
                  refine ⟨91675238558455459112263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488934605645095781932069 91675238558455459112263)
                  ·
                    rfl

theorem cell20_200854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_200854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200854 prefixEnd_200854 := by exact prefixLift 200854
  have htrace : WordTrace (prefixWord ++ tailWord_200854) baseStart_200854 baseEnd_200854 := by
    simpa [prefixWord, tailWord_200854, baseEnd_200854] using wordTrace_append hprefix tailTrace_200854
  have hstable : (prefixWord ++ tailWord_200854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200854).length < 2 ^ (prefixWord ++ tailWord_200854).sum := by decide
  have hdescent : baseEnd_200854 < baseStart_200854 := by decide
  rcases family_descends (prefixWord ++ tailWord_200854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200869 : List Nat := [1, 3, 1, 2, 1, 3, 5, 4]
def baseStart_200869 : Nat := 118140960795 + 200869 * 2 ^ 59
def prefixEnd_200869 : Nat := 4983230072969 + 3 ^ 40 * 200869 * 2
def baseEnd_200869 : Nat := 30560694989060691204067

theorem tailTrace_200869 : CollatzResearch.WordTrace tailWord_200869 prefixEnd_200869 30560694989060691204067 := by
  unfold tailWord_200869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7326294309293393539093661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4884196206195595692729107 7326294309293393539093661)
  ·
    refine ⟨2747360365985022577160123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7326294309293393539093661 2747360365985022577160123)
    ·
      refine ⟨4121040548977533865740185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747360365985022577160123 4121040548977533865740185)
      ·
        refine ⟨3090780411733150399305139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4121040548977533865740185 3090780411733150399305139)
        ·
          refine ⟨4636170617599725598957709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090780411733150399305139 4636170617599725598957709)
          ·
            refine ⟨1738563981599897099609141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4636170617599725598957709 1738563981599897099609141)
            ·
              refine ⟨162990373274990353088357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1738563981599897099609141 162990373274990353088357)
              ·
                refine ⟨30560694989060691204067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162990373274990353088357 30560694989060691204067)
                ·
                  rfl

theorem cell20_200869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_200869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200869 prefixEnd_200869 := by exact prefixLift 200869
  have htrace : WordTrace (prefixWord ++ tailWord_200869) baseStart_200869 baseEnd_200869 := by
    simpa [prefixWord, tailWord_200869, baseEnd_200869] using wordTrace_append hprefix tailTrace_200869
  have hstable : (prefixWord ++ tailWord_200869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200869).length < 2 ^ (prefixWord ++ tailWord_200869).sum := by decide
  have hdescent : baseEnd_200869 < baseStart_200869 := by decide
  rcases family_descends (prefixWord ++ tailWord_200869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200900 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_200900 : Nat := 118140960795 + 200900 * 2 ^ 59
def prefixEnd_200900 : Nat := 4983230072969 + 3 ^ 40 * 200900 * 2
def baseEnd_200900 : Nat := 91696234211883743578741

theorem tailTrace_200900 : CollatzResearch.WordTrace tailWord_200900 prefixEnd_200900 91696234211883743578741 := by
  unfold tailWord_200900
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663712486090542916736077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4884949981454057222314769 3663712486090542916736077)
  ·
    refine ⟨1373892182283953593776029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3663712486090542916736077 1373892182283953593776029)
    ·
      refine ⟨515209568356482597666011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1373892182283953593776029 515209568356482597666011)
      ·
        refine ⟨772814352534723896499017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515209568356482597666011 772814352534723896499017)
        ·
          refine ⟨579610764401042922374263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772814352534723896499017 579610764401042922374263)
          ·
            refine ⟨869416146601564383561395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579610764401042922374263 869416146601564383561395)
            ·
              refine ⟨1304124219902346575342093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869416146601564383561395 1304124219902346575342093)
              ·
                refine ⟨489046582463379965753285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304124219902346575342093 489046582463379965753285)
                ·
                  refine ⟨91696234211883743578741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489046582463379965753285 91696234211883743578741)
                  ·
                    rfl

theorem cell20_200900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_200900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200900 prefixEnd_200900 := by exact prefixLift 200900
  have htrace : WordTrace (prefixWord ++ tailWord_200900) baseStart_200900 baseEnd_200900 := by
    simpa [prefixWord, tailWord_200900, baseEnd_200900] using wordTrace_append hprefix tailTrace_200900
  have hstable : (prefixWord ++ tailWord_200900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200900).length < 2 ^ (prefixWord ++ tailWord_200900).sum := by decide
  have hdescent : baseEnd_200900 < baseStart_200900 := by decide
  rcases family_descends (prefixWord ++ tailWord_200900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200910 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_200910 : Nat := 118140960795 + 200910 * 2 ^ 59
def prefixEnd_200910 : Nat := 4983230072969 + 3 ^ 40 * 200910 * 2
def baseEnd_200910 : Nat := 91700798484368153245367

theorem tailTrace_200910 : CollatzResearch.WordTrace tailWord_200910 prefixEnd_200910 91700798484368153245367 := by
  unfold tailWord_200910
  simp only [CollatzResearch.WordTrace]
  refine ⟨915973712768107192667023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4885193134763238360890789 915973712768107192667023)
  ·
    refine ⟨1373960569152160789000535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915973712768107192667023 1373960569152160789000535)
    ·
      refine ⟨2060940853728241183500803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373960569152160789000535 2060940853728241183500803)
      ·
        refine ⟨3091411280592361775251205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060940853728241183500803 3091411280592361775251205)
        ·
          refine ⟨579639615111067832859601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3091411280592361775251205 579639615111067832859601)
          ·
            refine ⟨434729711333300874644701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579639615111067832859601 434729711333300874644701)
            ·
              refine ⟨163023641749987827991763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434729711333300874644701 163023641749987827991763)
              ·
                refine ⟨244535462624981741987645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163023641749987827991763 244535462624981741987645)
                ·
                  refine ⟨91700798484368153245367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244535462624981741987645 91700798484368153245367)
                  ·
                    rfl

theorem cell20_200910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_200910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200910 prefixEnd_200910 := by exact prefixLift 200910
  have htrace : WordTrace (prefixWord ++ tailWord_200910) baseStart_200910 baseEnd_200910 := by
    simpa [prefixWord, tailWord_200910, baseEnd_200910] using wordTrace_append hprefix tailTrace_200910
  have hstable : (prefixWord ++ tailWord_200910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200910).length < 2 ^ (prefixWord ++ tailWord_200910).sum := by decide
  have hdescent : baseEnd_200910 < baseStart_200910 := by decide
  rcases family_descends (prefixWord ++ tailWord_200910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200921 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_200921 : Nat := 118140960795 + 200921 * 2 ^ 59
def prefixEnd_200921 : Nat := 4983230072969 + 3 ^ 40 * 200921 * 2
def baseEnd_200921 : Nat := 91705819184101003878655

theorem tailTrace_200921 : CollatzResearch.WordTrace tailWord_200921 prefixEnd_200921 91705819184101003878655 := by
  unfold tailWord_200921
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328190905105006419986617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4885460603403337613324411 7328190905105006419986617)
  ·
    refine ⟨5496143178828754814989963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7328190905105006419986617 5496143178828754814989963)
    ·
      refine ⟨8244214768243132222484945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5496143178828754814989963 8244214768243132222484945)
      ·
        refine ⟨6183161076182349166863709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8244214768243132222484945 6183161076182349166863709)
        ·
          refine ⟨2318685403568380937573891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6183161076182349166863709 2318685403568380937573891)
          ·
            refine ⟨3478028105352571406360837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318685403568380937573891 3478028105352571406360837)
            ·
              refine ⟨652130269753607138692657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3478028105352571406360837 652130269753607138692657)
              ·
                refine ⟨489097702315205354019493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652130269753607138692657 489097702315205354019493)
                ·
                  refine ⟨91705819184101003878655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489097702315205354019493 91705819184101003878655)
                  ·
                    rfl

theorem cell20_200921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_200921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200921 prefixEnd_200921 := by exact prefixLift 200921
  have htrace : WordTrace (prefixWord ++ tailWord_200921) baseStart_200921 baseEnd_200921 := by
    simpa [prefixWord, tailWord_200921, baseEnd_200921] using wordTrace_append hprefix tailTrace_200921
  have hstable : (prefixWord ++ tailWord_200921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200921).length < 2 ^ (prefixWord ++ tailWord_200921).sum := by decide
  have hdescent : baseEnd_200921 < baseStart_200921 := by decide
  rcases family_descends (prefixWord ++ tailWord_200921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200928 : List Nat := [2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_200928 : Nat := 118140960795 + 200928 * 2 ^ 59
def prefixEnd_200928 : Nat := 4983230072969 + 3 ^ 40 * 200928 * 2
def baseEnd_200928 : Nat := 30569671391613363548431

theorem tailTrace_200928 : CollatzResearch.WordTrace tailWord_200928 prefixEnd_200928 30569671391613363548431 := by
  unfold tailWord_200928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664223108039823307745719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4885630810719764410327625 3664223108039823307745719)
  ·
    refine ⟨5496334662059734961618579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3664223108039823307745719 5496334662059734961618579)
    ·
      refine ⟨8244501993089602442427869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5496334662059734961618579 8244501993089602442427869)
      ·
        refine ⟨3091688247408600915910451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8244501993089602442427869 3091688247408600915910451)
        ·
          refine ⟨4637532371112901373865677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091688247408600915910451 4637532371112901373865677)
          ·
            refine ⟨1739074639167338015199629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4637532371112901373865677 1739074639167338015199629)
            ·
              refine ⟨652152989687751755699861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1739074639167338015199629 652152989687751755699861)
              ·
                refine ⟨30569671391613363548431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 652152989687751755699861 30569671391613363548431)
                ·
                  rfl

theorem cell20_200928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_200928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200928 prefixEnd_200928 := by exact prefixLift 200928
  have htrace : WordTrace (prefixWord ++ tailWord_200928) baseStart_200928 baseEnd_200928 := by
    simpa [prefixWord, tailWord_200928, baseEnd_200928] using wordTrace_append hprefix tailTrace_200928
  have hstable : (prefixWord ++ tailWord_200928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200928).length < 2 ^ (prefixWord ++ tailWord_200928).sum := by decide
  have hdescent : baseEnd_200928 < baseStart_200928 := by decide
  rcases family_descends (prefixWord ++ tailWord_200928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200962 : List Nat := [3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_200962 : Nat := 118140960795 + 200962 * 2 ^ 59
def prefixEnd_200962 : Nat := 4983230072969 + 3 ^ 40 * 200962 * 2
def baseEnd_200962 : Nat := 30574844233762361170607

theorem tailTrace_200962 : CollatzResearch.WordTrace tailWord_200962 prefixEnd_200962 30574844233762361170607 := by
  unfold tailWord_200962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832421574489117605557285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4886457531970980281486093 1832421574489117605557285)
  ·
    refine ⟨343579045216709551041991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1832421574489117605557285 343579045216709551041991)
    ·
      refine ⟨515368567825064326562987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343579045216709551041991 515368567825064326562987)
      ·
        refine ⟨773052851737596489844481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515368567825064326562987 773052851737596489844481)
        ·
          refine ⟨579789638803197367383361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773052851737596489844481 579789638803197367383361)
          ·
            refine ⟨434842229102398025537521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579789638803197367383361 434842229102398025537521)
            ·
              refine ⟨326131671826798519153141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434842229102398025537521 326131671826798519153141)
              ·
                refine ⟨30574844233762361170607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326131671826798519153141 30574844233762361170607)
                ·
                  rfl

theorem cell20_200962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_200962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200962 prefixEnd_200962 := by exact prefixLift 200962
  have htrace : WordTrace (prefixWord ++ tailWord_200962) baseStart_200962 baseEnd_200962 := by
    simpa [prefixWord, tailWord_200962, baseEnd_200962] using wordTrace_append hprefix tailTrace_200962
  have hstable : (prefixWord ++ tailWord_200962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200962).length < 2 ^ (prefixWord ++ tailWord_200962).sum := by decide
  have hdescent : baseEnd_200962 < baseStart_200962 := by decide
  rcases family_descends (prefixWord ++ tailWord_200962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200969 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 3]
def baseStart_200969 : Nat := 118140960795 + 200969 * 2 ^ 59
def prefixEnd_200969 : Nat := 4983230072969 + 3 ^ 40 * 200969 * 2
def baseEnd_200969 : Nat := 91727727692026170278459

theorem tailTrace_200969 : CollatzResearch.WordTrace tailWord_200969 prefixEnd_200969 91727727692026170278459 := by
  unfold tailWord_200969
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329941608931110617733961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4886627739287407078489307 7329941608931110617733961)
  ·
    refine ⟨5497456206698332963300471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7329941608931110617733961 5497456206698332963300471)
    ·
      refine ⟨8246184310047499444950707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497456206698332963300471 8246184310047499444950707)
      ·
        refine ⟨12369276465071249167426061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246184310047499444950707 12369276465071249167426061)
        ·
          refine ⟨4638478674401718437784773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12369276465071249167426061 4638478674401718437784773)
          ·
            refine ⟨869714751450322207084645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4638478674401718437784773 869714751450322207084645)
            ·
              refine ⟨163071515896935413828371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 869714751450322207084645 163071515896935413828371)
              ·
                refine ⟨244607273845403120742557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163071515896935413828371 244607273845403120742557)
                ·
                  refine ⟨91727727692026170278459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244607273845403120742557 91727727692026170278459)
                  ·
                    rfl

theorem cell20_200969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_200969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_200969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_200969 prefixEnd_200969 := by exact prefixLift 200969
  have htrace : WordTrace (prefixWord ++ tailWord_200969) baseStart_200969 baseEnd_200969 := by
    simpa [prefixWord, tailWord_200969, baseEnd_200969] using wordTrace_append hprefix tailTrace_200969
  have hstable : (prefixWord ++ tailWord_200969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200969).length < 2 ^ (prefixWord ++ tailWord_200969).sum := by decide
  have hdescent : baseEnd_200969 < baseStart_200969 := by decide
  rcases family_descends (prefixWord ++ tailWord_200969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201006 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_201006 : Nat := 118140960795 + 201006 * 2 ^ 59
def prefixEnd_201006 : Nat := 4983230072969 + 3 ^ 40 * 201006 * 2
def baseEnd_201006 : Nat := 91744615500218486044975

theorem tailTrace_201006 : CollatzResearch.WordTrace tailWord_201006 prefixEnd_201006 91744615500218486044975 := by
  unfold tailWord_201006
  simp only [CollatzResearch.WordTrace]
  refine ⟨916411388724633242103859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4887527406531377291220581 916411388724633242103859)
  ·
    refine ⟨1374617083086949863155789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 916411388724633242103859 1374617083086949863155789)
    ·
      refine ⟨515481406157606198683421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1374617083086949863155789 515481406157606198683421)
      ·
        refine ⟨193305527309102324506283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515481406157606198683421 193305527309102324506283)
        ·
          refine ⟨289958290963653486759425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193305527309102324506283 289958290963653486759425)
          ·
            refine ⟨217468718222740115069569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289958290963653486759425 217468718222740115069569)
            ·
              refine ⟨163101538667055086302177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217468718222740115069569 163101538667055086302177)
              ·
                refine ⟨122326154000291314726633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163101538667055086302177 122326154000291314726633)
                ·
                  refine ⟨91744615500218486044975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122326154000291314726633 91744615500218486044975)
                  ·
                    rfl

theorem cell20_201006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_201006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201006 prefixEnd_201006 := by exact prefixLift 201006
  have htrace : WordTrace (prefixWord ++ tailWord_201006) baseStart_201006 baseEnd_201006 := by
    simpa [prefixWord, tailWord_201006, baseEnd_201006] using wordTrace_append hprefix tailTrace_201006
  have hstable : (prefixWord ++ tailWord_201006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201006).length < 2 ^ (prefixWord ++ tailWord_201006).sum := by decide
  have hdescent : baseEnd_201006 < baseStart_201006 := by decide
  rcases family_descends (prefixWord ++ tailWord_201006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201042 : List Nat := [3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_201042 : Nat := 118140960795 + 201042 * 2 ^ 59
def prefixEnd_201042 : Nat := 4983230072969 + 3 ^ 40 * 201042 * 2
def baseEnd_201042 : Nat := 30587015627054120281609

theorem tailTrace_201042 : CollatzResearch.WordTrace tailWord_201042 prefixEnd_201042 30587015627054120281609 := by
  unfold tailWord_201042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833151034416661021285345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4888402758444429390094253 1833151034416661021285345)
  ·
    refine ⟨1374863275812495765964009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1833151034416661021285345 1374863275812495765964009)
    ·
      refine ⟨1031147456859371824473007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1374863275812495765964009 1031147456859371824473007)
      ·
        refine ⟨1546721185289057736709511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031147456859371824473007 1546721185289057736709511)
        ·
          refine ⟨2320081777933586605064267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546721185289057736709511 2320081777933586605064267)
          ·
            refine ⟨3480122666900379907596401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320081777933586605064267 3480122666900379907596401)
            ·
              refine ⟨2610092000175284930697301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480122666900379907596401 2610092000175284930697301)
              ·
                refine ⟨30587015627054120281609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2610092000175284930697301 30587015627054120281609)
                ·
                  rfl

theorem cell20_201042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_201042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201042 prefixEnd_201042 := by exact prefixLift 201042
  have htrace : WordTrace (prefixWord ++ tailWord_201042) baseStart_201042 baseEnd_201042 := by
    simpa [prefixWord, tailWord_201042, baseEnd_201042] using wordTrace_append hprefix tailTrace_201042
  have hstable : (prefixWord ++ tailWord_201042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201042).length < 2 ^ (prefixWord ++ tailWord_201042).sum := by decide
  have hdescent : baseEnd_201042 < baseStart_201042 := by decide
  rcases family_descends (prefixWord ++ tailWord_201042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201049 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_201049 : Nat := 118140960795 + 201049 * 2 ^ 59
def prefixEnd_201049 : Nat := 4983230072969 + 3 ^ 40 * 201049 * 2
def baseEnd_201049 : Nat := 91764241871901447611465

theorem tailTrace_201049 : CollatzResearch.WordTrace tailWord_201049 prefixEnd_201049 91764241871901447611465 := by
  unfold tailWord_201049
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332859448641284280646201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4888572965760856187097467 7332859448641284280646201)
  ·
    refine ⟨5499644586480963210484651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7332859448641284280646201 5499644586480963210484651)
    ·
      refine ⟨8249466879721444815726977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499644586480963210484651 8249466879721444815726977)
      ·
        refine ⟨6187100159791083611795233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8249466879721444815726977 6187100159791083611795233)
        ·
          refine ⟨4640325119843312708846425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6187100159791083611795233 4640325119843312708846425)
          ·
            refine ⟨3480243839882484531634819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4640325119843312708846425 3480243839882484531634819)
            ·
              refine ⟨5220365759823726797452229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480243839882484531634819 5220365759823726797452229)
              ·
                refine ⟨978818579966948774522293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5220365759823726797452229 978818579966948774522293)
                ·
                  refine ⟨91764241871901447611465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 978818579966948774522293 91764241871901447611465)
                  ·
                    rfl

theorem cell20_201049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_201049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201049 prefixEnd_201049 := by exact prefixLift 201049
  have htrace : WordTrace (prefixWord ++ tailWord_201049) baseStart_201049 baseEnd_201049 := by
    simpa [prefixWord, tailWord_201049, baseEnd_201049] using wordTrace_append hprefix tailTrace_201049
  have hstable : (prefixWord ++ tailWord_201049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201049).length < 2 ^ (prefixWord ++ tailWord_201049).sum := by decide
  have hdescent : baseEnd_201049 < baseStart_201049 := by decide
  rcases family_descends (prefixWord ++ tailWord_201049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201054 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_201054 : Nat := 118140960795 + 201054 * 2 ^ 59
def prefixEnd_201054 : Nat := 4983230072969 + 3 ^ 40 * 201054 * 2
def baseEnd_201054 : Nat := 91766524008143652444779

theorem tailTrace_201054 : CollatzResearch.WordTrace tailWord_201054 prefixEnd_201054 91766524008143652444779 := by
  unfold tailWord_201054
  simp only [CollatzResearch.WordTrace]
  refine ⟨916630226702896266822277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4888694542415446756385477 916630226702896266822277)
  ·
    refine ⟨171868167506793050029177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 916630226702896266822277 171868167506793050029177)
    ·
      refine ⟨128901125630094787521883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171868167506793050029177 128901125630094787521883)
      ·
        refine ⟨193351688445142181282825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128901125630094787521883 193351688445142181282825)
        ·
          refine ⟨145013766333856635962119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193351688445142181282825 145013766333856635962119)
          ·
            refine ⟨217520649500784953943179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145013766333856635962119 217520649500784953943179)
            ·
              refine ⟨326280974251177430914769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217520649500784953943179 326280974251177430914769)
              ·
                refine ⟨244710730688383073186077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326280974251177430914769 244710730688383073186077)
                ·
                  refine ⟨91766524008143652444779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244710730688383073186077 91766524008143652444779)
                  ·
                    rfl

theorem cell20_201054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_201054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201054 prefixEnd_201054 := by exact prefixLift 201054
  have htrace : WordTrace (prefixWord ++ tailWord_201054) baseStart_201054 baseEnd_201054 := by
    simpa [prefixWord, tailWord_201054, baseEnd_201054] using wordTrace_append hprefix tailTrace_201054
  have hstable : (prefixWord ++ tailWord_201054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201054).length < 2 ^ (prefixWord ++ tailWord_201054).sum := by decide
  have hdescent : baseEnd_201054 < baseStart_201054 := by decide
  rcases family_descends (prefixWord ++ tailWord_201054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201083 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 3]
def baseStart_201083 : Nat := 118140960795 + 201083 * 2 ^ 59
def prefixEnd_201083 : Nat := 4983230072969 + 3 ^ 40 * 201083 * 2
def baseEnd_201083 : Nat := 91779760398348440477993

theorem tailTrace_201083 : CollatzResearch.WordTrace tailWord_201083 prefixEnd_201083 91779760398348440477993 := by
  unfold tailWord_201083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334099530518108087383903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4889399687012072058255935 7334099530518108087383903)
  ·
    refine ⟨11001149295777162131075855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7334099530518108087383903 11001149295777162131075855)
    ·
      refine ⟨16501723943665743196613783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11001149295777162131075855 16501723943665743196613783)
      ·
        refine ⟨24752585915498614794920675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16501723943665743196613783 24752585915498614794920675)
        ·
          refine ⟨37128878873247922192381013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24752585915498614794920675 37128878873247922192381013)
          ·
            refine ⟨435104049295874088191965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 37128878873247922192381013 435104049295874088191965)
            ·
              refine ⟨163164018485952783071987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435104049295874088191965 163164018485952783071987)
              ·
                refine ⟨244746027728929174607981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163164018485952783071987 244746027728929174607981)
                ·
                  refine ⟨91779760398348440477993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244746027728929174607981 91779760398348440477993)
                  ·
                    rfl

theorem cell20_201083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_201083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201083 prefixEnd_201083 := by exact prefixLift 201083
  have htrace : WordTrace (prefixWord ++ tailWord_201083) baseStart_201083 baseEnd_201083 := by
    simpa [prefixWord, tailWord_201083, baseEnd_201083] using wordTrace_append hprefix tailTrace_201083
  have hstable : (prefixWord ++ tailWord_201083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201083).length < 2 ^ (prefixWord ++ tailWord_201083).sum := by decide
  have hdescent : baseEnd_201083 < baseStart_201083 := by decide
  rcases family_descends (prefixWord ++ tailWord_201083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201097 : List Nat := [1, 2, 1, 1, 6, 1, 4, 4]
def baseStart_201097 : Nat := 118140960795 + 201097 * 2 ^ 59
def prefixEnd_201097 : Nat := 4983230072969 + 3 ^ 40 * 201097 * 2
def baseEnd_201097 : Nat := 30595383459942204670423

theorem tailTrace_201097 : CollatzResearch.WordTrace tailWord_201097 prefixEnd_201097 30595383459942204670423 := by
  unfold tailWord_201097
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334610152467388478393545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4889740101644925652262363 7334610152467388478393545)
  ·
    refine ⟨5500957614350541358795159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334610152467388478393545 5500957614350541358795159)
    ·
      refine ⟨8251436421525812038192739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500957614350541358795159 8251436421525812038192739)
      ·
        refine ⟨12377154632288718057289109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8251436421525812038192739 12377154632288718057289109)
        ·
          refine ⟨580179123388533658935427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12377154632288718057289109 580179123388533658935427)
          ·
            refine ⟨870268685082800488403141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580179123388533658935427 870268685082800488403141)
            ·
              refine ⟨163175378453025091575589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 870268685082800488403141 163175378453025091575589)
              ·
                refine ⟨30595383459942204670423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163175378453025091575589 30595383459942204670423)
                ·
                  rfl

theorem cell20_201097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_201097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201097 prefixEnd_201097 := by exact prefixLift 201097
  have htrace : WordTrace (prefixWord ++ tailWord_201097) baseStart_201097 baseEnd_201097 := by
    simpa [prefixWord, tailWord_201097, baseEnd_201097] using wordTrace_append hprefix tailTrace_201097
  have hstable : (prefixWord ++ tailWord_201097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201097).length < 2 ^ (prefixWord ++ tailWord_201097).sum := by decide
  have hdescent : baseEnd_201097 < baseStart_201097 := by decide
  rcases family_descends (prefixWord ++ tailWord_201097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201110 : List Nat := [5, 3, 1, 2, 1, 2, 6]
def baseStart_201110 : Nat := 118140960795 + 201110 * 2 ^ 59
def prefixEnd_201110 : Nat := 4983230072969 + 3 ^ 40 * 201110 * 2
def baseEnd_201110 : Nat := 10199120437117371841987

theorem tailTrace_201110 : CollatzResearch.WordTrace tailWord_201110 prefixEnd_201110 10199120437117371841987 := by
  unfold tailWord_201110
  simp only [CollatzResearch.WordTrace]
  refine ⟨458442768838768231163549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4890056200946861132411189 458442768838768231163549)
  ·
    refine ⟨171916038314538086686331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 458442768838768231163549 171916038314538086686331)
    ·
      refine ⟨257874057471807130029497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171916038314538086686331 257874057471807130029497)
      ·
        refine ⟨193405543103855347522123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257874057471807130029497 193405543103855347522123)
        ·
          refine ⟨290108314655783021283185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193405543103855347522123 290108314655783021283185)
          ·
            refine ⟨217581235991837265962389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290108314655783021283185 217581235991837265962389)
            ·
              refine ⟨10199120437117371841987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217581235991837265962389 10199120437117371841987)
              ·
                rfl

theorem cell20_201110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 6].length) (baseStart_201110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201110 prefixEnd_201110 := by exact prefixLift 201110
  have htrace : WordTrace (prefixWord ++ tailWord_201110) baseStart_201110 baseEnd_201110 := by
    simpa [prefixWord, tailWord_201110, baseEnd_201110] using wordTrace_append hprefix tailTrace_201110
  have hstable : (prefixWord ++ tailWord_201110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201110).length < 2 ^ (prefixWord ++ tailWord_201110).sum := by decide
  have hdescent : baseEnd_201110 < baseStart_201110 := by decide
  rcases family_descends (prefixWord ++ tailWord_201110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201125 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_201125 : Nat := 118140960795 + 201125 * 2 ^ 59
def prefixEnd_201125 : Nat := 4983230072969 + 3 ^ 40 * 201125 * 2
def baseEnd_201125 : Nat := 91798930342782961077821

theorem tailTrace_201125 : CollatzResearch.WordTrace tailWord_201125 prefixEnd_201125 91798930342782961077821 := by
  unfold tailWord_201125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335631396365949260412829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4890420930910632840275219 7335631396365949260412829)
  ·
    refine ⟨2750861773637230972654811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7335631396365949260412829 2750861773637230972654811)
    ·
      refine ⟨4126292660455846458982217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750861773637230972654811 4126292660455846458982217)
      ·
        refine ⟨3094719495341884844236663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4126292660455846458982217 3094719495341884844236663)
        ·
          refine ⟨4642079243012827266354995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094719495341884844236663 4642079243012827266354995)
          ·
            refine ⟨6963118864519240899532493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642079243012827266354995 6963118864519240899532493)
            ·
              refine ⟨2611169574194715337324685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6963118864519240899532493 2611169574194715337324685)
              ·
                refine ⟨979188590323018251496757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2611169574194715337324685 979188590323018251496757)
                ·
                  refine ⟨91798930342782961077821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 979188590323018251496757 91798930342782961077821)
                  ·
                    rfl

theorem cell20_201125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_201125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201125 prefixEnd_201125 := by exact prefixLift 201125
  have htrace : WordTrace (prefixWord ++ tailWord_201125) baseStart_201125 baseEnd_201125 := by
    simpa [prefixWord, tailWord_201125, baseEnd_201125] using wordTrace_append hprefix tailTrace_201125
  have hstable : (prefixWord ++ tailWord_201125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201125).length < 2 ^ (prefixWord ++ tailWord_201125).sum := by decide
  have hdescent : baseEnd_201125 < baseStart_201125 := by decide
  rcases family_descends (prefixWord ++ tailWord_201125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201166 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_201166 : Nat := 118140960795 + 201166 * 2 ^ 59
def prefixEnd_201166 : Nat := 4983230072969 + 3 ^ 40 * 201166 * 2
def baseEnd_201166 : Nat := 91817643859969040710987

theorem tailTrace_201166 : CollatzResearch.WordTrace tailWord_201166 prefixEnd_201166 91817643859969040710987 := by
  unfold tailWord_201166
  simp only [CollatzResearch.WordTrace]
  refine ⟨917140848652176657831919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4891417859478275508436901 917140848652176657831919)
  ·
    refine ⟨1375711272978264986747879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 917140848652176657831919 1375711272978264986747879)
    ·
      refine ⟨2063566909467397480121819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375711272978264986747879 2063566909467397480121819)
      ·
        refine ⟨3095350364201096220182729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063566909467397480121819 3095350364201096220182729)
        ·
          refine ⟨2321512773150822165137047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095350364201096220182729 2321512773150822165137047)
          ·
            refine ⟨3482269159726233247705571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321512773150822165137047 3482269159726233247705571)
            ·
              refine ⟨5223403739589349871558357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482269159726233247705571 5223403739589349871558357)
              ·
                refine ⟨122423525146625387614649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5223403739589349871558357 122423525146625387614649)
                ·
                  refine ⟨91817643859969040710987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122423525146625387614649 91817643859969040710987)
                  ·
                    rfl

theorem cell20_201166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_201166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201166 prefixEnd_201166 := by exact prefixLift 201166
  have htrace : WordTrace (prefixWord ++ tailWord_201166) baseStart_201166 baseEnd_201166 := by
    simpa [prefixWord, tailWord_201166, baseEnd_201166] using wordTrace_append hprefix tailTrace_201166
  have hstable : (prefixWord ++ tailWord_201166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201166).length < 2 ^ (prefixWord ++ tailWord_201166).sum := by decide
  have hdescent : baseEnd_201166 < baseStart_201166 := by decide
  rcases family_descends (prefixWord ++ tailWord_201166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201183 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 2]
def baseStart_201183 : Nat := 118140960795 + 201183 * 2 ^ 59
def prefixEnd_201183 : Nat := 4983230072969 + 3 ^ 40 * 201183 * 2
def baseEnd_201183 : Nat := 91825403123192537144251

theorem tailTrace_201183 : CollatzResearch.WordTrace tailWord_201183 prefixEnd_201183 91825403123192537144251 := by
  unfold tailWord_201183
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337746830155825166024203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4891831220103883444016135 7337746830155825166024203)
  ·
    refine ⟨11006620245233737749036305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7337746830155825166024203 11006620245233737749036305)
    ·
      refine ⟨8254965183925303311777229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11006620245233737749036305 8254965183925303311777229)
      ·
        refine ⟨3095611943971988741916461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8254965183925303311777229 3095611943971988741916461)
        ·
          refine ⟨1160854478989495778218673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3095611943971988741916461 1160854478989495778218673)
          ·
            refine ⟨870640859242121833664005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160854478989495778218673 870640859242121833664005)
            ·
              refine ⟨163245161107897843812001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 870640859242121833664005 163245161107897843812001)
              ·
                refine ⟨122433870830923382859001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163245161107897843812001 122433870830923382859001)
                ·
                  refine ⟨91825403123192537144251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122433870830923382859001 91825403123192537144251)
                  ·
                    rfl

theorem cell20_201183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 2].length) (baseStart_201183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201183 prefixEnd_201183 := by exact prefixLift 201183
  have htrace : WordTrace (prefixWord ++ tailWord_201183) baseStart_201183 baseEnd_201183 := by
    simpa [prefixWord, tailWord_201183, baseEnd_201183] using wordTrace_append hprefix tailTrace_201183
  have hstable : (prefixWord ++ tailWord_201183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201183).length < 2 ^ (prefixWord ++ tailWord_201183).sum := by decide
  have hdescent : baseEnd_201183 < baseStart_201183 := by decide
  rcases family_descends (prefixWord ++ tailWord_201183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201186 : List Nat := [3, 3, 3, 2, 2, 1, 1, 5]
def baseStart_201186 : Nat := 118140960795 + 201186 * 2 ^ 59
def prefixEnd_201186 : Nat := 4983230072969 + 3 ^ 40 * 201186 * 2
def baseEnd_201186 : Nat := 30608924134979286681413

theorem tailTrace_201186 : CollatzResearch.WordTrace tailWord_201186 prefixEnd_201186 30608924134979286681413 := by
  unfold tailWord_201186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834464062286239169595853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4891904166096637785588941 1834464062286239169595853)
  ·
    refine ⟨687924023357339688598445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1834464062286239169595853 687924023357339688598445)
    ·
      refine ⟨257971508759002383224417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 687924023357339688598445 257971508759002383224417)
      ·
        refine ⟨193478631569251787418313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257971508759002383224417 193478631569251787418313)
        ·
          refine ⟨145108973676938840563735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193478631569251787418313 145108973676938840563735)
          ·
            refine ⟨217663460515408260845603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145108973676938840563735 217663460515408260845603)
            ·
              refine ⟨326495190773112391268405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217663460515408260845603 326495190773112391268405)
              ·
                refine ⟨30608924134979286681413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326495190773112391268405 30608924134979286681413)
                ·
                  rfl

theorem cell20_201186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_201186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201186 prefixEnd_201186 := by exact prefixLift 201186
  have htrace : WordTrace (prefixWord ++ tailWord_201186) baseStart_201186 baseEnd_201186 := by
    simpa [prefixWord, tailWord_201186, baseEnd_201186] using wordTrace_append hprefix tailTrace_201186
  have hstable : (prefixWord ++ tailWord_201186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201186).length < 2 ^ (prefixWord ++ tailWord_201186).sum := by decide
  have hdescent : baseEnd_201186 < baseStart_201186 := by decide
  rcases family_descends (prefixWord ++ tailWord_201186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201197 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_201197 : Nat := 118140960795 + 201197 * 2 ^ 59
def prefixEnd_201197 : Nat := 4983230072969 + 3 ^ 40 * 201197 * 2
def baseEnd_201197 : Nat := 91831793104670710677527

theorem tailTrace_201197 : CollatzResearch.WordTrace tailWord_201197 prefixEnd_201197 91831793104670710677527 := by
  unfold tailWord_201197
  simp only [CollatzResearch.WordTrace]
  refine ⟨7338257452105105557033845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4892171634736737038022563 7338257452105105557033845)
  ·
    refine ⟨687961636134853645971923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7338257452105105557033845 687961636134853645971923)
    ·
      refine ⟨1031942454202280468957885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687961636134853645971923 1031942454202280468957885)
      ·
        refine ⟨386978420325855175859207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1031942454202280468957885 386978420325855175859207)
        ·
          refine ⟨580467630488782763788811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386978420325855175859207 580467630488782763788811)
          ·
            refine ⟨870701445733174145683217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580467630488782763788811 870701445733174145683217)
            ·
              refine ⟨653026084299880609262413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870701445733174145683217 653026084299880609262413)
              ·
                refine ⟨244884781612455228473405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653026084299880609262413 244884781612455228473405)
                ·
                  refine ⟨91831793104670710677527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244884781612455228473405 91831793104670710677527)
                  ·
                    rfl

theorem cell20_201197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_201197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_201197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_201197 prefixEnd_201197 := by exact prefixLift 201197
  have htrace : WordTrace (prefixWord ++ tailWord_201197) baseStart_201197 baseEnd_201197 := by
    simpa [prefixWord, tailWord_201197, baseEnd_201197] using wordTrace_append hprefix tailTrace_201197
  have hstable : (prefixWord ++ tailWord_201197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201197).length < 2 ^ (prefixWord ++ tailWord_201197).sum := by decide
  have hdescent : baseEnd_201197 < baseStart_201197 := by decide
  rcases family_descends (prefixWord ++ tailWord_201197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
