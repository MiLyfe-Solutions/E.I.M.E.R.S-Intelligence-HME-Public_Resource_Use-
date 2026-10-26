import V185TrunkScan22Chunk452

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4038130 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_4038130 : Nat := 118140960795 + 4038130 * 2 ^ 59
def prefixEnd_4038130 : Nat := 4983230072969 + 3 ^ 40 * 4038130 * 2
def baseEnd_4038130 : Nat := 460778141186753562556441

theorem tailTrace_4038130 : CollatzResearch.WordTrace tailWord_4038130 prefixEnd_4038130 460778141186753562556441 := by
  unfold tailWord_4038130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36820675215138035635663961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98188467240368095028437229 36820675215138035635663961)
  ·
    refine ⟨27615506411353526726747971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36820675215138035635663961 27615506411353526726747971)
    ·
      refine ⟨41423259617030290090121957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27615506411353526726747971 41423259617030290090121957)
      ·
        refine ⟨7766861178193179391897867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41423259617030290090121957 7766861178193179391897867)
        ·
          refine ⟨11650291767289769087846801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766861178193179391897867 11650291767289769087846801)
          ·
            refine ⟨8737718825467326815885101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11650291767289769087846801 8737718825467326815885101)
            ·
              refine ⟨3276644559550247555956913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8737718825467326815885101 3276644559550247555956913)
              ·
                refine ⟨2457483419662685666967685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3276644559550247555956913 2457483419662685666967685)
                ·
                  refine ⟨460778141186753562556441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457483419662685666967685 460778141186753562556441)
                  ·
                    rfl

theorem cell22_4038130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_4038130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038130 prefixEnd_4038130 := by exact prefixLift 4038130
  have htrace : WordTrace (prefixWord ++ tailWord_4038130) baseStart_4038130 baseEnd_4038130 := by
    simpa [prefixWord, tailWord_4038130, baseEnd_4038130] using wordTrace_append hprefix tailTrace_4038130
  have hstable : (prefixWord ++ tailWord_4038130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038130).length < 2 ^ (prefixWord ++ tailWord_4038130).sum := by decide
  have hdescent : baseEnd_4038130 < baseStart_4038130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038201 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_4038201 : Nat := 118140960795 + 4038201 * 2 ^ 59
def prefixEnd_4038201 : Nat := 4983230072969 + 3 ^ 40 * 4038201 * 2
def baseEnd_4038201 : Nat := 1382358728311240169144105

theorem tailTrace_4038201 : CollatzResearch.WordTrace tailWord_4038201 prefixEnd_4038201 1382358728311240169144105 := by
  unfold tailWord_4038201
  simp only [CollatzResearch.WordTrace]
  refine ⟨147285290443294921668490457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98190193628863281112326971 147285290443294921668490457)
  ·
    refine ⟨110463967832471191251367843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147285290443294921668490457 110463967832471191251367843)
    ·
      refine ⟨165695951748706786877051765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110463967832471191251367843 165695951748706786877051765)
      ·
        refine ⟨15533995476441261269723603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165695951748706786877051765 15533995476441261269723603)
        ·
          refine ⟨23300993214661891904585405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15533995476441261269723603 23300993214661891904585405)
          ·
            refine ⟨8737872455498209464219527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23300993214661891904585405 8737872455498209464219527)
            ·
              refine ⟨13106808683247314196329291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8737872455498209464219527 13106808683247314196329291)
              ·
                refine ⟨19660213024870971294493937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13106808683247314196329291 19660213024870971294493937)
                ·
                  refine ⟨14745159768653228470870453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19660213024870971294493937 14745159768653228470870453)
                  ·
                    refine ⟨1382358728311240169144105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14745159768653228470870453 1382358728311240169144105)
                    ·
                      rfl

theorem cell22_4038201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_4038201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038201 prefixEnd_4038201 := by exact prefixLift 4038201
  have htrace : WordTrace (prefixWord ++ tailWord_4038201) baseStart_4038201 baseEnd_4038201 := by
    simpa [prefixWord, tailWord_4038201, baseEnd_4038201] using wordTrace_append hprefix tailTrace_4038201
  have hstable : (prefixWord ++ tailWord_4038201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038201).length < 2 ^ (prefixWord ++ tailWord_4038201).sum := by decide
  have hdescent : baseEnd_4038201 < baseStart_4038201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038237 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 5]
def baseStart_4038237 : Nat := 118140960795 + 4038237 * 2 ^ 59
def prefixEnd_4038237 : Nat := 4983230072969 + 3 ^ 40 * 4038237 * 2
def baseEnd_4038237 : Nat := 460790350615649358414665

theorem tailTrace_4038237 : CollatzResearch.WordTrace tailWord_4038237 prefixEnd_4038237 460790350615649358414665 := by
  unfold tailWord_4038237
  simp only [CollatzResearch.WordTrace]
  refine ⟨147286603471164499816800965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98191068980776333211200643 147286603471164499816800965)
  ·
    refine ⟨27616238150843343715650181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147286603471164499816800965 27616238150843343715650181)
    ·
      refine ⟨5178044653283126946684409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27616238150843343715650181 5178044653283126946684409)
      ·
        refine ⟨3883533489962345210013307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5178044653283126946684409 3883533489962345210013307)
        ·
          refine ⟨5825300234943517815019961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883533489962345210013307 5825300234943517815019961)
          ·
            refine ⟨4368975176207638361264971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5825300234943517815019961 4368975176207638361264971)
            ·
              refine ⟨6553462764311457541897457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368975176207638361264971 6553462764311457541897457)
              ·
                refine ⟨4915097073233593156423093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6553462764311457541897457 4915097073233593156423093)
                ·
                  refine ⟨460790350615649358414665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4915097073233593156423093 460790350615649358414665)
                  ·
                    rfl

theorem cell22_4038237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_4038237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038237 prefixEnd_4038237 := by exact prefixLift 4038237
  have htrace : WordTrace (prefixWord ++ tailWord_4038237) baseStart_4038237 baseEnd_4038237 := by
    simpa [prefixWord, tailWord_4038237, baseEnd_4038237] using wordTrace_append hprefix tailTrace_4038237
  have hstable : (prefixWord ++ tailWord_4038237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038237).length < 2 ^ (prefixWord ++ tailWord_4038237).sum := by decide
  have hdescent : baseEnd_4038237 < baseStart_4038237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038248 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_4038248 : Nat := 118140960795 + 4038248 * 2 ^ 59
def prefixEnd_4038248 : Nat := 4983230072969 + 3 ^ 40 * 4038248 * 2
def baseEnd_4038248 : Nat := 460791605790582571072987

theorem tailTrace_4038248 : CollatzResearch.WordTrace tailWord_4038248 prefixEnd_4038248 460791605790582571072987 := by
  unfold tailWord_4038248
  simp only [CollatzResearch.WordTrace]
  refine ⟨73643502337062324347725699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98191336449416432463634265 73643502337062324347725699)
  ·
    refine ⟨110465253505593486521588549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73643502337062324347725699 110465253505593486521588549)
    ·
      refine ⟨20712235032298778722797853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110465253505593486521588549 20712235032298778722797853)
      ·
        refine ⟨7767088137112042021049195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20712235032298778722797853 7767088137112042021049195)
        ·
          refine ⟨11650632205668063031573793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767088137112042021049195 11650632205668063031573793)
          ·
            refine ⟨8737974154251047273680345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11650632205668063031573793 8737974154251047273680345)
            ·
              refine ⟨6553480615688285455260259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8737974154251047273680345 6553480615688285455260259)
              ·
                refine ⟨9830220923532428182890389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553480615688285455260259 9830220923532428182890389)
                ·
                  refine ⟨460791605790582571072987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9830220923532428182890389 460791605790582571072987)
                  ·
                    rfl

theorem cell22_4038248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_4038248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038248 prefixEnd_4038248 := by exact prefixLift 4038248
  have htrace : WordTrace (prefixWord ++ tailWord_4038248) baseStart_4038248 baseEnd_4038248 := by
    simpa [prefixWord, tailWord_4038248, baseEnd_4038248] using wordTrace_append hprefix tailTrace_4038248
  have hstable : (prefixWord ++ tailWord_4038248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038248).length < 2 ^ (prefixWord ++ tailWord_4038248).sum := by decide
  have hdescent : baseEnd_4038248 < baseStart_4038248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038406 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4038406 : Nat := 118140960795 + 4038406 * 2 ^ 59
def prefixEnd_4038406 : Nat := 4983230072969 + 3 ^ 40 * 4038406 * 2
def baseEnd_4038406 : Nat := 460809634666895989256159

theorem tailTrace_4038406 : CollatzResearch.WordTrace tailWord_4038406 prefixEnd_4038406 460809634666895989256159 := by
  unfold tailWord_4038406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602898981486007552490721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98195178271701494453135381 4602898981486007552490721)
  ·
    refine ⟨3452174236114505664368041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4602898981486007552490721 3452174236114505664368041)
    ·
      refine ⟨2589130677085879248276031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3452174236114505664368041 2589130677085879248276031)
      ·
        refine ⟨3883696015628818872414047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589130677085879248276031 3883696015628818872414047)
        ·
          refine ⟨5825544023443228308621071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883696015628818872414047 5825544023443228308621071)
          ·
            refine ⟨8738316035164842462931607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825544023443228308621071 8738316035164842462931607)
            ·
              refine ⟨13107474052747263694397411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738316035164842462931607 13107474052747263694397411)
              ·
                refine ⟨19661211079120895541596117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13107474052747263694397411 19661211079120895541596117)
                ·
                  refine ⟨460809634666895989256159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19661211079120895541596117 460809634666895989256159)
                  ·
                    rfl

theorem cell22_4038406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4038406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038406 prefixEnd_4038406 := by exact prefixLift 4038406
  have htrace : WordTrace (prefixWord ++ tailWord_4038406) baseStart_4038406 baseEnd_4038406 := by
    simpa [prefixWord, tailWord_4038406, baseEnd_4038406] using wordTrace_append hprefix tailTrace_4038406
  have hstable : (prefixWord ++ tailWord_4038406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038406).length < 2 ^ (prefixWord ++ tailWord_4038406).sum := by decide
  have hdescent : baseEnd_4038406 < baseStart_4038406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038432 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 2, 3]
def baseStart_4038432 : Nat := 118140960795 + 4038432 * 2 ^ 59
def prefixEnd_4038432 : Nat := 4983230072969 + 3 ^ 40 * 4038432 * 2
def baseEnd_4038432 : Nat := 1382437804332032566618397

theorem tailTrace_4038432 : CollatzResearch.WordTrace tailWord_4038432 prefixEnd_4038432 1382437804332032566618397 := by
  unfold tailWord_4038432
  simp only [CollatzResearch.WordTrace]
  refine ⟨73646857852729024060074775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98195810470305365413433033 73646857852729024060074775)
  ·
    refine ⟨110470286779093536090112163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73646857852729024060074775 110470286779093536090112163)
    ·
      refine ⟨165705430168640304135168245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110470286779093536090112163 165705430168640304135168245)
      ·
        refine ⟨15534884078310028512672023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165705430168640304135168245 15534884078310028512672023)
        ·
          refine ⟨23302326117465042769008035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15534884078310028512672023 23302326117465042769008035)
          ·
            refine ⟨34953489176197564153512053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23302326117465042769008035 34953489176197564153512053)
            ·
              refine ⟨3276889610268521639391755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34953489176197564153512053 3276889610268521639391755)
              ·
                refine ⟨4915334415402782459087633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276889610268521639391755 4915334415402782459087633)
                ·
                  refine ⟨3686500811552086844315725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915334415402782459087633 3686500811552086844315725)
                  ·
                    refine ⟨1382437804332032566618397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686500811552086844315725 1382437804332032566618397)
                    ·
                      rfl

theorem cell22_4038432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_4038432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038432 prefixEnd_4038432 := by exact prefixLift 4038432
  have htrace : WordTrace (prefixWord ++ tailWord_4038432) baseStart_4038432 baseEnd_4038432 := by
    simpa [prefixWord, tailWord_4038432, baseEnd_4038432] using wordTrace_append hprefix tailTrace_4038432
  have hstable : (prefixWord ++ tailWord_4038432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038432).length < 2 ^ (prefixWord ++ tailWord_4038432).sum := by decide
  have hdescent : baseEnd_4038432 < baseStart_4038432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038473 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 5]
def baseStart_4038473 : Nat := 118140960795 + 4038473 * 2 ^ 59
def prefixEnd_4038473 : Nat := 4983230072969 + 3 ^ 40 * 4038473 * 2
def baseEnd_4038473 : Nat := 460817279823307375447757

theorem tailTrace_4038473 : CollatzResearch.WordTrace tailWord_4038473 prefixEnd_4038473 460817279823307375447757 := by
  unfold tailWord_4038473
  simp only [CollatzResearch.WordTrace]
  refine ⟨147295211098309512122392073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98196807398873008081594715 147295211098309512122392073)
  ·
    refine ⟨110471408323732134091794055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147295211098309512122392073 110471408323732134091794055)
    ·
      refine ⟨165707112485598201137691083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110471408323732134091794055 165707112485598201137691083)
      ·
        refine ⟨248560668728397301706536625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165707112485598201137691083 248560668728397301706536625)
        ·
          refine ⟨186420501546297976279902469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248560668728397301706536625 186420501546297976279902469)
          ·
            refine ⟨34953844039930870552481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186420501546297976279902469 34953844039930870552481713)
            ·
              refine ⟨26215383029948152914361285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34953844039930870552481713 26215383029948152914361285)
              ·
                refine ⟨4915384318115278671442741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26215383029948152914361285 4915384318115278671442741)
                ·
                  refine ⟨460817279823307375447757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4915384318115278671442741 460817279823307375447757)
                  ·
                    rfl

theorem cell22_4038473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_4038473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038473 prefixEnd_4038473 := by exact prefixLift 4038473
  have htrace : WordTrace (prefixWord ++ tailWord_4038473) baseStart_4038473 baseEnd_4038473 := by
    simpa [prefixWord, tailWord_4038473, baseEnd_4038473] using wordTrace_append hprefix tailTrace_4038473
  have hstable : (prefixWord ++ tailWord_4038473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038473).length < 2 ^ (prefixWord ++ tailWord_4038473).sum := by decide
  have hdescent : baseEnd_4038473 < baseStart_4038473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038533 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_4038533 : Nat := 118140960795 + 4038533 * 2 ^ 59
def prefixEnd_4038533 : Nat := 4983230072969 + 3 ^ 40 * 4038533 * 2
def baseEnd_4038533 : Nat := 1382472378696101969843087

theorem tailTrace_4038533 : CollatzResearch.WordTrace tailWord_4038533 prefixEnd_4038533 1382472378696101969843087 := by
  unfold tailWord_4038533
  simp only [CollatzResearch.WordTrace]
  refine ⟨147297399478092142369576253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98198266318728094913050835 147297399478092142369576253)
  ·
    refine ⟨55236524804284553388591095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147297399478092142369576253 55236524804284553388591095)
    ·
      refine ⟨82854787206426830082886643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55236524804284553388591095 82854787206426830082886643)
      ·
        refine ⟨124282180809640245124329965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82854787206426830082886643 124282180809640245124329965)
        ·
          refine ⟨46605817803615091921623737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124282180809640245124329965 46605817803615091921623737)
          ·
            refine ⟨34954363352711318941217803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46605817803615091921623737 34954363352711318941217803)
            ·
              refine ⟨52431545029066978411826705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34954363352711318941217803 52431545029066978411826705)
              ·
                refine ⟨39323658771800233808870029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52431545029066978411826705 39323658771800233808870029)
                ·
                  refine ⟨14746372039425087678326261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39323658771800233808870029 14746372039425087678326261)
                  ·
                    refine ⟨1382472378696101969843087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14746372039425087678326261 1382472378696101969843087)
                    ·
                      rfl

theorem cell22_4038533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_4038533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038533 prefixEnd_4038533 := by exact prefixLift 4038533
  have htrace : WordTrace (prefixWord ++ tailWord_4038533) baseStart_4038533 baseEnd_4038533 := by
    simpa [prefixWord, tailWord_4038533, baseEnd_4038533] using wordTrace_append hprefix tailTrace_4038533
  have hstable : (prefixWord ++ tailWord_4038533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038533).length < 2 ^ (prefixWord ++ tailWord_4038533).sum := by decide
  have hdescent : baseEnd_4038533 < baseStart_4038533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038552 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 6]
def baseStart_4038552 : Nat := 118140960795 + 4038552 * 2 ^ 59
def prefixEnd_4038552 : Nat := 4983230072969 + 3 ^ 40 * 4038552 * 2
def baseEnd_4038552 : Nat := 460826294261464084539343

theorem tailTrace_4038552 : CollatzResearch.WordTrace tailWord_4038552 prefixEnd_4038552 460826294261464084539343 := by
  unfold tailWord_4038552
  simp only [CollatzResearch.WordTrace]
  refine ⟨73649046232511654307258955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98198728310015539076345273 73649046232511654307258955)
  ·
    refine ⟨110473569348767481460888433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73649046232511654307258955 110473569348767481460888433)
    ·
      refine ⟨82855177011575611095666325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110473569348767481460888433 82855177011575611095666325)
      ·
        refine ⟨3883836422417606770109359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82855177011575611095666325 3883836422417606770109359)
        ·
          refine ⟨5825754633626410155164039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883836422417606770109359 5825754633626410155164039)
          ·
            refine ⟨8738631950439615232746059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825754633626410155164039 8738631950439615232746059)
            ·
              refine ⟨13107947925659422849119089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738631950439615232746059 13107947925659422849119089)
              ·
                refine ⟨9830960944244567136839317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13107947925659422849119089 9830960944244567136839317)
                ·
                  refine ⟨460826294261464084539343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9830960944244567136839317 460826294261464084539343)
                  ·
                    rfl

theorem cell22_4038552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_4038552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038552 prefixEnd_4038552 := by exact prefixLift 4038552
  have htrace : WordTrace (prefixWord ++ tailWord_4038552) baseStart_4038552 baseEnd_4038552 := by
    simpa [prefixWord, tailWord_4038552, baseEnd_4038552] using wordTrace_append hprefix tailTrace_4038552
  have hstable : (prefixWord ++ tailWord_4038552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038552).length < 2 ^ (prefixWord ++ tailWord_4038552).sum := by decide
  have hdescent : baseEnd_4038552 < baseStart_4038552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038578 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_4038578 : Nat := 118140960795 + 4038578 * 2 ^ 59
def prefixEnd_4038578 : Nat := 4983230072969 + 3 ^ 40 * 4038578 * 2
def baseEnd_4038578 : Nat := 1382487783115736852467949

theorem tailTrace_4038578 : CollatzResearch.WordTrace tailWord_4038578 prefixEnd_4038578 1382487783115736852467949 := by
  unfold tailWord_4038578
  simp only [CollatzResearch.WordTrace]
  refine ⟨36824760190732278763741097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98199360508619410036642925 36824760190732278763741097)
  ·
    refine ⟨27618570143049209072805823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36824760190732278763741097 27618570143049209072805823)
    ·
      refine ⟨41427855214573813609208735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27618570143049209072805823 41427855214573813609208735)
      ·
        refine ⟨62141782821860720413813103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41427855214573813609208735 62141782821860720413813103)
        ·
          refine ⟨93212674232791080620719655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62141782821860720413813103 93212674232791080620719655)
          ·
            refine ⟨139819011349186620931079483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93212674232791080620719655 139819011349186620931079483)
            ·
              refine ⟨209728517023779931396619225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139819011349186620931079483 209728517023779931396619225)
              ·
                refine ⟨157296387767834948547464419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209728517023779931396619225 157296387767834948547464419)
                ·
                  refine ⟨235944581651752422821196629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157296387767834948547464419 235944581651752422821196629)
                  ·
                    refine ⟨1382487783115736852467949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235944581651752422821196629 1382487783115736852467949)
                    ·
                      rfl

theorem cell22_4038578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_4038578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038578 prefixEnd_4038578 := by exact prefixLift 4038578
  have htrace : WordTrace (prefixWord ++ tailWord_4038578) baseStart_4038578 baseEnd_4038578 := by
    simpa [prefixWord, tailWord_4038578, baseEnd_4038578] using wordTrace_append hprefix tailTrace_4038578
  have hstable : (prefixWord ++ tailWord_4038578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038578).length < 2 ^ (prefixWord ++ tailWord_4038578).sum := by decide
  have hdescent : baseEnd_4038578 < baseStart_4038578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038612 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_4038612 : Nat := 118140960795 + 4038612 * 2 ^ 59
def prefixEnd_4038612 : Nat := 4983230072969 + 3 ^ 40 * 4038612 * 2
def baseEnd_4038612 : Nat := 1382499422010572097117845

theorem tailTrace_4038612 : CollatzResearch.WordTrace tailWord_4038612 prefixEnd_4038612 1382499422010572097117845 := by
  unfold tailWord_4038612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73650140422402969430851045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98200187229870625907801393 73650140422402969430851045)
  ·
    refine ⟨13809401329200556768284571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73650140422402969430851045 13809401329200556768284571)
    ·
      refine ⟨20714101993800835152426857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809401329200556768284571 20714101993800835152426857)
      ·
        refine ⟨15535576495350626364320143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20714101993800835152426857 15535576495350626364320143)
        ·
          refine ⟨23303364743025939546480215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15535576495350626364320143 23303364743025939546480215)
          ·
            refine ⟨34955047114538909319720323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23303364743025939546480215 34955047114538909319720323)
            ·
              refine ⟨52432570671808363979580485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34955047114538909319720323 52432570671808363979580485)
              ·
                refine ⟨9831107000964068246171341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52432570671808363979580485 9831107000964068246171341)
                ·
                  refine ⟨3686665125361525592314253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9831107000964068246171341 3686665125361525592314253)
                  ·
                    refine ⟨1382499422010572097117845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686665125361525592314253 1382499422010572097117845)
                    ·
                      rfl

theorem cell22_4038612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_4038612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038612 prefixEnd_4038612 := by exact prefixLift 4038612
  have htrace : WordTrace (prefixWord ++ tailWord_4038612) baseStart_4038612 baseEnd_4038612 := by
    simpa [prefixWord, tailWord_4038612, baseEnd_4038612] using wordTrace_append hprefix tailTrace_4038612
  have hstable : (prefixWord ++ tailWord_4038612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038612).length < 2 ^ (prefixWord ++ tailWord_4038612).sum := by decide
  have hdescent : baseEnd_4038612 < baseStart_4038612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038620 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 4]
def baseStart_4038620 : Nat := 118140960795 + 4038620 * 2 ^ 59
def prefixEnd_4038620 : Nat := 4983230072969 + 3 ^ 40 * 4038620 * 2
def baseEnd_4038620 : Nat := 460834053524687580972607

theorem tailTrace_4038620 : CollatzResearch.WordTrace tailWord_4038620 prefixEnd_4038620 460834053524687580972607 := by
  unfold tailWord_4038620
  simp only [CollatzResearch.WordTrace]
  refine ⟨73650286314388478113996657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98200381752517970818662209 73650286314388478113996657)
  ·
    refine ⟨55237714735791358585497493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73650286314388478113996657 55237714735791358585497493)
    ·
      refine ⟨2589267878240219933695195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55237714735791358585497493 2589267878240219933695195)
      ·
        refine ⟨3883901817360329900542793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589267878240219933695195 3883901817360329900542793)
        ·
          refine ⟨2912926363020247425407095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3883901817360329900542793 2912926363020247425407095)
          ·
            refine ⟨4369389544530371138110643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912926363020247425407095 4369389544530371138110643)
            ·
              refine ⟨6554084316795556707165965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369389544530371138110643 6554084316795556707165965)
              ·
                refine ⟨2457781618798333765187237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6554084316795556707165965 2457781618798333765187237)
                ·
                  refine ⟨460834053524687580972607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457781618798333765187237 460834053524687580972607)
                  ·
                    rfl

theorem cell22_4038620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_4038620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038620 prefixEnd_4038620 := by exact prefixLift 4038620
  have htrace : WordTrace (prefixWord ++ tailWord_4038620) baseStart_4038620 baseEnd_4038620 := by
    simpa [prefixWord, tailWord_4038620, baseEnd_4038620] using wordTrace_append hprefix tailTrace_4038620
  have hstable : (prefixWord ++ tailWord_4038620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038620).length < 2 ^ (prefixWord ++ tailWord_4038620).sum := by decide
  have hdescent : baseEnd_4038620 < baseStart_4038620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038646 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_4038646 : Nat := 118140960795 + 4038646 * 2 ^ 59
def prefixEnd_4038646 : Nat := 4983230072969 + 3 ^ 40 * 4038646 * 2
def baseEnd_4038646 : Nat := 1382511060905407341767741

theorem tailTrace_4038646 : CollatzResearch.WordTrace tailWord_4038646 prefixEnd_4038646 1382511060905407341767741 := by
  unfold tailWord_4038646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206345057917672666777487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98201013951121841778959861 9206345057917672666777487)
  ·
    refine ⟨13809517586876509000166231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9206345057917672666777487 13809517586876509000166231)
    ·
      refine ⟨20714276380314763500249347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809517586876509000166231 20714276380314763500249347)
      ·
        refine ⟨31071414570472145250374021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20714276380314763500249347 31071414570472145250374021)
        ·
          refine ⟨5825890231963527234445129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31071414570472145250374021 5825890231963527234445129)
          ·
            refine ⟨4369417673972645425833847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5825890231963527234445129 4369417673972645425833847)
            ·
              refine ⟨6554126510958968138750771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369417673972645425833847 6554126510958968138750771)
              ·
                refine ⟨9831189766438452208126157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554126510958968138750771 9831189766438452208126157)
                ·
                  refine ⟨3686696162414419578047309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9831189766438452208126157 3686696162414419578047309)
                  ·
                    refine ⟨1382511060905407341767741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686696162414419578047309 1382511060905407341767741)
                    ·
                      rfl

theorem cell22_4038646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_4038646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038646 prefixEnd_4038646 := by exact prefixLift 4038646
  have htrace : WordTrace (prefixWord ++ tailWord_4038646) baseStart_4038646 baseEnd_4038646 := by
    simpa [prefixWord, tailWord_4038646, baseEnd_4038646] using wordTrace_append hprefix tailTrace_4038646
  have hstable : (prefixWord ++ tailWord_4038646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038646).length < 2 ^ (prefixWord ++ tailWord_4038646).sum := by decide
  have hdescent : baseEnd_4038646 < baseStart_4038646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038670 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_4038670 : Nat := 118140960795 + 4038670 * 2 ^ 59
def prefixEnd_4038670 : Nat := 4983230072969 + 3 ^ 40 * 4038670 * 2
def baseEnd_4038670 : Nat := 460839758865293093055889

theorem tailTrace_4038670 : CollatzResearch.WordTrace tailWord_4038670 prefixEnd_4038670 460839758865293093055889 := by
  unfold tailWord_4038670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18412799534824476845914183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98201597519063876511542309 18412799534824476845914183)
  ·
    refine ⟨27619199302236715268871275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18412799534824476845914183 27619199302236715268871275)
    ·
      refine ⟨41428798953355072903306913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27619199302236715268871275 41428798953355072903306913)
      ·
        refine ⟨31071599215016304677480185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41428798953355072903306913 31071599215016304677480185)
        ·
          refine ⟨23303699411262228508110139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31071599215016304677480185 23303699411262228508110139)
          ·
            refine ⟨34955549116893342762165209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23303699411262228508110139 34955549116893342762165209)
            ·
              refine ⟨26216661837670007071623907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34955549116893342762165209 26216661837670007071623907)
              ·
                refine ⟨39324992756505010607435861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26216661837670007071623907 39324992756505010607435861)
                ·
                  refine ⟨460839758865293093055889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39324992756505010607435861 460839758865293093055889)
                  ·
                    rfl

theorem cell22_4038670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_4038670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038670 prefixEnd_4038670 := by exact prefixLift 4038670
  have htrace : WordTrace (prefixWord ++ tailWord_4038670) baseStart_4038670 baseEnd_4038670 := by
    simpa [prefixWord, tailWord_4038670, baseEnd_4038670] using wordTrace_append hprefix tailTrace_4038670
  have hstable : (prefixWord ++ tailWord_4038670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038670).length < 2 ^ (prefixWord ++ tailWord_4038670).sum := by decide
  have hdescent : baseEnd_4038670 < baseStart_4038670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038687 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 4]
def baseStart_4038687 : Nat := 118140960795 + 4038687 * 2 ^ 59
def prefixEnd_4038687 : Nat := 4983230072969 + 3 ^ 40 * 4038687 * 2
def baseEnd_4038687 : Nat := 460841698681098967164205

theorem tailTrace_4038687 : CollatzResearch.WordTrace tailWord_4038687 prefixEnd_4038687 460841698681098967164205 := by
  unfold tailWord_4038687
  simp only [CollatzResearch.WordTrace]
  refine ⟨147303016319534226670682315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98202010879689484447121543 147303016319534226670682315)
  ·
    refine ⟨220954524479301340006023473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147303016319534226670682315 220954524479301340006023473)
    ·
      refine ⟨165715893359476005004517605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220954524479301340006023473 165715893359476005004517605)
      ·
        refine ⟨31071730004901750938347051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165715893359476005004517605 31071730004901750938347051)
        ·
          refine ⟨46607595007352626407520577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31071730004901750938347051 46607595007352626407520577)
          ·
            refine ⟨34955696255514469805640433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46607595007352626407520577 34955696255514469805640433)
            ·
              refine ⟨26216772191635852354230325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34955696255514469805640433 26216772191635852354230325)
              ·
                refine ⟨2457822392965861158209093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26216772191635852354230325 2457822392965861158209093)
                ·
                  refine ⟨460841698681098967164205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457822392965861158209093 460841698681098967164205)
                  ·
                    rfl

theorem cell22_4038687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 4].length) (baseStart_4038687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038687 prefixEnd_4038687 := by exact prefixLift 4038687
  have htrace : WordTrace (prefixWord ++ tailWord_4038687) baseStart_4038687 baseEnd_4038687 := by
    simpa [prefixWord, tailWord_4038687, baseEnd_4038687] using wordTrace_append hprefix tailTrace_4038687
  have hstable : (prefixWord ++ tailWord_4038687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038687).length < 2 ^ (prefixWord ++ tailWord_4038687).sum := by decide
  have hdescent : baseEnd_4038687 < baseStart_4038687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038700 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_4038700 : Nat := 118140960795 + 4038700 * 2 ^ 59
def prefixEnd_4038700 : Nat := 4983230072969 + 3 ^ 40 * 4038700 * 2
def baseEnd_4038700 : Nat := 1382529546208969200917575

theorem tailTrace_4038700 : CollatzResearch.WordTrace tailWord_4038700 prefixEnd_4038700 1382529546208969200917575 := by
  unfold tailWord_4038700
  simp only [CollatzResearch.WordTrace]
  refine ⟨73651745234243564945452777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98202326978991419927270369 73651745234243564945452777)
  ·
    refine ⟨55238808925682673709089583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73651745234243564945452777 55238808925682673709089583)
    ·
      refine ⟨82858213388524010563634375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55238808925682673709089583 82858213388524010563634375)
      ·
        refine ⟨124287320082786015845451563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82858213388524010563634375 124287320082786015845451563)
        ·
          refine ⟨186430980124179023768177345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124287320082786015845451563 186430980124179023768177345)
          ·
            refine ⟨139823235093134267826133009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186430980124179023768177345 139823235093134267826133009)
            ·
              refine ⟨104867426319850700869599757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139823235093134267826133009 104867426319850700869599757)
              ·
                refine ⟨39325284869944012826099909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104867426319850700869599757 39325284869944012826099909)
                ·
                  refine ⟨7373490913114502404893733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39325284869944012826099909 7373490913114502404893733)
                  ·
                    refine ⟨1382529546208969200917575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7373490913114502404893733 1382529546208969200917575)
                    ·
                      rfl

theorem cell22_4038700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_4038700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038700 prefixEnd_4038700 := by exact prefixLift 4038700
  have htrace : WordTrace (prefixWord ++ tailWord_4038700) baseStart_4038700 baseEnd_4038700 := by
    simpa [prefixWord, tailWord_4038700, baseEnd_4038700] using wordTrace_append hprefix tailTrace_4038700
  have hstable : (prefixWord ++ tailWord_4038700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038700).length < 2 ^ (prefixWord ++ tailWord_4038700).sum := by decide
  have hdescent : baseEnd_4038700 < baseStart_4038700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038704 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 4]
def baseStart_4038704 : Nat := 118140960795 + 4038704 * 2 ^ 59
def prefixEnd_4038704 : Nat := 4983230072969 + 3 ^ 40 * 4038704 * 2
def baseEnd_4038704 : Nat := 460843638496904841272521

theorem tailTrace_4038704 : CollatzResearch.WordTrace tailWord_4038704 prefixEnd_4038704 460843638496904841272521 := by
  unfold tailWord_4038704
  simp only [CollatzResearch.WordTrace]
  refine ⟨73651818180236319287025583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98202424240315092382700777 73651818180236319287025583)
  ·
    refine ⟨110477727270354478930538375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73651818180236319287025583 110477727270354478930538375)
    ·
      refine ⟨165716590905531718395807563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110477727270354478930538375 165716590905531718395807563)
      ·
        refine ⟨248574886358297577593711345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165716590905531718395807563 248574886358297577593711345)
        ·
          refine ⟨186431164768723183195283509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248574886358297577593711345 186431164768723183195283509)
          ·
            refine ⟨17477921697067798424557829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186431164768723183195283509 17477921697067798424557829)
            ·
              refine ⟨3277110318200212204604593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17477921697067798424557829 3277110318200212204604593)
              ·
                refine ⟨2457832738650159153453445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277110318200212204604593 2457832738650159153453445)
                ·
                  refine ⟨460843638496904841272521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457832738650159153453445 460843638496904841272521)
                  ·
                    rfl

theorem cell22_4038704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_4038704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038704 prefixEnd_4038704 := by exact prefixLift 4038704
  have htrace : WordTrace (prefixWord ++ tailWord_4038704) baseStart_4038704 baseEnd_4038704 := by
    simpa [prefixWord, tailWord_4038704, baseEnd_4038704] using wordTrace_append hprefix tailTrace_4038704
  have hstable : (prefixWord ++ tailWord_4038704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038704).length < 2 ^ (prefixWord ++ tailWord_4038704).sum := by decide
  have hdescent : baseEnd_4038704 < baseStart_4038704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038734 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_4038734 : Nat := 118140960795 + 4038734 * 2 ^ 59
def prefixEnd_4038734 : Nat := 4983230072969 + 3 ^ 40 * 4038734 * 2
def baseEnd_4038734 : Nat := 1382541185103804445567471

theorem tailTrace_4038734 : CollatzResearch.WordTrace tailWord_4038734 prefixEnd_4038734 1382541185103804445567471 := by
  unfold tailWord_4038734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413091318795494212205407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98203153700242635798428837 18413091318795494212205407)
  ·
    refine ⟨27619636978193241318308111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18413091318795494212205407 27619636978193241318308111)
    ·
      refine ⟨41429455467289861977462167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27619636978193241318308111 41429455467289861977462167)
      ·
        refine ⟨62144183200934792966193251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41429455467289861977462167 62144183200934792966193251)
        ·
          refine ⟨93216274801402189449289877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62144183200934792966193251 93216274801402189449289877)
          ·
            refine ⟨4369512881315727630435463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93216274801402189449289877 4369512881315727630435463)
            ·
              refine ⟨6554269321973591445653195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369512881315727630435463 6554269321973591445653195)
              ·
                refine ⟨9831403982960387168479793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554269321973591445653195 9831403982960387168479793)
                ·
                  refine ⟨7373552987220290376359845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9831403982960387168479793 7373552987220290376359845)
                  ·
                    refine ⟨1382541185103804445567471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7373552987220290376359845 1382541185103804445567471)
                    ·
                      rfl

theorem cell22_4038734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_4038734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038734 prefixEnd_4038734 := by exact prefixLift 4038734
  have htrace : WordTrace (prefixWord ++ tailWord_4038734) baseStart_4038734 baseEnd_4038734 := by
    simpa [prefixWord, tailWord_4038734, baseEnd_4038734] using wordTrace_append hprefix tailTrace_4038734
  have hstable : (prefixWord ++ tailWord_4038734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038734).length < 2 ^ (prefixWord ++ tailWord_4038734).sum := by decide
  have hdescent : baseEnd_4038734 < baseStart_4038734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038764 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_4038764 : Nat := 118140960795 + 4038764 * 2 ^ 59
def prefixEnd_4038764 : Nat := 4983230072969 + 3 ^ 40 * 4038764 * 2
def baseEnd_4038764 : Nat := 1382551454716894367317379

theorem tailTrace_4038764 : CollatzResearch.WordTrace tailWord_4038764 prefixEnd_4038764 1382551454716894367317379 := by
  unfold tailWord_4038764
  simp only [CollatzResearch.WordTrace]
  refine ⟨73652912370127634410617673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98203883160170179214156897 73652912370127634410617673)
  ·
    refine ⟨55239684277595725807963255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73652912370127634410617673 55239684277595725807963255)
    ·
      refine ⟨82859526416393588711944883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55239684277595725807963255 82859526416393588711944883)
      ·
        refine ⟨124289289624590383067917325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82859526416393588711944883 124289289624590383067917325)
        ·
          refine ⟨46608483609221393650468997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124289289624590383067917325 46608483609221393650468997)
          ·
            refine ⟨8739090676729011309462937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46608483609221393650468997 8739090676729011309462937)
            ·
              refine ⟨6554318007546758482097203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739090676729011309462937 6554318007546758482097203)
              ·
                refine ⟨9831477011320137723145805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554318007546758482097203 9831477011320137723145805)
                ·
                  refine ⟨3686803879245051646179677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9831477011320137723145805 3686803879245051646179677)
                  ·
                    refine ⟨1382551454716894367317379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686803879245051646179677 1382551454716894367317379)
                    ·
                      rfl

theorem cell22_4038764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_4038764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038764 prefixEnd_4038764 := by exact prefixLift 4038764
  have htrace : WordTrace (prefixWord ++ tailWord_4038764) baseStart_4038764 baseEnd_4038764 := by
    simpa [prefixWord, tailWord_4038764, baseEnd_4038764] using wordTrace_append hprefix tailTrace_4038764
  have hstable : (prefixWord ++ tailWord_4038764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038764).length < 2 ^ (prefixWord ++ tailWord_4038764).sum := by decide
  have hdescent : baseEnd_4038764 < baseStart_4038764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038899 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 3, 3]
def baseStart_4038899 : Nat := 118140960795 + 4038899 * 2 ^ 59
def prefixEnd_4038899 : Nat := 4983230072969 + 3 ^ 40 * 4038899 * 2
def baseEnd_4038899 : Nat := 1382597667975799015191965

theorem tailTrace_4038899 : CollatzResearch.WordTrace tailWord_4038899 prefixEnd_4038899 1382597667975799015191965 := by
  unfold tailWord_4038899
  simp only [CollatzResearch.WordTrace]
  refine ⟨147310748594766186877399751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98207165729844124584933167 147310748594766186877399751)
  ·
    refine ⟨220966122892149280316099627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147310748594766186877399751 220966122892149280316099627)
    ·
      refine ⟨331449184338223920474149441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220966122892149280316099627 331449184338223920474149441)
      ·
        refine ⟨248586888253667940355612081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331449184338223920474149441 248586888253667940355612081)
        ·
          refine ⟨186440166190250955266709061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248586888253667940355612081 186440166190250955266709061)
          ·
            refine ⟨34957531160672054112507949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186440166190250955266709061 34957531160672054112507949)
            ·
              refine ⟨13109074185252020292190481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34957531160672054112507949 13109074185252020292190481)
              ·
                refine ⟨9831805638939015219142861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13109074185252020292190481 9831805638939015219142861)
                ·
                  refine ⟨3686927114602130707178573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9831805638939015219142861 3686927114602130707178573)
                  ·
                    refine ⟨1382597667975799015191965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686927114602130707178573 1382597667975799015191965)
                    ·
                      rfl

theorem cell22_4038899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 3].length) (baseStart_4038899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038899 prefixEnd_4038899 := by exact prefixLift 4038899
  have htrace : WordTrace (prefixWord ++ tailWord_4038899) baseStart_4038899 baseEnd_4038899 := by
    simpa [prefixWord, tailWord_4038899, baseEnd_4038899] using wordTrace_append hprefix tailTrace_4038899
  have hstable : (prefixWord ++ tailWord_4038899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038899).length < 2 ^ (prefixWord ++ tailWord_4038899).sum := by decide
  have hdescent : baseEnd_4038899 < baseStart_4038899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038929 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 5]
def baseStart_4038929 : Nat := 118140960795 + 4038929 * 2 ^ 59
def prefixEnd_4038929 : Nat := 4983230072969 + 3 ^ 40 * 4038929 * 2
def baseEnd_4038929 : Nat := 460869312529629645647291

theorem tailTrace_4038929 : CollatzResearch.WordTrace tailWord_4038929 prefixEnd_4038929 460869312529629645647291 := by
  unfold tailWord_4038929
  simp only [CollatzResearch.WordTrace]
  refine ⟨147311842784657502000991841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98207895189771668000661227 147311842784657502000991841)
  ·
    refine ⟨110483882088493126500743881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147311842784657502000991841 110483882088493126500743881)
    ·
      refine ⟨82862911566369844875557911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110483882088493126500743881 82862911566369844875557911)
      ·
        refine ⟨124294367349554767313336867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82862911566369844875557911 124294367349554767313336867)
        ·
          refine ⟨186441551024332150970005301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124294367349554767313336867 186441551024332150970005301)
          ·
            refine ⟨17478895408531139153437997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186441551024332150970005301 17478895408531139153437997)
            ·
              refine ⟨6554585778199177182539249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17478895408531139153437997 6554585778199177182539249)
              ·
                refine ⟨4915939333649382886904437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554585778199177182539249 4915939333649382886904437)
                ·
                  refine ⟨460869312529629645647291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4915939333649382886904437 460869312529629645647291)
                  ·
                    rfl

theorem cell22_4038929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_4038929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038929 prefixEnd_4038929 := by exact prefixLift 4038929
  have htrace : WordTrace (prefixWord ++ tailWord_4038929) baseStart_4038929 baseEnd_4038929 := by
    simpa [prefixWord, tailWord_4038929, baseEnd_4038929] using wordTrace_append hprefix tailTrace_4038929
  have hstable : (prefixWord ++ tailWord_4038929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038929).length < 2 ^ (prefixWord ++ tailWord_4038929).sum := by decide
  have hdescent : baseEnd_4038929 < baseStart_4038929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038944 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_4038944 : Nat := 118140960795 + 4038944 * 2 ^ 59
def prefixEnd_4038944 : Nat := 4983230072969 + 3 ^ 40 * 4038944 * 2
def baseEnd_4038944 : Nat := 1382613072395433897816827

theorem tailTrace_4038944 : CollatzResearch.WordTrace tailWord_4038944 prefixEnd_4038944 1382613072395433897816827 := by
  unfold tailWord_4038944
  simp only [CollatzResearch.WordTrace]
  refine ⟨73656194939801579781393943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98208259919735439708525257 73656194939801579781393943)
  ·
    refine ⟨110484292409702369672090915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73656194939801579781393943 110484292409702369672090915)
    ·
      refine ⟨165726438614553554508136373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110484292409702369672090915 165726438614553554508136373)
      ·
        refine ⟨15536853620114395735137785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165726438614553554508136373 15536853620114395735137785)
        ·
          refine ⟨11652640215085796801353339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15536853620114395735137785 11652640215085796801353339)
          ·
            refine ⟨17478960322628695202030009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652640215085796801353339 17478960322628695202030009)
            ·
              refine ⟨13109220241971521401522507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17478960322628695202030009 13109220241971521401522507)
              ·
                refine ⟨19663830362957282102283761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13109220241971521401522507 19663830362957282102283761)
                ·
                  refine ⟨14747872772217961576712821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19663830362957282102283761 14747872772217961576712821)
                  ·
                    refine ⟨1382613072395433897816827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14747872772217961576712821 1382613072395433897816827)
                    ·
                      rfl

theorem cell22_4038944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_4038944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038944 prefixEnd_4038944 := by exact prefixLift 4038944
  have htrace : WordTrace (prefixWord ++ tailWord_4038944) baseStart_4038944 baseEnd_4038944 := by
    simpa [prefixWord, tailWord_4038944, baseEnd_4038944] using wordTrace_append hprefix tailTrace_4038944
  have hstable : (prefixWord ++ tailWord_4038944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038944).length < 2 ^ (prefixWord ++ tailWord_4038944).sum := by decide
  have hdescent : baseEnd_4038944 < baseStart_4038944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038959 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 1, 4]
def baseStart_4038959 : Nat := 118140960795 + 4038959 * 2 ^ 59
def prefixEnd_4038959 : Nat := 4983230072969 + 3 ^ 40 * 4038959 * 2
def baseEnd_4038959 : Nat := 1382618207201978858691781

theorem tailTrace_4038959 : CollatzResearch.WordTrace tailWord_4038959 prefixEnd_4038959 1382618207201978858691781 := by
  unfold tailWord_4038959
  simp only [CollatzResearch.WordTrace]
  refine ⟨147312936974548817124583931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98208624649699211416389287 147312936974548817124583931)
  ·
    refine ⟨220969405461823225686875897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147312936974548817124583931 220969405461823225686875897)
    ·
      refine ⟨165727054096367419265156923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220969405461823225686875897 165727054096367419265156923)
      ·
        refine ⟨248590581144551128897735385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165727054096367419265156923 248590581144551128897735385)
        ·
          refine ⟨186442935858413346673301539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248590581144551128897735385 186442935858413346673301539)
          ·
            refine ⟨279664403787620020009952309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186442935858413346673301539 279664403787620020009952309)
            ·
              refine ⟨26218537855089376875933029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279664403787620020009952309 26218537855089376875933029)
              ·
                refine ⟨4915975847829258164237443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26218537855089376875933029 4915975847829258164237443)
                ·
                  refine ⟨7373963771743887246356165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915975847829258164237443 7373963771743887246356165)
                  ·
                    refine ⟨1382618207201978858691781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7373963771743887246356165 1382618207201978858691781)
                    ·
                      rfl

theorem cell22_4038959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_4038959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038959 prefixEnd_4038959 := by exact prefixLift 4038959
  have htrace : WordTrace (prefixWord ++ tailWord_4038959) baseStart_4038959 baseEnd_4038959 := by
    simpa [prefixWord, tailWord_4038959, baseEnd_4038959] using wordTrace_append hprefix tailTrace_4038959
  have hstable : (prefixWord ++ tailWord_4038959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038959).length < 2 ^ (prefixWord ++ tailWord_4038959).sum := by decide
  have hdescent : baseEnd_4038959 < baseStart_4038959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038987 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_4038987 : Nat := 118140960795 + 4038987 * 2 ^ 59
def prefixEnd_4038987 : Nat := 4983230072969 + 3 ^ 40 * 4038987 * 2
def baseEnd_4038987 : Nat := 1382627792174196118991695

theorem tailTrace_4038987 : CollatzResearch.WordTrace tailWord_4038987 prefixEnd_4038987 1382627792174196118991695 := by
  unfold tailWord_4038987
  simp only [CollatzResearch.WordTrace]
  refine ⟨147313958218447377906603215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98209305478964918604402143 147313958218447377906603215)
  ·
    refine ⟨220970937327671066859904823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147313958218447377906603215 220970937327671066859904823)
    ·
      refine ⟨331456405991506600289857235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220970937327671066859904823 331456405991506600289857235)
      ·
        refine ⟨497184608987259900434785853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331456405991506600289857235 497184608987259900434785853)
        ·
          refine ⟨186444228370222462663044695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497184608987259900434785853 186444228370222462663044695)
          ·
            refine ⟨279666342555333693994567043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186444228370222462663044695 279666342555333693994567043)
            ·
              refine ⟨419499513833000540991850565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279666342555333693994567043 419499513833000540991850565)
              ·
                refine ⟨78656158843687601435971981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419499513833000540991850565 78656158843687601435971981)
                ·
                  refine ⟨29496059566382850538489493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78656158843687601435971981 29496059566382850538489493)
                  ·
                    refine ⟨1382627792174196118991695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29496059566382850538489493 1382627792174196118991695)
                    ·
                      rfl

theorem cell22_4038987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_4038987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4038987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4038987 prefixEnd_4038987 := by exact prefixLift 4038987
  have htrace : WordTrace (prefixWord ++ tailWord_4038987) baseStart_4038987 baseEnd_4038987 := by
    simpa [prefixWord, tailWord_4038987, baseEnd_4038987] using wordTrace_append hprefix tailTrace_4038987
  have hstable : (prefixWord ++ tailWord_4038987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038987).length < 2 ^ (prefixWord ++ tailWord_4038987).sum := by decide
  have hdescent : baseEnd_4038987 < baseStart_4038987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039021 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_4039021 : Nat := 118140960795 + 4039021 * 2 ^ 59
def prefixEnd_4039021 : Nat := 4983230072969 + 3 ^ 40 * 4039021 * 2
def baseEnd_4039021 : Nat := 1382639431069031363641591

theorem tailTrace_4039021 : CollatzResearch.WordTrace tailWord_4039021 prefixEnd_4039021 1382639431069031363641591 := by
  unfold tailWord_4039021
  simp only [CollatzResearch.WordTrace]
  refine ⟨147315198300324201713340917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98210132200216134475560611 147315198300324201713340917)
  ·
    refine ⟨13810799840655393910625711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147315198300324201713340917 13810799840655393910625711)
    ·
      refine ⟨20716199760983090865938567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13810799840655393910625711 20716199760983090865938567)
      ·
        refine ⟨31074299641474636298907851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20716199760983090865938567 31074299641474636298907851)
        ·
          refine ⟨46611449462211954448361777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31074299641474636298907851 46611449462211954448361777)
          ·
            refine ⟨34958587096658965836271333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46611449462211954448361777 34958587096658965836271333)
            ·
              refine ⟨6554735080623556094300875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34958587096658965836271333 6554735080623556094300875)
              ·
                refine ⟨9832102620935334141451313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554735080623556094300875 9832102620935334141451313)
                ·
                  refine ⟨7374076965701500606088485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9832102620935334141451313 7374076965701500606088485)
                  ·
                    refine ⟨1382639431069031363641591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7374076965701500606088485 1382639431069031363641591)
                    ·
                      rfl

theorem cell22_4039021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_4039021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039021 prefixEnd_4039021 := by exact prefixLift 4039021
  have htrace : WordTrace (prefixWord ++ tailWord_4039021) baseStart_4039021 baseEnd_4039021 := by
    simpa [prefixWord, tailWord_4039021, baseEnd_4039021] using wordTrace_append hprefix tailTrace_4039021
  have hstable : (prefixWord ++ tailWord_4039021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039021).length < 2 ^ (prefixWord ++ tailWord_4039021).sum := by decide
  have hdescent : baseEnd_4039021 < baseStart_4039021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039049 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_4039049 : Nat := 118140960795 + 4039049 * 2 ^ 59
def prefixEnd_4039049 : Nat := 4983230072969 + 3 ^ 40 * 4039049 * 2
def baseEnd_4039049 : Nat := 1382649016041248623941505

theorem tailTrace_4039049 : CollatzResearch.WordTrace tailWord_4039049 prefixEnd_4039049 1382649016041248623941505 := by
  unfold tailWord_4039049
  simp only [CollatzResearch.WordTrace]
  refine ⟨147316219544222762495360201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98210813029481841663573467 147316219544222762495360201)
  ·
    refine ⟨110487164658167071871520151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147316219544222762495360201 110487164658167071871520151)
    ·
      refine ⟨165730746987250607807280227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110487164658167071871520151 165730746987250607807280227)
      ·
        refine ⟨248596120480875911710920341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165730746987250607807280227 248596120480875911710920341)
        ·
          refine ⟨11652943147541058361449391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248596120480875911710920341 11652943147541058361449391)
          ·
            refine ⟨17479414721311587542174087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652943147541058361449391 17479414721311587542174087)
            ·
              refine ⟨26219122081967381313261131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17479414721311587542174087 26219122081967381313261131)
              ·
                refine ⟨39328683122951071969891697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26219122081967381313261131 39328683122951071969891697)
                ·
                  refine ⟨29496512342213303977418773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39328683122951071969891697 29496512342213303977418773)
                  ·
                    refine ⟨1382649016041248623941505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29496512342213303977418773 1382649016041248623941505)
                    ·
                      rfl

theorem cell22_4039049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_4039049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039049 prefixEnd_4039049 := by exact prefixLift 4039049
  have htrace : WordTrace (prefixWord ++ tailWord_4039049) baseStart_4039049 baseEnd_4039049 := by
    simpa [prefixWord, tailWord_4039049, baseEnd_4039049] using wordTrace_append hprefix tailTrace_4039049
  have hstable : (prefixWord ++ tailWord_4039049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039049).length < 2 ^ (prefixWord ++ tailWord_4039049).sum := by decide
  have hdescent : baseEnd_4039049 < baseStart_4039049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039158 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_4039158 : Nat := 118140960795 + 4039158 * 2 ^ 59
def prefixEnd_4039158 : Nat := 4983230072969 + 3 ^ 40 * 4039158 * 2
def baseEnd_4039158 : Nat := 1382686328968808672966171

theorem tailTrace_4039158 : CollatzResearch.WordTrace tailWord_4039158 prefixEnd_4039158 1382686328968808672966171 := by
  unfold tailWord_4039158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207512193801742131942383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98213463400551916074052085 9207512193801742131942383)
  ·
    refine ⟨13811268290702613197913575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9207512193801742131942383 13811268290702613197913575)
    ·
      refine ⟨20716902436053919796870363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13811268290702613197913575 20716902436053919796870363)
      ·
        refine ⟨31075353654080879695305545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20716902436053919796870363 31075353654080879695305545)
        ·
          refine ⟨23306515240560659771479159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31075353654080879695305545 23306515240560659771479159)
          ·
            refine ⟨34959772860840989657218739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23306515240560659771479159 34959772860840989657218739)
            ·
              refine ⟨52439659291261484485828109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34959772860840989657218739 52439659291261484485828109)
              ·
                refine ⟨19664872234223056682185541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52439659291261484485828109 19664872234223056682185541)
                ·
                  refine ⟨3687163543916823127909789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19664872234223056682185541 3687163543916823127909789)
                  ·
                    refine ⟨1382686328968808672966171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687163543916823127909789 1382686328968808672966171)
                    ·
                      rfl

theorem cell22_4039158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_4039158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039158 prefixEnd_4039158 := by exact prefixLift 4039158
  have htrace : WordTrace (prefixWord ++ tailWord_4039158) baseStart_4039158 baseEnd_4039158 := by
    simpa [prefixWord, tailWord_4039158, baseEnd_4039158] using wordTrace_append hprefix tailTrace_4039158
  have hstable : (prefixWord ++ tailWord_4039158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039158).length < 2 ^ (prefixWord ++ tailWord_4039158).sum := by decide
  have hdescent : baseEnd_4039158 < baseStart_4039158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039175 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 2, 3]
def baseStart_4039175 : Nat := 118140960795 + 4039175 * 2 ^ 59
def prefixEnd_4039175 : Nat := 4983230072969 + 3 ^ 40 * 4039175 * 2
def baseEnd_4039175 : Nat := 1382692148416226295291119

theorem tailTrace_4039175 : CollatzResearch.WordTrace tailWord_4039175 prefixEnd_4039175 1382692148416226295291119 := by
  unfold tailWord_4039175
  simp only [CollatzResearch.WordTrace]
  refine ⟨147320815141766286014446979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98213876761177524009631319 147320815141766286014446979)
  ·
    refine ⟨220981222712649429021670469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147320815141766286014446979 220981222712649429021670469)
    ·
      refine ⟨41433979258621767941563213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220981222712649429021670469 41433979258621767941563213)
      ·
        refine ⟨15537742221983162978086205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41433979258621767941563213 15537742221983162978086205)
        ·
          refine ⟨5826653333243686116782327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15537742221983162978086205 5826653333243686116782327)
          ·
            refine ⟨8739979999865529175173491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826653333243686116782327 8739979999865529175173491)
            ·
              refine ⟨13109969999798293762760237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739979999865529175173491 13109969999798293762760237)
              ·
                refine ⟨4916238749924360161035089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13109969999798293762760237 4916238749924360161035089)
                ·
                  refine ⟨3687179062443270120776317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916238749924360161035089 3687179062443270120776317)
                  ·
                    refine ⟨1382692148416226295291119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687179062443270120776317 1382692148416226295291119)
                    ·
                      rfl

theorem cell22_4039175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_4039175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039175 prefixEnd_4039175 := by exact prefixLift 4039175
  have htrace : WordTrace (prefixWord ++ tailWord_4039175) baseStart_4039175 baseEnd_4039175 := by
    simpa [prefixWord, tailWord_4039175, baseEnd_4039175] using wordTrace_append hprefix tailTrace_4039175
  have hstable : (prefixWord ++ tailWord_4039175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039175).length < 2 ^ (prefixWord ++ tailWord_4039175).sum := by decide
  have hdescent : baseEnd_4039175 < baseStart_4039175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039188 : List Nat := [2, 4, 3, 1, 1, 1, 2, 8]
def baseStart_4039188 : Nat := 118140960795 + 4039188 * 2 ^ 59
def prefixEnd_4039188 : Nat := 4983230072969 + 3 ^ 40 * 4039188 * 2
def baseEnd_4039188 : Nat := 153632955397988732746231

theorem tailTrace_4039188 : CollatzResearch.WordTrace tailWord_4039188 prefixEnd_4039188 153632955397988732746231 := by
  unfold tailWord_4039188
  simp only [CollatzResearch.WordTrace]
  refine ⟨73660644645359594617335109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98214192860479459489780145 73660644645359594617335109)
  ·
    refine ⟨13811370871004923990750333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73660644645359594617335109 13811370871004923990750333)
    ·
      refine ⟨5179264076626846496531375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13811370871004923990750333 5179264076626846496531375)
      ·
        refine ⟨7768896114940269744797063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179264076626846496531375 7768896114940269744797063)
        ·
          refine ⟨11653344172410404617195595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768896114940269744797063 11653344172410404617195595)
          ·
            refine ⟨17480016258615606925793393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11653344172410404617195595 17480016258615606925793393)
            ·
              refine ⟨13110012193961705194345045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17480016258615606925793393 13110012193961705194345045)
              ·
                refine ⟨153632955397988732746231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13110012193961705194345045 153632955397988732746231)
                ·
                  rfl

theorem cell22_4039188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_4039188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039188 prefixEnd_4039188 := by exact prefixLift 4039188
  have htrace : WordTrace (prefixWord ++ tailWord_4039188) baseStart_4039188 baseEnd_4039188 := by
    simpa [prefixWord, tailWord_4039188, baseEnd_4039188] using wordTrace_append hprefix tailTrace_4039188
  have hstable : (prefixWord ++ tailWord_4039188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039188).length < 2 ^ (prefixWord ++ tailWord_4039188).sum := by decide
  have hdescent : baseEnd_4039188 < baseStart_4039188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039216 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_4039216 : Nat := 118140960795 + 4039216 * 2 ^ 59
def prefixEnd_4039216 : Nat := 4983230072969 + 3 ^ 40 * 4039216 * 2
def baseEnd_4039216 : Nat := 460902061184705285005331

theorem tailTrace_4039216 : CollatzResearch.WordTrace tailWord_4039216 prefixEnd_4039216 460902061184705285005331 := by
  unfold tailWord_4039216
  simp only [CollatzResearch.WordTrace]
  refine ⟨73661155267308875008344751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98214873689745166677793001 73661155267308875008344751)
  ·
    refine ⟨110491732900963312512517127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73661155267308875008344751 110491732900963312512517127)
    ·
      refine ⟨165737599351444968768775691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110491732900963312512517127 165737599351444968768775691)
      ·
        refine ⟨248606399027167453153163537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165737599351444968768775691 248606399027167453153163537)
        ·
          refine ⟨186454799270375589864872653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248606399027167453153163537 186454799270375589864872653)
          ·
            refine ⟨69920549726390846199327245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186454799270375589864872653 69920549726390846199327245)
            ·
              refine ⟨26220206147396567324747717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69920549726390846199327245 26220206147396567324747717)
              ·
                refine ⟨4916288652636856373390197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26220206147396567324747717 4916288652636856373390197)
                ·
                  refine ⟨460902061184705285005331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916288652636856373390197 460902061184705285005331)
                  ·
                    rfl

theorem cell22_4039216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_4039216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039216 prefixEnd_4039216 := by exact prefixLift 4039216
  have htrace : WordTrace (prefixWord ++ tailWord_4039216) baseStart_4039216 baseEnd_4039216 := by
    simpa [prefixWord, tailWord_4039216, baseEnd_4039216] using wordTrace_append hprefix tailTrace_4039216
  have hstable : (prefixWord ++ tailWord_4039216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039216).length < 2 ^ (prefixWord ++ tailWord_4039216).sum := by decide
  have hdescent : baseEnd_4039216 < baseStart_4039216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039231 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 2, 5]
def baseStart_4039231 : Nat := 118140960795 + 4039231 * 2 ^ 59
def prefixEnd_4039231 : Nat := 4983230072969 + 3 ^ 40 * 4039231 * 2
def baseEnd_4039231 : Nat := 1382711318360660815890947

theorem tailTrace_4039231 : CollatzResearch.WordTrace tailWord_4039231 prefixEnd_4039231 1382711318360660815890947 := by
  unfold tailWord_4039231
  simp only [CollatzResearch.WordTrace]
  refine ⟨147322857629563407578485547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98215238419708938385657031 147322857629563407578485547)
  ·
    refine ⟨220984286444345111367728321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147322857629563407578485547 220984286444345111367728321)
    ·
      refine ⟨165738214833258833525796241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220984286444345111367728321 165738214833258833525796241)
      ·
        refine ⟨124303661124944125144347181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165738214833258833525796241 124303661124944125144347181)
        ·
          refine ⟨46613872921854046929130193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124303661124944125144347181 46613872921854046929130193)
          ·
            refine ⟨34960404691390535196847645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46613872921854046929130193 34960404691390535196847645)
            ·
              refine ⟨13110151759271450698817867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34960404691390535196847645 13110151759271450698817867)
              ·
                refine ⟨19665227638907176048226801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13110151759271450698817867 19665227638907176048226801)
                ·
                  refine ⟨14748920729180382036170101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19665227638907176048226801 14748920729180382036170101)
                  ·
                    refine ⟨1382711318360660815890947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14748920729180382036170101 1382711318360660815890947)
                    ·
                      rfl

theorem cell22_4039231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_4039231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039231 prefixEnd_4039231 := by exact prefixLift 4039231
  have htrace : WordTrace (prefixWord ++ tailWord_4039231) baseStart_4039231 baseEnd_4039231 := by
    simpa [prefixWord, tailWord_4039231, baseEnd_4039231] using wordTrace_append hprefix tailTrace_4039231
  have hstable : (prefixWord ++ tailWord_4039231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039231).length < 2 ^ (prefixWord ++ tailWord_4039231).sum := by decide
  have hdescent : baseEnd_4039231 < baseStart_4039231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039233 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 5]
def baseStart_4039233 : Nat := 118140960795 + 4039233 * 2 ^ 59
def prefixEnd_4039233 : Nat := 4983230072969 + 3 ^ 40 * 4039233 * 2
def baseEnd_4039233 : Nat := 460904001000511159113647

theorem tailTrace_4039233 : CollatzResearch.WordTrace tailWord_4039233 prefixEnd_4039233 460904001000511159113647 := by
  unfold tailWord_4039233
  simp only [CollatzResearch.WordTrace]
  refine ⟨147322930575556161920058353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98215287050370774613372235 147322930575556161920058353)
  ·
    refine ⟨110492197931667121440043765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147322930575556161920058353 110492197931667121440043765)
    ·
      refine ⟨10358643556093792635004103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110492197931667121440043765 10358643556093792635004103)
      ·
        refine ⟨15537965334140688952506155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10358643556093792635004103 15537965334140688952506155)
        ·
          refine ⟨23306948001211033428759233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15537965334140688952506155 23306948001211033428759233)
          ·
            refine ⟨17480211000908275071569425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23306948001211033428759233 17480211000908275071569425)
            ·
              refine ⟨13110158250681206303677069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17480211000908275071569425 13110158250681206303677069)
              ·
                refine ⟨4916309344005452363878901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13110158250681206303677069 4916309344005452363878901)
                ·
                  refine ⟨460904001000511159113647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916309344005452363878901 460904001000511159113647)
                  ·
                    rfl

theorem cell22_4039233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_4039233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039233 prefixEnd_4039233 := by exact prefixLift 4039233
  have htrace : WordTrace (prefixWord ++ tailWord_4039233) baseStart_4039233 baseEnd_4039233 := by
    simpa [prefixWord, tailWord_4039233, baseEnd_4039233] using wordTrace_append hprefix tailTrace_4039233
  have hstable : (prefixWord ++ tailWord_4039233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039233).length < 2 ^ (prefixWord ++ tailWord_4039233).sum := by decide
  have hdescent : baseEnd_4039233 < baseStart_4039233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039276 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_4039276 : Nat := 118140960795 + 4039276 * 2 ^ 59
def prefixEnd_4039276 : Nat := 4983230072969 + 3 ^ 40 * 4039276 * 2
def baseEnd_4039276 : Nat := 1382726722780295698515809

theorem tailTrace_4039276 : CollatzResearch.WordTrace tailWord_4039276 prefixEnd_4039276 1382726722780295698515809 := by
  unfold tailWord_4039276
  simp only [CollatzResearch.WordTrace]
  refine ⟨73662249457200190131936841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98216332609600253509249121 73662249457200190131936841)
  ·
    refine ⟨55246687092900142598952631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73662249457200190131936841 55246687092900142598952631)
    ·
      refine ⟨82870030639350213898428947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55246687092900142598952631 82870030639350213898428947)
      ·
        refine ⟨124305045959025320847643421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82870030639350213898428947 124305045959025320847643421)
        ·
          refine ⟨46614392234634495317866283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124305045959025320847643421 46614392234634495317866283)
          ·
            refine ⟨69921588351951742976799425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46614392234634495317866283 69921588351951742976799425)
            ·
              refine ⟨52441191263963807232599569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69921588351951742976799425 52441191263963807232599569)
              ·
                refine ⟨39330893447972855424449677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52441191263963807232599569 39330893447972855424449677)
                ·
                  refine ⟨14749085042989820784168629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39330893447972855424449677 14749085042989820784168629)
                  ·
                    refine ⟨1382726722780295698515809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14749085042989820784168629 1382726722780295698515809)
                    ·
                      rfl

theorem cell22_4039276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_4039276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039276 prefixEnd_4039276 := by exact prefixLift 4039276
  have htrace : WordTrace (prefixWord ++ tailWord_4039276) baseStart_4039276 baseEnd_4039276 := by
    simpa [prefixWord, tailWord_4039276, baseEnd_4039276] using wordTrace_append hprefix tailTrace_4039276
  have hstable : (prefixWord ++ tailWord_4039276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039276).length < 2 ^ (prefixWord ++ tailWord_4039276).sum := by decide
  have hdescent : baseEnd_4039276 < baseStart_4039276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039278 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_4039278 : Nat := 118140960795 + 4039278 * 2 ^ 59
def prefixEnd_4039278 : Nat := 4983230072969 + 3 ^ 40 * 4039278 * 2
def baseEnd_4039278 : Nat := 460909135807056119988601

theorem tailTrace_4039278 : CollatzResearch.WordTrace tailWord_4039278 prefixEnd_4039278 460909135807056119988601 := by
  unfold tailWord_4039278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18415571482549141825680811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98216381240262089736964325 18415571482549141825680811)
  ·
    refine ⟨27623357223823712738521217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18415571482549141825680811 27623357223823712738521217)
    ·
      refine ⟨20717517917867784553890913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27623357223823712738521217 20717517917867784553890913)
      ·
        refine ⟨15538138438400838415418185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20717517917867784553890913 15538138438400838415418185)
        ·
          refine ⟨11653603828800628811563639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15538138438400838415418185 11653603828800628811563639)
          ·
            refine ⟨17480405743200943217345459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11653603828800628811563639 17480405743200943217345459)
            ·
              refine ⟨26220608614801414826018189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17480405743200943217345459 26220608614801414826018189)
              ·
                refine ⟨9832728230550530559756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26220608614801414826018189 9832728230550530559756821)
                ·
                  refine ⟨460909135807056119988601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9832728230550530559756821 460909135807056119988601)
                  ·
                    rfl

theorem cell22_4039278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_4039278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039278 prefixEnd_4039278 := by exact prefixLift 4039278
  have htrace : WordTrace (prefixWord ++ tailWord_4039278) baseStart_4039278 baseEnd_4039278 := by
    simpa [prefixWord, tailWord_4039278, baseEnd_4039278] using wordTrace_append hprefix tailTrace_4039278
  have hstable : (prefixWord ++ tailWord_4039278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039278).length < 2 ^ (prefixWord ++ tailWord_4039278).sum := by decide
  have hdescent : baseEnd_4039278 < baseStart_4039278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039291 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 6, 4]
def baseStart_4039291 : Nat := 118140960795 + 4039291 * 2 ^ 59
def prefixEnd_4039291 : Nat := 4983230072969 + 3 ^ 40 * 4039291 * 2
def baseEnd_4039291 : Nat := 1382731857586840659390763

theorem tailTrace_4039291 : CollatzResearch.WordTrace tailWord_4039291 prefixEnd_4039291 1382731857586840659390763 := by
  unfold tailWord_4039291
  simp only [CollatzResearch.WordTrace]
  refine ⟨147325046009346037825669727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98216697339564025217113151 147325046009346037825669727)
  ·
    refine ⟨220987569014019056738504591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147325046009346037825669727 220987569014019056738504591)
    ·
      refine ⟨331481353521028585107756887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220987569014019056738504591 331481353521028585107756887)
      ·
        refine ⟨497222030281542877661635331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331481353521028585107756887 497222030281542877661635331)
        ·
          refine ⟨745833045422314316492452997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497222030281542877661635331 745833045422314316492452997)
          ·
            refine ⟨139843696016683934342334937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 745833045422314316492452997 139843696016683934342334937)
            ·
              refine ⟨104882772012512950756751203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139843696016683934342334937 104882772012512950756751203)
              ·
                refine ⟨157324158018769426135126805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104882772012512950756751203 157324158018769426135126805)
                ·
                  refine ⟨7374569907129816850084069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157324158018769426135126805 7374569907129816850084069)
                  ·
                    refine ⟨1382731857586840659390763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7374569907129816850084069 1382731857586840659390763)
                    ·
                      rfl

theorem cell22_4039291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_4039291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039291 prefixEnd_4039291 := by exact prefixLift 4039291
  have htrace : WordTrace (prefixWord ++ tailWord_4039291) baseStart_4039291 baseEnd_4039291 := by
    simpa [prefixWord, tailWord_4039291, baseEnd_4039291] using wordTrace_append hprefix tailTrace_4039291
  have hstable : (prefixWord ++ tailWord_4039291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039291).length < 2 ^ (prefixWord ++ tailWord_4039291).sum := by decide
  have hdescent : baseEnd_4039291 < baseStart_4039291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039400 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4039400 : Nat := 118140960795 + 4039400 * 2 ^ 59
def prefixEnd_4039400 : Nat := 4983230072969 + 3 ^ 40 * 4039400 * 2
def baseEnd_4039400 : Nat := 1382769170514400708415429

theorem tailTrace_4039400 : CollatzResearch.WordTrace tailWord_4039400 prefixEnd_4039400 1382769170514400708415429 := by
  unfold tailWord_4039400
  simp only [CollatzResearch.WordTrace]
  refine ⟨73664510782975574720693827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98219347710634099627591769 73664510782975574720693827)
  ·
    refine ⟨110496766174463362081040741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73664510782975574720693827 110496766174463362081040741)
    ·
      refine ⟨20718143657711880390195139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110496766174463362081040741 20718143657711880390195139)
      ·
        refine ⟨31077215486567820585292709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20718143657711880390195139 31077215486567820585292709)
        ·
          refine ⟨5826977903731466359742383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31077215486567820585292709 5826977903731466359742383)
          ·
            refine ⟨8740466855597199539613575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826977903731466359742383 8740466855597199539613575)
            ·
              refine ⟨13110700283395799309420363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740466855597199539613575 13110700283395799309420363)
              ·
                refine ⟨19666050425093698964130545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13110700283395799309420363 19666050425093698964130545)
                ·
                  refine ⟨14749537818820274223097909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19666050425093698964130545 14749537818820274223097909)
                  ·
                    refine ⟨1382769170514400708415429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14749537818820274223097909 1382769170514400708415429)
                    ·
                      rfl

theorem cell22_4039400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4039400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039400 prefixEnd_4039400 := by exact prefixLift 4039400
  have htrace : WordTrace (prefixWord ++ tailWord_4039400) baseStart_4039400 baseEnd_4039400 := by
    simpa [prefixWord, tailWord_4039400, baseEnd_4039400] using wordTrace_append hprefix tailTrace_4039400
  have hstable : (prefixWord ++ tailWord_4039400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039400).length < 2 ^ (prefixWord ++ tailWord_4039400).sum := by decide
  have hdescent : baseEnd_4039400 < baseStart_4039400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039432 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 1, 4]
def baseStart_4039432 : Nat := 118140960795 + 4039432 * 2 ^ 59
def prefixEnd_4039432 : Nat := 4983230072969 + 3 ^ 40 * 4039432 * 2
def baseEnd_4039432 : Nat := 1382780124768363291615331

theorem tailTrace_4039432 : CollatzResearch.WordTrace tailWord_4039432 prefixEnd_4039432 1382780124768363291615331 := by
  unfold tailWord_4039432
  simp only [CollatzResearch.WordTrace]
  refine ⟨73665094350917609453276275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98220125801223479271035033 73665094350917609453276275)
  ·
    refine ⟨110497641526376414179914413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73665094350917609453276275 110497641526376414179914413)
    ·
      refine ⟨41436615572391155317467905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110497641526376414179914413 41436615572391155317467905)
      ·
        refine ⟨31077461679293366488100929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41436615572391155317467905 31077461679293366488100929)
        ·
          refine ⟨23308096259470024866075697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31077461679293366488100929 23308096259470024866075697)
          ·
            refine ⟨17481072194602518649556773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23308096259470024866075697 17481072194602518649556773)
            ·
              refine ⟨3277701036487972246791895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17481072194602518649556773 3277701036487972246791895)
              ·
                refine ⟨4916551554731958370187843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277701036487972246791895 4916551554731958370187843)
                ·
                  refine ⟨7374827332097937555281765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916551554731958370187843 7374827332097937555281765)
                  ·
                    refine ⟨1382780124768363291615331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7374827332097937555281765 1382780124768363291615331)
                    ·
                      rfl

theorem cell22_4039432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_4039432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039432 prefixEnd_4039432 := by exact prefixLift 4039432
  have htrace : WordTrace (prefixWord ++ tailWord_4039432) baseStart_4039432 baseEnd_4039432 := by
    simpa [prefixWord, tailWord_4039432, baseEnd_4039432] using wordTrace_append hprefix tailTrace_4039432
  have hstable : (prefixWord ++ tailWord_4039432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039432).length < 2 ^ (prefixWord ++ tailWord_4039432).sum := by decide
  have hdescent : baseEnd_4039432 < baseStart_4039432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039443 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 4, 4]
def baseStart_4039443 : Nat := 118140960795 + 4039443 * 2 ^ 59
def prefixEnd_4039443 : Nat := 4983230072969 + 3 ^ 40 * 4039443 * 2
def baseEnd_4039443 : Nat := 1382783890293162929590297

theorem tailTrace_4039443 : CollatzResearch.WordTrace tailWord_4039443 prefixEnd_4039443 1382783890293162929590297 := by
  unfold tailWord_4039443
  simp only [CollatzResearch.WordTrace]
  refine ⟨147330589904795367785202983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98220393269863578523468655 147330589904795367785202983)
  ·
    refine ⟨220995884857193051677804475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147330589904795367785202983 220995884857193051677804475)
    ·
      refine ⟨331493827285789577516706713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220995884857193051677804475 331493827285789577516706713)
      ·
        refine ⟨248620370464342183137530035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331493827285789577516706713 248620370464342183137530035)
        ·
          refine ⟨372930555696513274706295053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248620370464342183137530035 372930555696513274706295053)
          ·
            refine ⟨139848958386192478014860645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372930555696513274706295053 139848958386192478014860645)
            ·
              refine ⟨26221679697411089627786371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139848958386192478014860645 26221679697411089627786371)
              ·
                refine ⟨39332519546116634441679557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26221679697411089627786371 39332519546116634441679557)
                ·
                  refine ⟨7374847414896868957814917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39332519546116634441679557 7374847414896868957814917)
                  ·
                    refine ⟨1382783890293162929590297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7374847414896868957814917 1382783890293162929590297)
                    ·
                      rfl

theorem cell22_4039443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_4039443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039443 prefixEnd_4039443 := by exact prefixLift 4039443
  have htrace : WordTrace (prefixWord ++ tailWord_4039443) baseStart_4039443 baseEnd_4039443 := by
    simpa [prefixWord, tailWord_4039443, baseEnd_4039443] using wordTrace_append hprefix tailTrace_4039443
  have hstable : (prefixWord ++ tailWord_4039443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039443).length < 2 ^ (prefixWord ++ tailWord_4039443).sum := by decide
  have hdescent : baseEnd_4039443 < baseStart_4039443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039445 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_4039445 : Nat := 118140960795 + 4039445 * 2 ^ 59
def prefixEnd_4039445 : Nat := 4983230072969 + 3 ^ 40 * 4039445 * 2
def baseEnd_4039445 : Nat := 1382784574934035591040291

theorem tailTrace_4039445 : CollatzResearch.WordTrace tailWord_4039445 prefixEnd_4039445 1382784574934035591040291 := by
  unfold tailWord_4039445
  simp only [CollatzResearch.WordTrace]
  refine ⟨147330662850788122126775789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98220441900525414751183859 147330662850788122126775789)
  ·
    refine ⟨55248998569045545797540921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147330662850788122126775789 55248998569045545797540921)
    ·
      refine ⟨41436748926784159348155691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55248998569045545797540921 41436748926784159348155691)
      ·
        refine ⟨62155123390176239022233537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41436748926784159348155691 62155123390176239022233537)
        ·
          refine ⟨46616342542632179266675153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62155123390176239022233537 46616342542632179266675153)
          ·
            refine ⟨34962256906974134450006365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46616342542632179266675153 34962256906974134450006365)
            ·
              refine ⟨13110846340115300418752387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34962256906974134450006365 13110846340115300418752387)
              ·
                refine ⟨19666269510172950628128581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13110846340115300418752387 19666269510172950628128581)
                ·
                  refine ⟨3687425533157428242774109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19666269510172950628128581 3687425533157428242774109)
                  ·
                    refine ⟨1382784574934035591040291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687425533157428242774109 1382784574934035591040291)
                    ·
                      rfl

theorem cell22_4039445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_4039445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039445 prefixEnd_4039445 := by exact prefixLift 4039445
  have htrace : WordTrace (prefixWord ++ tailWord_4039445) baseStart_4039445 baseEnd_4039445 := by
    simpa [prefixWord, tailWord_4039445, baseEnd_4039445] using wordTrace_append hprefix tailTrace_4039445
  have hstable : (prefixWord ++ tailWord_4039445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039445).length < 2 ^ (prefixWord ++ tailWord_4039445).sum := by decide
  have hdescent : baseEnd_4039445 < baseStart_4039445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039473 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_4039473 : Nat := 118140960795 + 4039473 * 2 ^ 59
def prefixEnd_4039473 : Nat := 4983230072969 + 3 ^ 40 * 4039473 * 2
def baseEnd_4039473 : Nat := 1382794159906252851340205

theorem tailTrace_4039473 : CollatzResearch.WordTrace tailWord_4039473 prefixEnd_4039473 1382794159906252851340205 := by
  unfold tailWord_4039473
  simp only [CollatzResearch.WordTrace]
  refine ⟨147331684094686682908795073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98221122729791121939196715 147331684094686682908795073)
  ·
    refine ⟨110498763071015012181596305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147331684094686682908795073 110498763071015012181596305)
    ·
      refine ⟨82874072303261259136197229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110498763071015012181596305 82874072303261259136197229)
      ·
        refine ⟨31077777113722972176073961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82874072303261259136197229 31077777113722972176073961)
        ·
          refine ⟨23308332835292229132055471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31077777113722972176073961 23308332835292229132055471)
          ·
            refine ⟨34962499252938343698083207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23308332835292229132055471 34962499252938343698083207)
            ·
              refine ⟨52443748879407515547124811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34962499252938343698083207 52443748879407515547124811)
              ·
                refine ⟨78665623319111273320687217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52443748879407515547124811 78665623319111273320687217)
                ·
                  refine ⟨58999217489333454990515413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78665623319111273320687217 58999217489333454990515413)
                  ·
                    refine ⟨1382794159906252851340205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58999217489333454990515413 1382794159906252851340205)
                    ·
                      rfl

theorem cell22_4039473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_4039473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039473 prefixEnd_4039473 := by exact prefixLift 4039473
  have htrace : WordTrace (prefixWord ++ tailWord_4039473) baseStart_4039473 baseEnd_4039473 := by
    simpa [prefixWord, tailWord_4039473, baseEnd_4039473] using wordTrace_append hprefix tailTrace_4039473
  have hstable : (prefixWord ++ tailWord_4039473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039473).length < 2 ^ (prefixWord ++ tailWord_4039473).sum := by decide
  have hdescent : baseEnd_4039473 < baseStart_4039473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039475 : List Nat := [1, 1, 1, 2, 6, 1, 4, 6]
def baseStart_4039475 : Nat := 118140960795 + 4039475 * 2 ^ 59
def prefixEnd_4039475 : Nat := 4983230072969 + 3 ^ 40 * 4039475 * 2
def baseEnd_4039475 : Nat := 153643871616347279198911

theorem tailTrace_4039475 : CollatzResearch.WordTrace tailWord_4039475 prefixEnd_4039475 153643871616347279198911 := by
  unfold tailWord_4039475
  simp only [CollatzResearch.WordTrace]
  refine ⟨147331757040679437250367879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98221171360452958166911919 147331757040679437250367879)
  ·
    refine ⟨220997635561019155875551819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147331757040679437250367879 220997635561019155875551819)
    ·
      refine ⟨331496453341528733813327729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220997635561019155875551819 331496453341528733813327729)
      ·
        refine ⟨248622340006146550359995797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331496453341528733813327729 248622340006146550359995797)
        ·
          refine ⟨11654172187788119548124803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248622340006146550359995797 11654172187788119548124803)
          ·
            refine ⟨17481258281682179322187205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654172187788119548124803 17481258281682179322187205)
            ·
              refine ⟨3277735927815408622910101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17481258281682179322187205 3277735927815408622910101)
              ·
                refine ⟨153643871616347279198911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3277735927815408622910101 153643871616347279198911)
                ·
                  rfl

theorem cell22_4039475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 6].length) (baseStart_4039475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039475 prefixEnd_4039475 := by exact prefixLift 4039475
  have htrace : WordTrace (prefixWord ++ tailWord_4039475) baseStart_4039475 baseEnd_4039475 := by
    simpa [prefixWord, tailWord_4039475, baseEnd_4039475] using wordTrace_append hprefix tailTrace_4039475
  have hstable : (prefixWord ++ tailWord_4039475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039475).length < 2 ^ (prefixWord ++ tailWord_4039475).sum := by decide
  have hdescent : baseEnd_4039475 < baseStart_4039475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039507 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 1, 3]
def baseStart_4039507 : Nat := 118140960795 + 4039507 * 2 ^ 59
def prefixEnd_4039507 : Nat := 4983230072969 + 3 ^ 40 * 4039507 * 2
def baseEnd_4039507 : Nat := 1382805798801088095990101

theorem tailTrace_4039507 : CollatzResearch.WordTrace tailWord_4039507 prefixEnd_4039507 1382805798801088095990101 := by
  unfold tailWord_4039507
  simp only [CollatzResearch.WordTrace]
  refine ⟨147332924176563506715532775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98221949451042337810355183 147332924176563506715532775)
  ·
    refine ⟨220999386264845260073299163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147332924176563506715532775 220999386264845260073299163)
    ·
      refine ⟨331499079397267890109948745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220999386264845260073299163 331499079397267890109948745)
      ·
        refine ⟨248624309547950917582461559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331499079397267890109948745 248624309547950917582461559)
        ·
          refine ⟨372936464321926376373692339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248624309547950917582461559 372936464321926376373692339)
          ·
            refine ⟨559404696482889564560538509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372936464321926376373692339 559404696482889564560538509)
            ·
              refine ⟨209776761181083586710201941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559404696482889564560538509 209776761181083586710201941)
              ·
                refine ⟨2458321420090823281760179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 209776761181083586710201941 2458321420090823281760179)
                ·
                  refine ⟨3687482130136234922640269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458321420090823281760179 3687482130136234922640269)
                  ·
                    refine ⟨1382805798801088095990101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687482130136234922640269 1382805798801088095990101)
                    ·
                      rfl

theorem cell22_4039507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 3].length) (baseStart_4039507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039507 prefixEnd_4039507 := by exact prefixLift 4039507
  have htrace : WordTrace (prefixWord ++ tailWord_4039507) baseStart_4039507 baseEnd_4039507 := by
    simpa [prefixWord, tailWord_4039507, baseEnd_4039507] using wordTrace_append hprefix tailTrace_4039507
  have hstable : (prefixWord ++ tailWord_4039507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039507).length < 2 ^ (prefixWord ++ tailWord_4039507).sum := by decide
  have hdescent : baseEnd_4039507 < baseStart_4039507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039520 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_4039520 : Nat := 118140960795 + 4039520 * 2 ^ 59
def prefixEnd_4039520 : Nat := 4983230072969 + 3 ^ 40 * 4039520 * 2
def baseEnd_4039520 : Nat := 460936749655586798471687

theorem tailTrace_4039520 : CollatzResearch.WordTrace tailWord_4039520 prefixEnd_4039520 460936749655586798471687 := by
  unfold tailWord_4039520
  simp only [CollatzResearch.WordTrace]
  refine ⟨73666699162758204967878007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98222265550344273290504009 73666699162758204967878007)
  ·
    refine ⟨110500048744137307451817011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73666699162758204967878007 110500048744137307451817011)
    ·
      refine ⟨165750073116205961177725517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110500048744137307451817011 165750073116205961177725517)
      ·
        refine ⟨62156277418577235441647069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165750073116205961177725517 62156277418577235441647069)
        ·
          refine ⟨23308604031966463290617651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62156277418577235441647069 23308604031966463290617651)
          ·
            refine ⟨34962906047949694935926477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23308604031966463290617651 34962906047949694935926477)
            ·
              refine ⟨13111089767981135600972429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34962906047949694935926477 13111089767981135600972429)
              ·
                refine ⟨4916658662992925850364661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13111089767981135600972429 4916658662992925850364661)
                ·
                  refine ⟨460936749655586798471687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916658662992925850364661 460936749655586798471687)
                  ·
                    rfl

theorem cell22_4039520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_4039520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039520 prefixEnd_4039520 := by exact prefixLift 4039520
  have htrace : WordTrace (prefixWord ++ tailWord_4039520) baseStart_4039520 baseEnd_4039520 := by
    simpa [prefixWord, tailWord_4039520, baseEnd_4039520] using wordTrace_append hprefix tailTrace_4039520
  have hstable : (prefixWord ++ tailWord_4039520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039520).length < 2 ^ (prefixWord ++ tailWord_4039520).sum := by decide
  have hdescent : baseEnd_4039520 < baseStart_4039520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039601 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 1, 4]
def baseStart_4039601 : Nat := 118140960795 + 4039601 * 2 ^ 59
def prefixEnd_4039601 : Nat := 4983230072969 + 3 ^ 40 * 4039601 * 2
def baseEnd_4039601 : Nat := 1382837976922103184139813

theorem tailTrace_4039601 : CollatzResearch.WordTrace tailWord_4039601 prefixEnd_4039601 1382837976922103184139813 := by
  unfold tailWord_4039601
  simp only [CollatzResearch.WordTrace]
  refine ⟨147336352638222960769454657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98224235092148640512969771 147336352638222960769454657)
  ·
    refine ⟨110502264478667220577090993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147336352638222960769454657 110502264478667220577090993)
    ·
      refine ⟨82876698359000415432818245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110502264478667220577090993 82876698359000415432818245)
      ·
        refine ⟨15539380942312577893653421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82876698359000415432818245 15539380942312577893653421)
        ·
          refine ⟨5827267853367216710120033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15539380942312577893653421 5827267853367216710120033)
          ·
            refine ⟨4370450890025412532590025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827267853367216710120033 4370450890025412532590025)
            ·
              refine ⟨3277838167519059399442519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370450890025412532590025 3277838167519059399442519)
              ·
                refine ⟨4916757251278589099163779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277838167519059399442519 4916757251278589099163779)
                ·
                  refine ⟨7375135876917883648745669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916757251278589099163779 7375135876917883648745669)
                  ·
                    refine ⟨1382837976922103184139813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375135876917883648745669 1382837976922103184139813)
                    ·
                      rfl

theorem cell22_4039601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_4039601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039601 prefixEnd_4039601 := by exact prefixLift 4039601
  have htrace : WordTrace (prefixWord ++ tailWord_4039601) baseStart_4039601 baseEnd_4039601 := by
    simpa [prefixWord, tailWord_4039601, baseEnd_4039601] using wordTrace_append hprefix tailTrace_4039601
  have hstable : (prefixWord ++ tailWord_4039601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039601).length < 2 ^ (prefixWord ++ tailWord_4039601).sum := by decide
  have hdescent : baseEnd_4039601 < baseStart_4039601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039682 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_4039682 : Nat := 118140960795 + 4039682 * 2 ^ 59
def prefixEnd_4039682 : Nat := 4983230072969 + 3 ^ 40 * 4039682 * 2
def baseEnd_4039682 : Nat := 1382865704877445972864565

theorem tailTrace_4039682 : CollatzResearch.WordTrace tailWord_4039682 prefixEnd_4039682 1382865704877445972864565 := by
  unfold tailWord_4039682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36834826737732377900788325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98226204633953007735435533 36834826737732377900788325)
  ·
    refine ⟨6906530013324820856397811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36834826737732377900788325 6906530013324820856397811)
    ·
      refine ⟨10359795019987231284596717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6906530013324820856397811 10359795019987231284596717)
      ·
        refine ⟨3884923132495211731723769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10359795019987231284596717 3884923132495211731723769)
        ·
          refine ⟨2913692349371408798792827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3884923132495211731723769 2913692349371408798792827)
          ·
            refine ⟨4370538524057113198189241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913692349371408798792827 4370538524057113198189241)
            ·
              refine ⟨3277903893042834898641931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370538524057113198189241 3277903893042834898641931)
              ·
                refine ⟨4916855839564252347962897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277903893042834898641931 4916855839564252347962897)
                ·
                  refine ⟨3687641879673189260972173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916855839564252347962897 3687641879673189260972173)
                  ·
                    refine ⟨1382865704877445972864565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687641879673189260972173 1382865704877445972864565)
                    ·
                      rfl

theorem cell22_4039682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_4039682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039682 prefixEnd_4039682 := by exact prefixLift 4039682
  have htrace : WordTrace (prefixWord ++ tailWord_4039682) baseStart_4039682 baseEnd_4039682 := by
    simpa [prefixWord, tailWord_4039682, baseEnd_4039682] using wordTrace_append hprefix tailTrace_4039682
  have hstable : (prefixWord ++ tailWord_4039682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039682).length < 2 ^ (prefixWord ++ tailWord_4039682).sum := by decide
  have hdescent : baseEnd_4039682 < baseStart_4039682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039749 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_4039749 : Nat := 118140960795 + 4039749 * 2 ^ 59
def prefixEnd_4039749 : Nat := 4983230072969 + 3 ^ 40 * 4039749 * 2
def baseEnd_4039749 : Nat := 1382888640346680131439359

theorem tailTrace_4039749 : CollatzResearch.WordTrace tailWord_4039749 prefixEnd_4039749 1382888640346680131439359 := by
  unfold tailWord_4039749
  simp only [CollatzResearch.WordTrace]
  refine ⟨147341750641686782045842301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98227833761124521363894867 147341750641686782045842301)
  ·
    refine ⟨55253156490632543267190863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147341750641686782045842301 55253156490632543267190863)
    ·
      refine ⟨82879734735948814900786295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55253156490632543267190863 82879734735948814900786295)
      ·
        refine ⟨124319602103923222351179443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82879734735948814900786295 124319602103923222351179443)
        ·
          refine ⟨186479403155884833526769165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124319602103923222351179443 186479403155884833526769165)
          ·
            refine ⟨69929776183456812572538437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186479403155884833526769165 69929776183456812572538437)
            ·
              refine ⟨13111833034398152357350957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69929776183456812572538437 13111833034398152357350957)
              ·
                refine ⟨4916937387899307134006609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13111833034398152357350957 4916937387899307134006609)
                ·
                  refine ⟨3687703040924480350504957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916937387899307134006609 3687703040924480350504957)
                  ·
                    refine ⟨1382888640346680131439359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687703040924480350504957 1382888640346680131439359)
                    ·
                      rfl

theorem cell22_4039749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_4039749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039749 prefixEnd_4039749 := by exact prefixLift 4039749
  have htrace : WordTrace (prefixWord ++ tailWord_4039749) baseStart_4039749 baseEnd_4039749 := by
    simpa [prefixWord, tailWord_4039749, baseEnd_4039749] using wordTrace_append hprefix tailTrace_4039749
  have hstable : (prefixWord ++ tailWord_4039749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039749).length < 2 ^ (prefixWord ++ tailWord_4039749).sum := by decide
  have hdescent : baseEnd_4039749 < baseStart_4039749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039764 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_4039764 : Nat := 118140960795 + 4039764 * 2 ^ 59
def prefixEnd_4039764 : Nat := 4983230072969 + 3 ^ 40 * 4039764 * 2
def baseEnd_4039764 : Nat := 1382893775153225092314313

theorem tailTrace_4039764 : CollatzResearch.WordTrace tailWord_4039764 prefixEnd_4039764 1382893775153225092314313 := by
  unfold tailWord_4039764
  simp only [CollatzResearch.WordTrace]
  refine ⟨73671148868316219803819173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98228198491088293071758897 73671148868316219803819173)
  ·
    refine ⟨13813340412809291213216095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73671148868316219803819173 13813340412809291213216095)
    ·
      refine ⟨20720010619213936819824143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813340412809291213216095 20720010619213936819824143)
      ·
        refine ⟨31080015928820905229736215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20720010619213936819824143 31080015928820905229736215)
        ·
          refine ⟨46620023893231357844604323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31080015928820905229736215 46620023893231357844604323)
          ·
            refine ⟨69930035839847036766906485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46620023893231357844604323 69930035839847036766906485)
            ·
              refine ⟨6555940859985659696897483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69930035839847036766906485 6555940859985659696897483)
              ·
                refine ⟨9833911289978489545346225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6555940859985659696897483 9833911289978489545346225)
                ·
                  refine ⟨7375433467483867159009669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9833911289978489545346225 7375433467483867159009669)
                  ·
                    refine ⟨1382893775153225092314313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375433467483867159009669 1382893775153225092314313)
                    ·
                      rfl

theorem cell22_4039764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_4039764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039764 prefixEnd_4039764 := by exact prefixLift 4039764
  have htrace : WordTrace (prefixWord ++ tailWord_4039764) baseStart_4039764 baseEnd_4039764 := by
    simpa [prefixWord, tailWord_4039764, baseEnd_4039764] using wordTrace_append hprefix tailTrace_4039764
  have hstable : (prefixWord ++ tailWord_4039764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039764).length < 2 ^ (prefixWord ++ tailWord_4039764).sum := by decide
  have hdescent : baseEnd_4039764 < baseStart_4039764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039852 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_4039852 : Nat := 118140960795 + 4039852 * 2 ^ 59
def prefixEnd_4039852 : Nat := 4983230072969 + 3 ^ 40 * 4039852 * 2
def baseEnd_4039852 : Nat := 460974633117207398704681

theorem tailTrace_4039852 : CollatzResearch.WordTrace tailWord_4039852 prefixEnd_4039852 460974633117207398704681 := by
  unfold tailWord_4039852
  simp only [CollatzResearch.WordTrace]
  refine ⟨73672753680156815318420905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98230338240209087091227873 73672753680156815318420905)
  ·
    refine ⟨55254565260117611488815679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73672753680156815318420905 55254565260117611488815679)
    ·
      refine ⟨82881847890176417233223519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55254565260117611488815679 82881847890176417233223519)
      ·
        refine ⟨124322771835264625849835279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82881847890176417233223519 124322771835264625849835279)
        ·
          refine ⟨186484157752896938774752919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124322771835264625849835279 186484157752896938774752919)
          ·
            refine ⟨279726236629345408162129379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186484157752896938774752919 279726236629345408162129379)
            ·
              refine ⟨419589354944018112243194069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279726236629345408162129379 419589354944018112243194069)
              ·
                refine ⟨9834125506500424505699861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 419589354944018112243194069 9834125506500424505699861)
                ·
                  refine ⟨460974633117207398704681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9834125506500424505699861 460974633117207398704681)
                  ·
                    rfl

theorem cell22_4039852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_4039852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039852 prefixEnd_4039852 := by exact prefixLift 4039852
  have htrace : WordTrace (prefixWord ++ tailWord_4039852) baseStart_4039852 baseEnd_4039852 := by
    simpa [prefixWord, tailWord_4039852, baseEnd_4039852] using wordTrace_append hprefix tailTrace_4039852
  have hstable : (prefixWord ++ tailWord_4039852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039852).length < 2 ^ (prefixWord ++ tailWord_4039852).sum := by decide
  have hdescent : baseEnd_4039852 < baseStart_4039852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039914 : List Nat := [3, 1, 3, 1, 1, 3, 3, 7]
def baseStart_4039914 : Nat := 118140960795 + 4039914 * 2 ^ 59
def prefixEnd_4039914 : Nat := 4983230072969 + 3 ^ 40 * 4039914 * 2
def baseEnd_4039914 : Nat := 153660569246519411229317

theorem tailTrace_4039914 : CollatzResearch.WordTrace tailWord_4039914 prefixEnd_4039914 153660569246519411229317 := by
  unfold tailWord_4039914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836942171522253806399699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98231845790726010150399197 36836942171522253806399699)
  ·
    refine ⟨55255413257283380709599549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36836942171522253806399699 55255413257283380709599549)
    ·
      refine ⟨20720779971481267766099831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55255413257283380709599549 20720779971481267766099831)
      ·
        refine ⟨31081169957221901649149747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20720779971481267766099831 31081169957221901649149747)
        ·
          refine ⟨46621754935832852473724621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31081169957221901649149747 46621754935832852473724621)
          ·
            refine ⟨17483158100937319677646733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46621754935832852473724621 17483158100937319677646733)
            ·
              refine ⟨6556184287851494879117525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17483158100937319677646733 6556184287851494879117525)
              ·
                refine ⟨153660569246519411229317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6556184287851494879117525 153660569246519411229317)
                ·
                  rfl

theorem cell22_4039914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_4039914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039914 prefixEnd_4039914 := by exact prefixLift 4039914
  have htrace : WordTrace (prefixWord ++ tailWord_4039914) baseStart_4039914 baseEnd_4039914 := by
    simpa [prefixWord, tailWord_4039914, baseEnd_4039914] using wordTrace_append hprefix tailTrace_4039914
  have hstable : (prefixWord ++ tailWord_4039914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039914).length < 2 ^ (prefixWord ++ tailWord_4039914).sum := by decide
  have hdescent : baseEnd_4039914 < baseStart_4039914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039959 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 7]
def baseStart_4039959 : Nat := 118140960795 + 4039959 * 2 ^ 59
def prefixEnd_4039959 : Nat := 4983230072969 + 3 ^ 40 * 4039959 * 2
def baseEnd_4039959 : Nat := 460986842546103194562905

theorem tailTrace_4039959 : CollatzResearch.WordTrace tailWord_4039959 prefixEnd_4039959 460986842546103194562905 := by
  unfold tailWord_4039959
  simp only [CollatzResearch.WordTrace]
  refine ⟨147349409970925987910986931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98232939980617325273991287 147349409970925987910986931)
  ·
    refine ⟨221024114956388981866480397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147349409970925987910986931 221024114956388981866480397)
    ·
      refine ⟨82884043108645868199930149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221024114956388981866480397 82884043108645868199930149)
      ·
        refine ⟨15540758082871100287486903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82884043108645868199930149 15540758082871100287486903)
        ·
          refine ⟨23311137124306650431230355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15540758082871100287486903 23311137124306650431230355)
          ·
            refine ⟨34966705686459975646845533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23311137124306650431230355 34966705686459975646845533)
            ·
              refine ⟨13112514632422490867567075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34966705686459975646845533 13112514632422490867567075)
              ·
                refine ⟨19668771948633736301350613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13112514632422490867567075 19668771948633736301350613)
                ·
                  refine ⟨460986842546103194562905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19668771948633736301350613 460986842546103194562905)
                  ·
                    rfl

theorem cell22_4039959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 7].length) (baseStart_4039959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4039959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4039959 prefixEnd_4039959 := by exact prefixLift 4039959
  have htrace : WordTrace (prefixWord ++ tailWord_4039959) baseStart_4039959 baseEnd_4039959 := by
    simpa [prefixWord, tailWord_4039959, baseEnd_4039959] using wordTrace_append hprefix tailTrace_4039959
  have hstable : (prefixWord ++ tailWord_4039959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039959).length < 2 ^ (prefixWord ++ tailWord_4039959).sum := by decide
  have hdescent : baseEnd_4039959 < baseStart_4039959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040021 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 6]
def baseStart_4040021 : Nat := 118140960795 + 4040021 * 2 ^ 59
def prefixEnd_4040021 : Nat := 4983230072969 + 3 ^ 40 * 4040021 * 2
def baseEnd_4040021 : Nat := 460993917168454029546175

theorem tailTrace_4040021 : CollatzResearch.WordTrace tailWord_4040021 prefixEnd_4040021 460993917168454029546175 := by
  unfold tailWord_4040021
  simp only [CollatzResearch.WordTrace]
  refine ⟨147351671296701372499743917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98234447531134248333162611 147351671296701372499743917)
  ·
    refine ⟨55256876736263014687403969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147351671296701372499743917 55256876736263014687403969)
    ·
      refine ⟨41442657552197261015552977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55256876736263014687403969 41442657552197261015552977)
      ·
        refine ⟨31081993164147945761664733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41442657552197261015552977 31081993164147945761664733)
        ·
          refine ⟨11655747436555479660624275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31081993164147945761664733 11655747436555479660624275)
          ·
            refine ⟨17483621154833219490936413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11655747436555479660624275 17483621154833219490936413)
            ·
              refine ⟨6556357933062457309101155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17483621154833219490936413 6556357933062457309101155)
              ·
                refine ⟨9834536899593685963651733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556357933062457309101155 9834536899593685963651733)
                ·
                  refine ⟨460993917168454029546175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9834536899593685963651733 460993917168454029546175)
                  ·
                    rfl

theorem cell22_4040021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_4040021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040021 prefixEnd_4040021 := by exact prefixLift 4040021
  have htrace : WordTrace (prefixWord ++ tailWord_4040021) baseStart_4040021 baseEnd_4040021 := by
    simpa [prefixWord, tailWord_4040021, baseEnd_4040021] using wordTrace_append hprefix tailTrace_4040021
  have hstable : (prefixWord ++ tailWord_4040021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040021).length < 2 ^ (prefixWord ++ tailWord_4040021).sum := by decide
  have hdescent : baseEnd_4040021 < baseStart_4040021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040040 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_4040040 : Nat := 118140960795 + 4040040 * 2 ^ 59
def prefixEnd_4040040 : Nat := 4983230072969 + 3 ^ 40 * 4040040 * 2
def baseEnd_4040040 : Nat := 1382988255593652372413467

theorem tailTrace_4040040 : CollatzResearch.WordTrace tailWord_4040040 prefixEnd_4040040 1382988255593652372413467 := by
  unfold tailWord_4040040
  simp only [CollatzResearch.WordTrace]
  refine ⟨73676182141816269372342787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98234909522421692496457049 73676182141816269372342787)
  ·
    refine ⟨110514273212724404058514181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73676182141816269372342787 110514273212724404058514181)
    ·
      refine ⟨20721426227385825760971409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110514273212724404058514181 20721426227385825760971409)
      ·
        refine ⟨15541069670539369320728557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20721426227385825760971409 15541069670539369320728557)
        ·
          refine ⟨5827901126452263495273209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15541069670539369320728557 5827901126452263495273209)
          ·
            refine ⟨4370925844839197621454907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827901126452263495273209 4370925844839197621454907)
            ·
              refine ⟨6556388767258796432182361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370925844839197621454907 6556388767258796432182361)
              ·
                refine ⟨4917291575444097324136771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556388767258796432182361 4917291575444097324136771)
                ·
                  refine ⟨7375937363166145986205157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917291575444097324136771 7375937363166145986205157)
                  ·
                    refine ⟨1382988255593652372413467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375937363166145986205157 1382988255593652372413467)
                    ·
                      rfl

theorem cell22_4040040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_4040040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040040 prefixEnd_4040040 := by exact prefixLift 4040040
  have htrace : WordTrace (prefixWord ++ tailWord_4040040) baseStart_4040040 baseEnd_4040040 := by
    simpa [prefixWord, tailWord_4040040, baseEnd_4040040] using wordTrace_append hprefix tailTrace_4040040
  have hstable : (prefixWord ++ tailWord_4040040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040040).length < 2 ^ (prefixWord ++ tailWord_4040040).sum := by decide
  have hdescent : baseEnd_4040040 < baseStart_4040040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040049 : List Nat := [1, 2, 2, 2, 1, 2, 4, 8]
def baseStart_4040049 : Nat := 118140960795 + 4040049 * 2 ^ 59
def prefixEnd_4040049 : Nat := 4983230072969 + 3 ^ 40 * 4040049 * 2
def baseEnd_4040049 : Nat := 153665704053064372104271

theorem tailTrace_4040049 : CollatzResearch.WordTrace tailWord_4040049 prefixEnd_4040049 153665704053064372104271 := by
  unfold tailWord_4040049
  simp only [CollatzResearch.WordTrace]
  refine ⟨147352692540599933281763201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98235128360399955521175467 147352692540599933281763201)
  ·
    refine ⟨110514519405449949961322401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147352692540599933281763201 110514519405449949961322401)
    ·
      refine ⟨82885889554087462470991801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110514519405449949961322401 82885889554087462470991801)
      ·
        refine ⟨62164417165565596853243851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82885889554087462470991801 62164417165565596853243851)
        ·
          refine ⟨93246625748348395279865777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62164417165565596853243851 93246625748348395279865777)
          ·
            refine ⟨69934969311261296459899333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93246625748348395279865777 69934969311261296459899333)
            ·
              refine ⟨13112806745861493086231125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69934969311261296459899333 13112806745861493086231125)
              ·
                refine ⟨153665704053064372104271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13112806745861493086231125 153665704053064372104271)
                ·
                  rfl

theorem cell22_4040049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 8].length) (baseStart_4040049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040049 prefixEnd_4040049 := by exact prefixLift 4040049
  have htrace : WordTrace (prefixWord ++ tailWord_4040049) baseStart_4040049 baseEnd_4040049 := by
    simpa [prefixWord, tailWord_4040049, baseEnd_4040049] using wordTrace_append hprefix tailTrace_4040049
  have hstable : (prefixWord ++ tailWord_4040049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040049).length < 2 ^ (prefixWord ++ tailWord_4040049).sum := by decide
  have hdescent : baseEnd_4040049 < baseStart_4040049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040053 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4040053 : Nat := 118140960795 + 4040053 * 2 ^ 59
def prefixEnd_4040053 : Nat := 4983230072969 + 3 ^ 40 * 4040053 * 2
def baseEnd_4040053 : Nat := 1382992705759324671838427

theorem tailTrace_4040053 : CollatzResearch.WordTrace tailWord_4040053 prefixEnd_4040053 1382992705759324671838427 := by
  unfold tailWord_4040053
  simp only [CollatzResearch.WordTrace]
  refine ⟨147352838432585441964908813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98235225621723627976605875 147352838432585441964908813)
  ·
    refine ⟨55257314412219540736840805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147352838432585441964908813 55257314412219540736840805)
    ·
      refine ⟨10360746452291163888157651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55257314412219540736840805 10360746452291163888157651)
      ·
        refine ⟨15541119678436745832236477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10360746452291163888157651 15541119678436745832236477)
        ·
          refine ⟨5827919879413779687088679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15541119678436745832236477 5827919879413779687088679)
          ·
            refine ⟨8741879819120669530633019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827919879413779687088679 8741879819120669530633019)
            ·
              refine ⟨13112819728681004295949529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741879819120669530633019 13112819728681004295949529)
              ·
                refine ⟨9834614796510753221962147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112819728681004295949529 9834614796510753221962147)
                ·
                  refine ⟨14751922194766129832943221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9834614796510753221962147 14751922194766129832943221)
                  ·
                    refine ⟨1382992705759324671838427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14751922194766129832943221 1382992705759324671838427)
                    ·
                      rfl

theorem cell22_4040053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4040053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040053 prefixEnd_4040053 := by exact prefixLift 4040053
  have htrace : WordTrace (prefixWord ++ tailWord_4040053) baseStart_4040053 baseEnd_4040053 := by
    simpa [prefixWord, tailWord_4040053, baseEnd_4040053] using wordTrace_append hprefix tailTrace_4040053
  have hstable : (prefixWord ++ tailWord_4040053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040053).length < 2 ^ (prefixWord ++ tailWord_4040053).sum := by decide
  have hdescent : baseEnd_4040053 < baseStart_4040053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040098 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_4040098 : Nat := 118140960795 + 4040098 * 2 ^ 59
def prefixEnd_4040098 : Nat := 4983230072969 + 3 ^ 40 * 4040098 * 2
def baseEnd_4040098 : Nat := 1383008110178959554463289

theorem tailTrace_4040098 : CollatzResearch.WordTrace tailWord_4040098 prefixEnd_4040098 1383008110178959554463289 := by
  unfold tailWord_4040098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36838619929355603662574237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98236319811614943100197965 36838619929355603662574237)
  ·
    refine ⟨13814482473508351373465339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36838619929355603662574237 13814482473508351373465339)
    ·
      refine ⟨20721723710262527060198009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13814482473508351373465339 20721723710262527060198009)
      ·
        refine ⟨15541292782696895295148507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20721723710262527060198009 15541292782696895295148507)
        ·
          refine ⟨23311939174045342942722761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541292782696895295148507 23311939174045342942722761)
          ·
            refine ⟨17483954380534007207042071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23311939174045342942722761 17483954380534007207042071)
            ·
              refine ⟨26225931570801010810563107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17483954380534007207042071 26225931570801010810563107)
              ·
                refine ⟨39338897356201516215844661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26225931570801010810563107 39338897356201516215844661)
                ·
                  refine ⟨3688021627143892145235437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39338897356201516215844661 3688021627143892145235437)
                  ·
                    refine ⟨1383008110178959554463289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688021627143892145235437 1383008110178959554463289)
                    ·
                      rfl

theorem cell22_4040098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_4040098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040098 prefixEnd_4040098 := by exact prefixLift 4040098
  have htrace : WordTrace (prefixWord ++ tailWord_4040098) baseStart_4040098 baseEnd_4040098 := by
    simpa [prefixWord, tailWord_4040098, baseEnd_4040098] using wordTrace_append hprefix tailTrace_4040098
  have hstable : (prefixWord ++ tailWord_4040098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040098).length < 2 ^ (prefixWord ++ tailWord_4040098).sum := by decide
  have hdescent : baseEnd_4040098 < baseStart_4040098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040132 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4040132 : Nat := 118140960795 + 4040132 * 2 ^ 59
def prefixEnd_4040132 : Nat := 4983230072969 + 3 ^ 40 * 4040132 * 2
def baseEnd_4040132 : Nat := 1383019749073794799113185

theorem tailTrace_4040132 : CollatzResearch.WordTrace tailWord_4040132 prefixEnd_4040132 1383019749073794799113185 := by
  unfold tailWord_4040132
  simp only [CollatzResearch.WordTrace]
  refine ⟨73677859899649619228517325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98237146532866158971356433 73677859899649619228517325)
  ·
    refine ⟨27629197462368607210693997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73677859899649619228517325 27629197462368607210693997)
    ·
      refine ⟨10360949048388227704010249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27629197462368607210693997 10360949048388227704010249)
      ·
        refine ⟨7770711786291170778007687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10360949048388227704010249 7770711786291170778007687)
        ·
          refine ⟨11656067679436756167011531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7770711786291170778007687 11656067679436756167011531)
          ·
            refine ⟨17484101519155134250517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656067679436756167011531 17484101519155134250517297)
            ·
              refine ⟨13113076139366350687887973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17484101519155134250517297 13113076139366350687887973)
              ·
                refine ⟨2458701776131190753978995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13113076139366350687887973 2458701776131190753978995)
                ·
                  refine ⟨3688052664196786130968493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458701776131190753978995 3688052664196786130968493)
                  ·
                    refine ⟨1383019749073794799113185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688052664196786130968493 1383019749073794799113185)
                    ·
                      rfl

theorem cell22_4040132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4040132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040132 prefixEnd_4040132 := by exact prefixLift 4040132
  have htrace : WordTrace (prefixWord ++ tailWord_4040132) baseStart_4040132 baseEnd_4040132 := by
    simpa [prefixWord, tailWord_4040132, baseEnd_4040132] using wordTrace_append hprefix tailTrace_4040132
  have hstable : (prefixWord ++ tailWord_4040132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040132).length < 2 ^ (prefixWord ++ tailWord_4040132).sum := by decide
  have hdescent : baseEnd_4040132 < baseStart_4040132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040188 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_4040188 : Nat := 118140960795 + 4040188 * 2 ^ 59
def prefixEnd_4040188 : Nat := 4983230072969 + 3 ^ 40 * 4040188 * 2
def baseEnd_4040188 : Nat := 1383038919018229319713013

theorem tailTrace_4040188 : CollatzResearch.WordTrace tailWord_4040188 prefixEnd_4040188 1383038919018229319713013 := by
  unfold tailWord_4040188
  simp only [CollatzResearch.WordTrace]
  refine ⟨73678881143548180010536609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98238508191397573347382145 73678881143548180010536609)
  ·
    refine ⟨55259160857661135007902457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73678881143548180010536609 55259160857661135007902457)
    ·
      refine ⟨41444370643245851255926843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55259160857661135007902457 41444370643245851255926843)
      ·
        refine ⟨62166555964868776883890265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41444370643245851255926843 62166555964868776883890265)
        ·
          refine ⟨46624916973651582662917699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62166555964868776883890265 46624916973651582662917699)
          ·
            refine ⟨69937375460477373994376549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46624916973651582662917699 69937375460477373994376549)
            ·
              refine ⟨13113257898839507623945603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69937375460477373994376549 13113257898839507623945603)
              ·
                refine ⟨19669886848259261435918405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13113257898839507623945603 19669886848259261435918405)
                ·
                  refine ⟨3688103784048611519234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19669886848259261435918405 3688103784048611519234701)
                  ·
                    refine ⟨1383038919018229319713013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688103784048611519234701 1383038919018229319713013)
                    ·
                      rfl

theorem cell22_4040188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_4040188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040188 prefixEnd_4040188 := by exact prefixLift 4040188
  have htrace : WordTrace (prefixWord ++ tailWord_4040188) baseStart_4040188 baseEnd_4040188 := by
    simpa [prefixWord, tailWord_4040188, baseEnd_4040188] using wordTrace_append hprefix tailTrace_4040188
  have hstable : (prefixWord ++ tailWord_4040188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040188).length < 2 ^ (prefixWord ++ tailWord_4040188).sum := by decide
  have hdescent : baseEnd_4040188 < baseStart_4040188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040201 : List Nat := [1, 2, 1, 1, 3, 1, 6, 7]
def baseStart_4040201 : Nat := 118140960795 + 4040201 * 2 ^ 59
def prefixEnd_4040201 : Nat := 4983230072969 + 3 ^ 40 * 4040201 * 2
def baseEnd_4040201 : Nat := 153671485464877957681997

theorem tailTrace_4040201 : CollatzResearch.WordTrace tailWord_4040201 prefixEnd_4040201 153671485464877957681997 := by
  unfold tailWord_4040201
  simp only [CollatzResearch.WordTrace]
  refine ⟨147358236436049263241296457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98238824290699508827530971 147358236436049263241296457)
  ·
    refine ⟨110518677327036947430972343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147358236436049263241296457 110518677327036947430972343)
    ·
      refine ⟨165778015990555421146458515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110518677327036947430972343 165778015990555421146458515)
      ·
        refine ⟨248667023985833131719687773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165778015990555421146458515 248667023985833131719687773)
        ·
          refine ⟨93250133994687424394882915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248667023985833131719687773 93250133994687424394882915)
          ·
            refine ⟨139875200992031136592324373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93250133994687424394882915 139875200992031136592324373)
            ·
              refine ⟨6556650046501459527765205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139875200992031136592324373 6556650046501459527765205)
              ·
                refine ⟨153671485464877957681997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6556650046501459527765205 153671485464877957681997)
                ·
                  rfl

theorem cell22_4040201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 7].length) (baseStart_4040201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040201 prefixEnd_4040201 := by exact prefixLift 4040201
  have htrace : WordTrace (prefixWord ++ tailWord_4040201) baseStart_4040201 baseEnd_4040201 := by
    simpa [prefixWord, tailWord_4040201, baseEnd_4040201] using wordTrace_append hprefix tailTrace_4040201
  have hstable : (prefixWord ++ tailWord_4040201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040201).length < 2 ^ (prefixWord ++ tailWord_4040201).sum := by decide
  have hdescent : baseEnd_4040201 < baseStart_4040201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040284 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_4040284 : Nat := 118140960795 + 4040284 * 2 ^ 59
def prefixEnd_4040284 : Nat := 4983230072969 + 3 ^ 40 * 4040284 * 2
def baseEnd_4040284 : Nat := 1383071781780117069312719

theorem tailTrace_4040284 : CollatzResearch.WordTrace tailWord_4040284 prefixEnd_4040284 1383071781780117069312719 := by
  unfold tailWord_4040284
  simp only [CollatzResearch.WordTrace]
  refine ⟨73680631847374284208283953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98240842463165712277711937 73680631847374284208283953)
  ·
    refine ⟨55260473885530713156212965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73680631847374284208283953 55260473885530713156212965)
    ·
      refine ⟨10361338853537008716789931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55260473885530713156212965 10361338853537008716789931)
      ·
        refine ⟨15542008280305513075184897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10361338853537008716789931 15542008280305513075184897)
        ·
          refine ⟨11656506210229134806388673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15542008280305513075184897 11656506210229134806388673)
          ·
            refine ⟨8742379657671851104791505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11656506210229134806388673 8742379657671851104791505)
            ·
              refine ⟨6556784743253888328593629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8742379657671851104791505 6556784743253888328593629)
              ·
                refine ⟨2458794278720208123222611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6556784743253888328593629 2458794278720208123222611)
                ·
                  refine ⟨3688191418080312184833917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458794278720208123222611 3688191418080312184833917)
                  ·
                    refine ⟨1383071781780117069312719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688191418080312184833917 1383071781780117069312719)
                    ·
                      rfl

theorem cell22_4040284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_4040284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040284 prefixEnd_4040284 := by exact prefixLift 4040284
  have htrace : WordTrace (prefixWord ++ tailWord_4040284) baseStart_4040284 baseEnd_4040284 := by
    simpa [prefixWord, tailWord_4040284, baseEnd_4040284] using wordTrace_append hprefix tailTrace_4040284
  have hstable : (prefixWord ++ tailWord_4040284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040284).length < 2 ^ (prefixWord ++ tailWord_4040284).sum := by decide
  have hdescent : baseEnd_4040284 < baseStart_4040284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040353 : List Nat := [1, 2, 3, 3, 2, 1, 10]
def baseStart_4040353 : Nat := 118140960795 + 4040353 * 2 ^ 59
def prefixEnd_4040353 : Nat := 4983230072969 + 3 ^ 40 * 4040353 * 2
def baseEnd_4040353 : Nat := 51225755625563847753241

theorem tailTrace_4040353 : CollatzResearch.WordTrace tailWord_4040353 prefixEnd_4040353 51225755625563847753241 := by
  unfold tailWord_4040353
  simp only [CollatzResearch.WordTrace]
  refine ⟨147363780331498593200829713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98242520220999062133886475 147363780331498593200829713)
  ·
    refine ⟨110522835248623944900622285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147363780331498593200829713 110522835248623944900622285)
    ·
      refine ⟨41446063218233979337733357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110522835248623944900622285 41446063218233979337733357)
      ·
        refine ⟨15542273706837742251650009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41446063218233979337733357 15542273706837742251650009)
        ·
          refine ⟨11656705280128306688737507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15542273706837742251650009 11656705280128306688737507)
          ·
            refine ⟨17485057920192460033106261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656705280128306688737507 17485057920192460033106261)
            ·
              refine ⟨51225755625563847753241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17485057920192460033106261 51225755625563847753241)
              ·
                rfl

theorem cell22_4040353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 10].length) (baseStart_4040353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040353 prefixEnd_4040353 := by exact prefixLift 4040353
  have htrace : WordTrace (prefixWord ++ tailWord_4040353) baseStart_4040353 baseEnd_4040353 := by
    simpa [prefixWord, tailWord_4040353, baseEnd_4040353] using wordTrace_append hprefix tailTrace_4040353
  have hstable : (prefixWord ++ tailWord_4040353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040353).length < 2 ^ (prefixWord ++ tailWord_4040353).sum := by decide
  have hdescent : baseEnd_4040353 < baseStart_4040353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040415 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 5]
def baseStart_4040415 : Nat := 118140960795 + 4040415 * 2 ^ 59
def prefixEnd_4040415 : Nat := 4983230072969 + 3 ^ 40 * 4040415 * 2
def baseEnd_4040415 : Nat := 461038875252425464762439

theorem tailTrace_4040415 : CollatzResearch.WordTrace tailWord_4040415 prefixEnd_4040415 461038875252425464762439 := by
  unfold tailWord_4040415
  simp only [CollatzResearch.WordTrace]
  refine ⟨147366041657273977789586699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98244027771515985193057799 147366041657273977789586699)
  ·
    refine ⟨221049062485910966684380049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147366041657273977789586699 221049062485910966684380049)
    ·
      refine ⟨165786796864433225013285037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221049062485910966684380049 165786796864433225013285037)
      ·
        refine ⟨62170048824162459379981889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165786796864433225013285037 62170048824162459379981889)
        ·
          refine ⟨46627536618121844534986417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62170048824162459379981889 46627536618121844534986417)
          ·
            refine ⟨34970652463591383401239813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46627536618121844534986417 34970652463591383401239813)
            ·
              refine ⟨6556997336923384387732465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34970652463591383401239813 6556997336923384387732465)
              ·
                refine ⟨4917748002692538290799349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556997336923384387732465 4917748002692538290799349)
                ·
                  refine ⟨461038875252425464762439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4917748002692538290799349 461038875252425464762439)
                  ·
                    rfl

theorem cell22_4040415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 5].length) (baseStart_4040415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040415 prefixEnd_4040415 := by exact prefixLift 4040415
  have htrace : WordTrace (prefixWord ++ tailWord_4040415) baseStart_4040415 baseEnd_4040415 := by
    simpa [prefixWord, tailWord_4040415, baseEnd_4040415] using wordTrace_append hprefix tailTrace_4040415
  have hstable : (prefixWord ++ tailWord_4040415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040415).length < 2 ^ (prefixWord ++ tailWord_4040415).sum := by decide
  have hdescent : baseEnd_4040415 < baseStart_4040415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040430 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4040430 : Nat := 118140960795 + 4040430 * 2 ^ 59
def prefixEnd_4040430 : Nat := 4983230072969 + 3 ^ 40 * 4040430 * 2
def baseEnd_4040430 : Nat := 1383121760563821355162271

theorem tailTrace_4040430 : CollatzResearch.WordTrace tailWord_4040430 prefixEnd_4040430 1383121760563821355162271 := by
  unfold tailWord_4040430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18420823594027454418922843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98244392501479756900921829 18420823594027454418922843)
  ·
    refine ⟨27631235391041181628384265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18420823594027454418922843 27631235391041181628384265)
    ·
      refine ⟨20723426543280886221288199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27631235391041181628384265 20723426543280886221288199)
      ·
        refine ⟨31085139814921329331932299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20723426543280886221288199 31085139814921329331932299)
        ·
          refine ⟨46627709722381993997898449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31085139814921329331932299 46627709722381993997898449)
          ·
            refine ⟨34970782291786495498423837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46627709722381993997898449 34970782291786495498423837)
            ·
              refine ⟨13114043359419935811908939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34970782291786495498423837 13114043359419935811908939)
              ·
                refine ⟨19671065039129903717863409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13114043359419935811908939 19671065039129903717863409)
                ·
                  refine ⟨14753298779347427788397557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19671065039129903717863409 14753298779347427788397557)
                  ·
                    refine ⟨1383121760563821355162271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14753298779347427788397557 1383121760563821355162271)
                    ·
                      rfl

theorem cell22_4040430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4040430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040430 prefixEnd_4040430 := by exact prefixLift 4040430
  have htrace : WordTrace (prefixWord ++ tailWord_4040430) baseStart_4040430 baseEnd_4040430 := by
    simpa [prefixWord, tailWord_4040430, baseEnd_4040430] using wordTrace_append hprefix tailTrace_4040430
  have hstable : (prefixWord ++ tailWord_4040430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040430).length < 2 ^ (prefixWord ++ tailWord_4040430).sum := by decide
  have hdescent : baseEnd_4040430 < baseStart_4040430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040436 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4040436 : Nat := 118140960795 + 4040436 * 2 ^ 59
def prefixEnd_4040436 : Nat := 4983230072969 + 3 ^ 40 * 4040436 * 2
def baseEnd_4040436 : Nat := 1383123814486439339512253

theorem tailTrace_4040436 : CollatzResearch.WordTrace tailWord_4040436 prefixEnd_4040436 1383123814486439339512253 := by
  unfold tailWord_4040436
  simp only [CollatzResearch.WordTrace]
  refine ⟨73683403795098949188050581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98244538393465265584067441 73683403795098949188050581)
  ·
    refine ⟨3453909552895263243189871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73683403795098949188050581 3453909552895263243189871)
    ·
      refine ⟨5180864329342894864784807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453909552895263243189871 5180864329342894864784807)
      ·
        refine ⟨7771296494014342297177211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180864329342894864784807 7771296494014342297177211)
        ·
          refine ⟨11656944741021513445765817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7771296494014342297177211 11656944741021513445765817)
          ·
            refine ⟨8742708555766135084324363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11656944741021513445765817 8742708555766135084324363)
            ·
              refine ⟨13114062833649202626486545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8742708555766135084324363 13114062833649202626486545)
              ·
                refine ⟨9835547125236901969864909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13114062833649202626486545 9835547125236901969864909)
                ·
                  refine ⟨3688330171963838238699341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9835547125236901969864909 3688330171963838238699341)
                  ·
                    refine ⟨1383123814486439339512253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688330171963838238699341 1383123814486439339512253)
                    ·
                      rfl

theorem cell22_4040436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4040436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040436 prefixEnd_4040436 := by exact prefixLift 4040436
  have htrace : WordTrace (prefixWord ++ tailWord_4040436) baseStart_4040436 baseEnd_4040436 := by
    simpa [prefixWord, tailWord_4040436, baseEnd_4040436] using wordTrace_append hprefix tailTrace_4040436
  have hstable : (prefixWord ++ tailWord_4040436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040436).length < 2 ^ (prefixWord ++ tailWord_4040436).sum := by decide
  have hdescent : baseEnd_4040436 < baseStart_4040436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040475 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 4, 3]
def baseStart_4040475 : Nat := 118140960795 + 4040475 * 2 ^ 59
def prefixEnd_4040475 : Nat := 4983230072969 + 3 ^ 40 * 4040475 * 2
def baseEnd_4040475 : Nat := 1383137164983456237787133

theorem tailTrace_4040475 : CollatzResearch.WordTrace tailWord_4040475 prefixEnd_4040475 1383137164983456237787133 := by
  unfold tailWord_4040475
  simp only [CollatzResearch.WordTrace]
  refine ⟨147368230037056608036770879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98245486691371072024513919 147368230037056608036770879)
  ·
    refine ⟨221052345055584912055156319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147368230037056608036770879 221052345055584912055156319)
    ·
      refine ⟨331578517583377368082734479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221052345055584912055156319 331578517583377368082734479)
      ·
        refine ⟨497367776375066052124101719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331578517583377368082734479 497367776375066052124101719)
        ·
          refine ⟨746051664562599078186152579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497367776375066052124101719 746051664562599078186152579)
          ·
            refine ⟨1119077496843898617279228869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746051664562599078186152579 1119077496843898617279228869)
            ·
              refine ⟨209827030658230990739855413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1119077496843898617279228869 209827030658230990739855413)
              ·
                refine ⟨19671284124209155381861445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209827030658230990739855413 19671284124209155381861445)
                ·
                  refine ⟨3688365773289216634099021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19671284124209155381861445 3688365773289216634099021)
                  ·
                    refine ⟨1383137164983456237787133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688365773289216634099021 1383137164983456237787133)
                    ·
                      rfl

theorem cell22_4040475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 3].length) (baseStart_4040475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040475 prefixEnd_4040475 := by exact prefixLift 4040475
  have htrace : WordTrace (prefixWord ++ tailWord_4040475) baseStart_4040475 baseEnd_4040475 := by
    simpa [prefixWord, tailWord_4040475, baseEnd_4040475] using wordTrace_append hprefix tailTrace_4040475
  have hstable : (prefixWord ++ tailWord_4040475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040475).length < 2 ^ (prefixWord ++ tailWord_4040475).sum := by decide
  have hdescent : baseEnd_4040475 < baseStart_4040475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040492 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_4040492 : Nat := 118140960795 + 4040492 * 2 ^ 59
def prefixEnd_4040492 : Nat := 4983230072969 + 3 ^ 40 * 4040492 * 2
def baseEnd_4040492 : Nat := 1383142984430873860112081

theorem tailTrace_4040492 : CollatzResearch.WordTrace tailWord_4040492 prefixEnd_4040492 1383142984430873860112081 := by
  unfold tailWord_4040492
  simp only [CollatzResearch.WordTrace]
  refine ⟨73684425038997509970069865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98245900051996679960093153 73684425038997509970069865)
  ·
    refine ⟨55263318779248132477552399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73684425038997509970069865 55263318779248132477552399)
    ·
      refine ⟨82894978168872198716328599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55263318779248132477552399 82894978168872198716328599)
      ·
        refine ⟨124342467253308298074492899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82894978168872198716328599 124342467253308298074492899)
        ·
          refine ⟨186513700879962447111739349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124342467253308298074492899 186513700879962447111739349)
          ·
            refine ⟨4371414864374119854181391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 186513700879962447111739349 4371414864374119854181391)
            ·
              refine ⟨6557122296561179781272087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371414864374119854181391 6557122296561179781272087)
              ·
                refine ⟨9835683444841769671908131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6557122296561179781272087 9835683444841769671908131)
                ·
                  refine ⟨14753525167262654507862197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9835683444841769671908131 14753525167262654507862197)
                  ·
                    refine ⟨1383142984430873860112081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14753525167262654507862197 1383142984430873860112081)
                    ·
                      rfl

theorem cell22_4040492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_4040492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040492 prefixEnd_4040492 := by exact prefixLift 4040492
  have htrace : WordTrace (prefixWord ++ tailWord_4040492) baseStart_4040492 baseEnd_4040492 := by
    simpa [prefixWord, tailWord_4040492, baseEnd_4040492] using wordTrace_append hprefix tailTrace_4040492
  have hstable : (prefixWord ++ tailWord_4040492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040492).length < 2 ^ (prefixWord ++ tailWord_4040492).sum := by decide
  have hdescent : baseEnd_4040492 < baseStart_4040492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040511 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 4]
def baseStart_4040511 : Nat := 118140960795 + 4040511 * 2 ^ 59
def prefixEnd_4040511 : Nat := 4983230072969 + 3 ^ 40 * 4040511 * 2
def baseEnd_4040511 : Nat := 461049829506388047962341

theorem tailTrace_4040511 : CollatzResearch.WordTrace tailWord_4040511 prefixEnd_4040511 461049829506388047962341 := by
  unfold tailWord_4040511
  simp only [CollatzResearch.WordTrace]
  refine ⟨147369543064926186185081387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98246362043284124123387591 147369543064926186185081387)
  ·
    refine ⟨221054314597389279277622081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147369543064926186185081387 221054314597389279277622081)
    ·
      refine ⟨165790735948041959458216561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221054314597389279277622081 165790735948041959458216561)
      ·
        refine ⟨124343051961031469593662421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165790735948041959458216561 124343051961031469593662421)
        ·
          refine ⟨2914290280336675068601463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124343051961031469593662421 2914290280336675068601463)
          ·
            refine ⟨4371435420505012602902195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914290280336675068601463 4371435420505012602902195)
            ·
              refine ⟨6557153130757518904353293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371435420505012602902195 6557153130757518904353293)
              ·
                refine ⟨2458932424034069589132485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6557153130757518904353293 2458932424034069589132485)
                ·
                  refine ⟨461049829506388047962341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2458932424034069589132485 461049829506388047962341)
                  ·
                    rfl

theorem cell22_4040511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 4].length) (baseStart_4040511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040511 prefixEnd_4040511 := by exact prefixLift 4040511
  have htrace : WordTrace (prefixWord ++ tailWord_4040511) baseStart_4040511 baseEnd_4040511 := by
    simpa [prefixWord, tailWord_4040511, baseEnd_4040511] using wordTrace_append hprefix tailTrace_4040511
  have hstable : (prefixWord ++ tailWord_4040511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040511).length < 2 ^ (prefixWord ++ tailWord_4040511).sum := by decide
  have hdescent : baseEnd_4040511 < baseStart_4040511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040584 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_4040584 : Nat := 118140960795 + 4040584 * 2 ^ 59
def prefixEnd_4040584 : Nat := 4983230072969 + 3 ^ 40 * 4040584 * 2
def baseEnd_4040584 : Nat := 461058159303672095603933

theorem tailTrace_4040584 : CollatzResearch.WordTrace tailWord_4040584 prefixEnd_4040584 461058159303672095603933 := by
  unfold tailWord_4040584
  simp only [CollatzResearch.WordTrace]
  refine ⟨73686102796830859826244403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98248137062441146434992537 73686102796830859826244403)
  ·
    refine ⟨110529154195246289739366605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73686102796830859826244403 110529154195246289739366605)
    ·
      refine ⟨41448432823217358652262477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110529154195246289739366605 41448432823217358652262477)
      ·
        refine ⟨15543162308706509494598429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41448432823217358652262477 15543162308706509494598429)
        ·
          refine ⟨5828685865764941060474411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15543162308706509494598429 5828685865764941060474411)
          ·
            refine ⟨8743028798647411590711617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828685865764941060474411 8743028798647411590711617)
            ·
              refine ⟨6557271598985558693033713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8743028798647411590711617 6557271598985558693033713)
              ·
                refine ⟨4917953699239169019775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6557271598985558693033713 4917953699239169019775285)
                ·
                  refine ⟨461058159303672095603933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4917953699239169019775285 461058159303672095603933)
                  ·
                    rfl

theorem cell22_4040584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_4040584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040584 prefixEnd_4040584 := by exact prefixLift 4040584
  have htrace : WordTrace (prefixWord ++ tailWord_4040584) baseStart_4040584 baseEnd_4040584 := by
    simpa [prefixWord, tailWord_4040584, baseEnd_4040584] using wordTrace_append hprefix tailTrace_4040584
  have hstable : (prefixWord ++ tailWord_4040584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040584).length < 2 ^ (prefixWord ++ tailWord_4040584).sum := by decide
  have hdescent : baseEnd_4040584 < baseStart_4040584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040612 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_4040612 : Nat := 118140960795 + 4040612 * 2 ^ 59
def prefixEnd_4040612 : Nat := 4983230072969 + 3 ^ 40 * 4040612 * 2
def baseEnd_4040612 : Nat := 461061354294411182370571

theorem tailTrace_4040612 : CollatzResearch.WordTrace tailWord_4040612 prefixEnd_4040612 461061354294411182370571 := by
  unfold tailWord_4040612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73686613418780140217254045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98248817891706853623005393 73686613418780140217254045)
  ·
    refine ⟨27632480032042552581470267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73686613418780140217254045 27632480032042552581470267)
    ·
      refine ⟨41448720048063828872205401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27632480032042552581470267 41448720048063828872205401)
      ·
        refine ⟨31086540036047871654154051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41448720048063828872205401 31086540036047871654154051)
        ·
          refine ⟨46629810054071807481231077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31086540036047871654154051 46629810054071807481231077)
          ·
            refine ⟨8743089385138463902730827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46629810054071807481231077 8743089385138463902730827)
            ·
              refine ⟨13114634077707695854096241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743089385138463902730827 13114634077707695854096241)
              ·
                refine ⟨9835975558280771890572181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13114634077707695854096241 9835975558280771890572181)
                ·
                  refine ⟨461061354294411182370571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9835975558280771890572181 461061354294411182370571)
                  ·
                    rfl

theorem cell22_4040612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_4040612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040612 prefixEnd_4040612 := by exact prefixLift 4040612
  have htrace : WordTrace (prefixWord ++ tailWord_4040612) baseStart_4040612 baseEnd_4040612 := by
    simpa [prefixWord, tailWord_4040612, baseEnd_4040612] using wordTrace_append hprefix tailTrace_4040612
  have hstable : (prefixWord ++ tailWord_4040612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040612).length < 2 ^ (prefixWord ++ tailWord_4040612).sum := by decide
  have hdescent : baseEnd_4040612 < baseStart_4040612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040622 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4040622 : Nat := 118140960795 + 4040622 * 2 ^ 59
def prefixEnd_4040622 : Nat := 4983230072969 + 3 ^ 40 * 4040622 * 2
def baseEnd_4040622 : Nat := 1383187486087596854361683

theorem tailTrace_4040622 : CollatzResearch.WordTrace tailWord_4040622 prefixEnd_4040622 1383187486087596854361683 := by
  unfold tailWord_4040622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421698945940506517796515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98249061045016034761581413 18421698945940506517796515)
  ·
    refine ⟨27632548418910759776694773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18421698945940506517796515 27632548418910759776694773)
    ·
      refine ⟨2590551414272883729065135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27632548418910759776694773 2590551414272883729065135)
      ·
        refine ⟨3885827121409325593597703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590551414272883729065135 3885827121409325593597703)
        ·
          refine ⟨5828740682113988390396555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885827121409325593597703 5828740682113988390396555)
          ·
            refine ⟨8743111023170982585594833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828740682113988390396555 8743111023170982585594833)
            ·
              refine ⟨6557333267378236939196125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8743111023170982585594833 6557333267378236939196125)
              ·
                refine ⟨2458999975266838852198547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6557333267378236939196125 2458999975266838852198547)
                ·
                  refine ⟨3688499962900258278297821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458999975266838852198547 3688499962900258278297821)
                  ·
                    refine ⟨1383187486087596854361683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688499962900258278297821 1383187486087596854361683)
                    ·
                      rfl

theorem cell22_4040622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4040622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040622 prefixEnd_4040622 := by exact prefixLift 4040622
  have htrace : WordTrace (prefixWord ++ tailWord_4040622) baseStart_4040622 baseEnd_4040622 := by
    simpa [prefixWord, tailWord_4040622, baseEnd_4040622] using wordTrace_append hprefix tailTrace_4040622
  have hstable : (prefixWord ++ tailWord_4040622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040622).length < 2 ^ (prefixWord ++ tailWord_4040622).sum := by decide
  have hdescent : baseEnd_4040622 < baseStart_4040622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040627 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 4, 3]
def baseStart_4040627 : Nat := 118140960795 + 4040627 * 2 ^ 59
def prefixEnd_4040627 : Nat := 4983230072969 + 3 ^ 40 * 4040627 * 2
def baseEnd_4040627 : Nat := 1383189197689778507986667

theorem tailTrace_4040627 : CollatzResearch.WordTrace tailWord_4040627 prefixEnd_4040627 1383189197689778507986667 := by
  unfold tailWord_4040627
  simp only [CollatzResearch.WordTrace]
  refine ⟨147373773932505937996304135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98249182621670625330869423 147373773932505937996304135)
  ·
    refine ⟨221060660898758906994456203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147373773932505937996304135 221060660898758906994456203)
    ·
      refine ⟨331590991348138360491684305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221060660898758906994456203 331590991348138360491684305)
      ·
        refine ⟨248693243511103770368763229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331590991348138360491684305 248693243511103770368763229)
        ·
          refine ⟨93259966316663913888286211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248693243511103770368763229 93259966316663913888286211)
          ·
            refine ⟨139889949474995870832429317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93259966316663913888286211 139889949474995870832429317)
            ·
              refine ⟨26229365526561725781080497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139889949474995870832429317 26229365526561725781080497)
              ·
                refine ⟨19672024144921294335810373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26229365526561725781080497 19672024144921294335810373)
                ·
                  refine ⟨3688504527172742687964445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19672024144921294335810373 3688504527172742687964445)
                  ·
                    refine ⟨1383189197689778507986667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688504527172742687964445 1383189197689778507986667)
                    ·
                      rfl

theorem cell22_4040627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 3].length) (baseStart_4040627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040627 prefixEnd_4040627 := by exact prefixLift 4040627
  have htrace : WordTrace (prefixWord ++ tailWord_4040627) baseStart_4040627 baseEnd_4040627 := by
    simpa [prefixWord, tailWord_4040627, baseEnd_4040627] using wordTrace_append hprefix tailTrace_4040627
  have hstable : (prefixWord ++ tailWord_4040627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040627).length < 2 ^ (prefixWord ++ tailWord_4040627).sum := by decide
  have hdescent : baseEnd_4040627 < baseStart_4040627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040629 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 4]
def baseStart_4040629 : Nat := 118140960795 + 4040629 * 2 ^ 59
def prefixEnd_4040629 : Nat := 4983230072969 + 3 ^ 40 * 4040629 * 2
def baseEnd_4040629 : Nat := 461063294110217056478887

theorem tailTrace_4040629 : CollatzResearch.WordTrace tailWord_4040629 prefixEnd_4040629 461063294110217056478887 := by
  unfold tailWord_4040629
  simp only [CollatzResearch.WordTrace]
  refine ⟨147373846878498692337876941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98249231252332461558584627 147373846878498692337876941)
  ·
    refine ⟨55265192579437009626703853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147373846878498692337876941 55265192579437009626703853)
    ·
      refine ⟨20724447217288878610013945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55265192579437009626703853 20724447217288878610013945)
      ·
        refine ⟨15543335412966658957510459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20724447217288878610013945 15543335412966658957510459)
        ·
          refine ⟨23315003119449988436265689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15543335412966658957510459 23315003119449988436265689)
          ·
            refine ⟨17486252339587491327199267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23315003119449988436265689 17486252339587491327199267)
            ·
              refine ⟨26229378509381236990798901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17486252339587491327199267 26229378509381236990798901)
              ·
                refine ⟨2459004235254490967887397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26229378509381236990798901 2459004235254490967887397)
                ·
                  refine ⟨461063294110217056478887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459004235254490967887397 461063294110217056478887)
                  ·
                    rfl

theorem cell22_4040629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_4040629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040629 prefixEnd_4040629 := by exact prefixLift 4040629
  have htrace : WordTrace (prefixWord ++ tailWord_4040629) baseStart_4040629 baseEnd_4040629 := by
    simpa [prefixWord, tailWord_4040629, baseEnd_4040629] using wordTrace_append hprefix tailTrace_4040629
  have hstable : (prefixWord ++ tailWord_4040629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040629).length < 2 ^ (prefixWord ++ tailWord_4040629).sum := by decide
  have hdescent : baseEnd_4040629 < baseStart_4040629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040640 : List Nat := [2, 1, 1, 2, 3, 2, 11]
def baseStart_4040640 : Nat := 118140960795 + 4040640 * 2 ^ 59
def prefixEnd_4040640 : Nat := 4983230072969 + 3 ^ 40 * 4040640 * 2
def baseEnd_4040640 : Nat := 51229394365016696570801

theorem tailTrace_4040640 : CollatzResearch.WordTrace tailWord_4040640 prefixEnd_4040640 51229394365016696570801 := by
  unfold tailWord_4040640
  simp only [CollatzResearch.WordTrace]
  refine ⟨73687124040729420608263687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98249498720972560811018249 73687124040729420608263687)
  ·
    refine ⟨110530686061094130912395531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73687124040729420608263687 110530686061094130912395531)
    ·
      refine ⟨165796029091641196368593297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110530686061094130912395531 165796029091641196368593297)
      ·
        refine ⟨124347021818730897276444973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165796029091641196368593297 124347021818730897276444973)
        ·
          refine ⟨46630133182024086478666865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124347021818730897276444973 46630133182024086478666865)
          ·
            refine ⟨34972599886518064859000149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46630133182024086478666865 34972599886518064859000149)
            ·
              refine ⟨51229394365016696570801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34972599886518064859000149 51229394365016696570801)
              ·
                rfl

theorem cell22_4040640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 11].length) (baseStart_4040640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040640 prefixEnd_4040640 := by exact prefixLift 4040640
  have htrace : WordTrace (prefixWord ++ tailWord_4040640) baseStart_4040640 baseEnd_4040640 := by
    simpa [prefixWord, tailWord_4040640, baseEnd_4040640] using wordTrace_append hprefix tailTrace_4040640
  have hstable : (prefixWord ++ tailWord_4040640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040640).length < 2 ^ (prefixWord ++ tailWord_4040640).sum := by decide
  have hdescent : baseEnd_4040640 < baseStart_4040640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040762 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_4040762 : Nat := 118140960795 + 4040762 * 2 ^ 59
def prefixEnd_4040762 : Nat := 4983230072969 + 3 ^ 40 * 4040762 * 2
def baseEnd_4040762 : Nat := 1383235410948683155861253

theorem tailTrace_4040762 : CollatzResearch.WordTrace tailWord_4040762 prefixEnd_4040762 1383235410948683155861253 := by
  unfold tailWord_4040762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36844674446754214013117135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98252465191344570701645693 36844674446754214013117135)
  ·
    refine ⟨55267011670131321019675703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36844674446754214013117135 55267011670131321019675703)
    ·
      refine ⟨82900517505196981529513555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55267011670131321019675703 82900517505196981529513555)
      ·
        refine ⟨124350776257795472294270333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82900517505196981529513555 124350776257795472294270333)
        ·
          refine ⟨46631541096673302110351375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124350776257795472294270333 46631541096673302110351375)
          ·
            refine ⟨69947311645009953165527063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46631541096673302110351375 69947311645009953165527063)
            ·
              refine ⟨104920967467514929748290595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69947311645009953165527063 104920967467514929748290595)
              ·
                refine ⟨157381451201272394622435893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104920967467514929748290595 157381451201272394622435893)
                ·
                  refine ⟨14754511050119286995853365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157381451201272394622435893 14754511050119286995853365)
                  ·
                    refine ⟨1383235410948683155861253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14754511050119286995853365 1383235410948683155861253)
                    ·
                      rfl

theorem cell22_4040762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_4040762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040762 prefixEnd_4040762 := by exact prefixLift 4040762
  have htrace : WordTrace (prefixWord ++ tailWord_4040762) baseStart_4040762 baseEnd_4040762 := by
    simpa [prefixWord, tailWord_4040762, baseEnd_4040762] using wordTrace_append hprefix tailTrace_4040762
  have hstable : (prefixWord ++ tailWord_4040762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040762).length < 2 ^ (prefixWord ++ tailWord_4040762).sum := by decide
  have hdescent : baseEnd_4040762 < baseStart_4040762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040777 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_4040777 : Nat := 118140960795 + 4040777 * 2 ^ 59
def prefixEnd_4040777 : Nat := 4983230072969 + 3 ^ 40 * 4040777 * 2
def baseEnd_4040777 : Nat := 1383240545755228116736207

theorem tailTrace_4040777 : CollatzResearch.WordTrace tailWord_4040777 prefixEnd_4040777 1383240545755228116736207 := by
  unfold tailWord_4040777
  simp only [CollatzResearch.WordTrace]
  refine ⟨147379244881962513614264585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98252829921308342409509723 147379244881962513614264585)
  ·
    refine ⟨110534433661471885210698439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147379244881962513614264585 110534433661471885210698439)
    ·
      refine ⟨165801650492207827816047659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110534433661471885210698439 165801650492207827816047659)
      ·
        refine ⟨248702475738311741724071489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165801650492207827816047659 248702475738311741724071489)
        ·
          refine ⟨186526856803733806293053617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248702475738311741724071489 186526856803733806293053617)
          ·
            refine ⟨139895142602800354719790213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186526856803733806293053617 139895142602800354719790213)
            ·
              refine ⟨26230339238025066509960665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139895142602800354719790213 26230339238025066509960665)
              ·
                refine ⟨19672754428518799882470499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26230339238025066509960665 19672754428518799882470499)
                ·
                  refine ⟨29509131642778199823705749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19672754428518799882470499 29509131642778199823705749)
                  ·
                    refine ⟨1383240545755228116736207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29509131642778199823705749 1383240545755228116736207)
                    ·
                      rfl

theorem cell22_4040777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_4040777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040777 prefixEnd_4040777 := by exact prefixLift 4040777
  have htrace : WordTrace (prefixWord ++ tailWord_4040777) baseStart_4040777 baseEnd_4040777 := by
    simpa [prefixWord, tailWord_4040777, baseEnd_4040777] using wordTrace_append hprefix tailTrace_4040777
  have hstable : (prefixWord ++ tailWord_4040777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040777).length < 2 ^ (prefixWord ++ tailWord_4040777).sum := by decide
  have hdescent : baseEnd_4040777 < baseStart_4040777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040901 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_4040901 : Nat := 118140960795 + 4040901 * 2 ^ 59
def prefixEnd_4040901 : Nat := 4983230072969 + 3 ^ 40 * 4040901 * 2
def baseEnd_4040901 : Nat := 1383282993489333126635827

theorem tailTrace_4040901 : CollatzResearch.WordTrace tailWord_4040901 prefixEnd_4040901 1383282993489333126635827 := by
  unfold tailWord_4040901
  simp only [CollatzResearch.WordTrace]
  refine ⟨147383767533513282791778557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98255845022342188527852371 147383767533513282791778557)
  ·
    refine ⟨55268912825067481046916959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147383767533513282791778557 55268912825067481046916959)
    ·
      refine ⟨82903369237601221570375439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55268912825067481046916959 82903369237601221570375439)
      ·
        refine ⟨124355053856401832355563159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82903369237601221570375439 124355053856401832355563159)
        ·
          refine ⟨186532580784602748533344739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124355053856401832355563159 186532580784602748533344739)
          ·
            refine ⟨279798871176904122800017109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186532580784602748533344739 279798871176904122800017109)
            ·
              refine ⟨6557786043208690378125401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 279798871176904122800017109 6557786043208690378125401)
              ·
                refine ⟨4918339532406517783594051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6557786043208690378125401 4918339532406517783594051)
                ·
                  refine ⟨7377509298609776675391077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918339532406517783594051 7377509298609776675391077)
                  ·
                    refine ⟨1383282993489333126635827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7377509298609776675391077 1383282993489333126635827)
                    ·
                      rfl

theorem cell22_4040901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_4040901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040901 prefixEnd_4040901 := by exact prefixLift 4040901
  have htrace : WordTrace (prefixWord ++ tailWord_4040901) baseStart_4040901 baseEnd_4040901 := by
    simpa [prefixWord, tailWord_4040901, baseEnd_4040901] using wordTrace_append hprefix tailTrace_4040901
  have hstable : (prefixWord ++ tailWord_4040901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040901).length < 2 ^ (prefixWord ++ tailWord_4040901).sum := by decide
  have hdescent : baseEnd_4040901 < baseStart_4040901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040933 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 4]
def baseStart_4040933 : Nat := 118140960795 + 4040933 * 2 ^ 59
def prefixEnd_4040933 : Nat := 4983230072969 + 3 ^ 40 * 4040933 * 2
def baseEnd_4040933 : Nat := 461097982581098569945243

theorem tailTrace_4040933 : CollatzResearch.WordTrace tailWord_4040933 prefixEnd_4040933 461097982581098569945243 := by
  unfold tailWord_4040933
  simp only [CollatzResearch.WordTrace]
  refine ⟨147384934669397352256943453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98256623112931568171295635 147384934669397352256943453)
  ·
    refine ⟨55269350501024007096353795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147384934669397352256943453 55269350501024007096353795)
    ·
      refine ⟨82904025751536010644530693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55269350501024007096353795 82904025751536010644530693)
      ·
        refine ⟨15544504828413001995849505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82904025751536010644530693 15544504828413001995849505)
        ·
          refine ⟨11658378621309751496887129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15544504828413001995849505 11658378621309751496887129)
          ·
            refine ⟨8743783965982313622665347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11658378621309751496887129 8743783965982313622665347)
            ·
              refine ⟨13115675948973470433998021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743783965982313622665347 13115675948973470433998021)
              ·
                refine ⟨2459189240432525706374629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13115675948973470433998021 2459189240432525706374629)
                ·
                  refine ⟨461097982581098569945243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459189240432525706374629 461097982581098569945243)
                  ·
                    rfl

theorem cell22_4040933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_4040933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040933 prefixEnd_4040933 := by exact prefixLift 4040933
  have htrace : WordTrace (prefixWord ++ tailWord_4040933) baseStart_4040933 baseEnd_4040933 := by
    simpa [prefixWord, tailWord_4040933, baseEnd_4040933] using wordTrace_append hprefix tailTrace_4040933
  have hstable : (prefixWord ++ tailWord_4040933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040933).length < 2 ^ (prefixWord ++ tailWord_4040933).sum := by decide
  have hdescent : baseEnd_4040933 < baseStart_4040933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040961 : List Nat := [1, 2, 4, 1, 1, 2, 5, 6]
def baseStart_4040961 : Nat := 118140960795 + 4040961 * 2 ^ 59
def prefixEnd_4040961 : Nat := 4983230072969 + 3 ^ 40 * 4040961 * 2
def baseEnd_4040961 : Nat := 153700392523945885570627

theorem tailTrace_4040961 : CollatzResearch.WordTrace tailWord_4040961 prefixEnd_4040961 153700392523945885570627 := by
  unfold tailWord_4040961
  simp only [CollatzResearch.WordTrace]
  refine ⟨147385955913295913038962737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98257303942197275359308491 147385955913295913038962737)
  ·
    refine ⟨110539466934971934779222053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147385955913295913038962737 110539466934971934779222053)
    ·
      refine ⟨20726150050307237771104135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110539466934971934779222053 20726150050307237771104135)
      ·
        refine ⟨31089225075460856656656203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20726150050307237771104135 31089225075460856656656203)
        ·
          refine ⟨46633837613191284984984305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31089225075460856656656203 46633837613191284984984305)
          ·
            refine ⟨34975378209893463738738229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46633837613191284984984305 34975378209893463738738229)
            ·
              refine ⟨3278941707177512225506709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34975378209893463738738229 3278941707177512225506709)
              ·
                refine ⟨153700392523945885570627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3278941707177512225506709 153700392523945885570627)
                ·
                  rfl

theorem cell22_4040961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 6].length) (baseStart_4040961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040961 prefixEnd_4040961 := by exact prefixLift 4040961
  have htrace : WordTrace (prefixWord ++ tailWord_4040961) baseStart_4040961 baseEnd_4040961 := by
    simpa [prefixWord, tailWord_4040961, baseEnd_4040961] using wordTrace_append hprefix tailTrace_4040961
  have hstable : (prefixWord ++ tailWord_4040961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040961).length < 2 ^ (prefixWord ++ tailWord_4040961).sum := by decide
  have hdescent : baseEnd_4040961 < baseStart_4040961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040999 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4040999 : Nat := 118140960795 + 4040999 * 2 ^ 59
def prefixEnd_4040999 : Nat := 4983230072969 + 3 ^ 40 * 4040999 * 2
def baseEnd_4040999 : Nat := 1383316540892093537685527

theorem tailTrace_4040999 : CollatzResearch.WordTrace tailWord_4040999 prefixEnd_4040999 1383316540892093537685527 := by
  unfold tailWord_4040999
  simp only [CollatzResearch.WordTrace]
  refine ⟨147387341887158245528846051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98258227924772163685897367 147387341887158245528846051)
  ·
    refine ⟨221081012830737368293269077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147387341887158245528846051 221081012830737368293269077)
    ·
      refine ⟨2590793119110203534686747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 221081012830737368293269077 2590793119110203534686747)
      ·
        refine ⟨3886189678665305302030121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590793119110203534686747 3886189678665305302030121)
        ·
          refine ⟨2914642258998978976522591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3886189678665305302030121 2914642258998978976522591)
          ·
            refine ⟨4371963388498468464783887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914642258998978976522591 4371963388498468464783887)
            ·
              refine ⟨6557945082747702697175831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371963388498468464783887 6557945082747702697175831)
              ·
                refine ⟨9836917624121554045763747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6557945082747702697175831 9836917624121554045763747)
                ·
                  refine ⟨14755376436182331068645621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9836917624121554045763747 14755376436182331068645621)
                  ·
                    refine ⟨1383316540892093537685527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14755376436182331068645621 1383316540892093537685527)
                    ·
                      rfl

theorem cell22_4040999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4040999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4040999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4040999 prefixEnd_4040999 := by exact prefixLift 4040999
  have htrace : WordTrace (prefixWord ++ tailWord_4040999) baseStart_4040999 baseEnd_4040999 := by
    simpa [prefixWord, tailWord_4040999, baseEnd_4040999] using wordTrace_append hprefix tailTrace_4040999
  have hstable : (prefixWord ++ tailWord_4040999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040999).length < 2 ^ (prefixWord ++ tailWord_4040999).sum := by decide
  have hdescent : baseEnd_4040999 < baseStart_4040999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041100 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_4041100 : Nat := 118140960795 + 4041100 * 2 ^ 59
def prefixEnd_4041100 : Nat := 4983230072969 + 3 ^ 40 * 4041100 * 2
def baseEnd_4041100 : Nat := 1383351115256162940910217

theorem tailTrace_4041100 : CollatzResearch.WordTrace tailWord_4041100 prefixEnd_4041100 1383351115256162940910217 := by
  unfold tailWord_4041100
  simp only [CollatzResearch.WordTrace]
  refine ⟨73695512829896169889136377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98260683773194893185515169 73695512829896169889136377)
  ·
    refine ⟨55271634622422127416852283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73695512829896169889136377 55271634622422127416852283)
    ·
      refine ⟨82907451933633191125278425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55271634622422127416852283 82907451933633191125278425)
      ·
        refine ⟨62180588950224893343958819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82907451933633191125278425 62180588950224893343958819)
        ·
          refine ⟨93270883425337340015938229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62180588950224893343958819 93270883425337340015938229)
          ·
            refine ⟨8744145321125375626494209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93270883425337340015938229 8744145321125375626494209)
            ·
              refine ⟨6558108990844031719870657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8744145321125375626494209 6558108990844031719870657)
              ·
                refine ⟨4918581743133023789902993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6558108990844031719870657 4918581743133023789902993)
                ·
                  refine ⟨3688936307349767842427245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4918581743133023789902993 3688936307349767842427245)
                  ·
                    refine ⟨1383351115256162940910217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688936307349767842427245 1383351115256162940910217)
                    ·
                      rfl

theorem cell22_4041100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_4041100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041100 prefixEnd_4041100 := by exact prefixLift 4041100
  have htrace : WordTrace (prefixWord ++ tailWord_4041100) baseStart_4041100 baseEnd_4041100 := by
    simpa [prefixWord, tailWord_4041100, baseEnd_4041100] using wordTrace_append hprefix tailTrace_4041100
  have hstable : (prefixWord ++ tailWord_4041100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041100).length < 2 ^ (prefixWord ++ tailWord_4041100).sum := by decide
  have hdescent : baseEnd_4041100 < baseStart_4041100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041102 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_4041102 : Nat := 118140960795 + 4041102 * 2 ^ 59
def prefixEnd_4041102 : Nat := 4983230072969 + 3 ^ 40 * 4041102 * 2
def baseEnd_4041102 : Nat := 461117266632345200786737

theorem tailTrace_4041102 : CollatzResearch.WordTrace tailWord_4041102 prefixEnd_4041102 461117266632345200786737 := by
  unfold tailWord_4041102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18423887325723136764980695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98260732403856729413230373 18423887325723136764980695)
  ·
    refine ⟨27635830988584705147471043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18423887325723136764980695 27635830988584705147471043)
    ·
      refine ⟨41453746482877057721206565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27635830988584705147471043 41453746482877057721206565)
      ·
        refine ⟨7772577465539448322726231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41453746482877057721206565 7772577465539448322726231)
        ·
          refine ⟨11658866198309172484089347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772577465539448322726231 11658866198309172484089347)
          ·
            refine ⟨17488299297463758726134021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11658866198309172484089347 17488299297463758726134021)
            ·
              refine ⟨3279056118274454761150129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17488299297463758726134021 3279056118274454761150129)
              ·
                refine ⟨2459292088705841070862597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3279056118274454761150129 2459292088705841070862597)
                ·
                  refine ⟨461117266632345200786737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459292088705841070862597 461117266632345200786737)
                  ·
                    rfl

theorem cell22_4041102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_4041102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041102 prefixEnd_4041102 := by exact prefixLift 4041102
  have htrace : WordTrace (prefixWord ++ tailWord_4041102) baseStart_4041102 baseEnd_4041102 := by
    simpa [prefixWord, tailWord_4041102, baseEnd_4041102] using wordTrace_append hprefix tailTrace_4041102
  have hstable : (prefixWord ++ tailWord_4041102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041102).length < 2 ^ (prefixWord ++ tailWord_4041102).sum := by decide
  have hdescent : baseEnd_4041102 < baseStart_4041102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041173 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_4041173 : Nat := 118140960795 + 4041173 * 2 ^ 59
def prefixEnd_4041173 : Nat := 4983230072969 + 3 ^ 40 * 4041173 * 2
def baseEnd_4041173 : Nat := 1383376104648015083834993

theorem tailTrace_4041173 : CollatzResearch.WordTrace tailWord_4041173 prefixEnd_4041173 1383376104648015083834993 := by
  unfold tailWord_4041173
  simp only [CollatzResearch.WordTrace]
  refine ⟨147393688188527873245680173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98262458792351915497120115 147393688188527873245680173)
  ·
    refine ⟨55272633070697952467130065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147393688188527873245680173 55272633070697952467130065)
    ·
      refine ⟨41454474803023464350347549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55272633070697952467130065 41454474803023464350347549)
      ·
        refine ⟨15545428051133799131380331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41454474803023464350347549 15545428051133799131380331)
        ·
          refine ⟨23318142076700698697070497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15545428051133799131380331 23318142076700698697070497)
          ·
            refine ⟨17488606557525524022802873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23318142076700698697070497 17488606557525524022802873)
            ·
              refine ⟨13116454918144143017102155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17488606557525524022802873 13116454918144143017102155)
              ·
                refine ⟨19674682377216214525653233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13116454918144143017102155 19674682377216214525653233)
                ·
                  refine ⟨14756011782912160894239925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19674682377216214525653233 14756011782912160894239925)
                  ·
                    refine ⟨1383376104648015083834993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14756011782912160894239925 1383376104648015083834993)
                    ·
                      rfl

theorem cell22_4041173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_4041173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041173 prefixEnd_4041173 := by exact prefixLift 4041173
  have htrace : WordTrace (prefixWord ++ tailWord_4041173) baseStart_4041173 baseEnd_4041173 := by
    simpa [prefixWord, tailWord_4041173, baseEnd_4041173] using wordTrace_append hprefix tailTrace_4041173
  have hstable : (prefixWord ++ tailWord_4041173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041173).length < 2 ^ (prefixWord ++ tailWord_4041173).sum := by decide
  have hdescent : baseEnd_4041173 < baseStart_4041173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041216 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_4041216 : Nat := 118140960795 + 4041216 * 2 ^ 59
def prefixEnd_4041216 : Nat := 4983230072969 + 3 ^ 40 * 4041216 * 2
def baseEnd_4041216 : Nat := 1383390824426777305009861

theorem tailTrace_4041216 : CollatzResearch.WordTrace tailWord_4041216 prefixEnd_4041216 1383390824426777305009861 := by
  unfold tailWord_4041216
  simp only [CollatzResearch.WordTrace]
  refine ⟨73697628263686045794747751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98263504351581394392997001 73697628263686045794747751)
  ·
    refine ⟨110546442395529068692121627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73697628263686045794747751 110546442395529068692121627)
    ·
      refine ⟨165819663593293603038182441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110546442395529068692121627 165819663593293603038182441)
      ·
        refine ⟨124364747694970202278636831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165819663593293603038182441 124364747694970202278636831)
        ·
          refine ⟨186547121542455303417955247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124364747694970202278636831 186547121542455303417955247)
          ·
            refine ⟨279820682313682955126932871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186547121542455303417955247 279820682313682955126932871)
            ·
              refine ⟨419731023470524432690399307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279820682313682955126932871 419731023470524432690399307)
              ·
                refine ⟨629596535205786649035598961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419731023470524432690399307 629596535205786649035598961)
                ·
                  refine ⟨472197401404339986776699221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629596535205786649035598961 472197401404339986776699221)
                  ·
                    refine ⟨1383390824426777305009861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 472197401404339986776699221 1383390824426777305009861)
                    ·
                      rfl

theorem cell22_4041216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_4041216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041216 prefixEnd_4041216 := by exact prefixLift 4041216
  have htrace : WordTrace (prefixWord ++ tailWord_4041216) baseStart_4041216 baseEnd_4041216 := by
    simpa [prefixWord, tailWord_4041216, baseEnd_4041216] using wordTrace_append hprefix tailTrace_4041216
  have hstable : (prefixWord ++ tailWord_4041216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041216).length < 2 ^ (prefixWord ++ tailWord_4041216).sum := by decide
  have hdescent : baseEnd_4041216 < baseStart_4041216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041220 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_4041220 : Nat := 118140960795 + 4041220 * 2 ^ 59
def prefixEnd_4041220 : Nat := 4983230072969 + 3 ^ 40 * 4041220 * 2
def baseEnd_4041220 : Nat := 461130731236174209303283

theorem tailTrace_4041220 : CollatzResearch.WordTrace tailWord_4041220 prefixEnd_4041220 461130731236174209303283 := by
  unfold tailWord_4041220
  simp only [CollatzResearch.WordTrace]
  refine ⟨73697701209678800136320557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98263601612905066848427409 73697701209678800136320557)
  ·
    refine ⟨27636637953629550051120209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73697701209678800136320557 27636637953629550051120209)
    ·
      refine ⟨20727478465222162538340157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27636637953629550051120209 20727478465222162538340157)
      ·
        refine ⟨7772804424458310951877559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20727478465222162538340157 7772804424458310951877559)
        ·
          refine ⟨11659206636687466427816339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772804424458310951877559 11659206636687466427816339)
          ·
            refine ⟨17488809955031199641724509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11659206636687466427816339 17488809955031199641724509)
            ·
              refine ⟨6558303733136699865646691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17488809955031199641724509 6558303733136699865646691)
              ·
                refine ⟨9837455599705049798470037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558303733136699865646691 9837455599705049798470037)
                ·
                  refine ⟨461130731236174209303283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9837455599705049798470037 461130731236174209303283)
                  ·
                    rfl

theorem cell22_4041220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_4041220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041220 prefixEnd_4041220 := by exact prefixLift 4041220
  have htrace : WordTrace (prefixWord ++ tailWord_4041220) baseStart_4041220 baseEnd_4041220 := by
    simpa [prefixWord, tailWord_4041220, baseEnd_4041220] using wordTrace_append hprefix tailTrace_4041220
  have hstable : (prefixWord ++ tailWord_4041220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041220).length < 2 ^ (prefixWord ++ tailWord_4041220).sum := by decide
  have hdescent : baseEnd_4041220 < baseStart_4041220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041231 : List Nat := [1, 1, 2, 1, 1, 1, 2, 13]
def baseStart_4041231 : Nat := 118140960795 + 4041231 * 2 ^ 59
def prefixEnd_4041231 : Nat := 4983230072969 + 3 ^ 40 * 4041231 * 2
def baseEnd_4041231 : Nat := 153710662137035807320535

theorem tailTrace_4041231 : CollatzResearch.WordTrace tailWord_4041231 prefixEnd_4041231 153710662137035807320535 := by
  unfold tailWord_4041231
  simp only [CollatzResearch.WordTrace]
  refine ⟨147395803622317749151291547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98263869081545166100861031 147395803622317749151291547)
  ·
    refine ⟨221093705433476623726937321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147395803622317749151291547 221093705433476623726937321)
    ·
      refine ⟨165820279075107467795202991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221093705433476623726937321 165820279075107467795202991)
      ·
        refine ⟨248730418612661201692804487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165820279075107467795202991 248730418612661201692804487)
        ·
          refine ⟨373095627918991802539206731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248730418612661201692804487 373095627918991802539206731)
          ·
            refine ⟨559643441878487703808810097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373095627918991802539206731 559643441878487703808810097)
            ·
              refine ⟨419732581408865777856607573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559643441878487703808810097 419732581408865777856607573)
              ·
                refine ⟨153710662137035807320535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 419732581408865777856607573 153710662137035807320535)
                ·
                  rfl

theorem cell22_4041231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 13].length) (baseStart_4041231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041231 prefixEnd_4041231 := by exact prefixLift 4041231
  have htrace : WordTrace (prefixWord ++ tailWord_4041231) baseStart_4041231 baseEnd_4041231 := by
    simpa [prefixWord, tailWord_4041231, baseEnd_4041231] using wordTrace_append hprefix tailTrace_4041231
  have hstable : (prefixWord ++ tailWord_4041231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041231).length < 2 ^ (prefixWord ++ tailWord_4041231).sum := by decide
  have hdescent : baseEnd_4041231 < baseStart_4041231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041235 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 2, 3]
def baseStart_4041235 : Nat := 118140960795 + 4041235 * 2 ^ 59
def prefixEnd_4041235 : Nat := 4983230072969 + 3 ^ 40 * 4041235 * 2
def baseEnd_4041235 : Nat := 1383397328515067588784803

theorem tailTrace_4041235 : CollatzResearch.WordTrace tailWord_4041235 prefixEnd_4041235 1383397328515067588784803 := by
  unfold tailWord_4041235
  simp only [CollatzResearch.WordTrace]
  refine ⟨147395949514303257834437159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98263966342868838556291439 147395949514303257834437159)
  ·
    refine ⟨221093924271454886751655739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147395949514303257834437159 221093924271454886751655739)
    ·
      refine ⟨331640886407182330127483609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221093924271454886751655739 331640886407182330127483609)
      ·
        refine ⟨248730664805386747595612707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331640886407182330127483609 248730664805386747595612707)
        ·
          refine ⟨373095997208080121393419061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248730664805386747595612707 373095997208080121393419061)
          ·
            refine ⟨34977749738257511380633037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373095997208080121393419061 34977749738257511380633037)
            ·
              refine ⟨13116656151846566767737389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34977749738257511380633037 13116656151846566767737389)
              ·
                refine ⟨4918746056942462537901521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13116656151846566767737389 4918746056942462537901521)
                ·
                  refine ⟨3689059542706846903426141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4918746056942462537901521 3689059542706846903426141)
                  ·
                    refine ⟨1383397328515067588784803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689059542706846903426141 1383397328515067588784803)
                    ·
                      rfl

theorem cell22_4041235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 3].length) (baseStart_4041235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041235 prefixEnd_4041235 := by exact prefixLift 4041235
  have htrace : WordTrace (prefixWord ++ tailWord_4041235) baseStart_4041235 baseEnd_4041235 := by
    simpa [prefixWord, tailWord_4041235, baseEnd_4041235] using wordTrace_append hprefix tailTrace_4041235
  have hstable : (prefixWord ++ tailWord_4041235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041235).length < 2 ^ (prefixWord ++ tailWord_4041235).sum := by decide
  have hdescent : baseEnd_4041235 < baseStart_4041235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041239 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 1, 4]
def baseStart_4041239 : Nat := 118140960795 + 4041239 * 2 ^ 59
def prefixEnd_4041239 : Nat := 4983230072969 + 3 ^ 40 * 4041239 * 2
def baseEnd_4041239 : Nat := 1383398697796812911684791

theorem tailTrace_4041239 : CollatzResearch.WordTrace tailWord_4041239 prefixEnd_4041239 1383398697796812911684791 := by
  unfold tailWord_4041239
  simp only [CollatzResearch.WordTrace]
  refine ⟨147396095406288766517582771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98264063604192511011721847 147396095406288766517582771)
  ·
    refine ⟨221094143109433149776374157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147396095406288766517582771 221094143109433149776374157)
    ·
      refine ⟨82910303666037431166140309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221094143109433149776374157 82910303666037431166140309)
      ·
        refine ⟨3886420484345504585912827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82910303666037431166140309 3886420484345504585912827)
        ·
          refine ⟨5829630726518256878869241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886420484345504585912827 5829630726518256878869241)
          ·
            refine ⟨4372223044888692659151931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5829630726518256878869241 4372223044888692659151931)
            ·
              refine ⟨6558334567333038988727897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372223044888692659151931 6558334567333038988727897)
              ·
                refine ⟨4918750925499779241545923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6558334567333038988727897 4918750925499779241545923)
                ·
                  refine ⟨7378126388249668862318885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918750925499779241545923 7378126388249668862318885)
                  ·
                    refine ⟨1383398697796812911684791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7378126388249668862318885 1383398697796812911684791)
                    ·
                      rfl

theorem cell22_4041239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_4041239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041239 prefixEnd_4041239 := by exact prefixLift 4041239
  have htrace : WordTrace (prefixWord ++ tailWord_4041239) baseStart_4041239 baseEnd_4041239 := by
    simpa [prefixWord, tailWord_4041239, baseEnd_4041239] using wordTrace_append hprefix tailTrace_4041239
  have hstable : (prefixWord ++ tailWord_4041239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041239).length < 2 ^ (prefixWord ++ tailWord_4041239).sum := by decide
  have hdescent : baseEnd_4041239 < baseStart_4041239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041252 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_4041252 : Nat := 118140960795 + 4041252 * 2 ^ 59
def prefixEnd_4041252 : Nat := 4983230072969 + 3 ^ 40 * 4041252 * 2
def baseEnd_4041252 : Nat := 1383403147962485211109751

theorem tailTrace_4041252 : CollatzResearch.WordTrace tailWord_4041252 prefixEnd_4041252 1383403147962485211109751 := by
  unfold tailWord_4041252
  simp only [CollatzResearch.WordTrace]
  refine ⟨73698284777620834868903005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98264379703494446491870673 73698284777620834868903005)
  ·
    refine ⟨27636856791607813075838627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73698284777620834868903005 27636856791607813075838627)
    ·
      refine ⟨41455285187411719613757941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27636856791607813075838627 41455285187411719613757941)
      ·
        refine ⟨3886432986319848713789807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41455285187411719613757941 3886432986319848713789807)
        ·
          refine ⟨5829649479479773070684711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886432986319848713789807 5829649479479773070684711)
          ·
            refine ⟨8744474219219659606027067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829649479479773070684711 8744474219219659606027067)
            ·
              refine ⟨13116711328829489409040601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744474219219659606027067 13116711328829489409040601)
              ·
                refine ⟨9837533496622117056780451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13116711328829489409040601 9837533496622117056780451)
                ·
                  refine ⟨14756300244933175585170677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9837533496622117056780451 14756300244933175585170677)
                  ·
                    refine ⟨1383403147962485211109751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14756300244933175585170677 1383403147962485211109751)
                    ·
                      rfl

theorem cell22_4041252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_4041252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041252 prefixEnd_4041252 := by exact prefixLift 4041252
  have htrace : WordTrace (prefixWord ++ tailWord_4041252) baseStart_4041252 baseEnd_4041252 := by
    simpa [prefixWord, tailWord_4041252, baseEnd_4041252] using wordTrace_append hprefix tailTrace_4041252
  have hstable : (prefixWord ++ tailWord_4041252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041252).length < 2 ^ (prefixWord ++ tailWord_4041252).sum := by decide
  have hdescent : baseEnd_4041252 < baseStart_4041252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041323 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 5, 4]
def baseStart_4041323 : Nat := 118140960795 + 4041323 * 2 ^ 59
def prefixEnd_4041323 : Nat := 4983230072969 + 3 ^ 40 * 4041323 * 2
def baseEnd_4041323 : Nat := 1383427452713464692584533

theorem tailTrace_4041323 : CollatzResearch.WordTrace tailWord_4041323 prefixEnd_4041323 1383427452713464692584533 := by
  unfold tailWord_4041323
  simp only [CollatzResearch.WordTrace]
  refine ⟨147399159137984448863640623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98266106091989632575760415 147399159137984448863640623)
  ·
    refine ⟨221098738706976673295460935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147399159137984448863640623 221098738706976673295460935)
    ·
      refine ⟨331648108060465009943191403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221098738706976673295460935 331648108060465009943191403)
      ·
        refine ⟨497472162090697514914787105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331648108060465009943191403 497472162090697514914787105)
        ·
          refine ⟨373104121568023136186090329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497472162090697514914787105 373104121568023136186090329)
          ·
            refine ⟨279828091176017352139567747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373104121568023136186090329 279828091176017352139567747)
            ·
              refine ⟨419742136764026028209351621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279828091176017352139567747 419742136764026028209351621)
              ·
                refine ⟨78701650643254880289253429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419742136764026028209351621 78701650643254880289253429)
                ·
                  refine ⟨7378279747805145027117509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78701650643254880289253429 7378279747805145027117509)
                  ·
                    refine ⟨1383427452713464692584533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7378279747805145027117509 1383427452713464692584533)
                    ·
                      rfl

theorem cell22_4041323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_4041323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041323 prefixEnd_4041323 := by exact prefixLift 4041323
  have htrace : WordTrace (prefixWord ++ tailWord_4041323) baseStart_4041323 baseEnd_4041323 := by
    simpa [prefixWord, tailWord_4041323, baseEnd_4041323] using wordTrace_append hprefix tailTrace_4041323
  have hstable : (prefixWord ++ tailWord_4041323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041323).length < 2 ^ (prefixWord ++ tailWord_4041323).sum := by decide
  have hdescent : baseEnd_4041323 < baseStart_4041323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041325 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_4041325 : Nat := 118140960795 + 4041325 * 2 ^ 59
def prefixEnd_4041325 : Nat := 4983230072969 + 3 ^ 40 * 4041325 * 2
def baseEnd_4041325 : Nat := 1383428137354337354034527

theorem tailTrace_4041325 : CollatzResearch.WordTrace tailWord_4041325 prefixEnd_4041325 1383428137354337354034527 := by
  unfold tailWord_4041325
  simp only [CollatzResearch.WordTrace]
  refine ⟨147399232083977203205213429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98266154722651468803475619 147399232083977203205213429)
  ·
    refine ⟨13818678007872862800488759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147399232083977203205213429 13818678007872862800488759)
    ·
      refine ⟨20728017011809294200733139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13818678007872862800488759 20728017011809294200733139)
      ·
        refine ⟨31092025517713941301099709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20728017011809294200733139 31092025517713941301099709)
        ·
          refine ⟨11659509569142727987912391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31092025517713941301099709 11659509569142727987912391)
          ·
            refine ⟨17489264353714091981868587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11659509569142727987912391 17489264353714091981868587)
            ·
              refine ⟨26233896530571137972802881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17489264353714091981868587 26233896530571137972802881)
              ·
                refine ⟨19675422397928353479602161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26233896530571137972802881 19675422397928353479602161)
                ·
                  refine ⟨14756566798446265109701621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19675422397928353479602161 14756566798446265109701621)
                  ·
                    refine ⟨1383428137354337354034527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14756566798446265109701621 1383428137354337354034527)
                    ·
                      rfl

theorem cell22_4041325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_4041325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041325 prefixEnd_4041325 := by exact prefixLift 4041325
  have htrace : WordTrace (prefixWord ++ tailWord_4041325) baseStart_4041325 baseEnd_4041325 := by
    simpa [prefixWord, tailWord_4041325, baseEnd_4041325] using wordTrace_append hprefix tailTrace_4041325
  have hstable : (prefixWord ++ tailWord_4041325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041325).length < 2 ^ (prefixWord ++ tailWord_4041325).sum := by decide
  have hdescent : baseEnd_4041325 < baseStart_4041325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041462 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_4041462 : Nat := 118140960795 + 4041462 * 2 ^ 59
def prefixEnd_4041462 : Nat := 4983230072969 + 3 ^ 40 * 4041462 * 2
def baseEnd_4041462 : Nat := 461158345084704887786369

theorem tailTrace_4041462 : CollatzResearch.WordTrace tailWord_4041462 prefixEnd_4041462 461158345084704887786369 := by
  unfold tailWord_4041462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212764305280054725184415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98269485922987250401967093 9212764305280054725184415)
  ·
    refine ⟨13819146457920082087776623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9212764305280054725184415 13819146457920082087776623)
    ·
      refine ⟨20728719686880123131664935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13819146457920082087776623 20728719686880123131664935)
      ·
        refine ⟨31093079530320184697497403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20728719686880123131664935 31093079530320184697497403)
        ·
          refine ⟨46639619295480277046246105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31093079530320184697497403 46639619295480277046246105)
          ·
            refine ⟨34979714471610207784684579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46639619295480277046246105 34979714471610207784684579)
            ·
              refine ⟨52469571707415311677026869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34979714471610207784684579 52469571707415311677026869)
              ·
                refine ⟨4919022347570185469721269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52469571707415311677026869 4919022347570185469721269)
                ·
                  refine ⟨461158345084704887786369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919022347570185469721269 461158345084704887786369)
                  ·
                    rfl

theorem cell22_4041462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_4041462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041462 prefixEnd_4041462 := by exact prefixLift 4041462
  have htrace : WordTrace (prefixWord ++ tailWord_4041462) baseStart_4041462 baseEnd_4041462 := by
    simpa [prefixWord, tailWord_4041462, baseEnd_4041462] using wordTrace_append hprefix tailTrace_4041462
  have hstable : (prefixWord ++ tailWord_4041462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041462).length < 2 ^ (prefixWord ++ tailWord_4041462).sum := by decide
  have hdescent : baseEnd_4041462 < baseStart_4041462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041661 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_4041661 : Nat := 118140960795 + 4041661 * 2 ^ 59
def prefixEnd_4041661 : Nat := 4983230072969 + 3 ^ 40 * 4041661 * 2
def baseEnd_4041661 : Nat := 1383543157020944477633497

theorem tailTrace_4041661 : CollatzResearch.WordTrace tailWord_4041661 prefixEnd_4041661 1383543157020944477633497 := by
  unfold tailWord_4041661
  simp only [CollatzResearch.WordTrace]
  refine ⟨147411487010759932589444837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98274324673839955059629891 147411487010759932589444837)
  ·
    refine ⟨27639653814517487360520907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147411487010759932589444837 27639653814517487360520907)
    ·
      refine ⟨41459480721776231040781361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27639653814517487360520907 41459480721776231040781361)
      ·
        refine ⟨31094610541332173280586021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41459480721776231040781361 31094610541332173280586021)
        ·
          refine ⟨5830239476499782490109879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31094610541332173280586021 5830239476499782490109879)
          ·
            refine ⟨8745359214749673735164819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830239476499782490109879 8745359214749673735164819)
            ·
              refine ⟨13118038822124510602747229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745359214749673735164819 13118038822124510602747229)
              ·
                refine ⟨4919264558296691476030211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13118038822124510602747229 4919264558296691476030211)
                ·
                  refine ⟨7378896837445037214045317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919264558296691476030211 7378896837445037214045317)
                  ·
                    refine ⟨1383543157020944477633497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7378896837445037214045317 1383543157020944477633497)
                    ·
                      rfl

theorem cell22_4041661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_4041661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041661 prefixEnd_4041661 := by exact prefixLift 4041661
  have htrace : WordTrace (prefixWord ++ tailWord_4041661) baseStart_4041661 baseEnd_4041661 := by
    simpa [prefixWord, tailWord_4041661, baseEnd_4041661] using wordTrace_append hprefix tailTrace_4041661
  have hstable : (prefixWord ++ tailWord_4041661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041661).length < 2 ^ (prefixWord ++ tailWord_4041661).sum := by decide
  have hdescent : baseEnd_4041661 < baseStart_4041661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041704 : List Nat := [2, 1, 4, 1, 1, 1, 6, 6]
def baseStart_4041704 : Nat := 118140960795 + 4041704 * 2 ^ 59
def prefixEnd_4041704 : Nat := 4983230072969 + 3 ^ 40 * 4041704 * 2
def baseEnd_4041704 : Nat := 153728652977745188756485

theorem tailTrace_4041704 : CollatzResearch.WordTrace tailWord_4041704 prefixEnd_4041704 153728652977745188756485 := by
  unfold tailWord_4041704
  simp only [CollatzResearch.WordTrace]
  refine ⟨73706527674802075466630083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98275370233069433955506777 73706527674802075466630083)
  ·
    refine ⟨110559791512203113199945125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73706527674802075466630083 110559791512203113199945125)
    ·
      refine ⟨20729960908538083724989711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110559791512203113199945125 20729960908538083724989711)
      ·
        refine ⟨31094941362807125587484567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729960908538083724989711 31094941362807125587484567)
        ·
          refine ⟨46642412044210688381226851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31094941362807125587484567 46642412044210688381226851)
          ·
            refine ⟨69963618066316032571840277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46642412044210688381226851 69963618066316032571840277)
            ·
              refine ⟨3279544596858564026805013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69963618066316032571840277 3279544596858564026805013)
              ·
                refine ⟨153728652977745188756485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3279544596858564026805013 153728652977745188756485)
                ·
                  rfl

theorem cell22_4041704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_4041704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041704 prefixEnd_4041704 := by exact prefixLift 4041704
  have htrace : WordTrace (prefixWord ++ tailWord_4041704) baseStart_4041704 baseEnd_4041704 := by
    simpa [prefixWord, tailWord_4041704, baseEnd_4041704] using wordTrace_append hprefix tailTrace_4041704
  have hstable : (prefixWord ++ tailWord_4041704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041704).length < 2 ^ (prefixWord ++ tailWord_4041704).sum := by decide
  have hdescent : baseEnd_4041704 < baseStart_4041704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041710 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_4041710 : Nat := 118140960795 + 4041710 * 2 ^ 59
def prefixEnd_4041710 : Nat := 4983230072969 + 3 ^ 40 * 4041710 * 2
def baseEnd_4041710 : Nat := 461186643574108227719449

theorem tailTrace_4041710 : CollatzResearch.WordTrace tailWord_4041710 prefixEnd_4041710 461186643574108227719449 := by
  unfold tailWord_4041710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426659273447801744747323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98275516125054942638652389 18426659273447801744747323)
  ·
    refine ⟨27639988910171702617120985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18426659273447801744747323 27639988910171702617120985)
    ·
      refine ⟨20729991682628776962840739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27639988910171702617120985 20729991682628776962840739)
      ·
        refine ⟨31094987523943165444261109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729991682628776962840739 31094987523943165444261109)
        ·
          refine ⟨2915155080369671760399479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31094987523943165444261109 2915155080369671760399479)
          ·
            refine ⟨4372732620554507640599219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915155080369671760399479 4372732620554507640599219)
            ·
              refine ⟨6559098930831761460898829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372732620554507640599219 6559098930831761460898829)
              ·
                refine ⟨2459662099061910547837061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6559098930831761460898829 2459662099061910547837061)
                ·
                  refine ⟨461186643574108227719449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459662099061910547837061 461186643574108227719449)
                  ·
                    rfl

theorem cell22_4041710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_4041710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041710 prefixEnd_4041710 := by exact prefixLift 4041710
  have htrace : WordTrace (prefixWord ++ tailWord_4041710) baseStart_4041710 baseEnd_4041710 := by
    simpa [prefixWord, tailWord_4041710, baseEnd_4041710] using wordTrace_append hprefix tailTrace_4041710
  have hstable : (prefixWord ++ tailWord_4041710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041710).length < 2 ^ (prefixWord ++ tailWord_4041710).sum := by decide
  have hdescent : baseEnd_4041710 < baseStart_4041710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041736 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_4041736 : Nat := 118140960795 + 4041736 * 2 ^ 59
def prefixEnd_4041736 : Nat := 4983230072969 + 3 ^ 40 * 4041736 * 2
def baseEnd_4041736 : Nat := 1383568831053669282008267

theorem tailTrace_4041736 : CollatzResearch.WordTrace tailWord_4041736 prefixEnd_4041736 1383568831053669282008267 := by
  unfold tailWord_4041736
  simp only [CollatzResearch.WordTrace]
  refine ⟨73707111242744110199212531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98276148323658813598950041 73707111242744110199212531)
  ·
    refine ⟨110560666864116165298818797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73707111242744110199212531 110560666864116165298818797)
    ·
      refine ⟨41460250074043561987057049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110560666864116165298818797 41460250074043561987057049)
      ·
        refine ⟨31095187555532671490292787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41460250074043561987057049 31095187555532671490292787)
        ·
          refine ⟨46642781333299007235439181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31095187555532671490292787 46642781333299007235439181)
          ·
            refine ⟨17491042999987127713289693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46642781333299007235439181 17491042999987127713289693)
            ·
              refine ⟨6559141124995172892483635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17491042999987127713289693 6559141124995172892483635)
              ·
                refine ⟨9838711687492759338725453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559141124995172892483635 9838711687492759338725453)
                ·
                  refine ⟨3689516882809784752022045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9838711687492759338725453 3689516882809784752022045)
                  ·
                    refine ⟨1383568831053669282008267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689516882809784752022045 1383568831053669282008267)
                    ·
                      rfl

theorem cell22_4041736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_4041736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041736 prefixEnd_4041736 := by exact prefixLift 4041736
  have htrace : WordTrace (prefixWord ++ tailWord_4041736) baseStart_4041736 baseEnd_4041736 := by
    simpa [prefixWord, tailWord_4041736, baseEnd_4041736] using wordTrace_append hprefix tailTrace_4041736
  have hstable : (prefixWord ++ tailWord_4041736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041736).length < 2 ^ (prefixWord ++ tailWord_4041736).sum := by decide
  have hdescent : baseEnd_4041736 < baseStart_4041736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041747 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_4041747 : Nat := 118140960795 + 4041747 * 2 ^ 59
def prefixEnd_4041747 : Nat := 4983230072969 + 3 ^ 40 * 4041747 * 2
def baseEnd_4041747 : Nat := 1383572596578468919983233

theorem tailTrace_4041747 : CollatzResearch.WordTrace tailWord_4041747 prefixEnd_4041747 1383572596578468919983233 := by
  unfold tailWord_4041747
  simp only [CollatzResearch.WordTrace]
  refine ⟨147414623688448369277075495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98276415792298912851383663 147414623688448369277075495)
  ·
    refine ⟨221121935532672553915613243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147414623688448369277075495 221121935532672553915613243)
    ·
      refine ⟨331682903299008830873419865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221121935532672553915613243 331682903299008830873419865)
      ·
        refine ⟨248762177474256623155064899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331682903299008830873419865 248762177474256623155064899)
        ·
          refine ⟨373143266211384934732597349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248762177474256623155064899 373143266211384934732597349)
          ·
            refine ⟨69964362414634675262362003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373143266211384934732597349 69964362414634675262362003)
            ·
              refine ⟨104946543621952012893543005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69964362414634675262362003 104946543621952012893543005)
              ·
                refine ⟨39354953858232004835078627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104946543621952012893543005 39354953858232004835078627)
                ·
                  refine ⟨59032430787348007252617941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39354953858232004835078627 59032430787348007252617941)
                  ·
                    refine ⟨1383572596578468919983233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59032430787348007252617941 1383572596578468919983233)
                    ·
                      rfl

theorem cell22_4041747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_4041747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041747 prefixEnd_4041747 := by exact prefixLift 4041747
  have htrace : WordTrace (prefixWord ++ tailWord_4041747) baseStart_4041747 baseEnd_4041747 := by
    simpa [prefixWord, tailWord_4041747, baseEnd_4041747] using wordTrace_append hprefix tailTrace_4041747
  have hstable : (prefixWord ++ tailWord_4041747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041747).length < 2 ^ (prefixWord ++ tailWord_4041747).sum := by decide
  have hdescent : baseEnd_4041747 < baseStart_4041747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041798 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4041798 : Nat := 118140960795 + 4041798 * 2 ^ 59
def prefixEnd_4041798 : Nat := 4983230072969 + 3 ^ 40 * 4041798 * 2
def baseEnd_4041798 : Nat := 1383590054920721786958077

theorem tailTrace_4041798 : CollatzResearch.WordTrace tailWord_4041798 prefixEnd_4041798 1383590054920721786958077 := by
  unfold tailWord_4041798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606765119101987655849439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98277655874175736658121365 4606765119101987655849439)
  ·
    refine ⟨6910147678652981483774159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4606765119101987655849439 6910147678652981483774159)
    ·
      refine ⟨10365221517979472225661239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6910147678652981483774159 10365221517979472225661239)
      ·
        refine ⟨15547832276969208338491859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10365221517979472225661239 15547832276969208338491859)
        ·
          refine ⟨23321748415453812507737789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15547832276969208338491859 23321748415453812507737789)
          ·
            refine ⟨8745655655795179690401671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23321748415453812507737789 8745655655795179690401671)
            ·
              refine ⟨13118483483692769535602507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745655655795179690401671 13118483483692769535602507)
              ·
                refine ⟨19677725225539154303403761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13118483483692769535602507 19677725225539154303403761)
                ·
                  refine ⟨14758293919154365727552821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19677725225539154303403761 14758293919154365727552821)
                  ·
                    refine ⟨1383590054920721786958077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14758293919154365727552821 1383590054920721786958077)
                    ·
                      rfl

theorem cell22_4041798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4041798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041798 prefixEnd_4041798 := by exact prefixLift 4041798
  have htrace : WordTrace (prefixWord ++ tailWord_4041798) baseStart_4041798 baseEnd_4041798 := by
    simpa [prefixWord, tailWord_4041798, baseEnd_4041798] using wordTrace_append hprefix tailTrace_4041798
  have hstable : (prefixWord ++ tailWord_4041798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041798).length < 2 ^ (prefixWord ++ tailWord_4041798).sum := by decide
  have hdescent : baseEnd_4041798 < baseStart_4041798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041809 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_4041809 : Nat := 118140960795 + 4041809 * 2 ^ 59
def prefixEnd_4041809 : Nat := 4983230072969 + 3 ^ 40 * 4041809 * 2
def baseEnd_4041809 : Nat := 1383593820445521424933043

theorem tailTrace_4041809 : CollatzResearch.WordTrace tailWord_4041809 prefixEnd_4041809 1383593820445521424933043 := by
  unfold tailWord_4041809
  simp only [CollatzResearch.WordTrace]
  refine ⟨147416885014223753865832481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98277923342815835910554987 147416885014223753865832481)
  ·
    refine ⟨110562663760667815399374361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147416885014223753865832481 110562663760667815399374361)
    ·
      refine ⟨82921997820500861549530771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110562663760667815399374361 82921997820500861549530771)
      ·
        refine ⟨124382996730751292324296157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82921997820500861549530771 124382996730751292324296157)
        ·
          refine ⟨46643623774031734621611059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124382996730751292324296157 46643623774031734621611059)
          ·
            refine ⟨69965435661047601932416589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46643623774031734621611059 69965435661047601932416589)
            ·
              refine ⟨26237038372892850724656221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69965435661047601932416589 26237038372892850724656221)
              ·
                refine ⟨9838889389834819021746083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26237038372892850724656221 9838889389834819021746083)
                ·
                  refine ⟨14758334084752228532619125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838889389834819021746083 14758334084752228532619125)
                  ·
                    refine ⟨1383593820445521424933043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14758334084752228532619125 1383593820445521424933043)
                    ·
                      rfl

theorem cell22_4041809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_4041809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041809 prefixEnd_4041809 := by exact prefixLift 4041809
  have htrace : WordTrace (prefixWord ++ tailWord_4041809) baseStart_4041809 baseEnd_4041809 := by
    simpa [prefixWord, tailWord_4041809, baseEnd_4041809] using wordTrace_append hprefix tailTrace_4041809
  have hstable : (prefixWord ++ tailWord_4041809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041809).length < 2 ^ (prefixWord ++ tailWord_4041809).sum := by decide
  have hdescent : baseEnd_4041809 < baseStart_4041809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041824 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_4041824 : Nat := 118140960795 + 4041824 * 2 ^ 59
def prefixEnd_4041824 : Nat := 4983230072969 + 3 ^ 40 * 4041824 * 2
def baseEnd_4041824 : Nat := 1383598955252066385807997

theorem tailTrace_4041824 : CollatzResearch.WordTrace tailWord_4041824 prefixEnd_4041824 1383598955252066385807997 := by
  unfold tailWord_4041824
  simp only [CollatzResearch.WordTrace]
  refine ⟨73708716054584705713814263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98278288072779607618419017 73708716054584705713814263)
  ·
    refine ⟨110563074081877058570721395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73708716054584705713814263 110563074081877058570721395)
    ·
      refine ⟨165844611122815587856082093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110563074081877058570721395 165844611122815587856082093)
      ·
        refine ⟨62191729171055845446030785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165844611122815587856082093 62191729171055845446030785)
        ·
          refine ⟨46643796878291884084523089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62191729171055845446030785 46643796878291884084523089)
          ·
            refine ⟨34982847658718913063392317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46643796878291884084523089 34982847658718913063392317)
            ·
              refine ⟨13118567872019592398772119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34982847658718913063392317 13118567872019592398772119)
              ·
                refine ⟨19677851808029388598158179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13118567872019592398772119 19677851808029388598158179)
                ·
                  refine ⟨29516777712044082897237269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19677851808029388598158179 29516777712044082897237269)
                  ·
                    refine ⟨1383598955252066385807997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29516777712044082897237269 1383598955252066385807997)
                    ·
                      rfl

theorem cell22_4041824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_4041824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041824 prefixEnd_4041824 := by exact prefixLift 4041824
  have htrace : WordTrace (prefixWord ++ tailWord_4041824) baseStart_4041824 baseEnd_4041824 := by
    simpa [prefixWord, tailWord_4041824, baseEnd_4041824] using wordTrace_append hprefix tailTrace_4041824
  have hstable : (prefixWord ++ tailWord_4041824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041824).length < 2 ^ (prefixWord ++ tailWord_4041824).sum := by decide
  have hdescent : baseEnd_4041824 < baseStart_4041824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041860 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_4041860 : Nat := 118140960795 + 4041860 * 2 ^ 59
def prefixEnd_4041860 : Nat := 4983230072969 + 3 ^ 40 * 4041860 * 2
def baseEnd_4041860 : Nat := 1383611278787774291907887

theorem tailTrace_4041860 : CollatzResearch.WordTrace tailWord_4041860 prefixEnd_4041860 1383611278787774291907887 := by
  unfold tailWord_4041860
  simp only [CollatzResearch.WordTrace]
  refine ⟨73709372568519494787969517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98279163424692659717292689 73709372568519494787969517)
  ·
    refine ⟨27641014713194810545488569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73709372568519494787969517 27641014713194810545488569)
    ·
      refine ⟨20730761034896107909116427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27641014713194810545488569 20730761034896107909116427)
      ·
        refine ⟨31096141552344161863674641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20730761034896107909116427 31096141552344161863674641)
        ·
          refine ⟨23322106164258121397755981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31096141552344161863674641 23322106164258121397755981)
          ·
            refine ⟨8745789811596795524158493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23322106164258121397755981 8745789811596795524158493)
            ·
              refine ⟨3279671179348798321559435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8745789811596795524158493 3279671179348798321559435)
              ·
                refine ⟨4919506769023197482339153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279671179348798321559435 4919506769023197482339153)
                ·
                  refine ⟨3689630076767398111754365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919506769023197482339153 3689630076767398111754365)
                  ·
                    refine ⟨1383611278787774291907887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689630076767398111754365 1383611278787774291907887)
                    ·
                      rfl

theorem cell22_4041860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_4041860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041860 prefixEnd_4041860 := by exact prefixLift 4041860
  have htrace : WordTrace (prefixWord ++ tailWord_4041860) baseStart_4041860 baseEnd_4041860 := by
    simpa [prefixWord, tailWord_4041860, baseEnd_4041860] using wordTrace_append hprefix tailTrace_4041860
  have hstable : (prefixWord ++ tailWord_4041860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041860).length < 2 ^ (prefixWord ++ tailWord_4041860).sum := by decide
  have hdescent : baseEnd_4041860 < baseStart_4041860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041905 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_4041905 : Nat := 118140960795 + 4041905 * 2 ^ 59
def prefixEnd_4041905 : Nat := 4983230072969 + 3 ^ 40 * 4041905 * 2
def baseEnd_4041905 : Nat := 1383626683207409174532749

theorem tailTrace_4041905 : CollatzResearch.WordTrace tailWord_4041905 prefixEnd_4041905 1383626683207409174532749 := by
  unfold tailWord_4041905
  simp only [CollatzResearch.WordTrace]
  refine ⟨147420386421875962261327169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98280257614583974840884779 147420386421875962261327169)
  ·
    refine ⟨110565289816406971695995377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147420386421875962261327169 110565289816406971695995377)
    ·
      refine ⟨82923967362305228771996533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110565289816406971695995377 82923967362305228771996533)
      ·
        refine ⟨7774121940216115197374675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82923967362305228771996533 7774121940216115197374675)
        ·
          refine ⟨11661182910324172796062013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774121940216115197374675 11661182910324172796062013)
          ·
            refine ⟨4372943591371564798523255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11661182910324172796062013 4372943591371564798523255)
            ·
              refine ⟨6559415387057347197784883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372943591371564798523255 6559415387057347197784883)
              ·
                refine ⟨9839123080586020796677325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559415387057347197784883 9839123080586020796677325)
                ·
                  refine ⟨3689671155219757798753997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9839123080586020796677325 3689671155219757798753997)
                  ·
                    refine ⟨1383626683207409174532749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689671155219757798753997 1383626683207409174532749)
                    ·
                      rfl

theorem cell22_4041905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_4041905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041905 prefixEnd_4041905 := by exact prefixLift 4041905
  have htrace : WordTrace (prefixWord ++ tailWord_4041905) baseStart_4041905 baseEnd_4041905 := by
    simpa [prefixWord, tailWord_4041905, baseEnd_4041905] using wordTrace_append hprefix tailTrace_4041905
  have hstable : (prefixWord ++ tailWord_4041905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041905).length < 2 ^ (prefixWord ++ tailWord_4041905).sum := by decide
  have hdescent : baseEnd_4041905 < baseStart_4041905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041914 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_4041914 : Nat := 118140960795 + 4041914 * 2 ^ 59
def prefixEnd_4041914 : Nat := 4983230072969 + 3 ^ 40 * 4041914 * 2
def baseEnd_4041914 : Nat := 1383629764091336151057721

theorem tailTrace_4041914 : CollatzResearch.WordTrace tailWord_4041914 prefixEnd_4041914 1383629764091336151057721 := by
  unfold tailWord_4041914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36855178669710839199601199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98280476452562237865603197 36855178669710839199601199)
  ·
    refine ⟨55282768004566258799401799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36855178669710839199601199 55282768004566258799401799)
    ·
      refine ⟨82924152006849388199102699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55282768004566258799401799 82924152006849388199102699)
      ·
        refine ⟨124386228010274082298654049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82924152006849388199102699 124386228010274082298654049)
        ·
          refine ⟨93289671007705561723990537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124386228010274082298654049 93289671007705561723990537)
          ·
            refine ⟨69967253255779171292992903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93289671007705561723990537 69967253255779171292992903)
            ·
              refine ⟨104950879883668756939489355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69967253255779171292992903 104950879883668756939489355)
              ·
                refine ⟨157426319825503135409234033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104950879883668756939489355 157426319825503135409234033)
                ·
                  refine ⟨118069739869127351556925525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157426319825503135409234033 118069739869127351556925525)
                  ·
                    refine ⟨1383629764091336151057721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118069739869127351556925525 1383629764091336151057721)
                    ·
                      rfl

theorem cell22_4041914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_4041914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041914 prefixEnd_4041914 := by exact prefixLift 4041914
  have htrace : WordTrace (prefixWord ++ tailWord_4041914) baseStart_4041914 baseEnd_4041914 := by
    simpa [prefixWord, tailWord_4041914, baseEnd_4041914] using wordTrace_append hprefix tailTrace_4041914
  have hstable : (prefixWord ++ tailWord_4041914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041914).length < 2 ^ (prefixWord ++ tailWord_4041914).sum := by decide
  have hdescent : baseEnd_4041914 < baseStart_4041914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041918 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_4041918 : Nat := 118140960795 + 4041918 * 2 ^ 59
def prefixEnd_4041918 : Nat := 4983230072969 + 3 ^ 40 * 4041918 * 2
def baseEnd_4041918 : Nat := 461210377791027157985903

theorem tailTrace_4041918 : CollatzResearch.WordTrace tailWord_4041918 prefixEnd_4041918 461210377791027157985903 := by
  unfold tailWord_4041918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427607571353608185193801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98280573713885910321033605 18427607571353608185193801)
  ·
    refine ⟨13820705678515206138895351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18427607571353608185193801 13820705678515206138895351)
    ·
      refine ⟨20731058517772809208343027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13820705678515206138895351 20731058517772809208343027)
      ·
        refine ⟨31096587776659213812514541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20731058517772809208343027 31096587776659213812514541)
        ·
          refine ⟨11661220416247205179692953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31096587776659213812514541 11661220416247205179692953)
          ·
            refine ⟨8745915312185403884769715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11661220416247205179692953 8745915312185403884769715)
            ·
              refine ⟨13118872968278105827154573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745915312185403884769715 13118872968278105827154573)
              ·
                refine ⟨4919577363104289685182965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13118872968278105827154573 4919577363104289685182965)
                ·
                  refine ⟨461210377791027157985903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919577363104289685182965 461210377791027157985903)
                  ·
                    rfl

theorem cell22_4041918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_4041918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041918 prefixEnd_4041918 := by exact prefixLift 4041918
  have htrace : WordTrace (prefixWord ++ tailWord_4041918) baseStart_4041918 baseEnd_4041918 := by
    simpa [prefixWord, tailWord_4041918, baseEnd_4041918] using wordTrace_append hprefix tailTrace_4041918
  have hstable : (prefixWord ++ tailWord_4041918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041918).length < 2 ^ (prefixWord ++ tailWord_4041918).sum := by decide
  have hdescent : baseEnd_4041918 < baseStart_4041918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041931 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 1, 4]
def baseStart_4041931 : Nat := 118140960795 + 4041931 * 2 ^ 59
def prefixEnd_4041931 : Nat := 4983230072969 + 3 ^ 40 * 4041931 * 2
def baseEnd_4041931 : Nat := 1383635583538753773382669

theorem tailTrace_4041931 : CollatzResearch.WordTrace tailWord_4041931 prefixEnd_4041931 1383635583538753773382669 := by
  unfold tailWord_4041931
  simp only [CollatzResearch.WordTrace]
  refine ⟨147421334719781768701773647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98280889813187845801182431 147421334719781768701773647)
  ·
    refine ⟨221132002079672653052660471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147421334719781768701773647 221132002079672653052660471)
    ·
      refine ⟨331698003119508979578990707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221132002079672653052660471 331698003119508979578990707)
      ·
        refine ⟨497547004679263469368486061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331698003119508979578990707 497547004679263469368486061)
        ·
          refine ⟨186580126754723801013182273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497547004679263469368486061 186580126754723801013182273)
          ·
            refine ⟨139935095066042850759886705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186580126754723801013182273 139935095066042850759886705)
            ·
              refine ⟨104951321299532138069915029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139935095066042850759886705 104951321299532138069915029)
              ·
                refine ⟨4919593185915568972027267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104951321299532138069915029 4919593185915568972027267)
                ·
                  refine ⟨7379389778873353458040901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919593185915568972027267 7379389778873353458040901)
                  ·
                    refine ⟨1383635583538753773382669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7379389778873353458040901 1383635583538753773382669)
                    ·
                      rfl

theorem cell22_4041931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 4].length) (baseStart_4041931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041931 prefixEnd_4041931 := by exact prefixLift 4041931
  have htrace : WordTrace (prefixWord ++ tailWord_4041931) baseStart_4041931 baseEnd_4041931 := by
    simpa [prefixWord, tailWord_4041931, baseEnd_4041931] using wordTrace_append hprefix tailTrace_4041931
  have hstable : (prefixWord ++ tailWord_4041931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041931).length < 2 ^ (prefixWord ++ tailWord_4041931).sum := by decide
  have hdescent : baseEnd_4041931 < baseStart_4041931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041963 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 4]
def baseStart_4041963 : Nat := 118140960795 + 4041963 * 2 ^ 59
def prefixEnd_4041963 : Nat := 4983230072969 + 3 ^ 40 * 4041963 * 2
def baseEnd_4041963 : Nat := 461215512597572118860857

theorem tailTrace_4041963 : CollatzResearch.WordTrace tailWord_4041963 prefixEnd_4041963 461215512597572118860857 := by
  unfold tailWord_4041963
  simp only [CollatzResearch.WordTrace]
  refine ⟨147422501855665838166938543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98281667903777225444625695 147422501855665838166938543)
  ·
    refine ⟨221133752783498757250407815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147422501855665838166938543 221133752783498757250407815)
    ·
      refine ⟨331700629175248135875611723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221133752783498757250407815 331700629175248135875611723)
      ·
        refine ⟨497550943762872203813417585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331700629175248135875611723 497550943762872203813417585)
        ·
          refine ⟨373163207822154152860063189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497550943762872203813417585 373163207822154152860063189)
          ·
            refine ⟨8746012683331737957657731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 373163207822154152860063189 8746012683331737957657731)
            ·
              refine ⟨13119019024997606936486597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746012683331737957657731 13119019024997606936486597)
              ·
                refine ⟨2459816067187051300591237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13119019024997606936486597 2459816067187051300591237)
                ·
                  refine ⟨461215512597572118860857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459816067187051300591237 461215512597572118860857)
                  ·
                    rfl

theorem cell22_4041963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 4].length) (baseStart_4041963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041963 prefixEnd_4041963 := by exact prefixLift 4041963
  have htrace : WordTrace (prefixWord ++ tailWord_4041963) baseStart_4041963 baseEnd_4041963 := by
    simpa [prefixWord, tailWord_4041963, baseEnd_4041963] using wordTrace_append hprefix tailTrace_4041963
  have hstable : (prefixWord ++ tailWord_4041963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041963).length < 2 ^ (prefixWord ++ tailWord_4041963).sum := by decide
  have hdescent : baseEnd_4041963 < baseStart_4041963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041978 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_4041978 : Nat := 118140960795 + 4041978 * 2 ^ 59
def prefixEnd_4041978 : Nat := 4983230072969 + 3 ^ 40 * 4041978 * 2
def baseEnd_4041978 : Nat := 1383651672599261317457525

theorem tailTrace_4041978 : CollatzResearch.WordTrace tailWord_4041978 prefixEnd_4041978 1383651672599261317457525 := by
  unfold tailWord_4041978
  simp only [CollatzResearch.WordTrace]
  refine ⟨36855762237652873932183647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98282032633740997152489725 36855762237652873932183647)
  ·
    refine ⟨55283643356479310898275471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36855762237652873932183647 55283643356479310898275471)
    ·
      refine ⟨82925465034718966347413207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55283643356479310898275471 82925465034718966347413207)
      ·
        refine ⟨124388197552078449521119811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82925465034718966347413207 124388197552078449521119811)
        ·
          refine ⟨186582296328117674281679717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124388197552078449521119811 186582296328117674281679717)
          ·
            refine ⟨34984180561522063927814947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186582296328117674281679717 34984180561522063927814947)
            ·
              refine ⟨52476270842283095891722421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34984180561522063927814947 52476270842283095891722421)
              ·
                refine ⟨4919650391464040239848977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52476270842283095891722421 4919650391464040239848977)
                ·
                  refine ⟨3689737793598030179886733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919650391464040239848977 3689737793598030179886733)
                  ·
                    refine ⟨1383651672599261317457525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689737793598030179886733 1383651672599261317457525)
                    ·
                      rfl

theorem cell22_4041978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_4041978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4041978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4041978 prefixEnd_4041978 := by exact prefixLift 4041978
  have htrace : WordTrace (prefixWord ++ tailWord_4041978) baseStart_4041978 baseEnd_4041978 := by
    simpa [prefixWord, tailWord_4041978, baseEnd_4041978] using wordTrace_append hprefix tailTrace_4041978
  have hstable : (prefixWord ++ tailWord_4041978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041978).length < 2 ^ (prefixWord ++ tailWord_4041978).sum := by decide
  have hdescent : baseEnd_4041978 < baseStart_4041978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042029 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4042029 : Nat := 118140960795 + 4042029 * 2 ^ 59
def prefixEnd_4042029 : Nat := 4983230072969 + 3 ^ 40 * 4042029 * 2
def baseEnd_4042029 : Nat := 1383669130941514184432369

theorem tailTrace_4042029 : CollatzResearch.WordTrace tailWord_4042029 prefixEnd_4042029 1383669130941514184432369 := by
  unfold tailWord_4042029
  simp only [CollatzResearch.WordTrace]
  refine ⟨147424909073426731438841141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98283272715617820959227427 147424909073426731438841141)
  ·
    refine ⟨13821085225633756072391357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147424909073426731438841141 13821085225633756072391357)
    ·
      refine ⟨5182906959612658527146759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13821085225633756072391357 5182906959612658527146759)
      ·
        refine ⟨7774360439418987790720139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182906959612658527146759 7774360439418987790720139)
        ·
          refine ⟨11661540659128481686080209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774360439418987790720139 11661540659128481686080209)
          ·
            refine ⟨8746155494346361264560157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11661540659128481686080209 8746155494346361264560157)
            ·
              refine ⟨3279808310379885474210059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8746155494346361264560157 3279808310379885474210059)
              ·
                refine ⟨4919712465569828211315089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279808310379885474210059 4919712465569828211315089)
                ·
                  refine ⟨3689784349177371158486317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919712465569828211315089 3689784349177371158486317)
                  ·
                    refine ⟨1383669130941514184432369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689784349177371158486317 1383669130941514184432369)
                    ·
                      rfl

theorem cell22_4042029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4042029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042029 prefixEnd_4042029 := by exact prefixLift 4042029
  have htrace : WordTrace (prefixWord ++ tailWord_4042029) baseStart_4042029 baseEnd_4042029 := by
    simpa [prefixWord, tailWord_4042029, baseEnd_4042029] using wordTrace_append hprefix tailTrace_4042029
  have hstable : (prefixWord ++ tailWord_4042029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042029).length < 2 ^ (prefixWord ++ tailWord_4042029).sum := by decide
  have hdescent : baseEnd_4042029 < baseStart_4042029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042087 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 5]
def baseStart_4042087 : Nat := 118140960795 + 4042087 * 2 ^ 59
def prefixEnd_4042087 : Nat := 4983230072969 + 3 ^ 40 * 4042087 * 2
def baseEnd_4042087 : Nat := 461229661842273788827397

theorem tailTrace_4042087 : CollatzResearch.WordTrace tailWord_4042087 prefixEnd_4042087 461229661842273788827397 := by
  unfold tailWord_4042087
  simp only [CollatzResearch.WordTrace]
  refine ⟨147427024507216607344452515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98284683004811071562968343 147427024507216607344452515)
  ·
    refine ⟨221140536760824911016678773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147427024507216607344452515 221140536760824911016678773)
    ·
      refine ⟨20731925321327335407813635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221140536760824911016678773 20731925321327335407813635)
      ·
        refine ⟨31097887981991003111720453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20731925321327335407813635 31097887981991003111720453)
        ·
          refine ⟨5830853996623313083447585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31097887981991003111720453 5830853996623313083447585)
          ·
            refine ⟨4373140497467484812585689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5830853996623313083447585 4373140497467484812585689)
            ·
              refine ⟨3279855373100613609439267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373140497467484812585689 3279855373100613609439267)
              ·
                refine ⟨4919783059650920414158901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279855373100613609439267 4919783059650920414158901)
                ·
                  refine ⟨461229661842273788827397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919783059650920414158901 461229661842273788827397)
                  ·
                    rfl

theorem cell22_4042087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 5].length) (baseStart_4042087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042087 prefixEnd_4042087 := by exact prefixLift 4042087
  have htrace : WordTrace (prefixWord ++ tailWord_4042087) baseStart_4042087 baseEnd_4042087 := by
    simpa [prefixWord, tailWord_4042087, baseEnd_4042087] using wordTrace_append hprefix tailTrace_4042087
  have hstable : (prefixWord ++ tailWord_4042087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042087).length < 2 ^ (prefixWord ++ tailWord_4042087).sum := by decide
  have hdescent : baseEnd_4042087 < baseStart_4042087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042132 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 4]
def baseStart_4042132 : Nat := 118140960795 + 4042132 * 2 ^ 59
def prefixEnd_4042132 : Nat := 4983230072969 + 3 ^ 40 * 4042132 * 2
def baseEnd_4042132 : Nat := 461234796648818749702351

theorem tailTrace_4042132 : CollatzResearch.WordTrace tailWord_4042132 prefixEnd_4042132 461234796648818749702351 := by
  unfold tailWord_4042132
  simp only [CollatzResearch.WordTrace]
  refine ⟨73714332896026790014920325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98285777194702386686560433 73714332896026790014920325)
  ·
    refine ⟨13821437418005023127797561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73714332896026790014920325 13821437418005023127797561)
    ·
      refine ⟨10366078063503767345848171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13821437418005023127797561 10366078063503767345848171)
      ·
        refine ⟨15549117095255651018772257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10366078063503767345848171 15549117095255651018772257)
        ·
          refine ⟨11661837821441738264079193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15549117095255651018772257 11661837821441738264079193)
          ·
            refine ⟨8746378366081303698059395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11661837821441738264079193 8746378366081303698059395)
            ·
              refine ⟨13119567549121955547089093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746378366081303698059395 13119567549121955547089093)
              ·
                refine ⟨2459918915460366665079205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13119567549121955547089093 2459918915460366665079205)
                ·
                  refine ⟨461234796648818749702351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459918915460366665079205 461234796648818749702351)
                  ·
                    rfl

theorem cell22_4042132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_4042132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042132 prefixEnd_4042132 := by exact prefixLift 4042132
  have htrace : WordTrace (prefixWord ++ tailWord_4042132) baseStart_4042132 baseEnd_4042132 := by
    simpa [prefixWord, tailWord_4042132, baseEnd_4042132] using wordTrace_append hprefix tailTrace_4042132
  have hstable : (prefixWord ++ tailWord_4042132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042132).length < 2 ^ (prefixWord ++ tailWord_4042132).sum := by decide
  have hdescent : baseEnd_4042132 < baseStart_4042132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042143 : List Nat := [1, 1, 2, 5, 1, 2, 3, 7]
def baseStart_4042143 : Nat := 118140960795 + 4042143 * 2 ^ 59
def prefixEnd_4042143 : Nat := 4983230072969 + 3 ^ 40 * 4042143 * 2
def baseEnd_4042143 : Nat := 153745350607917320786891

theorem tailTrace_4042143 : CollatzResearch.WordTrace tailWord_4042143 prefixEnd_4042143 153745350607917320786891 := by
  unfold tailWord_4042143
  simp only [CollatzResearch.WordTrace]
  refine ⟨147429066995013728908491083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98286044663342485938994055 147429066995013728908491083)
  ·
    refine ⟨221143600492520593362736625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147429066995013728908491083 221143600492520593362736625)
    ·
      refine ⟨165857700369390445022052469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221143600492520593362736625 165857700369390445022052469)
      ·
        refine ⟨15549159409630354220817419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165857700369390445022052469 15549159409630354220817419)
        ·
          refine ⟨23323739114445531331226129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15549159409630354220817419 23323739114445531331226129)
          ·
            refine ⟨17492804335834148498419597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23323739114445531331226129 17492804335834148498419597)
            ·
              refine ⟨6559801625937805686907349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17492804335834148498419597 6559801625937805686907349)
              ·
                refine ⟨153745350607917320786891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6559801625937805686907349 153745350607917320786891)
                ·
                  rfl

theorem cell22_4042143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 7].length) (baseStart_4042143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042143 prefixEnd_4042143 := by exact prefixLift 4042143
  have htrace : WordTrace (prefixWord ++ tailWord_4042143) baseStart_4042143 baseEnd_4042143 := by
    simpa [prefixWord, tailWord_4042143, baseEnd_4042143] using wordTrace_append hprefix tailTrace_4042143
  have hstable : (prefixWord ++ tailWord_4042143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042143).length < 2 ^ (prefixWord ++ tailWord_4042143).sum := by decide
  have hdescent : baseEnd_4042143 < baseStart_4042143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042226 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_4042226 : Nat := 118140960795 + 4042226 * 2 ^ 59
def prefixEnd_4042226 : Nat := 4983230072969 + 3 ^ 40 * 4042226 * 2
def baseEnd_4042226 : Nat := 1383736568067471337256765

theorem tailTrace_4042226 : CollatzResearch.WordTrace tailWord_4042226 prefixEnd_4042226 1383736568067471337256765 := by
  unfold tailWord_4042226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36858023563428258520940633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98288062835808689389175021 36858023563428258520940633)
  ·
    refine ⟨27643517672571193890705475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36858023563428258520940633 27643517672571193890705475)
    ·
      refine ⟨41465276508856790836058213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27643517672571193890705475 41465276508856790836058213)
      ·
        refine ⟨7774739345410648281760915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41465276508856790836058213 7774739345410648281760915)
        ·
          refine ⟨11662109018115972422641373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774739345410648281760915 11662109018115972422641373)
          ·
            refine ⟨4373290881793489658490515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11662109018115972422641373 4373290881793489658490515)
            ·
              refine ⟨6559936322690234487735773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373290881793489658490515 6559936322690234487735773)
              ·
                refine ⟨2459976121008837932900915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6559936322690234487735773 2459976121008837932900915)
                ·
                  refine ⟨3689964181513256899351373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459976121008837932900915 3689964181513256899351373)
                  ·
                    refine ⟨1383736568067471337256765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689964181513256899351373 1383736568067471337256765)
                    ·
                      rfl

theorem cell22_4042226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_4042226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042226 prefixEnd_4042226 := by exact prefixLift 4042226
  have htrace : WordTrace (prefixWord ++ tailWord_4042226) baseStart_4042226 baseEnd_4042226 := by
    simpa [prefixWord, tailWord_4042226, baseEnd_4042226] using wordTrace_append hprefix tailTrace_4042226
  have hstable : (prefixWord ++ tailWord_4042226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042226).length < 2 ^ (prefixWord ++ tailWord_4042226).sum := by decide
  have hdescent : baseEnd_4042226 < baseStart_4042226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042250 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_4042250 : Nat := 118140960795 + 4042250 * 2 ^ 59
def prefixEnd_4042250 : Nat := 4983230072969 + 3 ^ 40 * 4042250 * 2
def baseEnd_4042250 : Nat := 461248261252647758218897

theorem tailTrace_4042250 : CollatzResearch.WordTrace tailWord_4042250 prefixEnd_4042250 461248261252647758218897 := by
  unfold tailWord_4042250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36858242401406521545659051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98288646403750724121757469 36858242401406521545659051)
  ·
    refine ⟨55287363602109782318488577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36858242401406521545659051 55287363602109782318488577)
    ·
      refine ⟨41465522701582336738866433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55287363602109782318488577 41465522701582336738866433)
      ·
        refine ⟨31099142026186752554149825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41465522701582336738866433 31099142026186752554149825)
        ·
          refine ⟨23324356519640064415612369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31099142026186752554149825 23324356519640064415612369)
          ·
            refine ⟨17493267389730048311709277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23324356519640064415612369 17493267389730048311709277)
            ·
              refine ⟨6559975271148768116890979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17493267389730048311709277 6559975271148768116890979)
              ·
                refine ⟨9839962906723152175336469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559975271148768116890979 9839962906723152175336469)
                ·
                  refine ⟨461248261252647758218897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9839962906723152175336469 461248261252647758218897)
                  ·
                    rfl

theorem cell22_4042250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_4042250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042250 prefixEnd_4042250 := by exact prefixLift 4042250
  have htrace : WordTrace (prefixWord ++ tailWord_4042250) baseStart_4042250 baseEnd_4042250 := by
    simpa [prefixWord, tailWord_4042250, baseEnd_4042250] using wordTrace_append hprefix tailTrace_4042250
  have hstable : (prefixWord ++ tailWord_4042250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042250).length < 2 ^ (prefixWord ++ tailWord_4042250).sum := by decide
  have hdescent : baseEnd_4042250 < baseStart_4042250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042301 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 4]
def baseStart_4042301 : Nat := 118140960795 + 4042301 * 2 ^ 59
def prefixEnd_4042301 : Nat := 4983230072969 + 3 ^ 40 * 4042301 * 2
def baseEnd_4042301 : Nat := 461254080700065380543845

theorem tailTrace_4042301 : CollatzResearch.WordTrace tailWord_4042301 prefixEnd_4042301 461254080700065380543845 := by
  unfold tailWord_4042301
  simp only [CollatzResearch.WordTrace]
  refine ⟨147434829728441321892742757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98289886485627547928495171 147434829728441321892742757)
  ·
    refine ⟨27644030574082747854889267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147434829728441321892742757 27644030574082747854889267)
    ·
      refine ⟨41466045861124121782333901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27644030574082747854889267 41466045861124121782333901)
      ·
        refine ⟨15549767197921545668375213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41466045861124121782333901 15549767197921545668375213)
        ·
          refine ⟨5831162699220579625640705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15549767197921545668375213 5831162699220579625640705)
          ·
            refine ⟨4373372024415434719230529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5831162699220579625640705 4373372024415434719230529)
            ·
              refine ⟨3280029018311576039422897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373372024415434719230529 3280029018311576039422897)
              ·
                refine ⟨2460021763733682029567173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280029018311576039422897 2460021763733682029567173)
                ·
                  refine ⟨461254080700065380543845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460021763733682029567173 461254080700065380543845)
                  ·
                    rfl

theorem cell22_4042301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_4042301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042301 prefixEnd_4042301 := by exact prefixLift 4042301
  have htrace : WordTrace (prefixWord ++ tailWord_4042301) baseStart_4042301 baseEnd_4042301 := by
    simpa [prefixWord, tailWord_4042301, baseEnd_4042301] using wordTrace_append hprefix tailTrace_4042301
  have hstable : (prefixWord ++ tailWord_4042301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042301).length < 2 ^ (prefixWord ++ tailWord_4042301).sum := by decide
  have hdescent : baseEnd_4042301 < baseStart_4042301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042327 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 3, 3]
def baseStart_4042327 : Nat := 118140960795 + 4042327 * 2 ^ 59
def prefixEnd_4042327 : Nat := 4983230072969 + 3 ^ 40 * 4042327 * 2
def baseEnd_4042327 : Nat := 1383771142431540740481455

theorem tailTrace_4042327 : CollatzResearch.WordTrace tailWord_4042327 prefixEnd_4042327 1383771142431540740481455 := by
  unfold tailWord_4042327
  simp only [CollatzResearch.WordTrace]
  refine ⟨147435778026347128333189235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98290518684231418888792823 147435778026347128333189235)
  ·
    refine ⟨221153667039520692499783853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147435778026347128333189235 221153667039520692499783853)
    ·
      refine ⟨82932625139820259687418945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221153667039520692499783853 82932625139820259687418945)
      ·
        refine ⟨62199468854865194765564209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82932625139820259687418945 62199468854865194765564209)
        ·
          refine ⟨46649601641148896074173157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62199468854865194765564209 46649601641148896074173157)
          ·
            refine ⟨8746800307715418013907467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46649601641148896074173157 8746800307715418013907467)
            ·
              refine ⟨13120200461573127020861201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746800307715418013907467 13120200461573127020861201)
              ·
                refine ⟨9840150346179845265645901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13120200461573127020861201 9840150346179845265645901)
                ·
                  refine ⟨3690056379817441974617213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9840150346179845265645901 3690056379817441974617213)
                  ·
                    refine ⟨1383771142431540740481455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690056379817441974617213 1383771142431540740481455)
                    ·
                      rfl

theorem cell22_4042327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_4042327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042327 prefixEnd_4042327 := by exact prefixLift 4042327
  have htrace : WordTrace (prefixWord ++ tailWord_4042327) baseStart_4042327 baseEnd_4042327 := by
    simpa [prefixWord, tailWord_4042327, baseEnd_4042327] using wordTrace_append hprefix tailTrace_4042327
  have hstable : (prefixWord ++ tailWord_4042327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042327).length < 2 ^ (prefixWord ++ tailWord_4042327).sum := by decide
  have hdescent : baseEnd_4042327 < baseStart_4042327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042357 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 7]
def baseStart_4042357 : Nat := 118140960795 + 4042357 * 2 ^ 59
def prefixEnd_4042357 : Nat := 4983230072969 + 3 ^ 40 * 4042357 * 2
def baseEnd_4042357 : Nat := 461260470681543554077121

theorem tailTrace_4042357 : CollatzResearch.WordTrace tailWord_4042357 prefixEnd_4042357 461260470681543554077121 := by
  unfold tailWord_4042357
  simp only [CollatzResearch.WordTrace]
  refine ⟨147436872216238443456781325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98291248144158962304520883 147436872216238443456781325)
  ·
    refine ⟨55288827081089416296292997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147436872216238443456781325 55288827081089416296292997)
    ·
      refine ⟨10366655077704265555554937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55288827081089416296292997 10366655077704265555554937)
      ·
        refine ⟨7774991308278199166666203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10366655077704265555554937 7774991308278199166666203)
        ·
          refine ⟨11662486962417298749999305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774991308278199166666203 11662486962417298749999305)
          ·
            refine ⟨8746865221812974062499479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11662486962417298749999305 8746865221812974062499479)
            ·
              refine ⟨13120297832719461093749219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746865221812974062499479 13120297832719461093749219)
              ·
                refine ⟨19680446749079191640623829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120297832719461093749219 19680446749079191640623829)
                ·
                  refine ⟨461260470681543554077121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19680446749079191640623829 461260470681543554077121)
                  ·
                    rfl

theorem cell22_4042357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_4042357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042357 prefixEnd_4042357 := by exact prefixLift 4042357
  have htrace : WordTrace (prefixWord ++ tailWord_4042357) baseStart_4042357 baseEnd_4042357 := by
    simpa [prefixWord, tailWord_4042357, baseEnd_4042357] using wordTrace_append hprefix tailTrace_4042357
  have hstable : (prefixWord ++ tailWord_4042357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042357).length < 2 ^ (prefixWord ++ tailWord_4042357).sum := by decide
  have hdescent : baseEnd_4042357 < baseStart_4042357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042419 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 4]
def baseStart_4042419 : Nat := 118140960795 + 4042419 * 2 ^ 59
def prefixEnd_4042419 : Nat := 4983230072969 + 3 ^ 40 * 4042419 * 2
def baseEnd_4042419 : Nat := 461267545303894389060391

theorem tailTrace_4042419 : CollatzResearch.WordTrace tailWord_4042419 prefixEnd_4042419 461267545303894389060391 := by
  unfold tailWord_4042419
  simp only [CollatzResearch.WordTrace]
  refine ⟨147439133542013828045538311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98292755694675885363692207 147439133542013828045538311)
  ·
    refine ⟨221158700313020742068307467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147439133542013828045538311 221158700313020742068307467)
    ·
      refine ⟨331738050469531113102461201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221158700313020742068307467 331738050469531113102461201)
      ·
        refine ⟨248803537852148334826845901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331738050469531113102461201 248803537852148334826845901)
        ·
          refine ⟨93301326694555625560067213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248803537852148334826845901 93301326694555625560067213)
          ·
            refine ⟨34987997510458359585025205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93301326694555625560067213 34987997510458359585025205)
            ·
              refine ⟨3280124766605471211096113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34987997510458359585025205 3280124766605471211096113)
              ·
                refine ⟨2460093574954103408322085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280124766605471211096113 2460093574954103408322085)
                ·
                  refine ⟨461267545303894389060391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460093574954103408322085 461267545303894389060391)
                  ·
                    rfl

theorem cell22_4042419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 4].length) (baseStart_4042419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042419 prefixEnd_4042419 := by exact prefixLift 4042419
  have htrace : WordTrace (prefixWord ++ tailWord_4042419) baseStart_4042419 baseEnd_4042419 := by
    simpa [prefixWord, tailWord_4042419, baseEnd_4042419] using wordTrace_append hprefix tailTrace_4042419
  have hstable : (prefixWord ++ tailWord_4042419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042419).length < 2 ^ (prefixWord ++ tailWord_4042419).sum := by decide
  have hdescent : baseEnd_4042419 < baseStart_4042419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042438 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4042438 : Nat := 118140960795 + 4042438 * 2 ^ 59
def prefixEnd_4042438 : Nat := 4983230072969 + 3 ^ 40 * 4042438 * 2
def baseEnd_4042438 : Nat := 1383809139999973450956115

theorem tailTrace_4042438 : CollatzResearch.WordTrace tailWord_4042438 prefixEnd_4042438 1383809139999973450956115 := by
  unfold tailWord_4042438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607494579029531071577499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98293217685963329526986645 4607494579029531071577499)
  ·
    refine ⟨6911241868544296607366249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607494579029531071577499 6911241868544296607366249)
    ·
      refine ⟨5183431401408222455524687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911241868544296607366249 5183431401408222455524687)
      ·
        refine ⟨7775147102112333683287031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183431401408222455524687 7775147102112333683287031)
        ·
          refine ⟨11662720653168500524930547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775147102112333683287031 11662720653168500524930547)
          ·
            refine ⟨17494080979752750787395821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11662720653168500524930547 17494080979752750787395821)
            ·
              refine ⟨6560280367407281545273433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17494080979752750787395821 6560280367407281545273433)
              ·
                refine ⟨4920210275555461158955075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560280367407281545273433 4920210275555461158955075)
                ·
                  refine ⟨7380315413333191738432613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920210275555461158955075 7380315413333191738432613)
                  ·
                    refine ⟨1383809139999973450956115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7380315413333191738432613 1383809139999973450956115)
                    ·
                      rfl

theorem cell22_4042438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4042438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042438 prefixEnd_4042438 := by exact prefixLift 4042438
  have htrace : WordTrace (prefixWord ++ tailWord_4042438) baseStart_4042438 baseEnd_4042438 := by
    simpa [prefixWord, tailWord_4042438, baseEnd_4042438] using wordTrace_append hprefix tailTrace_4042438
  have hstable : (prefixWord ++ tailWord_4042438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042438).length < 2 ^ (prefixWord ++ tailWord_4042438).sum := by decide
  have hdescent : baseEnd_4042438 < baseStart_4042438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042475 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 7]
def baseStart_4042475 : Nat := 118140960795 + 4042475 * 2 ^ 59
def prefixEnd_4042475 : Nat := 4983230072969 + 3 ^ 40 * 4042475 * 2
def baseEnd_4042475 : Nat := 461273935285372562593667

theorem tailTrace_4042475 : CollatzResearch.WordTrace tailWord_4042475 prefixEnd_4042475 461273935285372562593667 := by
  unfold tailWord_4042475
  simp only [CollatzResearch.WordTrace]
  refine ⟨147441176029810949609576879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98294117353207299739717919 147441176029810949609576879)
  ·
    refine ⟨221161764044716424414365319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147441176029810949609576879 221161764044716424414365319)
    ·
      refine ⟨331742646067074636621547979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221161764044716424414365319 331742646067074636621547979)
      ·
        refine ⟨497613969100611954932321969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331742646067074636621547979 497613969100611954932321969)
        ·
          refine ⟨373210476825458966199241477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497613969100611954932321969 373210476825458966199241477)
          ·
            refine ⟨69976964404773556162357777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373210476825458966199241477 69976964404773556162357777)
            ·
              refine ⟨52482723303580167121768333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69976964404773556162357777 52482723303580167121768333)
              ·
                refine ⟨19681021238842562670663125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52482723303580167121768333 19681021238842562670663125)
                ·
                  refine ⟨461273935285372562593667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19681021238842562670663125 461273935285372562593667)
                  ·
                    rfl

theorem cell22_4042475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_4042475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042475 prefixEnd_4042475 := by exact prefixLift 4042475
  have htrace : WordTrace (prefixWord ++ tailWord_4042475) baseStart_4042475 baseEnd_4042475 := by
    simpa [prefixWord, tailWord_4042475, baseEnd_4042475] using wordTrace_append hprefix tailTrace_4042475
  have hstable : (prefixWord ++ tailWord_4042475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042475).length < 2 ^ (prefixWord ++ tailWord_4042475).sum := by decide
  have hdescent : baseEnd_4042475 < baseStart_4042475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042477 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_4042477 : Nat := 118140960795 + 4042477 * 2 ^ 59
def prefixEnd_4042477 : Nat := 4983230072969 + 3 ^ 40 * 4042477 * 2
def baseEnd_4042477 : Nat := 1383822490496990349230995

theorem tailTrace_4042477 : CollatzResearch.WordTrace tailWord_4042477 prefixEnd_4042477 1383822490496990349230995 := by
  unfold tailWord_4042477
  simp only [CollatzResearch.WordTrace]
  refine ⟨147441248975803703951149685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98294165983869135967433123 147441248975803703951149685)
  ·
    refine ⟨13822617091481597245420283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147441248975803703951149685 13822617091481597245420283)
    ·
      refine ⟨20733925637222395868130425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13822617091481597245420283 20733925637222395868130425)
      ·
        refine ⟨15550444227916796901097819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20733925637222395868130425 15550444227916796901097819)
        ·
          refine ⟨23325666341875195351646729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15550444227916796901097819 23325666341875195351646729)
          ·
            refine ⟨17494249756406396513735047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23325666341875195351646729 17494249756406396513735047)
            ·
              refine ⟨26241374634609594770602571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17494249756406396513735047 26241374634609594770602571)
              ·
                refine ⟨39362061951914392155903857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26241374634609594770602571 39362061951914392155903857)
                ·
                  refine ⟨29521546463935794116927893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39362061951914392155903857 29521546463935794116927893)
                  ·
                    refine ⟨1383822490496990349230995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29521546463935794116927893 1383822490496990349230995)
                    ·
                      rfl

theorem cell22_4042477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_4042477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042477 prefixEnd_4042477 := by exact prefixLift 4042477
  have htrace : WordTrace (prefixWord ++ tailWord_4042477) baseStart_4042477 baseEnd_4042477 := by
    simpa [prefixWord, tailWord_4042477, baseEnd_4042477] using wordTrace_append hprefix tailTrace_4042477
  have hstable : (prefixWord ++ tailWord_4042477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042477).length < 2 ^ (prefixWord ++ tailWord_4042477).sum := by decide
  have hdescent : baseEnd_4042477 < baseStart_4042477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042492 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_4042492 : Nat := 118140960795 + 4042492 * 2 ^ 59
def prefixEnd_4042492 : Nat := 4983230072969 + 3 ^ 40 * 4042492 * 2
def baseEnd_4042492 : Nat := 461275875101178436701983

theorem tailTrace_4042492 : CollatzResearch.WordTrace tailWord_4042492 prefixEnd_4042492 461275875101178436701983 := by
  unfold tailWord_4042492
  simp only [CollatzResearch.WordTrace]
  refine ⟨73720898035374680756472865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98294530713832907675297153 73720898035374680756472865)
  ·
    refine ⟨55290673526531010567354649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73720898035374680756472865 55290673526531010567354649)
    ·
      refine ⟨41468005144898257925515987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55290673526531010567354649 41468005144898257925515987)
      ·
        refine ⟨62202007717347386888273981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41468005144898257925515987 62202007717347386888273981)
        ·
          refine ⟨23325752894005270083102743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62202007717347386888273981 23325752894005270083102743)
          ·
            refine ⟨34988629341007905124654115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23325752894005270083102743 34988629341007905124654115)
            ·
              refine ⟨52482944011511857686981173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34988629341007905124654115 52482944011511857686981173)
              ·
                refine ⟨4920276001079236658154485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52482944011511857686981173 4920276001079236658154485)
                ·
                  refine ⟨461275875101178436701983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4920276001079236658154485 461275875101178436701983)
                  ·
                    rfl

theorem cell22_4042492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_4042492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042492 prefixEnd_4042492 := by exact prefixLift 4042492
  have htrace : WordTrace (prefixWord ++ tailWord_4042492) baseStart_4042492 baseEnd_4042492 := by
    simpa [prefixWord, tailWord_4042492, baseEnd_4042492] using wordTrace_append hprefix tailTrace_4042492
  have hstable : (prefixWord ++ tailWord_4042492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042492).length < 2 ^ (prefixWord ++ tailWord_4042492).sum := by decide
  have hdescent : baseEnd_4042492 < baseStart_4042492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042567 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 1, 6]
def baseStart_4042567 : Nat := 118140960795 + 4042567 * 2 ^ 59
def prefixEnd_4042567 : Nat := 4983230072969 + 3 ^ 40 * 4042567 * 2
def baseEnd_4042567 : Nat := 1383853299336260114480719

theorem tailTrace_4042567 : CollatzResearch.WordTrace tailWord_4042567 prefixEnd_4042567 1383853299336260114480719 := by
  unfold tailWord_4042567
  simp only [CollatzResearch.WordTrace]
  refine ⟨147444531545477649321925955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98296354363651766214617303 147444531545477649321925955)
  ·
    refine ⟨221166797318216473982888933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147444531545477649321925955 221166797318216473982888933)
    ·
      refine ⟨41468774497165588871791675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221166797318216473982888933 41468774497165588871791675)
      ·
        refine ⟨62203161745748383307687513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41468774497165588871791675 62203161745748383307687513)
        ·
          refine ⟨46652371309311287480765635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62203161745748383307687513 46652371309311287480765635)
          ·
            refine ⟨69978556963966931221148453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46652371309311287480765635 69978556963966931221148453)
            ·
              refine ⟨13120979430743799603965335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69978556963966931221148453 13120979430743799603965335)
              ·
                refine ⟨19681469146115699405948003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120979430743799603965335 19681469146115699405948003)
                ·
                  refine ⟨29522203719173549108922005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19681469146115699405948003 29522203719173549108922005)
                  ·
                    refine ⟨1383853299336260114480719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29522203719173549108922005 1383853299336260114480719)
                    ·
                      rfl

theorem cell22_4042567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_4042567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042567 prefixEnd_4042567 := by exact prefixLift 4042567
  have htrace : WordTrace (prefixWord ++ tailWord_4042567) baseStart_4042567 baseEnd_4042567 := by
    simpa [prefixWord, tailWord_4042567, baseEnd_4042567] using wordTrace_append hprefix tailTrace_4042567
  have hstable : (prefixWord ++ tailWord_4042567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042567).length < 2 ^ (prefixWord ++ tailWord_4042567).sum := by decide
  have hdescent : baseEnd_4042567 < baseStart_4042567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042588 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 6]
def baseStart_4042588 : Nat := 118140960795 + 4042588 * 2 ^ 59
def prefixEnd_4042588 : Nat := 4983230072969 + 3 ^ 40 * 4042588 * 2
def baseEnd_4042588 : Nat := 461286829355141019901885

theorem tailTrace_4042588 : CollatzResearch.WordTrace tailWord_4042588 prefixEnd_4042588 461286829355141019901885 := by
  unfold tailWord_4042588
  simp only [CollatzResearch.WordTrace]
  refine ⟨73722648739200784954220209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98296864985601046605626945 73722648739200784954220209)
  ·
    refine ⟨55291986554400588715665157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73722648739200784954220209 55291986554400588715665157)
    ·
      refine ⟨10367247478950110384187217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55291986554400588715665157 10367247478950110384187217)
      ·
        refine ⟨7775435609212582788140413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10367247478950110384187217 7775435609212582788140413)
        ·
          refine ⟨2915788353454718545552655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7775435609212582788140413 2915788353454718545552655)
          ·
            refine ⟨4373682530182077818328983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915788353454718545552655 4373682530182077818328983)
            ·
              refine ⟨6560523795273116727493475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373682530182077818328983 6560523795273116727493475)
              ·
                refine ⟨9840785692909675091240213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560523795273116727493475 9840785692909675091240213)
                ·
                  refine ⟨461286829355141019901885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9840785692909675091240213 461286829355141019901885)
                  ·
                    rfl

theorem cell22_4042588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_4042588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042588 prefixEnd_4042588 := by exact prefixLift 4042588
  have htrace : WordTrace (prefixWord ++ tailWord_4042588) baseStart_4042588 baseEnd_4042588 := by
    simpa [prefixWord, tailWord_4042588, baseEnd_4042588] using wordTrace_append hprefix tailTrace_4042588
  have hstable : (prefixWord ++ tailWord_4042588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042588).length < 2 ^ (prefixWord ++ tailWord_4042588).sum := by decide
  have hdescent : baseEnd_4042588 < baseStart_4042588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042719 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 1, 6]
def baseStart_4042719 : Nat := 118140960795 + 4042719 * 2 ^ 59
def prefixEnd_4042719 : Nat := 4983230072969 + 3 ^ 40 * 4042719 * 2
def baseEnd_4042719 : Nat := 1383905332042582384680253

theorem tailTrace_4042719 : CollatzResearch.WordTrace tailWord_4042719 prefixEnd_4042719 1383905332042582384680253 := by
  unfold tailWord_4042719
  simp only [CollatzResearch.WordTrace]
  refine ⟨147450075440926979281459211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98300050293951319520972807 147450075440926979281459211)
  ·
    refine ⟨221175113161390468922188817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147450075440926979281459211 221175113161390468922188817)
    ·
      refine ⟨165881334871042851691641613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221175113161390468922188817 165881334871042851691641613)
      ·
        refine ⟨62205500576641069384365605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165881334871042851691641613 62205500576641069384365605)
        ·
          refine ⟨11663531358120200509568551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62205500576641069384365605 11663531358120200509568551)
          ·
            refine ⟨17495297037180300764352827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663531358120200509568551 17495297037180300764352827)
            ·
              refine ⟨26242945555770451146529241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495297037180300764352827 26242945555770451146529241)
              ·
                refine ⟨19682209166827838359896931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26242945555770451146529241 19682209166827838359896931)
                ·
                  refine ⟨29523313750241757539845397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19682209166827838359896931 29523313750241757539845397)
                  ·
                    refine ⟨1383905332042582384680253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29523313750241757539845397 1383905332042582384680253)
                    ·
                      rfl

theorem cell22_4042719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_4042719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042719 prefixEnd_4042719 := by exact prefixLift 4042719
  have htrace : WordTrace (prefixWord ++ tailWord_4042719) baseStart_4042719 baseEnd_4042719 := by
    simpa [prefixWord, tailWord_4042719, baseEnd_4042719] using wordTrace_append hprefix tailTrace_4042719
  have hstable : (prefixWord ++ tailWord_4042719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042719).length < 2 ^ (prefixWord ++ tailWord_4042719).sum := by decide
  have hdescent : baseEnd_4042719 < baseStart_4042719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042721 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_4042721 : Nat := 118140960795 + 4042721 * 2 ^ 59
def prefixEnd_4042721 : Nat := 4983230072969 + 3 ^ 40 * 4042721 * 2
def baseEnd_4042721 : Nat := 1383906016683455046130247

theorem tailTrace_4042721 : CollatzResearch.WordTrace tailWord_4042721 prefixEnd_4042721 1383906016683455046130247 := by
  unfold tailWord_4042721
  simp only [CollatzResearch.WordTrace]
  refine ⟨147450148386919733623032017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98300098924613155748688011 147450148386919733623032017)
  ·
    refine ⟨110587611290189800217274013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147450148386919733623032017 110587611290189800217274013)
    ·
      refine ⟨41470354233821175081477755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110587611290189800217274013 41470354233821175081477755)
      ·
        refine ⟨62205531350731762622216633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41470354233821175081477755 62205531350731762622216633)
        ·
          refine ⟨46654148513048821966662475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62205531350731762622216633 46654148513048821966662475)
          ·
            refine ⟨69981222769573232949993713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46654148513048821966662475 69981222769573232949993713)
            ·
              refine ⟨52485917077179924712495285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69981222769573232949993713 52485917077179924712495285)
              ·
                refine ⟨4920554725985617941796433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52485917077179924712495285 4920554725985617941796433)
                ·
                  refine ⟨3690416044489213456347325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920554725985617941796433 3690416044489213456347325)
                  ·
                    refine ⟨1383906016683455046130247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690416044489213456347325 1383906016683455046130247)
                    ·
                      rfl

theorem cell22_4042721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_4042721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042721 prefixEnd_4042721 := by exact prefixLift 4042721
  have htrace : WordTrace (prefixWord ++ tailWord_4042721) baseStart_4042721 baseEnd_4042721 := by
    simpa [prefixWord, tailWord_4042721, baseEnd_4042721] using wordTrace_append hprefix tailTrace_4042721
  have hstable : (prefixWord ++ tailWord_4042721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042721).length < 2 ^ (prefixWord ++ tailWord_4042721).sum := by decide
  have hdescent : baseEnd_4042721 < baseStart_4042721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042764 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_4042764 : Nat := 118140960795 + 4042764 * 2 ^ 59
def prefixEnd_4042764 : Nat := 4983230072969 + 3 ^ 40 * 4042764 * 2
def baseEnd_4042764 : Nat := 1383920736462217267305115

theorem tailTrace_4042764 : CollatzResearch.WordTrace tailWord_4042764 prefixEnd_4042764 1383920736462217267305115 := by
  unfold tailWord_4042764
  simp only [CollatzResearch.WordTrace]
  refine ⟨73725858362881975983423673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98301144483842634644564897 73725858362881975983423673)
  ·
    refine ⟨55294393772161481987567755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73725858362881975983423673 55294393772161481987567755)
    ·
      refine ⟨82941590658242222981351633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55294393772161481987567755 82941590658242222981351633)
      ·
        refine ⟨62206192993681667236013725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82941590658242222981351633 62206192993681667236013725)
        ·
          refine ⟨23327322372630625213505147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62206192993681667236013725 23327322372630625213505147)
          ·
            refine ⟨34990983558945937820257721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23327322372630625213505147 34990983558945937820257721)
            ·
              refine ⟨26243237669209453365193291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34990983558945937820257721 26243237669209453365193291)
              ·
                refine ⟨39364856503814180047789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26243237669209453365193291 39364856503814180047789937)
                ·
                  refine ⟨29523642377860635035842453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39364856503814180047789937 29523642377860635035842453)
                  ·
                    refine ⟨1383920736462217267305115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29523642377860635035842453 1383920736462217267305115)
                    ·
                      rfl

theorem cell22_4042764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_4042764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042764 prefixEnd_4042764 := by exact prefixLift 4042764
  have htrace : WordTrace (prefixWord ++ tailWord_4042764) baseStart_4042764 baseEnd_4042764 := by
    simpa [prefixWord, tailWord_4042764, baseEnd_4042764] using wordTrace_append hprefix tailTrace_4042764
  have hstable : (prefixWord ++ tailWord_4042764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042764).length < 2 ^ (prefixWord ++ tailWord_4042764).sum := by decide
  have hdescent : baseEnd_4042764 < baseStart_4042764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042772 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4042772 : Nat := 118140960795 + 4042772 * 2 ^ 59
def prefixEnd_4042772 : Nat := 4983230072969 + 3 ^ 40 * 4042772 * 2
def baseEnd_4042772 : Nat := 1383923475025707913105091

theorem tailTrace_4042772 : CollatzResearch.WordTrace tailWord_4042772 prefixEnd_4042772 1383923475025707913105091 := by
  unfold tailWord_4042772
  simp only [CollatzResearch.WordTrace]
  refine ⟨73726004254867484666569285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98301339006489979555425713 73726004254867484666569285)
  ·
    refine ⟨13823625797787653374981741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73726004254867484666569285 13823625797787653374981741)
    ·
      refine ⟨5183859674170370015618153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13823625797787653374981741 5183859674170370015618153)
      ·
        refine ⟨3887894755627777511713615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5183859674170370015618153 3887894755627777511713615)
        ·
          refine ⟨5831842133441666267570423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887894755627777511713615 5831842133441666267570423)
          ·
            refine ⟨8747763200162499401355635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831842133441666267570423 8747763200162499401355635)
            ·
              refine ⟨13121644800243749102033453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747763200162499401355635 13121644800243749102033453)
              ·
                refine ⟨4920616800091405913262545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13121644800243749102033453 4920616800091405913262545)
                ·
                  refine ⟨3690462600068554434946909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920616800091405913262545 3690462600068554434946909)
                  ·
                    refine ⟨1383923475025707913105091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690462600068554434946909 1383923475025707913105091)
                    ·
                      rfl

theorem cell22_4042772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4042772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042772 prefixEnd_4042772 := by exact prefixLift 4042772
  have htrace : WordTrace (prefixWord ++ tailWord_4042772) baseStart_4042772 baseEnd_4042772 := by
    simpa [prefixWord, tailWord_4042772, baseEnd_4042772] using wordTrace_append hprefix tailTrace_4042772
  have hstable : (prefixWord ++ tailWord_4042772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042772).length < 2 ^ (prefixWord ++ tailWord_4042772).sum := by decide
  have hdescent : baseEnd_4042772 < baseStart_4042772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042817 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 1, 3]
def baseStart_4042817 : Nat := 118140960795 + 4042817 * 2 ^ 59
def prefixEnd_4042817 : Nat := 4983230072969 + 3 ^ 40 * 4042817 * 2
def baseEnd_4042817 : Nat := 1383938879445342795729953

theorem tailTrace_4042817 : CollatzResearch.WordTrace tailWord_4042817 prefixEnd_4042817 1383938879445342795729953 := by
  unfold tailWord_4042817
  simp only [CollatzResearch.WordTrace]
  refine ⟨147453649794571942018526705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98302433196381294679017803 147453649794571942018526705)
  ·
    refine ⟨110590237345928956513895029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147453649794571942018526705 110590237345928956513895029)
    ·
      refine ⟨10367834751180839673177659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110590237345928956513895029 10367834751180839673177659)
      ·
        refine ⟨15551752126771259509766489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10367834751180839673177659 15551752126771259509766489)
        ·
          refine ⟨11663814095078444632324867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15551752126771259509766489 11663814095078444632324867)
          ·
            refine ⟨17495721142617666948487301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663814095078444632324867 17495721142617666948487301)
            ·
              refine ⟨3280447714240812552841369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17495721142617666948487301 3280447714240812552841369)
              ·
                refine ⟨2460335785680609414631027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280447714240812552841369 2460335785680609414631027)
                ·
                  refine ⟨3690503678520914121946541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460335785680609414631027 3690503678520914121946541)
                  ·
                    refine ⟨1383938879445342795729953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690503678520914121946541 1383938879445342795729953)
                    ·
                      rfl

theorem cell22_4042817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_4042817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042817 prefixEnd_4042817 := by exact prefixLift 4042817
  have htrace : WordTrace (prefixWord ++ tailWord_4042817) baseStart_4042817 baseEnd_4042817 := by
    simpa [prefixWord, tailWord_4042817, baseEnd_4042817] using wordTrace_append hprefix tailTrace_4042817
  have hstable : (prefixWord ++ tailWord_4042817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042817).length < 2 ^ (prefixWord ++ tailWord_4042817).sum := by decide
  have hdescent : baseEnd_4042817 < baseStart_4042817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042860 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_4042860 : Nat := 118140960795 + 4042860 * 2 ^ 59
def prefixEnd_4042860 : Nat := 4983230072969 + 3 ^ 40 * 4042860 * 2
def baseEnd_4042860 : Nat := 1383953599224105016904821

theorem tailTrace_4042860 : CollatzResearch.WordTrace tailWord_4042860 prefixEnd_4042860 1383953599224105016904821 := by
  unfold tailWord_4042860
  simp only [CollatzResearch.WordTrace]
  refine ⟨73727609066708080181171017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98303478755610773574894689 73727609066708080181171017)
  ·
    refine ⟨55295706800031060135878263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73727609066708080181171017 55295706800031060135878263)
    ·
      refine ⟨82943560200046590203817395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55295706800031060135878263 82943560200046590203817395)
      ·
        refine ⟨124415340300069885305726093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82943560200046590203817395 124415340300069885305726093)
        ·
          refine ⟨46655752612526206989647285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124415340300069885305726093 46655752612526206989647285)
          ·
            refine ⟨4373976807424331905279433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46655752612526206989647285 4373976807424331905279433)
            ·
              refine ⟨3280482605568248928959575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373976807424331905279433 3280482605568248928959575)
              ·
                refine ⟨4920723908352373393439363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280482605568248928959575 4920723908352373393439363)
                ·
                  refine ⟨7381085862528560090159045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920723908352373393439363 7381085862528560090159045)
                  ·
                    refine ⟨1383953599224105016904821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7381085862528560090159045 1383953599224105016904821)
                    ·
                      rfl

theorem cell22_4042860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_4042860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042860 prefixEnd_4042860 := by exact prefixLift 4042860
  have htrace : WordTrace (prefixWord ++ tailWord_4042860) baseStart_4042860 baseEnd_4042860 := by
    simpa [prefixWord, tailWord_4042860, baseEnd_4042860] using wordTrace_append hprefix tailTrace_4042860
  have hstable : (prefixWord ++ tailWord_4042860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042860).length < 2 ^ (prefixWord ++ tailWord_4042860).sum := by decide
  have hdescent : baseEnd_4042860 < baseStart_4042860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042873 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_4042873 : Nat := 118140960795 + 4042873 * 2 ^ 59
def prefixEnd_4042873 : Nat := 4983230072969 + 3 ^ 40 * 4042873 * 2
def baseEnd_4042873 : Nat := 1383958049389777316329781

theorem tailTrace_4042873 : CollatzResearch.WordTrace tailWord_4042873 prefixEnd_4042873 1383958049389777316329781 := by
  unfold tailWord_4042873
  simp only [CollatzResearch.WordTrace]
  refine ⟨147455692282369063582565273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98303794854912709055043515 147455692282369063582565273)
  ·
    refine ⟨110591769211776797686923955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147455692282369063582565273 110591769211776797686923955)
    ·
      refine ⟨165887653817665196530385933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110591769211776797686923955 165887653817665196530385933)
      ·
        refine ⟨62207870181624448698894725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165887653817665196530385933 62207870181624448698894725)
        ·
          refine ⟨11663975659054584131042761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62207870181624448698894725 11663975659054584131042761)
          ·
            refine ⟨8747981744290938098282071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11663975659054584131042761 8747981744290938098282071)
            ·
              refine ⟨13121972616436407147423107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747981744290938098282071 13121972616436407147423107)
              ·
                refine ⟨19682958924654610721134661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13121972616436407147423107 19682958924654610721134661)
                ·
                  refine ⟨3690554798372739510212749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19682958924654610721134661 3690554798372739510212749)
                  ·
                    refine ⟨1383958049389777316329781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690554798372739510212749 1383958049389777316329781)
                    ·
                      rfl

theorem cell22_4042873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_4042873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042873 prefixEnd_4042873 := by exact prefixLift 4042873
  have htrace : WordTrace (prefixWord ++ tailWord_4042873) baseStart_4042873 baseEnd_4042873 := by
    simpa [prefixWord, tailWord_4042873, baseEnd_4042873] using wordTrace_append hprefix tailTrace_4042873
  have hstable : (prefixWord ++ tailWord_4042873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042873).length < 2 ^ (prefixWord ++ tailWord_4042873).sum := by decide
  have hdescent : baseEnd_4042873 < baseStart_4042873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042931 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 5]
def baseStart_4042931 : Nat := 118140960795 + 4042931 * 2 ^ 59
def prefixEnd_4042931 : Nat := 4983230072969 + 3 ^ 40 * 4042931 * 2
def baseEnd_4042931 : Nat := 461325967991694832793201

theorem tailTrace_4042931 : CollatzResearch.WordTrace tailWord_4042931 prefixEnd_4042931 461325967991694832793201 := by
  unfold tailWord_4042931
  simp only [CollatzResearch.WordTrace]
  refine ⟨147457807716158939488176647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98305205144105959658784431 147457807716158939488176647)
  ·
    refine ⟨221186711574238409232264971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147457807716158939488176647 221186711574238409232264971)
    ·
      refine ⟨331780067361357613848397457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221186711574238409232264971 331780067361357613848397457)
      ·
        refine ⟨248835050521018210386298093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331780067361357613848397457 248835050521018210386298093)
        ·
          refine ⟨93313143945381828894861785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248835050521018210386298093 93313143945381828894861785)
          ·
            refine ⟨69984857959036371671146339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93313143945381828894861785 69984857959036371671146339)
            ·
              refine ⟨104977286938554557506719509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69984857959036371671146339 104977286938554557506719509)
              ·
                refine ⟨4920810325244744883127477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104977286938554557506719509 4920810325244744883127477)
                ·
                  refine ⟨461325967991694832793201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4920810325244744883127477 461325967991694832793201)
                  ·
                    rfl

theorem cell22_4042931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 5].length) (baseStart_4042931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042931 prefixEnd_4042931 := by exact prefixLift 4042931
  have htrace : WordTrace (prefixWord ++ tailWord_4042931) baseStart_4042931 baseEnd_4042931 := by
    simpa [prefixWord, tailWord_4042931, baseEnd_4042931] using wordTrace_append hprefix tailTrace_4042931
  have hstable : (prefixWord ++ tailWord_4042931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042931).length < 2 ^ (prefixWord ++ tailWord_4042931).sum := by decide
  have hdescent : baseEnd_4042931 < baseStart_4042931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042935 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 3, 3]
def baseStart_4042935 : Nat := 118140960795 + 4042935 * 2 ^ 59
def prefixEnd_4042935 : Nat := 4983230072969 + 3 ^ 40 * 4042935 * 2
def baseEnd_4042935 : Nat := 1383979273256829821279591

theorem tailTrace_4042935 : CollatzResearch.WordTrace tailWord_4042935 prefixEnd_4042935 1383979273256829821279591 := by
  unfold tailWord_4042935
  simp only [CollatzResearch.WordTrace]
  refine ⟨147457953608144448171322259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98305302405429632114214839 147457953608144448171322259)
  ·
    refine ⟨221186930412216672256983389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147457953608144448171322259 221186930412216672256983389)
    ·
      refine ⟨82945098904581252096368771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221186930412216672256983389 82945098904581252096368771)
      ·
        refine ⟨124417648356871878144553157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82945098904581252096368771 124417648356871878144553157)
        ·
          refine ⟨23328309066913477152103717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124417648356871878144553157 23328309066913477152103717)
          ·
            refine ⟨4374057950046276966019447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23328309066913477152103717 4374057950046276966019447)
            ·
              refine ⟨6561086925069415449029171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374057950046276966019447 6561086925069415449029171)
              ·
                refine ⟨9841630387604123173543757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6561086925069415449029171 9841630387604123173543757)
                ·
                  refine ⟨3690611395351546190078909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9841630387604123173543757 3690611395351546190078909)
                  ·
                    refine ⟨1383979273256829821279591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690611395351546190078909 1383979273256829821279591)
                    ·
                      rfl

theorem cell22_4042935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_4042935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4042935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4042935 prefixEnd_4042935 := by exact prefixLift 4042935
  have htrace : WordTrace (prefixWord ++ tailWord_4042935) baseStart_4042935 baseEnd_4042935 := by
    simpa [prefixWord, tailWord_4042935, baseEnd_4042935] using wordTrace_append hprefix tailTrace_4042935
  have hstable : (prefixWord ++ tailWord_4042935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042935).length < 2 ^ (prefixWord ++ tailWord_4042935).sum := by decide
  have hdescent : baseEnd_4042935 < baseStart_4042935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043010 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4043010 : Nat := 118140960795 + 4043010 * 2 ^ 59
def prefixEnd_4043010 : Nat := 4983230072969 + 3 ^ 40 * 4043010 * 2
def baseEnd_4043010 : Nat := 461334982429851541884787

theorem tailTrace_4043010 : CollatzResearch.WordTrace tailWord_4043010 prefixEnd_4043010 461334982429851541884787 := by
  unfold tailWord_4043010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36865172270718183995075621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98307126055248490653534989 36865172270718183995075621)
  ·
    refine ⟨6912219800759659499076679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36865172270718183995075621 6912219800759659499076679)
    ·
      refine ⟨10368329701139489248615019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6912219800759659499076679 10368329701139489248615019)
      ·
        refine ⟨15552494551709233872922529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10368329701139489248615019 15552494551709233872922529)
        ·
          refine ⟨11664370913781925404691897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15552494551709233872922529 11664370913781925404691897)
          ·
            refine ⟨8748278185336444053518923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11664370913781925404691897 8748278185336444053518923)
            ·
              refine ⟨13122417278004666080278385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748278185336444053518923 13122417278004666080278385)
              ·
                refine ⟨9841812958503499560208789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13122417278004666080278385 9841812958503499560208789)
                ·
                  refine ⟨461334982429851541884787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9841812958503499560208789 461334982429851541884787)
                  ·
                    rfl

theorem cell22_4043010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4043010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043010 prefixEnd_4043010 := by exact prefixLift 4043010
  have htrace : WordTrace (prefixWord ++ tailWord_4043010) baseStart_4043010 baseEnd_4043010 := by
    simpa [prefixWord, tailWord_4043010, baseEnd_4043010] using wordTrace_append hprefix tailTrace_4043010
  have hstable : (prefixWord ++ tailWord_4043010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043010).length < 2 ^ (prefixWord ++ tailWord_4043010).sum := by decide
  have hdescent : baseEnd_4043010 < baseStart_4043010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043042 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4043042 : Nat := 118140960795 + 4043042 * 2 ^ 59
def prefixEnd_4043042 : Nat := 4983230072969 + 3 ^ 40 * 4043042 * 2
def baseEnd_4043042 : Nat := 1384015901543517208854263

theorem tailTrace_4043042 : CollatzResearch.WordTrace tailWord_4043042 prefixEnd_4043042 1384015901543517208854263 := by
  unfold tailWord_4043042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36865464054689201361366845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98307904145837870296978253 36865464054689201361366845)
  ·
    refine ⟨13824549020508450510512567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36865464054689201361366845 13824549020508450510512567)
    ·
      refine ⟨20736823530762675765768851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13824549020508450510512567 20736823530762675765768851)
      ·
        refine ⟨31105235296144013648653277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20736823530762675765768851 31105235296144013648653277)
        ·
          refine ⟨11664463236054005118244979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31105235296144013648653277 11664463236054005118244979)
          ·
            refine ⟨17496694854081007677367469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11664463236054005118244979 17496694854081007677367469)
            ·
              refine ⟨6561260570280377879012801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17496694854081007677367469 6561260570280377879012801)
              ·
                refine ⟨4920945427710283409259601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561260570280377879012801 4920945427710283409259601)
                ·
                  refine ⟨3690709070782712556944701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920945427710283409259601 3690709070782712556944701)
                  ·
                    refine ⟨1384015901543517208854263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690709070782712556944701 1384015901543517208854263)
                    ·
                      rfl

theorem cell22_4043042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4043042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043042 prefixEnd_4043042 := by exact prefixLift 4043042
  have htrace : WordTrace (prefixWord ++ tailWord_4043042) baseStart_4043042 baseEnd_4043042 := by
    simpa [prefixWord, tailWord_4043042, baseEnd_4043042] using wordTrace_append hprefix tailTrace_4043042
  have hstable : (prefixWord ++ tailWord_4043042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043042).length < 2 ^ (prefixWord ++ tailWord_4043042).sum := by decide
  have hdescent : baseEnd_4043042 < baseStart_4043042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043104 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 3, 3]
def baseStart_4043104 : Nat := 118140960795 + 4043104 * 2 ^ 59
def prefixEnd_4043104 : Nat := 4983230072969 + 3 ^ 40 * 4043104 * 2
def baseEnd_4043104 : Nat := 1384037125410569713804073

theorem tailTrace_4043104 : CollatzResearch.WordTrace tailWord_4043104 prefixEnd_4043104 1384037125410569713804073 := by
  unfold tailWord_4043104
  simp only [CollatzResearch.WordTrace]
  refine ⟨73732058772266095017112183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98309411696354793356149577 73732058772266095017112183)
  ·
    refine ⟨110598088158399142525668275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73732058772266095017112183 110598088158399142525668275)
    ·
      refine ⟨165897132237598713788502413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110598088158399142525668275 165897132237598713788502413)
      ·
        refine ⟨62211424589099517670688405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165897132237598713788502413 62211424589099517670688405)
        ·
          refine ⟨2916160527614039890813519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62211424589099517670688405 2916160527614039890813519)
          ·
            refine ⟨4374240791421059836220279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916160527614039890813519 4374240791421059836220279)
            ·
              refine ⟨6561361187131589754330419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374240791421059836220279 6561361187131589754330419)
              ·
                refine ⟨9842041780697384631495629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6561361187131589754330419 9842041780697384631495629)
                ·
                  refine ⟨3690765667761519236810861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9842041780697384631495629 3690765667761519236810861)
                  ·
                    refine ⟨1384037125410569713804073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690765667761519236810861 1384037125410569713804073)
                    ·
                      rfl

theorem cell22_4043104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_4043104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043104 prefixEnd_4043104 := by exact prefixLift 4043104
  have htrace : WordTrace (prefixWord ++ tailWord_4043104) baseStart_4043104 baseEnd_4043104 := by
    simpa [prefixWord, tailWord_4043104, baseEnd_4043104] using wordTrace_append hprefix tailTrace_4043104
  have hstable : (prefixWord ++ tailWord_4043104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043104).length < 2 ^ (prefixWord ++ tailWord_4043104).sum := by decide
  have hdescent : baseEnd_4043104 < baseStart_4043104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043113 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_4043113 : Nat := 118140960795 + 4043113 * 2 ^ 59
def prefixEnd_4043113 : Nat := 4983230072969 + 3 ^ 40 * 4043113 * 2
def baseEnd_4043113 : Nat := 1384040206294496690329045

theorem tailTrace_4043113 : CollatzResearch.WordTrace tailWord_4043113 prefixEnd_4043113 1384040206294496690329045 := by
  unfold tailWord_4043113
  simp only [CollatzResearch.WordTrace]
  refine ⟨147464445801499584571301993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98309630534333056380867995 147464445801499584571301993)
  ·
    refine ⟨110598334351124688428476495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147464445801499584571301993 110598334351124688428476495)
    ·
      refine ⟨165897501526687032642714743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110598334351124688428476495 165897501526687032642714743)
      ·
        refine ⟨248846252290030548964072115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165897501526687032642714743 248846252290030548964072115)
        ·
          refine ⟨373269378435045823446108173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248846252290030548964072115 373269378435045823446108173)
          ·
            refine ⟨139976016913142183792290565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373269378435045823446108173 139976016913142183792290565)
            ·
              refine ⟨26245503171214159461054481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139976016913142183792290565 26245503171214159461054481)
              ·
                refine ⟨19684127378410619595790861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26245503171214159461054481 19684127378410619595790861)
                ·
                  refine ⟨7381547766903982348421573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19684127378410619595790861 7381547766903982348421573)
                  ·
                    refine ⟨1384040206294496690329045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7381547766903982348421573 1384040206294496690329045)
                    ·
                      rfl

theorem cell22_4043113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_4043113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043113 prefixEnd_4043113 := by exact prefixLift 4043113
  have htrace : WordTrace (prefixWord ++ tailWord_4043113) baseStart_4043113 baseEnd_4043113 := by
    simpa [prefixWord, tailWord_4043113, baseEnd_4043113] using wordTrace_append hprefix tailTrace_4043113
  have hstable : (prefixWord ++ tailWord_4043113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043113).length < 2 ^ (prefixWord ++ tailWord_4043113).sum := by decide
  have hdescent : baseEnd_4043113 < baseStart_4043113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043147 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 1, 4]
def baseStart_4043147 : Nat := 118140960795 + 4043147 * 2 ^ 59
def prefixEnd_4043147 : Nat := 4983230072969 + 3 ^ 40 * 4043147 * 2
def baseEnd_4043147 : Nat := 1384051845189331934978941

theorem tailTrace_4043147 : CollatzResearch.WordTrace tailWord_4043147 prefixEnd_4043147 1384051845189331934978941 := by
  unfold tailWord_4043147
  simp only [CollatzResearch.WordTrace]
  refine ⟨147465685883376408378039695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98310457255584272252026463 147465685883376408378039695)
  ·
    refine ⟨221198528825064612567059543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147465685883376408378039695 221198528825064612567059543)
    ·
      refine ⟨331797793237596918850589315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221198528825064612567059543 331797793237596918850589315)
      ·
        refine ⟨497696689856395378275883973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331797793237596918850589315 497696689856395378275883973)
        ·
          refine ⟨93318129348074133426728245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497696689856395378275883973 93318129348074133426728245)
          ·
            refine ⟨8748574626381950008755773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93318129348074133426728245 8748574626381950008755773)
            ·
              refine ⟨3280715484893231253283415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8748574626381950008755773 3280715484893231253283415)
              ·
                refine ⟨4921073227339846879925123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280715484893231253283415 4921073227339846879925123)
                ·
                  refine ⟨7381609841009770319887685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921073227339846879925123 7381609841009770319887685)
                  ·
                    refine ⟨1384051845189331934978941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7381609841009770319887685 1384051845189331934978941)
                    ·
                      rfl

theorem cell22_4043147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 4].length) (baseStart_4043147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043147 prefixEnd_4043147 := by exact prefixLift 4043147
  have htrace : WordTrace (prefixWord ++ tailWord_4043147) baseStart_4043147 baseEnd_4043147 := by
    simpa [prefixWord, tailWord_4043147, baseEnd_4043147] using wordTrace_append hprefix tailTrace_4043147
  have hstable : (prefixWord ++ tailWord_4043147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043147).length < 2 ^ (prefixWord ++ tailWord_4043147).sum := by decide
  have hdescent : baseEnd_4043147 < baseStart_4043147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043162 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_4043162 : Nat := 118140960795 + 4043162 * 2 ^ 59
def prefixEnd_4043162 : Nat := 4983230072969 + 3 ^ 40 * 4043162 * 2
def baseEnd_4043162 : Nat := 461352326665292298617965

theorem tailTrace_4043162 : CollatzResearch.WordTrace tailWord_4043162 prefixEnd_4043162 461352326665292298617965 := by
  unfold tailWord_4043162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36866558244580516484958935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98310821985548043959890493 36866558244580516484958935)
  ·
    refine ⟨55299837366870774727438403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36866558244580516484958935 55299837366870774727438403)
    ·
      refine ⟨82949756050306162091157605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55299837366870774727438403 82949756050306162091157605)
      ·
        refine ⟨15553079259432405392092051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82949756050306162091157605 15553079259432405392092051)
        ·
          refine ⟨23329618889148608088138077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15553079259432405392092051 23329618889148608088138077)
          ·
            refine ⟨8748607083430728033051779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23329618889148608088138077 8748607083430728033051779)
            ·
              refine ⟨13122910625146092049577669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748607083430728033051779 13122910625146092049577669)
              ·
                refine ⟨2460545742214892259295813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13122910625146092049577669 2460545742214892259295813)
                ·
                  refine ⟨461352326665292298617965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460545742214892259295813 461352326665292298617965)
                  ·
                    rfl

theorem cell22_4043162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_4043162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043162 prefixEnd_4043162 := by exact prefixLift 4043162
  have htrace : WordTrace (prefixWord ++ tailWord_4043162) baseStart_4043162 baseEnd_4043162 := by
    simpa [prefixWord, tailWord_4043162, baseEnd_4043162] using wordTrace_append hprefix tailTrace_4043162
  have hstable : (prefixWord ++ tailWord_4043162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043162).length < 2 ^ (prefixWord ++ tailWord_4043162).sum := by decide
  have hdescent : baseEnd_4043162 < baseStart_4043162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043295 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 1, 5]
def baseStart_4043295 : Nat := 118140960795 + 4043295 * 2 ^ 59
def prefixEnd_4043295 : Nat := 4983230072969 + 3 ^ 40 * 4043295 * 2
def baseEnd_4043295 : Nat := 1384102508613908882278487

theorem tailTrace_4043295 : CollatzResearch.WordTrace tailWord_4043295 prefixEnd_4043295 1384102508613908882278487 := by
  unfold tailWord_4043295
  simp only [CollatzResearch.WordTrace]
  refine ⟨147471083886840229654427339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98314055924560153102951559 147471083886840229654427339)
  ·
    refine ⟨221206625830260344481641009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147471083886840229654427339 221206625830260344481641009)
    ·
      refine ⟨165904969372695258361230757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221206625830260344481641009 165904969372695258361230757)
      ·
        refine ⟨31107181757380360942730767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165904969372695258361230757 31107181757380360942730767)
        ·
          refine ⟨46660772636070541414096151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31107181757380360942730767 46660772636070541414096151)
          ·
            refine ⟨69991158954105812121144227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46660772636070541414096151 69991158954105812121144227)
            ·
              refine ⟨104986738431158718181716341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69991158954105812121144227 104986738431158718181716341)
              ·
                refine ⟨9842506727921129829535907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104986738431158718181716341 9842506727921129829535907)
                ·
                  refine ⟨14763760091881694744303861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9842506727921129829535907 14763760091881694744303861)
                  ·
                    refine ⟨1384102508613908882278487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14763760091881694744303861 1384102508613908882278487)
                    ·
                      rfl

theorem cell22_4043295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_4043295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043295 prefixEnd_4043295 := by exact prefixLift 4043295
  have htrace : WordTrace (prefixWord ++ tailWord_4043295) baseStart_4043295 baseEnd_4043295 := by
    simpa [prefixWord, tailWord_4043295, baseEnd_4043295] using wordTrace_append hprefix tailTrace_4043295
  have hstable : (prefixWord ++ tailWord_4043295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043295).length < 2 ^ (prefixWord ++ tailWord_4043295).sum := by decide
  have hdescent : baseEnd_4043295 < baseStart_4043295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043299 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 1, 4]
def baseStart_4043299 : Nat := 118140960795 + 4043299 * 2 ^ 59
def prefixEnd_4043299 : Nat := 4983230072969 + 3 ^ 40 * 4043299 * 2
def baseEnd_4043299 : Nat := 1384103877895654205178475

theorem tailTrace_4043299 : CollatzResearch.WordTrace tailWord_4043299 prefixEnd_4043299 1384103877895654205178475 := by
  unfold tailWord_4043299
  simp only [CollatzResearch.WordTrace]
  refine ⟨147471229778825738337572951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98314153185883825558381967 147471229778825738337572951)
  ·
    refine ⟨221206844668238607506359427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147471229778825738337572951 221206844668238607506359427)
    ·
      refine ⟨331810267002357911259539141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221206844668238607506359427 331810267002357911259539141)
      ·
        refine ⟨62214425062942108361163589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331810267002357911259539141 62214425062942108361163589)
        ·
          refine ⟨11665204699301645317718173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62214425062942108361163589 11665204699301645317718173)
          ·
            refine ⟨4374451762238116994144315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11665204699301645317718173 4374451762238116994144315)
            ·
              refine ⟨6561677643357175491216473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374451762238116994144315 6561677643357175491216473)
              ·
                refine ⟨4921258232517881618412355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561677643357175491216473 4921258232517881618412355)
                ·
                  refine ⟨7381887348776822427618533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921258232517881618412355 7381887348776822427618533)
                  ·
                    refine ⟨1384103877895654205178475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7381887348776822427618533 1384103877895654205178475)
                    ·
                      rfl

theorem cell22_4043299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 4].length) (baseStart_4043299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043299 prefixEnd_4043299 := by exact prefixLift 4043299
  have htrace : WordTrace (prefixWord ++ tailWord_4043299) baseStart_4043299 baseEnd_4043299 := by
    simpa [prefixWord, tailWord_4043299, baseEnd_4043299] using wordTrace_append hprefix tailTrace_4043299
  have hstable : (prefixWord ++ tailWord_4043299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043299).length < 2 ^ (prefixWord ++ tailWord_4043299).sum := by decide
  have hdescent : baseEnd_4043299 < baseStart_4043299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043325 : List Nat := [1, 4, 1, 3, 2, 11]
def baseStart_4043325 : Nat := 118140960795 + 4043325 * 2 ^ 59
def prefixEnd_4043325 : Nat := 4983230072969 + 3 ^ 40 * 4043325 * 2
def baseEnd_4043325 : Nat := 17087812076876528444795

theorem tailTrace_4043325 : CollatzResearch.WordTrace tailWord_4043325 prefixEnd_4043325 17087812076876528444795 := by
  unfold tailWord_4043325
  simp only [CollatzResearch.WordTrace]
  refine ⟨147472178076731544778019429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98314785384487696518679619 147472178076731544778019429)
  ·
    refine ⟨27651033389387164645878643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147472178076731544778019429 27651033389387164645878643)
    ·
      refine ⟨41476550084080746968817965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27651033389387164645878643 41476550084080746968817965)
      ·
        refine ⟨15553706281530280113306737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41476550084080746968817965 15553706281530280113306737)
        ·
          refine ⟨11665279711147710084980053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15553706281530280113306737 11665279711147710084980053)
          ·
            refine ⟨17087812076876528444795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11665279711147710084980053 17087812076876528444795)
            ·
              rfl

theorem cell22_4043325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 11].length) (baseStart_4043325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043325 prefixEnd_4043325 := by exact prefixLift 4043325
  have htrace : WordTrace (prefixWord ++ tailWord_4043325) baseStart_4043325 baseEnd_4043325 := by
    simpa [prefixWord, tailWord_4043325, baseEnd_4043325] using wordTrace_append hprefix tailTrace_4043325
  have hstable : (prefixWord ++ tailWord_4043325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043325).length < 2 ^ (prefixWord ++ tailWord_4043325).sum := by decide
  have hdescent : baseEnd_4043325 < baseStart_4043325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043329 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_4043329 : Nat := 118140960795 + 4043329 * 2 ^ 59
def prefixEnd_4043329 : Nat := 4983230072969 + 3 ^ 40 * 4043329 * 2
def baseEnd_4043329 : Nat := 1384114147508744126928383

theorem tailTrace_4043329 : CollatzResearch.WordTrace tailWord_4043329 prefixEnd_4043329 1384114147508744126928383 := by
  unfold tailWord_4043329
  simp only [CollatzResearch.WordTrace]
  refine ⟨147472323968717053461165041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98314882645811368974110027 147472323968717053461165041)
  ·
    refine ⟨110604242976537790095873781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147472323968717053461165041 110604242976537790095873781)
    ·
      refine ⟨10369147779050417821488167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110604242976537790095873781 10369147779050417821488167)
      ·
        refine ⟨15553721668575626732232251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10369147779050417821488167 15553721668575626732232251)
        ·
          refine ⟨23330582502863440098348377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15553721668575626732232251 23330582502863440098348377)
          ·
            refine ⟨17497936877147580073761283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23330582502863440098348377 17497936877147580073761283)
            ·
              refine ⟨26246905315721370110641925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17497936877147580073761283 26246905315721370110641925)
              ·
                refine ⟨4921294746697756895745361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26246905315721370110641925 4921294746697756895745361)
                ·
                  refine ⟨3690971060023317671809021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4921294746697756895745361 3690971060023317671809021)
                  ·
                    refine ⟨1384114147508744126928383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690971060023317671809021 1384114147508744126928383)
                    ·
                      rfl

theorem cell22_4043329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_4043329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043329 prefixEnd_4043329 := by exact prefixLift 4043329
  have htrace : WordTrace (prefixWord ++ tailWord_4043329) baseStart_4043329 baseEnd_4043329 := by
    simpa [prefixWord, tailWord_4043329, baseEnd_4043329] using wordTrace_append hprefix tailTrace_4043329
  have hstable : (prefixWord ++ tailWord_4043329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043329).length < 2 ^ (prefixWord ++ tailWord_4043329).sum := by decide
  have hdescent : baseEnd_4043329 < baseStart_4043329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043425 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 1, 3]
def baseStart_4043425 : Nat := 118140960795 + 4043425 * 2 ^ 59
def prefixEnd_4043425 : Nat := 4983230072969 + 3 ^ 40 * 4043425 * 2
def baseEnd_4043425 : Nat := 1384147010270631876528089

theorem tailTrace_4043425 : CollatzResearch.WordTrace tailWord_4043425 prefixEnd_4043425 1384147010270631876528089 := by
  unfold tailWord_4043425
  simp only [CollatzResearch.WordTrace]
  refine ⟨147475825376369261856659729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98317216917579507904439819 147475825376369261856659729)
  ·
    refine ⟨110606869032276946392494797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147475825376369261856659729 110606869032276946392494797)
    ·
      refine ⟨41477575887103854897185549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110606869032276946392494797 41477575887103854897185549)
      ·
        refine ⟨15554090957663945586444581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41477575887103854897185549 15554090957663945586444581)
        ·
          refine ⟨2916392054561989797458359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15554090957663945586444581 2916392054561989797458359)
          ·
            refine ⟨4374588081842984696187539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916392054561989797458359 4374588081842984696187539)
            ·
              refine ⟨6561882122764477044281309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374588081842984696187539 6561882122764477044281309)
              ·
                refine ⟨2460705796036678891605491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6561882122764477044281309 2460705796036678891605491)
                ·
                  refine ⟨3691058694055018337408237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460705796036678891605491 3691058694055018337408237)
                  ·
                    refine ⟨1384147010270631876528089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691058694055018337408237 1384147010270631876528089)
                    ·
                      rfl

theorem cell22_4043425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_4043425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043425 prefixEnd_4043425 := by exact prefixLift 4043425
  have htrace : WordTrace (prefixWord ++ tailWord_4043425) baseStart_4043425 baseEnd_4043425 := by
    simpa [prefixWord, tailWord_4043425, baseEnd_4043425] using wordTrace_append hprefix tailTrace_4043425
  have hstable : (prefixWord ++ tailWord_4043425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043425).length < 2 ^ (prefixWord ++ tailWord_4043425).sum := by decide
  have hdescent : baseEnd_4043425 < baseStart_4043425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043479 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 2, 4]
def baseStart_4043479 : Nat := 118140960795 + 4043479 * 2 ^ 59
def prefixEnd_4043479 : Nat := 4983230072969 + 3 ^ 40 * 4043479 * 2
def baseEnd_4043479 : Nat := 1384165495574193735677923

theorem tailTrace_4043479 : CollatzResearch.WordTrace tailWord_4043479 prefixEnd_4043479 1384165495574193735677923 := by
  unfold tailWord_4043479
  simp only [CollatzResearch.WordTrace]
  refine ⟨147477794918173629079125491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98318529945449086052750327 147477794918173629079125491)
  ·
    refine ⟨221216692377260443618688237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147477794918173629079125491 221216692377260443618688237)
    ·
      refine ⟨82956259641472666357008089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221216692377260443618688237 82956259641472666357008089)
      ·
        refine ⟨62217194731104499767756067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82956259641472666357008089 62217194731104499767756067)
        ·
          refine ⟨93325792096656749651634101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62217194731104499767756067 93325792096656749651634101)
          ·
            refine ⟨8749293009061570279840697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93325792096656749651634101 8749293009061570279840697)
            ·
              refine ⟨6561969756796177709880523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8749293009061570279840697 6561969756796177709880523)
              ·
                refine ⟨9842954635194266564820785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6561969756796177709880523 9842954635194266564820785)
                ·
                  refine ⟨7382215976395699923615589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9842954635194266564820785 7382215976395699923615589)
                  ·
                    refine ⟨1384165495574193735677923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382215976395699923615589 1384165495574193735677923)
                    ·
                      rfl

theorem cell22_4043479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_4043479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043479 prefixEnd_4043479 := by exact prefixLift 4043479
  have htrace : WordTrace (prefixWord ++ tailWord_4043479) baseStart_4043479 baseEnd_4043479 := by
    simpa [prefixWord, tailWord_4043479, baseEnd_4043479] using wordTrace_append hprefix tailTrace_4043479
  have hstable : (prefixWord ++ tailWord_4043479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043479).length < 2 ^ (prefixWord ++ tailWord_4043479).sum := by decide
  have hdescent : baseEnd_4043479 < baseStart_4043479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043554 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4043554 : Nat := 118140960795 + 4043554 * 2 ^ 59
def prefixEnd_4043554 : Nat := 4983230072969 + 3 ^ 40 * 4043554 * 2
def baseEnd_4043554 : Nat := 1384191169606918540052693

theorem tailTrace_4043554 : CollatzResearch.WordTrace tailWord_4043554 prefixEnd_4043554 1384191169606918540052693 := by
  unfold tailWord_4043554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36870132598225479222026429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98320353595267944592070477 36870132598225479222026429)
  ·
    refine ⟨13826299724334554708259911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36870132598225479222026429 13826299724334554708259911)
    ·
      refine ⟨20739449586501832062389867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13826299724334554708259911 20739449586501832062389867)
      ·
        refine ⟨31109174379752748093584801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20739449586501832062389867 31109174379752748093584801)
        ·
          refine ⟨23331880784814561070188601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31109174379752748093584801 23331880784814561070188601)
          ·
            refine ⟨17498910588610920802641451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23331880784814561070188601 17498910588610920802641451)
            ·
              refine ⟨26248365882916381203962177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17498910588610920802641451 26248365882916381203962177)
              ·
                refine ⟨19686274412187285902971633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26248365882916381203962177 19686274412187285902971633)
                ·
                  refine ⟨14764705809140464427228725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19686274412187285902971633 14764705809140464427228725)
                  ·
                    refine ⟨1384191169606918540052693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14764705809140464427228725 1384191169606918540052693)
                    ·
                      rfl

theorem cell22_4043554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4043554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043554 prefixEnd_4043554 := by exact prefixLift 4043554
  have htrace : WordTrace (prefixWord ++ tailWord_4043554) baseStart_4043554 baseEnd_4043554 := by
    simpa [prefixWord, tailWord_4043554, baseEnd_4043554] using wordTrace_append hprefix tailTrace_4043554
  have hstable : (prefixWord ++ tailWord_4043554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043554).length < 2 ^ (prefixWord ++ tailWord_4043554).sum := by decide
  have hdescent : baseEnd_4043554 < baseStart_4043554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043616 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_4043616 : Nat := 118140960795 + 4043616 * 2 ^ 59
def prefixEnd_4043616 : Nat := 4983230072969 + 3 ^ 40 * 4043616 * 2
def baseEnd_4043616 : Nat := 1384212393473971045002503

theorem tailTrace_4043616 : CollatzResearch.WordTrace tailWord_4043616 prefixEnd_4043616 1384212393473971045002503 := by
  unfold tailWord_4043616
  simp only [CollatzResearch.WordTrace]
  refine ⟨73741395859338650738431351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98321861145784867651241801 73741395859338650738431351)
  ·
    refine ⟨110612093789007976107647027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73741395859338650738431351 110612093789007976107647027)
    ·
      refine ⟨165918140683511964161470541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110612093789007976107647027 165918140683511964161470541)
      ·
        refine ⟨62219302756316986560551453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165918140683511964161470541 62219302756316986560551453)
        ·
          refine ⟨23332238533618869960206795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62219302756316986560551453 23332238533618869960206795)
          ·
            refine ⟨34998357800428304940310193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23332238533618869960206795 34998357800428304940310193)
            ·
              refine ⟨26248768350321228705232645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34998357800428304940310193 26248768350321228705232645)
              ·
                refine ⟨4921644065685230382231121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26248768350321228705232645 4921644065685230382231121)
                ·
                  refine ⟨3691233049263922786673341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4921644065685230382231121 3691233049263922786673341)
                  ·
                    refine ⟨1384212393473971045002503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691233049263922786673341 1384212393473971045002503)
                    ·
                      rfl

theorem cell22_4043616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_4043616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043616 prefixEnd_4043616 := by exact prefixLift 4043616
  have htrace : WordTrace (prefixWord ++ tailWord_4043616) baseStart_4043616 baseEnd_4043616 := by
    simpa [prefixWord, tailWord_4043616, baseEnd_4043616] using wordTrace_append hprefix tailTrace_4043616
  have hstable : (prefixWord ++ tailWord_4043616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043616).length < 2 ^ (prefixWord ++ tailWord_4043616).sum := by decide
  have hdescent : baseEnd_4043616 < baseStart_4043616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043618 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_4043618 : Nat := 118140960795 + 4043618 * 2 ^ 59
def prefixEnd_4043618 : Nat := 4983230072969 + 3 ^ 40 * 4043618 * 2
def baseEnd_4043618 : Nat := 461404359371614568817499

theorem tailTrace_4043618 : CollatzResearch.WordTrace tailWord_4043618 prefixEnd_4043618 461404359371614568817499 := by
  unfold tailWord_4043618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36870716166167513954608877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98321909776446703878957005 36870716166167513954608877)
  ·
    refine ⟨13826518562312817732978329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36870716166167513954608877 13826518562312817732978329)
    ·
      refine ⟨10369888921734613299733747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13826518562312817732978329 10369888921734613299733747)
      ·
        refine ⟨15554833382601919949600621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10369888921734613299733747 15554833382601919949600621)
        ·
          refine ⟨5833062518475719981100233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15554833382601919949600621 5833062518475719981100233)
          ·
            refine ⟨4374796888856789985825175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5833062518475719981100233 4374796888856789985825175)
            ·
              refine ⟨6562195333285184978737763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374796888856789985825175 6562195333285184978737763)
              ·
                refine ⟨9843292999927777468106645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562195333285184978737763 9843292999927777468106645)
                ·
                  refine ⟨461404359371614568817499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9843292999927777468106645 461404359371614568817499)
                  ·
                    rfl

theorem cell22_4043618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_4043618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043618 prefixEnd_4043618 := by exact prefixLift 4043618
  have htrace : WordTrace (prefixWord ++ tailWord_4043618) baseStart_4043618 baseEnd_4043618 := by
    simpa [prefixWord, tailWord_4043618, baseEnd_4043618] using wordTrace_append hprefix tailTrace_4043618
  have hstable : (prefixWord ++ tailWord_4043618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043618).length < 2 ^ (prefixWord ++ tailWord_4043618).sum := by decide
  have hdescent : baseEnd_4043618 < baseStart_4043618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043633 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 2, 3]
def baseStart_4043633 : Nat := 118140960795 + 4043633 * 2 ^ 59
def prefixEnd_4043633 : Nat := 4983230072969 + 3 ^ 40 * 4043633 * 2
def baseEnd_4043633 : Nat := 1384218212921388667327451

theorem tailTrace_4043633 : CollatzResearch.WordTrace tailWord_4043633 prefixEnd_4043633 1384218212921388667327451 := by
  unfold tailWord_4043633
  simp only [CollatzResearch.WordTrace]
  refine ⟨147483411759615713380231553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98322274506410475586821035 147483411759615713380231553)
  ·
    refine ⟨110612558819711785035173665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147483411759615713380231553 110612558819711785035173665)
    ·
      refine ⟨82959419114783838776380249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110612558819711785035173665 82959419114783838776380249)
      ·
        refine ⟨62219564336087879082285187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82959419114783838776380249 62219564336087879082285187)
        ·
          refine ⟨93329346504131818623427781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62219564336087879082285187 93329346504131818623427781)
          ·
            refine ⟨17499252469524715991892709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93329346504131818623427781 17499252469524715991892709)
            ·
              refine ⟨3281109838035884248479883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17499252469524715991892709 3281109838035884248479883)
              ·
                refine ⟨4921664757053826372719825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281109838035884248479883 4921664757053826372719825)
                ·
                  refine ⟨3691248567790369779539869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4921664757053826372719825 3691248567790369779539869)
                  ·
                    refine ⟨1384218212921388667327451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691248567790369779539869 1384218212921388667327451)
                    ·
                      rfl

theorem cell22_4043633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_4043633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043633 prefixEnd_4043633 := by exact prefixLift 4043633
  have htrace : WordTrace (prefixWord ++ tailWord_4043633) baseStart_4043633 baseEnd_4043633 := by
    simpa [prefixWord, tailWord_4043633, baseEnd_4043633] using wordTrace_append hprefix tailTrace_4043633
  have hstable : (prefixWord ++ tailWord_4043633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043633).length < 2 ^ (prefixWord ++ tailWord_4043633).sum := by decide
  have hdescent : baseEnd_4043633 < baseStart_4043633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043650 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4043650 : Nat := 118140960795 + 4043650 * 2 ^ 59
def prefixEnd_4043650 : Nat := 4983230072969 + 3 ^ 40 * 4043650 * 2
def baseEnd_4043650 : Nat := 1384224032368806289652399

theorem tailTrace_4043650 : CollatzResearch.WordTrace tailWord_4043650 prefixEnd_4043650 1384224032368806289652399 := by
  unfold tailWord_4043650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36871007950138531320900101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98322687867036083522400269 36871007950138531320900101)
  ·
    refine ⟨6913313990650974622668769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36871007950138531320900101 6913313990650974622668769)
    ·
      refine ⟨5184985492988230967001577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6913313990650974622668769 5184985492988230967001577)
      ·
        refine ⟨3888739119741173225251183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5184985492988230967001577 3888739119741173225251183)
        ·
          refine ⟨5833108679611759837876775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888739119741173225251183 5833108679611759837876775)
          ·
            refine ⟨8749663019417639756815163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833108679611759837876775 8749663019417639756815163)
            ·
              refine ⟨13124494529126459635222745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749663019417639756815163 13124494529126459635222745)
              ·
                refine ⟨9843370896844844726417059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13124494529126459635222745 9843370896844844726417059)
                ·
                  refine ⟨14765056345267267089625589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9843370896844844726417059 14765056345267267089625589)
                  ·
                    refine ⟨1384224032368806289652399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14765056345267267089625589 1384224032368806289652399)
                    ·
                      rfl

theorem cell22_4043650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4043650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043650 prefixEnd_4043650 := by exact prefixLift 4043650
  have htrace : WordTrace (prefixWord ++ tailWord_4043650) baseStart_4043650 baseEnd_4043650 := by
    simpa [prefixWord, tailWord_4043650, baseEnd_4043650] using wordTrace_append hprefix tailTrace_4043650
  have hstable : (prefixWord ++ tailWord_4043650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043650).length < 2 ^ (prefixWord ++ tailWord_4043650).sum := by decide
  have hdescent : baseEnd_4043650 < baseStart_4043650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043689 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_4043689 : Nat := 118140960795 + 4043689 * 2 ^ 59
def prefixEnd_4043689 : Nat := 4983230072969 + 3 ^ 40 * 4043689 * 2
def baseEnd_4043689 : Nat := 1384237382865823187927279

theorem tailTrace_4043689 : CollatzResearch.WordTrace tailWord_4043689 prefixEnd_4043689 1384237382865823187927279 := by
  unfold tailWord_4043689
  simp only [CollatzResearch.WordTrace]
  refine ⟨147485454247412834944270121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98323636164941889962846747 147485454247412834944270121)
  ·
    refine ⟨110614090685559626208202591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147485454247412834944270121 110614090685559626208202591)
    ·
      refine ⟨165921136028339439312303887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110614090685559626208202591 165921136028339439312303887)
      ·
        refine ⟨248881704042509158968455831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165921136028339439312303887 248881704042509158968455831)
        ·
          refine ⟨373322556063763738452683747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248881704042509158968455831 373322556063763738452683747)
          ·
            refine ⟨559983834095645607679025621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373322556063763738452683747 559983834095645607679025621)
            ·
              refine ⟨13124621111616693929977163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 559983834095645607679025621 13124621111616693929977163)
              ·
                refine ⟨19686931667425040894965745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13124621111616693929977163 19686931667425040894965745)
                ·
                  refine ⟨14765198750568780671224309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19686931667425040894965745 14765198750568780671224309)
                  ·
                    refine ⟨1384237382865823187927279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14765198750568780671224309 1384237382865823187927279)
                    ·
                      rfl

theorem cell22_4043689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_4043689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043689 prefixEnd_4043689 := by exact prefixLift 4043689
  have htrace : WordTrace (prefixWord ++ tailWord_4043689) baseStart_4043689 baseEnd_4043689 := by
    simpa [prefixWord, tailWord_4043689, baseEnd_4043689] using wordTrace_append hprefix tailTrace_4043689
  have hstable : (prefixWord ++ tailWord_4043689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043689).length < 2 ^ (prefixWord ++ tailWord_4043689).sum := by decide
  have hdescent : baseEnd_4043689 < baseStart_4043689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043718 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4043718 : Nat := 118140960795 + 4043718 * 2 ^ 59
def prefixEnd_4043718 : Nat := 4983230072969 + 3 ^ 40 * 4043718 * 2
def baseEnd_4043718 : Nat := 1384247310158476778952191

theorem tailTrace_4043718 : CollatzResearch.WordTrace tailWord_4043718 prefixEnd_4043718 1384247310158476778952191 := by
  unfold tailWord_4043718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608953498884617903033619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98324341309538515264717205 4608953498884617903033619)
  ·
    refine ⟨6913430248326926854550429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608953498884617903033619 6913430248326926854550429)
    ·
      refine ⟨2592536343122597570456411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6913430248326926854550429 2592536343122597570456411)
      ·
        refine ⟨3888804514683896355684617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592536343122597570456411 3888804514683896355684617)
        ·
          refine ⟨2916603386012922266763463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3888804514683896355684617 2916603386012922266763463)
          ·
            refine ⟨4374905079019383400145195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916603386012922266763463 4374905079019383400145195)
            ·
              refine ⟨6562357618529075100217793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374905079019383400145195 6562357618529075100217793)
              ·
                refine ⟨4921768213896806325163345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562357618529075100217793 4921768213896806325163345)
                ·
                  refine ⟨3691326160422604743872509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4921768213896806325163345 3691326160422604743872509)
                  ·
                    refine ⟨1384247310158476778952191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691326160422604743872509 1384247310158476778952191)
                    ·
                      rfl

theorem cell22_4043718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4043718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043718 prefixEnd_4043718 := by exact prefixLift 4043718
  have htrace : WordTrace (prefixWord ++ tailWord_4043718) baseStart_4043718 baseEnd_4043718 := by
    simpa [prefixWord, tailWord_4043718, baseEnd_4043718] using wordTrace_append hprefix tailTrace_4043718
  have hstable : (prefixWord ++ tailWord_4043718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043718).length < 2 ^ (prefixWord ++ tailWord_4043718).sum := by decide
  have hdescent : baseEnd_4043718 < baseStart_4043718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043736 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_4043736 : Nat := 118140960795 + 4043736 * 2 ^ 59
def prefixEnd_4043736 : Nat := 4983230072969 + 3 ^ 40 * 4043736 * 2
def baseEnd_4043736 : Nat := 461417823975443577334045

theorem tailTrace_4043736 : CollatzResearch.WordTrace tailWord_4043736 prefixEnd_4043736 461417823975443577334045 := by
  unfold tailWord_4043736
  simp only [CollatzResearch.WordTrace]
  refine ⟨73743584239121280985615531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98324778985495041314154041 73743584239121280985615531)
  ·
    refine ⟨110615376358681921478423297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73743584239121280985615531 110615376358681921478423297)
    ·
      refine ⟨82961532269011441108817473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110615376358681921478423297 82961532269011441108817473)
      ·
        refine ⟨62221149201758580831613105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82961532269011441108817473 62221149201758580831613105)
        ·
          refine ⟨46665861901318935623709829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62221149201758580831613105 46665861901318935623709829)
          ·
            refine ⟨8749849106497300429445593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46665861901318935623709829 8749849106497300429445593)
            ·
              refine ⟨6562386829872975322084195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8749849106497300429445593 6562386829872975322084195)
              ·
                refine ⟨9843580244809462983126293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562386829872975322084195 9843580244809462983126293)
                ·
                  refine ⟨461417823975443577334045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9843580244809462983126293 461417823975443577334045)
                  ·
                    rfl

theorem cell22_4043736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_4043736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043736 prefixEnd_4043736 := by exact prefixLift 4043736
  have htrace : WordTrace (prefixWord ++ tailWord_4043736) baseStart_4043736 baseEnd_4043736 := by
    simpa [prefixWord, tailWord_4043736, baseEnd_4043736] using wordTrace_append hprefix tailTrace_4043736
  have hstable : (prefixWord ++ tailWord_4043736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043736).length < 2 ^ (prefixWord ++ tailWord_4043736).sum := by decide
  have hdescent : baseEnd_4043736 < baseStart_4043736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043847 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 1, 3]
def baseStart_4043847 : Nat := 118140960795 + 4043847 * 2 ^ 59
def prefixEnd_4043847 : Nat := 4983230072969 + 3 ^ 40 * 4043847 * 2
def baseEnd_4043847 : Nat := 1384291469494763442476795

theorem tailTrace_4043847 : CollatzResearch.WordTrace tailWord_4043847 prefixEnd_4043847 1384291469494763442476795 := by
  unfold tailWord_4043847
  simp only [CollatzResearch.WordTrace]
  refine ⟨147491216980840427928521795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98327477987226951952347863 147491216980840427928521795)
  ·
    refine ⟨221236825471260641892782693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147491216980840427928521795 221236825471260641892782693)
    ·
      refine ⟨41481904775861370354896755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221236825471260641892782693 41481904775861370354896755)
      ·
        refine ⟨62222857163792055532345133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41481904775861370354896755 62222857163792055532345133)
        ·
          refine ⟨23333571436422020824629425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62222857163792055532345133 23333571436422020824629425)
          ·
            refine ⟨17500178577316515618472069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23333571436422020824629425 17500178577316515618472069)
            ·
              refine ⟨3281283483246846678463513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17500178577316515618472069 3281283483246846678463513)
              ·
                refine ⟨2460962612435135008847635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281283483246846678463513 2460962612435135008847635)
                ·
                  refine ⟨3691443918652702513271453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460962612435135008847635 3691443918652702513271453)
                  ·
                    refine ⟨1384291469494763442476795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691443918652702513271453 1384291469494763442476795)
                    ·
                      rfl

theorem cell22_4043847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_4043847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043847 prefixEnd_4043847 := by exact prefixLift 4043847
  have htrace : WordTrace (prefixWord ++ tailWord_4043847) baseStart_4043847 baseEnd_4043847 := by
    simpa [prefixWord, tailWord_4043847, baseEnd_4043847] using wordTrace_append hprefix tailTrace_4043847
  have hstable : (prefixWord ++ tailWord_4043847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043847).length < 2 ^ (prefixWord ++ tailWord_4043847).sum := by decide
  have hdescent : baseEnd_4043847 < baseStart_4043847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043858 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_4043858 : Nat := 118140960795 + 4043858 * 2 ^ 59
def prefixEnd_4043858 : Nat := 4983230072969 + 3 ^ 40 * 4043858 * 2
def baseEnd_4043858 : Nat := 1384295235019563080451761

theorem tailTrace_4043858 : CollatzResearch.WordTrace tailWord_4043858 prefixEnd_4043858 1384295235019563080451761 := by
  unfold tailWord_4043858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36872904545950144201793057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98327745455867051204781485 36872904545950144201793057)
  ·
    refine ⟨27654678409462608151344793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36872904545950144201793057 27654678409462608151344793)
    ·
      refine ⟨20741008807096956113508595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27654678409462608151344793 20741008807096956113508595)
      ·
        refine ⟨31111513210645434170262893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20741008807096956113508595 31111513210645434170262893)
        ·
          refine ⟨11666817453992037813848585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31111513210645434170262893 11666817453992037813848585)
          ·
            refine ⟨8750113090494028360386439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11666817453992037813848585 8750113090494028360386439)
            ·
              refine ⟨13125169635741042540579659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750113090494028360386439 13125169635741042540579659)
              ·
                refine ⟨19687754453611563810869489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13125169635741042540579659 19687754453611563810869489)
                ·
                  refine ⟨14765815840208672858152117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19687754453611563810869489 14765815840208672858152117)
                  ·
                    refine ⟨1384295235019563080451761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14765815840208672858152117 1384295235019563080451761)
                    ·
                      rfl

theorem cell22_4043858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_4043858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043858 prefixEnd_4043858 := by exact prefixLift 4043858
  have htrace : WordTrace (prefixWord ++ tailWord_4043858) baseStart_4043858 baseEnd_4043858 := by
    simpa [prefixWord, tailWord_4043858, baseEnd_4043858] using wordTrace_append hprefix tailTrace_4043858
  have hstable : (prefixWord ++ tailWord_4043858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043858).length < 2 ^ (prefixWord ++ tailWord_4043858).sum := by decide
  have hdescent : baseEnd_4043858 < baseStart_4043858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043871 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 6]
def baseStart_4043871 : Nat := 118140960795 + 4043871 * 2 ^ 59
def prefixEnd_4043871 : Nat := 4983230072969 + 3 ^ 40 * 4043871 * 2
def baseEnd_4043871 : Nat := 461433228395078459958907

theorem tailTrace_4043871 : CollatzResearch.WordTrace tailWord_4043871 prefixEnd_4043871 461433228395078459958907 := by
  unfold tailWord_4043871
  simp only [CollatzResearch.WordTrace]
  refine ⟨147492092332753480027395467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98328061555168986684930311 147492092332753480027395467)
  ·
    refine ⟨221238138499130220041093201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147492092332753480027395467 221238138499130220041093201)
    ·
      refine ⟨165928603874347665030819901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221238138499130220041093201 165928603874347665030819901)
      ·
        refine ⟨62223226452880374386557463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165928603874347665030819901 62223226452880374386557463)
        ·
          refine ⟨93334839679320561579836195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62223226452880374386557463 93334839679320561579836195)
          ·
            refine ⟨140002259518980842369754293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93334839679320561579836195 140002259518980842369754293)
            ·
              refine ⟨13125211829904453972164465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140002259518980842369754293 13125211829904453972164465)
              ·
                refine ⟨9843908872428340479123349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13125211829904453972164465 9843908872428340479123349)
                ·
                  refine ⟨461433228395078459958907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9843908872428340479123349 461433228395078459958907)
                  ·
                    rfl

theorem cell22_4043871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 6].length) (baseStart_4043871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043871 prefixEnd_4043871 := by exact prefixLift 4043871
  have htrace : WordTrace (prefixWord ++ tailWord_4043871) baseStart_4043871 baseEnd_4043871 := by
    simpa [prefixWord, tailWord_4043871, baseEnd_4043871] using wordTrace_append hprefix tailTrace_4043871
  have hstable : (prefixWord ++ tailWord_4043871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043871).length < 2 ^ (prefixWord ++ tailWord_4043871).sum := by decide
  have hdescent : baseEnd_4043871 < baseStart_4043871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043905 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 4]
def baseStart_4043905 : Nat := 118140960795 + 4043905 * 2 ^ 59
def prefixEnd_4043905 : Nat := 4983230072969 + 3 ^ 40 * 4043905 * 2
def baseEnd_4043905 : Nat := 461437108026690208175539

theorem tailTrace_4043905 : CollatzResearch.WordTrace tailWord_4043905 prefixEnd_4043905 461437108026690208175539 := by
  unfold tailWord_4043905
  simp only [CollatzResearch.WordTrace]
  refine ⟨147493332414630303834133169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98328888276420202556088779 147493332414630303834133169)
  ·
    refine ⟨110619999310972727875599877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147493332414630303834133169 110619999310972727875599877)
    ·
      refine ⟨20741249870807386476674977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110619999310972727875599877 20741249870807386476674977)
      ·
        refine ⟨15555937403105539857506233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20741249870807386476674977 15555937403105539857506233)
        ·
          refine ⟨11666953052329154893129675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15555937403105539857506233 11666953052329154893129675)
          ·
            refine ⟨17500429578493732339694513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666953052329154893129675 17500429578493732339694513)
            ·
              refine ⟨13125322183870299254770885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17500429578493732339694513 13125322183870299254770885)
              ·
                refine ⟨2460997909475681110269541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13125322183870299254770885 2460997909475681110269541)
                ·
                  refine ⟨461437108026690208175539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460997909475681110269541 461437108026690208175539)
                  ·
                    rfl

theorem cell22_4043905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_4043905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043905 prefixEnd_4043905 := by exact prefixLift 4043905
  have htrace : WordTrace (prefixWord ++ tailWord_4043905) baseStart_4043905 baseEnd_4043905 := by
    simpa [prefixWord, tailWord_4043905, baseEnd_4043905] using wordTrace_append hprefix tailTrace_4043905
  have hstable : (prefixWord ++ tailWord_4043905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043905).length < 2 ^ (prefixWord ++ tailWord_4043905).sum := by decide
  have hdescent : baseEnd_4043905 < baseStart_4043905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043918 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_4043918 : Nat := 118140960795 + 4043918 * 2 ^ 59
def prefixEnd_4043918 : Nat := 4983230072969 + 3 ^ 40 * 4043918 * 2
def baseEnd_4043918 : Nat := 1384315774245742923951577

theorem tailTrace_4043918 : CollatzResearch.WordTrace tailWord_4043918 prefixEnd_4043918 1384315774245742923951577 := by
  unfold tailWord_4043918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18436725820447900881794551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98329204375722138036237605 18436725820447900881794551)
  ·
    refine ⟨27655088730671851322691827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18436725820447900881794551 27655088730671851322691827)
    ·
      refine ⟨41482633096007776984037741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655088730671851322691827 41482633096007776984037741)
      ·
        refine ⟨15555987411002916369014153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41482633096007776984037741 15555987411002916369014153)
        ·
          refine ⟨11666990558252187276760615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15555987411002916369014153 11666990558252187276760615)
          ·
            refine ⟨17500485837378280915140923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666990558252187276760615 17500485837378280915140923)
            ·
              refine ⟨26250728756067421372711385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500485837378280915140923 26250728756067421372711385)
              ·
                refine ⟨19688046567050566029533539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26250728756067421372711385 19688046567050566029533539)
                ·
                  refine ⟨29532069850575849044300309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19688046567050566029533539 29532069850575849044300309)
                  ·
                    refine ⟨1384315774245742923951577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29532069850575849044300309 1384315774245742923951577)
                    ·
                      rfl

theorem cell22_4043918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_4043918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043918 prefixEnd_4043918 := by exact prefixLift 4043918
  have htrace : WordTrace (prefixWord ++ tailWord_4043918) baseStart_4043918 baseEnd_4043918 := by
    simpa [prefixWord, tailWord_4043918, baseEnd_4043918] using wordTrace_append hprefix tailTrace_4043918
  have hstable : (prefixWord ++ tailWord_4043918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043918).length < 2 ^ (prefixWord ++ tailWord_4043918).sum := by decide
  have hdescent : baseEnd_4043918 < baseStart_4043918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043965 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_4043965 : Nat := 118140960795 + 4043965 * 2 ^ 59
def prefixEnd_4043965 : Nat := 4983230072969 + 3 ^ 40 * 4043965 * 2
def baseEnd_4043965 : Nat := 1384331863306250468026433

theorem tailTrace_4043965 : CollatzResearch.WordTrace tailWord_4043965 prefixEnd_4043965 1384331863306250468026433 := by
  unfold tailWord_4043965
  simp only [CollatzResearch.WordTrace]
  refine ⟨147495520794412934081317349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98330347196275289387544899 147495520794412934081317349)
  ·
    refine ⟨27655410148952425140247003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147495520794412934081317349 27655410148952425140247003)
    ·
      refine ⟨41483115223428637710370505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655410148952425140247003 41483115223428637710370505)
      ·
        refine ⟨31112336417571478282777879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41483115223428637710370505 31112336417571478282777879)
        ·
          refine ⟨46668504626357217424166819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31112336417571478282777879 46668504626357217424166819)
          ·
            refine ⟨70002756939535826136250229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46668504626357217424166819 70002756939535826136250229)
            ·
              refine ⟨6562758463081483700273459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70002756939535826136250229 6562758463081483700273459)
              ·
                refine ⟨9844137694622225550410189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562758463081483700273459 9844137694622225550410189)
                ·
                  refine ⟨3691551635483334581403821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9844137694622225550410189 3691551635483334581403821)
                  ·
                    refine ⟨1384331863306250468026433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691551635483334581403821 1384331863306250468026433)
                    ·
                      rfl

theorem cell22_4043965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_4043965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4043965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4043965 prefixEnd_4043965 := by exact prefixLift 4043965
  have htrace : WordTrace (prefixWord ++ tailWord_4043965) baseStart_4043965 baseEnd_4043965 := by
    simpa [prefixWord, tailWord_4043965, baseEnd_4043965] using wordTrace_append hprefix tailTrace_4043965
  have hstable : (prefixWord ++ tailWord_4043965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043965).length < 2 ^ (prefixWord ++ tailWord_4043965).sum := by decide
  have hdescent : baseEnd_4043965 < baseStart_4043965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044040 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_4044040 : Nat := 118140960795 + 4044040 * 2 ^ 59
def prefixEnd_4044040 : Nat := 4983230072969 + 3 ^ 40 * 4044040 * 2
def baseEnd_4044040 : Nat := 461452512446325090800401

theorem tailTrace_4044040 : CollatzResearch.WordTrace tailWord_4044040 prefixEnd_4044040 461452512446325090800401 := by
  unfold tailWord_4044040
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749128134570610945148787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98332170846094147926865049 73749128134570610945148787)
  ·
    refine ⟨110623692201855916417723181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73749128134570610945148787 110623692201855916417723181)
    ·
      refine ⟨41483884575695968656646193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110623692201855916417723181 41483884575695968656646193)
      ·
        refine ⟨31112913431771976492484645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41483884575695968656646193 31112913431771976492484645)
        ·
          refine ⟨5833671268457245592340871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31112913431771976492484645 5833671268457245592340871)
          ·
            refine ⟨8750506902685868388511307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833671268457245592340871 8750506902685868388511307)
            ·
              refine ⟨13125760354028802582766961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750506902685868388511307 13125760354028802582766961)
              ·
                refine ⟨9844320265521601937075221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13125760354028802582766961 9844320265521601937075221)
                ·
                  refine ⟨461452512446325090800401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9844320265521601937075221 461452512446325090800401)
                  ·
                    rfl

theorem cell22_4044040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_4044040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044040 prefixEnd_4044040 := by exact prefixLift 4044040
  have htrace : WordTrace (prefixWord ++ tailWord_4044040) baseStart_4044040 baseEnd_4044040 := by
    simpa [prefixWord, tailWord_4044040, baseEnd_4044040] using wordTrace_append hprefix tailTrace_4044040
  have hstable : (prefixWord ++ tailWord_4044040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044040).length < 2 ^ (prefixWord ++ tailWord_4044040).sum := by decide
  have hdescent : baseEnd_4044040 < baseStart_4044040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044055 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 4, 3]
def baseStart_4044055 : Nat := 118140960795 + 4044055 * 2 ^ 59
def prefixEnd_4044055 : Nat := 4983230072969 + 3 ^ 40 * 4044055 * 2
def baseEnd_4044055 : Nat := 1384362672145520233276157

theorem tailTrace_4044055 : CollatzResearch.WordTrace tailWord_4044055 prefixEnd_4044055 1384362672145520233276157 := by
  unfold tailWord_4044055
  simp only [CollatzResearch.WordTrace]
  refine ⟨147498803364086879452093619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98332535576057919634729079 147498803364086879452093619)
  ·
    refine ⟨221248205046130319178140429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147498803364086879452093619 221248205046130319178140429)
    ·
      refine ⟨82968076892298869691802661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221248205046130319178140429 82968076892298869691802661)
      ·
        refine ⟨15556514417306038067212999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82968076892298869691802661 15556514417306038067212999)
        ·
          refine ⟨23334771625959057100819499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556514417306038067212999 23334771625959057100819499)
          ·
            refine ⟨35002157438938585651229249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23334771625959057100819499 35002157438938585651229249)
            ·
              refine ⟨26251618079203939238421937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35002157438938585651229249 26251618079203939238421937)
              ·
                refine ⟨19688713559402954428816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26251618079203939238421937 19688713559402954428816453)
                ·
                  refine ⟨3691633792388053955403085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19688713559402954428816453 3691633792388053955403085)
                  ·
                    refine ⟨1384362672145520233276157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691633792388053955403085 1384362672145520233276157)
                    ·
                      rfl

theorem cell22_4044055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_4044055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044055 prefixEnd_4044055 := by exact prefixLift 4044055
  have htrace : WordTrace (prefixWord ++ tailWord_4044055) baseStart_4044055 baseEnd_4044055 := by
    simpa [prefixWord, tailWord_4044055, baseEnd_4044055] using wordTrace_append hprefix tailTrace_4044055
  have hstable : (prefixWord ++ tailWord_4044055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044055).length < 2 ^ (prefixWord ++ tailWord_4044055).sum := by decide
  have hdescent : baseEnd_4044055 < baseStart_4044055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044068 : List Nat := [2, 3, 1, 3, 1, 1, 11]
def baseStart_4044068 : Nat := 118140960795 + 4044068 * 2 ^ 59
def prefixEnd_4044068 : Nat := 4983230072969 + 3 ^ 40 * 4044068 * 2
def baseEnd_4044068 : Nat := 51272856381896019729671

theorem tailTrace_4044068 : CollatzResearch.WordTrace tailWord_4044068 prefixEnd_4044068 51272856381896019729671 := by
  unfold tailWord_4044068
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749638756519891336158429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98332851675359855114877905 73749638756519891336158429)
  ·
    refine ⟨27656114533694959251059411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73749638756519891336158429 27656114533694959251059411)
    ·
      refine ⟨41484171800542438876589117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27656114533694959251059411 41484171800542438876589117)
      ·
        refine ⟨15556564425203414578720919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41484171800542438876589117 15556564425203414578720919)
        ·
          refine ⟨23334846637805121868081379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556564425203414578720919 23334846637805121868081379)
          ·
            refine ⟨35002269956707682802122069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23334846637805121868081379 35002269956707682802122069)
            ·
              refine ⟨51272856381896019729671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35002269956707682802122069 51272856381896019729671)
              ·
                rfl

theorem cell22_4044068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 11].length) (baseStart_4044068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044068 prefixEnd_4044068 := by exact prefixLift 4044068
  have htrace : WordTrace (prefixWord ++ tailWord_4044068) baseStart_4044068 baseEnd_4044068 := by
    simpa [prefixWord, tailWord_4044068, baseEnd_4044068] using wordTrace_append hprefix tailTrace_4044068
  have hstable : (prefixWord ++ tailWord_4044068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044068).length < 2 ^ (prefixWord ++ tailWord_4044068).sum := by decide
  have hdescent : baseEnd_4044068 < baseStart_4044068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044072 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_4044072 : Nat := 118140960795 + 4044072 * 2 ^ 59
def prefixEnd_4044072 : Nat := 4983230072969 + 3 ^ 40 * 4044072 * 2
def baseEnd_4044072 : Nat := 1384368491592937855601105

theorem tailTrace_4044072 : CollatzResearch.WordTrace tailWord_4044072 prefixEnd_4044072 1384368491592937855601105 := by
  unfold tailWord_4044072
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749711702512645677731235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98332948936683527570308313 73749711702512645677731235)
  ·
    refine ⟨110624567553768968516596853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73749711702512645677731235 110624567553768968516596853)
    ·
      refine ⟨10371053208165840798430955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110624567553768968516596853 10371053208165840798430955)
      ·
        refine ⟨15556579812248761197646433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371053208165840798430955 15556579812248761197646433)
        ·
          refine ⟨11667434859186570898234825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15556579812248761197646433 11667434859186570898234825)
          ·
            refine ⟨8750576144389928173676119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11667434859186570898234825 8750576144389928173676119)
            ·
              refine ⟨13125864216584892260514179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750576144389928173676119 13125864216584892260514179)
              ·
                refine ⟨19688796324877338390771269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13125864216584892260514179 19688796324877338390771269)
                ·
                  refine ⟨3691649310914500948269613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19688796324877338390771269 3691649310914500948269613)
                  ·
                    refine ⟨1384368491592937855601105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691649310914500948269613 1384368491592937855601105)
                    ·
                      rfl

theorem cell22_4044072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_4044072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044072 prefixEnd_4044072 := by exact prefixLift 4044072
  have htrace : WordTrace (prefixWord ++ tailWord_4044072) baseStart_4044072 baseEnd_4044072 := by
    simpa [prefixWord, tailWord_4044072, baseEnd_4044072] using wordTrace_append hprefix tailTrace_4044072
  have hstable : (prefixWord ++ tailWord_4044072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044072).length < 2 ^ (prefixWord ++ tailWord_4044072).sum := by decide
  have hdescent : baseEnd_4044072 < baseStart_4044072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044089 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 1, 5]
def baseStart_4044089 : Nat := 118140960795 + 4044089 * 2 ^ 59
def prefixEnd_4044089 : Nat := 4983230072969 + 3 ^ 40 * 4044089 * 2
def baseEnd_4044089 : Nat := 1384374311040355477926053

theorem tailTrace_4044089 : CollatzResearch.WordTrace tailWord_4044089 prefixEnd_4044089 1384374311040355477926053 := by
  unfold tailWord_4044089
  simp only [CollatzResearch.WordTrace]
  refine ⟨147500043445963703258831321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98333362297309135505887547 147500043445963703258831321)
  ·
    refine ⟨110625032584472777444123491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147500043445963703258831321 110625032584472777444123491)
    ·
      refine ⟨165937548876709166166185237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110625032584472777444123491 165937548876709166166185237)
      ·
        refine ⟨7778322603595742164039933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165937548876709166166185237 7778322603595742164039933)
        ·
          refine ⟨2916870976348403311514975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7778322603595742164039933 2916870976348403311514975)
          ·
            refine ⟨4375306464522604967272463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916870976348403311514975 4375306464522604967272463)
            ·
              refine ⟨6562959696783907450908695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375306464522604967272463 6562959696783907450908695)
              ·
                refine ⟨9844439545175861176363043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562959696783907450908695 9844439545175861176363043)
                ·
                  refine ⟨14766659317763791764544565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9844439545175861176363043 14766659317763791764544565)
                  ·
                    refine ⟨1384374311040355477926053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14766659317763791764544565 1384374311040355477926053)
                    ·
                      rfl

theorem cell22_4044089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_4044089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044089 prefixEnd_4044089 := by exact prefixLift 4044089
  have htrace : WordTrace (prefixWord ++ tailWord_4044089) baseStart_4044089 baseEnd_4044089 := by
    simpa [prefixWord, tailWord_4044089, baseEnd_4044089] using wordTrace_append hprefix tailTrace_4044089
  have hstable : (prefixWord ++ tailWord_4044089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044089).length < 2 ^ (prefixWord ++ tailWord_4044089).sum := by decide
  have hdescent : baseEnd_4044089 < baseStart_4044089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044113 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 9]
def baseStart_4044113 : Nat := 118140960795 + 4044113 * 2 ^ 59
def prefixEnd_4044113 : Nat := 4983230072969 + 3 ^ 40 * 4044113 * 2
def baseEnd_4044113 : Nat := 461460842243609138441993

theorem tailTrace_4044113 : CollatzResearch.WordTrace tailWord_4044113 prefixEnd_4044113 461460842243609138441993 := by
  unfold tailWord_4044113
  simp only [CollatzResearch.WordTrace]
  refine ⟨147500918797876755357704993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98333945865251170238469995 147500918797876755357704993)
  ·
    refine ⟨110625689098407566518278745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147500918797876755357704993 110625689098407566518278745)
    ·
      refine ⟨82969266823805674888709059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110625689098407566518278745 82969266823805674888709059)
      ·
        refine ⟨124453900235708512333063589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82969266823805674888709059 124453900235708512333063589)
        ·
          refine ⟨23335106294195346062449423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124453900235708512333063589 23335106294195346062449423)
          ·
            refine ⟨35002659441293019093674135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23335106294195346062449423 35002659441293019093674135)
            ·
              refine ⟨52503989161939528640511203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35002659441293019093674135 52503989161939528640511203)
              ·
                refine ⟨78755983742909292960766805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52503989161939528640511203 78755983742909292960766805)
                ·
                  refine ⟨461460842243609138441993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78755983742909292960766805 461460842243609138441993)
                  ·
                    rfl

theorem cell22_4044113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_4044113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044113 prefixEnd_4044113 := by exact prefixLift 4044113
  have htrace : WordTrace (prefixWord ++ tailWord_4044113) baseStart_4044113 baseEnd_4044113 := by
    simpa [prefixWord, tailWord_4044113, baseEnd_4044113] using wordTrace_append hprefix tailTrace_4044113
  have hstable : (prefixWord ++ tailWord_4044113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044113).length < 2 ^ (prefixWord ++ tailWord_4044113).sum := by decide
  have hdescent : baseEnd_4044113 < baseStart_4044113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044130 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_4044130 : Nat := 118140960795 + 4044130 * 2 ^ 59
def prefixEnd_4044130 : Nat := 4983230072969 + 3 ^ 40 * 4044130 * 2
def baseEnd_4044130 : Nat := 461462782059415012550309

theorem tailTrace_4044130 : CollatzResearch.WordTrace tailWord_4044130 prefixEnd_4044130 461462782059415012550309 := by
  unfold tailWord_4044130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36875384709703791815268461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98334359225876778174049229 36875384709703791815268461)
  ·
    refine ⟨13828269266138921930725673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36875384709703791815268461 13828269266138921930725673)
    ·
      refine ⟨10371201949604191448044255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13828269266138921930725673 10371201949604191448044255)
      ·
        refine ⟨15556802924406287172066383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371201949604191448044255 15556802924406287172066383)
        ·
          refine ⟨23335204386609430758099575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556802924406287172066383 23335204386609430758099575)
          ·
            refine ⟨35002806579914146137149363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23335204386609430758099575 35002806579914146137149363)
            ·
              refine ⟨52504209869871219205724045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35002806579914146137149363 52504209869871219205724045)
              ·
                refine ⟨19689078701201707202146517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52504209869871219205724045 19689078701201707202146517)
                ·
                  refine ⟨461462782059415012550309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19689078701201707202146517 461462782059415012550309)
                  ·
                    rfl

theorem cell22_4044130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_4044130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044130 prefixEnd_4044130 := by exact prefixLift 4044130
  have htrace : WordTrace (prefixWord ++ tailWord_4044130) baseStart_4044130 baseEnd_4044130 := by
    simpa [prefixWord, tailWord_4044130, baseEnd_4044130] using wordTrace_append hprefix tailTrace_4044130
  have hstable : (prefixWord ++ tailWord_4044130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044130).length < 2 ^ (prefixWord ++ tailWord_4044130).sum := by decide
  have hdescent : baseEnd_4044130 < baseStart_4044130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044192 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 4]
def baseStart_4044192 : Nat := 118140960795 + 4044192 * 2 ^ 59
def prefixEnd_4044192 : Nat := 4983230072969 + 3 ^ 40 * 4044192 * 2
def baseEnd_4044192 : Nat := 461469856681765847533579

theorem tailTrace_4044192 : CollatzResearch.WordTrace tailWord_4044192 prefixEnd_4044192 461469856681765847533579 := by
  unfold tailWord_4044192
  simp only [CollatzResearch.WordTrace]
  refine ⟨73751900082295275924915415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98335866776393701233220553 73751900082295275924915415)
  ·
    refine ⟨110627850123442913887373123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73751900082295275924915415 110627850123442913887373123)
    ·
      refine ⟨165941775185164370831059685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110627850123442913887373123 165941775185164370831059685)
      ·
        refine ⟨31114082847218319530823691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165941775185164370831059685 31114082847218319530823691)
        ·
          refine ⟨46671124270827479296235537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31114082847218319530823691 46671124270827479296235537)
          ·
            refine ⟨35003343203120609472176653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46671124270827479296235537 35003343203120609472176653)
            ·
              refine ⟨13126253701170228552066245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35003343203120609472176653 13126253701170228552066245)
              ·
                refine ⟨2461172568969417853512421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13126253701170228552066245 2461172568969417853512421)
                ·
                  refine ⟨461469856681765847533579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461172568969417853512421 461469856681765847533579)
                  ·
                    rfl

theorem cell22_4044192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_4044192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044192 prefixEnd_4044192 := by exact prefixLift 4044192
  have htrace : WordTrace (prefixWord ++ tailWord_4044192) baseStart_4044192 baseEnd_4044192 := by
    simpa [prefixWord, tailWord_4044192, baseEnd_4044192] using wordTrace_append hprefix tailTrace_4044192
  have hstable : (prefixWord ++ tailWord_4044192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044192).length < 2 ^ (prefixWord ++ tailWord_4044192).sum := by decide
  have hdescent : baseEnd_4044192 < baseStart_4044192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044357 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_4044357 : Nat := 118140960795 + 4044357 * 2 ^ 59
def prefixEnd_4044357 : Nat := 4983230072969 + 3 ^ 40 * 4044357 * 2
def baseEnd_4044357 : Nat := 1384466052917292112225231

theorem tailTrace_4044357 : CollatzResearch.WordTrace tailWord_4044357 prefixEnd_4044357 1384466052917292112225231 := by
  unfold tailWord_4044357
  simp only [CollatzResearch.WordTrace]
  refine ⟨147509818208992785029587325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98339878805995190019724883 147509818208992785029587325)
  ·
    refine ⟨55316181828372294386095247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147509818208992785029587325 55316181828372294386095247)
    ·
      refine ⟨82974272742558441579142871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55316181828372294386095247 82974272742558441579142871)
      ·
        refine ⟨124461409113837662368714307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82974272742558441579142871 124461409113837662368714307)
        ·
          refine ⟨186692113670756493553071461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124461409113837662368714307 186692113670756493553071461)
          ·
            refine ⟨35004771313266842541200899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186692113670756493553071461 35004771313266842541200899)
            ·
              refine ⟨52507156969900263811801349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35004771313266842541200899 52507156969900263811801349)
              ·
                refine ⟨9845091931856299464712753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52507156969900263811801349 9845091931856299464712753)
                ·
                  refine ⟨7383818948892224598534565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9845091931856299464712753 7383818948892224598534565)
                  ·
                    refine ⟨1384466052917292112225231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383818948892224598534565 1384466052917292112225231)
                    ·
                      rfl

theorem cell22_4044357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_4044357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044357 prefixEnd_4044357 := by exact prefixLift 4044357
  have htrace : WordTrace (prefixWord ++ tailWord_4044357) baseStart_4044357 baseEnd_4044357 := by
    simpa [prefixWord, tailWord_4044357, baseEnd_4044357] using wordTrace_append hprefix tailTrace_4044357
  have hstable : (prefixWord ++ tailWord_4044357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044357).length < 2 ^ (prefixWord ++ tailWord_4044357).sum := by decide
  have hdescent : baseEnd_4044357 < baseStart_4044357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044389 : List Nat := [1, 3, 1, 3, 3, 2, 3, 6]
def baseStart_4044389 : Nat := 118140960795 + 4044389 * 2 ^ 59
def prefixEnd_4044389 : Nat := 4983230072969 + 3 ^ 40 * 4044389 * 2
def baseEnd_4044389 : Nat := 153830778574583855047237

theorem tailTrace_4044389 : CollatzResearch.WordTrace tailWord_4044389 prefixEnd_4044389 153830778574583855047237 := by
  unfold tailWord_4044389
  simp only [CollatzResearch.WordTrace]
  refine ⟨147510985344876854494752221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98340656896584569663168147 147510985344876854494752221)
  ·
    refine ⟨55316619504328820435532083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147510985344876854494752221 55316619504328820435532083)
    ·
      refine ⟨82974929256493230653298125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55316619504328820435532083 82974929256493230653298125)
      ·
        refine ⟨31115598471184961494986797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82974929256493230653298125 31115598471184961494986797)
        ·
          refine ⟨11668349426694360560620049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31115598471184961494986797 11668349426694360560620049)
          ·
            refine ⟨8751262070020770420465037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11668349426694360560620049 8751262070020770420465037)
            ·
              refine ⟨3281723276257788907674389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8751262070020770420465037 3281723276257788907674389)
              ·
                refine ⟨153830778574583855047237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3281723276257788907674389 153830778574583855047237)
                ·
                  rfl

theorem cell22_4044389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 6].length) (baseStart_4044389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044389 prefixEnd_4044389 := by exact prefixLift 4044389
  have htrace : WordTrace (prefixWord ++ tailWord_4044389) baseStart_4044389 baseEnd_4044389 := by
    simpa [prefixWord, tailWord_4044389, baseEnd_4044389] using wordTrace_append hprefix tailTrace_4044389
  have hstable : (prefixWord ++ tailWord_4044389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044389).length < 2 ^ (prefixWord ++ tailWord_4044389).sum := by decide
  have hdescent : baseEnd_4044389 < baseStart_4044389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044421 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_4044421 : Nat := 118140960795 + 4044421 * 2 ^ 59
def prefixEnd_4044421 : Nat := 4983230072969 + 3 ^ 40 * 4044421 * 2
def baseEnd_4044421 : Nat := 1384487961425217278625035

theorem tailTrace_4044421 : CollatzResearch.WordTrace tailWord_4044421 prefixEnd_4044421 1384487961425217278625035 := by
  unfold tailWord_4044421
  simp only [CollatzResearch.WordTrace]
  refine ⟨147512152480760923959917117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98341434987173949306611411 147512152480760923959917117)
  ·
    refine ⟨55317057180285346484968919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147512152480760923959917117 55317057180285346484968919)
    ·
      refine ⟨82975585770428019727453379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55317057180285346484968919 82975585770428019727453379)
      ·
        refine ⟨124463378655642029591180069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82975585770428019727453379 124463378655642029591180069)
        ·
          refine ⟨23336883497932880548346263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124463378655642029591180069 23336883497932880548346263)
          ·
            refine ⟨35005325246899320822519395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23336883497932880548346263 35005325246899320822519395)
            ·
              refine ⟨52507987870348981233779093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35005325246899320822519395 52507987870348981233779093)
              ·
                refine ⟨2461311931422608495333395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52507987870348981233779093 2461311931422608495333395)
                ·
                  refine ⟨3691967897133912743000093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461311931422608495333395 3691967897133912743000093)
                  ·
                    refine ⟨1384487961425217278625035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691967897133912743000093 1384487961425217278625035)
                    ·
                      rfl

theorem cell22_4044421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_4044421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044421 prefixEnd_4044421 := by exact prefixLift 4044421
  have htrace : WordTrace (prefixWord ++ tailWord_4044421) baseStart_4044421 baseEnd_4044421 := by
    simpa [prefixWord, tailWord_4044421, baseEnd_4044421] using wordTrace_append hprefix tailTrace_4044421
  have hstable : (prefixWord ++ tailWord_4044421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044421).length < 2 ^ (prefixWord ++ tailWord_4044421).sum := by decide
  have hdescent : baseEnd_4044421 < baseStart_4044421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044464 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_4044464 : Nat := 118140960795 + 4044464 * 2 ^ 59
def prefixEnd_4044464 : Nat := 4983230072969 + 3 ^ 40 * 4044464 * 2
def baseEnd_4044464 : Nat := 1384502681203979499799903

theorem tailTrace_4044464 : CollatzResearch.WordTrace tailWord_4044464 prefixEnd_4044464 1384502681203979499799903 := by
  unfold tailWord_4044464
  simp only [CollatzResearch.WordTrace]
  refine ⟨73756860409802571151866223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98342480546403428202488297 73756860409802571151866223)
  ·
    refine ⟨110635290614703856727799335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73756860409802571151866223 110635290614703856727799335)
    ·
      refine ⟨165952935922055785091699003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110635290614703856727799335 165952935922055785091699003)
      ·
        refine ⟨248929403883083677637548505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165952935922055785091699003 248929403883083677637548505)
        ·
          refine ⟨186697052912312758228161379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248929403883083677637548505 186697052912312758228161379)
          ·
            refine ⟨280045579368469137342242069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186697052912312758228161379 280045579368469137342242069)
            ·
              refine ⟨13127136532896990812917597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 280045579368469137342242069 13127136532896990812917597)
              ·
                refine ⟨4922676199836371554844099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13127136532896990812917597 4922676199836371554844099)
                ·
                  refine ⟨7384014299754557332266149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922676199836371554844099 7384014299754557332266149)
                  ·
                    refine ⟨1384502681203979499799903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384014299754557332266149 1384502681203979499799903)
                    ·
                      rfl

theorem cell22_4044464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_4044464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044464 prefixEnd_4044464 := by exact prefixLift 4044464
  have htrace : WordTrace (prefixWord ++ tailWord_4044464) baseStart_4044464 baseEnd_4044464 := by
    simpa [prefixWord, tailWord_4044464, baseEnd_4044464] using wordTrace_append hprefix tailTrace_4044464
  have hstable : (prefixWord ++ tailWord_4044464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044464).length < 2 ^ (prefixWord ++ tailWord_4044464).sum := by decide
  have hdescent : baseEnd_4044464 < baseStart_4044464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044494 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_4044494 : Nat := 118140960795 + 4044494 * 2 ^ 59
def prefixEnd_4044494 : Nat := 4983230072969 + 3 ^ 40 * 4044494 * 2
def baseEnd_4044494 : Nat := 1384512950817069421549811

theorem tailTrace_4044494 : CollatzResearch.WordTrace tailWord_4044494 prefixEnd_4044494 1384512950817069421549811 := by
  unfold tailWord_4044494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18439351876187057178415567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98343210006330971618216357 18439351876187057178415567)
  ·
    refine ⟨27659027814280585767623351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18439351876187057178415567 27659027814280585767623351)
    ·
      refine ⟨41488541721420878651435027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27659027814280585767623351 41488541721420878651435027)
      ·
        refine ⟨62232812582131317977152541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41488541721420878651435027 62232812582131317977152541)
        ·
          refine ⟨23337304718299244241432203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62232812582131317977152541 23337304718299244241432203)
          ·
            refine ⟨35005957077448866362148305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23337304718299244241432203 35005957077448866362148305)
            ·
              refine ⟨26254467808086649771611229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35005957077448866362148305 26254467808086649771611229)
              ·
                refine ⟨9845425428032493664354211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26254467808086649771611229 9845425428032493664354211)
                ·
                  refine ⟨14768138142048740496531317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9845425428032493664354211 14768138142048740496531317)
                  ·
                    refine ⟨1384512950817069421549811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14768138142048740496531317 1384512950817069421549811)
                    ·
                      rfl

theorem cell22_4044494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_4044494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044494 prefixEnd_4044494 := by exact prefixLift 4044494
  have htrace : WordTrace (prefixWord ++ tailWord_4044494) baseStart_4044494 baseEnd_4044494 := by
    simpa [prefixWord, tailWord_4044494, baseEnd_4044494] using wordTrace_append hprefix tailTrace_4044494
  have hstable : (prefixWord ++ tailWord_4044494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044494).length < 2 ^ (prefixWord ++ tailWord_4044494).sum := by decide
  have hdescent : baseEnd_4044494 < baseStart_4044494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044498 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_4044498 : Nat := 118140960795 + 4044498 * 2 ^ 59
def prefixEnd_4044498 : Nat := 4983230072969 + 3 ^ 40 * 4044498 * 2
def baseEnd_4044498 : Nat := 1384514320098814744449799

theorem tailTrace_4044498 : CollatzResearch.WordTrace tailWord_4044498 prefixEnd_4044498 1384514320098814744449799 := by
  unfold tailWord_4044498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36878740225370491527617537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98343307267654644073646765 36878740225370491527617537)
  ·
    refine ⟨27659055169027868645713153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36878740225370491527617537 27659055169027868645713153)
    ·
      refine ⟨20744291376770901484284865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27659055169027868645713153 20744291376770901484284865)
      ·
        refine ⟨15558218532578176113213649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20744291376770901484284865 15558218532578176113213649)
        ·
          refine ⟨11668663899433632084910237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15558218532578176113213649 11668663899433632084910237)
          ·
            refine ⟨4375748962287612031841339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11668663899433632084910237 4375748962287612031841339)
            ·
              refine ⟨6563623443431418047762009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375748962287612031841339 6563623443431418047762009)
              ·
                refine ⟨4922717582573563535821507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6563623443431418047762009 4922717582573563535821507)
                ·
                  refine ⟨7384076373860345303732261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922717582573563535821507 7384076373860345303732261)
                  ·
                    refine ⟨1384514320098814744449799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384076373860345303732261 1384514320098814744449799)
                    ·
                      rfl

theorem cell22_4044498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_4044498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044498 prefixEnd_4044498 := by exact prefixLift 4044498
  have htrace : WordTrace (prefixWord ++ tailWord_4044498) baseStart_4044498 baseEnd_4044498 := by
    simpa [prefixWord, tailWord_4044498, baseEnd_4044498] using wordTrace_append hprefix tailTrace_4044498
  have hstable : (prefixWord ++ tailWord_4044498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044498).length < 2 ^ (prefixWord ++ tailWord_4044498).sum := by decide
  have hdescent : baseEnd_4044498 < baseStart_4044498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044590 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_4044590 : Nat := 118140960795 + 4044590 * 2 ^ 59
def prefixEnd_4044590 : Nat := 4983230072969 + 3 ^ 40 * 4044590 * 2
def baseEnd_4044590 : Nat := 1384545813578957171149517

theorem tailTrace_4044590 : CollatzResearch.WordTrace tailWord_4044590 prefixEnd_4044590 1384545813578957171149517 := by
  unfold tailWord_4044590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18439789552143583227852403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98345544278099110548546149 18439789552143583227852403)
  ·
    refine ⟨27659684328215374841778605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18439789552143583227852403 27659684328215374841778605)
    ·
      refine ⟨10372381623080765565666977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27659684328215374841778605 10372381623080765565666977)
      ·
        refine ⟨7779286217310574174250233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10372381623080765565666977 7779286217310574174250233)
        ·
          refine ⟨5834464662982930630687675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7779286217310574174250233 5834464662982930630687675)
          ·
            refine ⟨8751696994474395946031513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834464662982930630687675 8751696994474395946031513)
            ·
              refine ⟨6563772745855796959523635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8751696994474395946031513 6563772745855796959523635)
              ·
                refine ⟨9845659118783695439285453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563772745855796959523635 9845659118783695439285453)
                ·
                  refine ⟨3692122169543885789732045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9845659118783695439285453 3692122169543885789732045)
                  ·
                    refine ⟨1384545813578957171149517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3692122169543885789732045 1384545813578957171149517)
                    ·
                      rfl

theorem cell22_4044590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_4044590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044590 prefixEnd_4044590 := by exact prefixLift 4044590
  have htrace : WordTrace (prefixWord ++ tailWord_4044590) baseStart_4044590 baseEnd_4044590 := by
    simpa [prefixWord, tailWord_4044590, baseEnd_4044590] using wordTrace_append hprefix tailTrace_4044590
  have hstable : (prefixWord ++ tailWord_4044590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044590).length < 2 ^ (prefixWord ++ tailWord_4044590).sum := by decide
  have hdescent : baseEnd_4044590 < baseStart_4044590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044599 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 3, 4]
def baseStart_4044599 : Nat := 118140960795 + 4044599 * 2 ^ 59
def prefixEnd_4044599 : Nat := 4983230072969 + 3 ^ 40 * 4044599 * 2
def baseEnd_4044599 : Nat := 1384548894462884147674489

theorem tailTrace_4044599 : CollatzResearch.WordTrace tailWord_4044599 prefixEnd_4044599 1384548894462884147674489 := by
  unfold tailWord_4044599
  simp only [CollatzResearch.WordTrace]
  refine ⟨147518644674116060359896851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98345763116077373573264567 147518644674116060359896851)
  ·
    refine ⟨221277967011174090539845277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147518644674116060359896851 221277967011174090539845277)
    ·
      refine ⟨82979237629190283952441979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221277967011174090539845277 82979237629190283952441979)
      ·
        refine ⟨124468856443785425928662969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82979237629190283952441979 124468856443785425928662969)
        ·
          refine ⟨93351642332839069446497227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124468856443785425928662969 93351642332839069446497227)
          ·
            refine ⟨140027463499258604169745841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93351642332839069446497227 140027463499258604169745841)
            ·
              refine ⟨105020597624443953127309381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140027463499258604169745841 105020597624443953127309381)
              ·
                refine ⟨19691362054583241211370509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105020597624443953127309381 19691362054583241211370509)
                ·
                  refine ⟨7384260770468715454263941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19691362054583241211370509 7384260770468715454263941)
                  ·
                    refine ⟨1384548894462884147674489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384260770468715454263941 1384548894462884147674489)
                    ·
                      rfl

theorem cell22_4044599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_4044599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044599 prefixEnd_4044599 := by exact prefixLift 4044599
  have htrace : WordTrace (prefixWord ++ tailWord_4044599) baseStart_4044599 baseEnd_4044599 := by
    simpa [prefixWord, tailWord_4044599, baseEnd_4044599] using wordTrace_append hprefix tailTrace_4044599
  have hstable : (prefixWord ++ tailWord_4044599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044599).length < 2 ^ (prefixWord ++ tailWord_4044599).sum := by decide
  have hdescent : baseEnd_4044599 < baseStart_4044599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044616 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_4044616 : Nat := 118140960795 + 4044616 * 2 ^ 59
def prefixEnd_4044616 : Nat := 4983230072969 + 3 ^ 40 * 4044616 * 2
def baseEnd_4044616 : Nat := 1384554713910301769999437

theorem tailTrace_4044616 : CollatzResearch.WordTrace tailWord_4044616 prefixEnd_4044616 1384554713910301769999437 := by
  unfold tailWord_4044616
  simp only [CollatzResearch.WordTrace]
  refine ⟨73759632357527236131632851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98346176476702981508843801 73759632357527236131632851)
  ·
    refine ⟨110639448536290854197449277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73759632357527236131632851 110639448536290854197449277)
    ·
      refine ⟨41489793201109070324043479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110639448536290854197449277 41489793201109070324043479)
      ·
        refine ⟨62234689801663605486065219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41489793201109070324043479 62234689801663605486065219)
        ·
          refine ⟨93352034702495408229097829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62234689801663605486065219 93352034702495408229097829)
          ·
            refine ⟨17503506506717889042955843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93352034702495408229097829 17503506506717889042955843)
            ·
              refine ⟨26255259760076833564433765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17503506506717889042955843 26255259760076833564433765)
              ·
                refine ⟨4922861205014406293331331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26255259760076833564433765 4922861205014406293331331)
                ·
                  refine ⟨7384291807521609439996997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922861205014406293331331 7384291807521609439996997)
                  ·
                    refine ⟨1384554713910301769999437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384291807521609439996997 1384554713910301769999437)
                    ·
                      rfl

theorem cell22_4044616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_4044616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044616 prefixEnd_4044616 := by exact prefixLift 4044616
  have htrace : WordTrace (prefixWord ++ tailWord_4044616) baseStart_4044616 baseEnd_4044616 := by
    simpa [prefixWord, tailWord_4044616, baseEnd_4044616] using wordTrace_append hprefix tailTrace_4044616
  have hstable : (prefixWord ++ tailWord_4044616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044616).length < 2 ^ (prefixWord ++ tailWord_4044616).sum := by decide
  have hdescent : baseEnd_4044616 < baseStart_4044616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044661 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4044661 : Nat := 118140960795 + 4044661 * 2 ^ 59
def prefixEnd_4044661 : Nat := 4983230072969 + 3 ^ 40 * 4044661 * 2
def baseEnd_4044661 : Nat := 1384570118329936652624299

theorem tailTrace_4044661 : CollatzResearch.WordTrace tailWord_4044661 prefixEnd_4044661 1384570118329936652624299 := by
  unfold tailWord_4044661
  simp only [CollatzResearch.WordTrace]
  refine ⟨147520905999891444948653837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98347270666594296632435891 147520905999891444948653837)
  ·
    refine ⟨55320339749959291855745189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147520905999891444948653837 55320339749959291855745189)
    ·
      refine ⟨10372563703117367222952223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55320339749959291855745189 10372563703117367222952223)
      ·
        refine ⟨15558845554676050834428335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10372563703117367222952223 15558845554676050834428335)
        ·
          refine ⟨23338268332014076251642503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15558845554676050834428335 23338268332014076251642503)
          ·
            refine ⟨35007402498021114377463755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23338268332014076251642503 35007402498021114377463755)
            ·
              refine ⟨52511103747031671566195633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35007402498021114377463755 52511103747031671566195633)
              ·
                refine ⟨39383327810273753674646725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52511103747031671566195633 39383327810273753674646725)
                ·
                  refine ⟨7384373964426328813996261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39383327810273753674646725 7384373964426328813996261)
                  ·
                    refine ⟨1384570118329936652624299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384373964426328813996261 1384570118329936652624299)
                    ·
                      rfl

theorem cell22_4044661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4044661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044661 prefixEnd_4044661 := by exact prefixLift 4044661
  have htrace : WordTrace (prefixWord ++ tailWord_4044661) baseStart_4044661 baseEnd_4044661 := by
    simpa [prefixWord, tailWord_4044661, baseEnd_4044661] using wordTrace_append hprefix tailTrace_4044661
  have hstable : (prefixWord ++ tailWord_4044661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044661).length < 2 ^ (prefixWord ++ tailWord_4044661).sum := by decide
  have hdescent : baseEnd_4044661 < baseStart_4044661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044785 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_4044785 : Nat := 118140960795 + 4044785 * 2 ^ 59
def prefixEnd_4044785 : Nat := 4983230072969 + 3 ^ 40 * 4044785 * 2
def baseEnd_4044785 : Nat := 1384612566064041662523919

theorem tailTrace_4044785 : CollatzResearch.WordTrace tailWord_4044785 prefixEnd_4044785 1384612566064041662523919 := by
  unfold tailWord_4044785
  simp only [CollatzResearch.WordTrace]
  refine ⟨147525428651442214126167809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98350285767628142750778539 147525428651442214126167809)
  ·
    refine ⟨110644071488581660594625857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147525428651442214126167809 110644071488581660594625857)
    ·
      refine ⟨82983053616436245445969393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110644071488581660594625857 82983053616436245445969393)
      ·
        refine ⟨62237290212327184084477045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82983053616436245445969393 62237290212327184084477045)
        ·
          refine ⟨5834745957405673507919723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62237290212327184084477045 5834745957405673507919723)
          ·
            refine ⟨8752118936108510261879585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834745957405673507919723 8752118936108510261879585)
            ·
              refine ⟨6564089202081382696409689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8752118936108510261879585 6564089202081382696409689)
              ·
                refine ⟨4923066901561037022307267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6564089202081382696409689 4923066901561037022307267)
                ·
                  refine ⟨7384600352341555533460901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923066901561037022307267 7384600352341555533460901)
                  ·
                    refine ⟨1384612566064041662523919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384600352341555533460901 1384612566064041662523919)
                    ·
                      rfl

theorem cell22_4044785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_4044785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044785 prefixEnd_4044785 := by exact prefixLift 4044785
  have htrace : WordTrace (prefixWord ++ tailWord_4044785) baseStart_4044785 baseEnd_4044785 := by
    simpa [prefixWord, tailWord_4044785, baseEnd_4044785] using wordTrace_append hprefix tailTrace_4044785
  have hstable : (prefixWord ++ tailWord_4044785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044785).length < 2 ^ (prefixWord ++ tailWord_4044785).sum := by decide
  have hdescent : baseEnd_4044785 < baseStart_4044785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044796 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_4044796 : Nat := 118140960795 + 4044796 * 2 ^ 59
def prefixEnd_4044796 : Nat := 4983230072969 + 3 ^ 40 * 4044796 * 2
def baseEnd_4044796 : Nat := 1384616331588841300498885

theorem tailTrace_4044796 : CollatzResearch.WordTrace tailWord_4044796 prefixEnd_4044796 1384616331588841300498885 := by
  unfold tailWord_4044796
  simp only [CollatzResearch.WordTrace]
  refine ⟨73762914927201181502409121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98350553236268242003212161 73762914927201181502409121)
  ·
    refine ⟨55322186195400886126806841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73762914927201181502409121 55322186195400886126806841)
    ·
      refine ⟨41491639646550664595105131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55322186195400886126806841 41491639646550664595105131)
      ·
        refine ⟨62237459469825996892657697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41491639646550664595105131 62237459469825996892657697)
        ·
          refine ⟨46678094602369497669493273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62237459469825996892657697 46678094602369497669493273)
          ·
            refine ⟨35008570951777123252119955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46678094602369497669493273 35008570951777123252119955)
            ·
              refine ⟨52512856427665684878179933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35008570951777123252119955 52512856427665684878179933)
              ·
                refine ⟨19692321160374631829317475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52512856427665684878179933 19692321160374631829317475)
                ·
                  refine ⟨29538481740561947743976213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19692321160374631829317475 29538481740561947743976213)
                  ·
                    refine ⟨1384616331588841300498885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29538481740561947743976213 1384616331588841300498885)
                    ·
                      rfl

theorem cell22_4044796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_4044796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044796 prefixEnd_4044796 := by exact prefixLift 4044796
  have htrace : WordTrace (prefixWord ++ tailWord_4044796) baseStart_4044796 baseEnd_4044796 := by
    simpa [prefixWord, tailWord_4044796, baseEnd_4044796] using wordTrace_append hprefix tailTrace_4044796
  have hstable : (prefixWord ++ tailWord_4044796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044796).length < 2 ^ (prefixWord ++ tailWord_4044796).sum := by decide
  have hdescent : baseEnd_4044796 < baseStart_4044796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044828 : List Nat := [2, 2, 3, 1, 3, 2, 2, 7]
def baseStart_4044828 : Nat := 118140960795 + 4044828 * 2 ^ 59
def prefixEnd_4044828 : Nat := 4983230072969 + 3 ^ 40 * 4044828 * 2
def baseEnd_4044828 : Nat := 153847476204755987077643

theorem tailTrace_4044828 : CollatzResearch.WordTrace tailWord_4044828 prefixEnd_4044828 153847476204755987077643 := by
  unfold tailWord_4044828
  simp only [CollatzResearch.WordTrace]
  refine ⟨73763498495143216234991569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98351331326857621646655425 73763498495143216234991569)
  ·
    refine ⟨55322623871357412176243677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73763498495143216234991569 55322623871357412176243677)
    ·
      refine ⟨20745983951759029566091379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55322623871357412176243677 20745983951759029566091379)
      ·
        refine ⟨31118975927638544349137069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20745983951759029566091379 31118975927638544349137069)
        ·
          refine ⟨11669615972864454130926401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31118975927638544349137069 11669615972864454130926401)
          ·
            refine ⟨8752211979648340598194801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11669615972864454130926401 8752211979648340598194801)
            ·
              refine ⟨6564158984736255448646101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8752211979648340598194801 6564158984736255448646101)
              ·
                refine ⟨153847476204755987077643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6564158984736255448646101 153847476204755987077643)
                ·
                  rfl

theorem cell22_4044828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_4044828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044828 prefixEnd_4044828 := by exact prefixLift 4044828
  have htrace : WordTrace (prefixWord ++ tailWord_4044828) baseStart_4044828 baseEnd_4044828 := by
    simpa [prefixWord, tailWord_4044828, baseEnd_4044828] using wordTrace_append hprefix tailTrace_4044828
  have hstable : (prefixWord ++ tailWord_4044828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044828).length < 2 ^ (prefixWord ++ tailWord_4044828).sum := by decide
  have hdescent : baseEnd_4044828 < baseStart_4044828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044873 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 5]
def baseStart_4044873 : Nat := 118140960795 + 4044873 * 2 ^ 59
def prefixEnd_4044873 : Nat := 4983230072969 + 3 ^ 40 * 4044873 * 2
def baseEnd_4044873 : Nat := 461547563420812922107883

theorem tailTrace_4044873 : CollatzResearch.WordTrace tailWord_4044873 prefixEnd_4044873 461547563420812922107883 := by
  unfold tailWord_4044873
  simp only [CollatzResearch.WordTrace]
  refine ⟨147528638275123405155371273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98352425516748936770247515 147528638275123405155371273)
  ·
    refine ⟨110646478706342553866528455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147528638275123405155371273 110646478706342553866528455)
    ·
      refine ⟨165969718059513830799792683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110646478706342553866528455 165969718059513830799792683)
      ·
        refine ⟨248954577089270746199689025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165969718059513830799792683 248954577089270746199689025)
        ·
          refine ⟨186715932816953059649766769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248954577089270746199689025 186715932816953059649766769)
          ·
            refine ⟨140036949612714794737325077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186715932816953059649766769 140036949612714794737325077)
            ·
              refine ⟨6564232013096006003312113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140036949612714794737325077 6564232013096006003312113)
              ·
                refine ⟨4923174009822004502484085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6564232013096006003312113 4923174009822004502484085)
                ·
                  refine ⟨461547563420812922107883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4923174009822004502484085 461547563420812922107883)
                  ·
                    rfl

theorem cell22_4044873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_4044873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044873 prefixEnd_4044873 := by exact prefixLift 4044873
  have htrace : WordTrace (prefixWord ++ tailWord_4044873) baseStart_4044873 baseEnd_4044873 := by
    simpa [prefixWord, tailWord_4044873, baseEnd_4044873] using wordTrace_append hprefix tailTrace_4044873
  have hstable : (prefixWord ++ tailWord_4044873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044873).length < 2 ^ (prefixWord ++ tailWord_4044873).sum := by decide
  have hdescent : baseEnd_4044873 < baseStart_4044873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044888 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_4044888 : Nat := 118140960795 + 4044888 * 2 ^ 59
def prefixEnd_4044888 : Nat := 4983230072969 + 3 ^ 40 * 4044888 * 2
def baseEnd_4044888 : Nat := 1384647825068983727198603

theorem tailTrace_4044888 : CollatzResearch.WordTrace tailWord_4044888 prefixEnd_4044888 1384647825068983727198603 := by
  unfold tailWord_4044888
  simp only [CollatzResearch.WordTrace]
  refine ⟨73764592685034531358583659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98352790246712708478111545 73764592685034531358583659)
  ·
    refine ⟨110646889027551797037875489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73764592685034531358583659 110646889027551797037875489)
    ·
      refine ⟨82985166770663847778406617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110646889027551797037875489 82985166770663847778406617)
      ·
        refine ⟨62238875077997885833804963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82985166770663847778406617 62238875077997885833804963)
        ·
          refine ⟨93358312616996828750707445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62238875077997885833804963 93358312616996828750707445)
          ·
            refine ⟨8752341807843452695378823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93358312616996828750707445 8752341807843452695378823)
            ·
              refine ⟨13128512711765179043068235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752341807843452695378823 13128512711765179043068235)
              ·
                refine ⟨19692769067647768564602353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13128512711765179043068235 19692769067647768564602353)
                ·
                  refine ⟨14769576800735826423451765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19692769067647768564602353 14769576800735826423451765)
                  ·
                    refine ⟨1384647825068983727198603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14769576800735826423451765 1384647825068983727198603)
                    ·
                      rfl

theorem cell22_4044888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_4044888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044888 prefixEnd_4044888 := by exact prefixLift 4044888
  have htrace : WordTrace (prefixWord ++ tailWord_4044888) baseStart_4044888 baseEnd_4044888 := by
    simpa [prefixWord, tailWord_4044888, baseEnd_4044888] using wordTrace_append hprefix tailTrace_4044888
  have hstable : (prefixWord ++ tailWord_4044888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044888).length < 2 ^ (prefixWord ++ tailWord_4044888).sum := by decide
  have hdescent : baseEnd_4044888 < baseStart_4044888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044903 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4044903 : Nat := 118140960795 + 4044903 * 2 ^ 59
def prefixEnd_4044903 : Nat := 4983230072969 + 3 ^ 40 * 4044903 * 2
def baseEnd_4044903 : Nat := 1384652959875528688073557

theorem tailTrace_4044903 : CollatzResearch.WordTrace tailWord_4044903 prefixEnd_4044903 1384652959875528688073557 := by
  unfold tailWord_4044903
  simp only [CollatzResearch.WordTrace]
  refine ⟨147529732465014720278963363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98353154976676480185975575 147529732465014720278963363)
  ·
    refine ⟨221294598697522080418445045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147529732465014720278963363 221294598697522080418445045)
    ·
      refine ⟨20746368627892695039229223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221294598697522080418445045 20746368627892695039229223)
      ·
        refine ⟨31119552941839042558843835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20746368627892695039229223 31119552941839042558843835)
        ·
          refine ⟨46679329412758563838265753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31119552941839042558843835 46679329412758563838265753)
          ·
            refine ⟨35009497059568922878699315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46679329412758563838265753 35009497059568922878699315)
            ·
              refine ⟨52514245589353384318048973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35009497059568922878699315 52514245589353384318048973)
              ·
                refine ⟨19692842096007519119268365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52514245589353384318048973 19692842096007519119268365)
                ·
                  refine ⟨7384815786002819669725637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19692842096007519119268365 7384815786002819669725637)
                  ·
                    refine ⟨1384652959875528688073557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384815786002819669725637 1384652959875528688073557)
                    ·
                      rfl

theorem cell22_4044903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4044903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044903 prefixEnd_4044903 := by exact prefixLift 4044903
  have htrace : WordTrace (prefixWord ++ tailWord_4044903) baseStart_4044903 baseEnd_4044903 := by
    simpa [prefixWord, tailWord_4044903, baseEnd_4044903] using wordTrace_append hprefix tailTrace_4044903
  have hstable : (prefixWord ++ tailWord_4044903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044903).length < 2 ^ (prefixWord ++ tailWord_4044903).sum := by decide
  have hdescent : baseEnd_4044903 < baseStart_4044903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044935 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 4]
def baseStart_4044935 : Nat := 118140960795 + 4044935 * 2 ^ 59
def prefixEnd_4044935 : Nat := 4983230072969 + 3 ^ 40 * 4044935 * 2
def baseEnd_4044935 : Nat := 461554638043163757091153

theorem tailTrace_4044935 : CollatzResearch.WordTrace tailWord_4044935 prefixEnd_4044935 461554638043163757091153 := by
  unfold tailWord_4044935
  simp only [CollatzResearch.WordTrace]
  refine ⟨147530899600898789744128259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98353933067265859829418839 147530899600898789744128259)
  ·
    refine ⟨221296349401348184616192389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147530899600898789744128259 221296349401348184616192389)
    ·
      refine ⟨41493065512752784615536073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221296349401348184616192389 41493065512752784615536073)
      ·
        refine ⟨31119799134564588461652055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41493065512752784615536073 31119799134564588461652055)
        ·
          refine ⟨46679698701846882692478083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31119799134564588461652055 46679698701846882692478083)
          ·
            refine ⟨70019548052770324038717125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46679698701846882692478083 70019548052770324038717125)
            ·
              refine ⟨13128665259894435757259461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70019548052770324038717125 13128665259894435757259461)
              ·
                refine ⟨2461624736230206704486149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13128665259894435757259461 2461624736230206704486149)
                ·
                  refine ⟨461554638043163757091153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461624736230206704486149 461554638043163757091153)
                  ·
                    rfl

theorem cell22_4044935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 4].length) (baseStart_4044935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4044935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4044935 prefixEnd_4044935 := by exact prefixLift 4044935
  have htrace : WordTrace (prefixWord ++ tailWord_4044935) baseStart_4044935 baseEnd_4044935 := by
    simpa [prefixWord, tailWord_4044935, baseEnd_4044935] using wordTrace_append hprefix tailTrace_4044935
  have hstable : (prefixWord ++ tailWord_4044935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044935).length < 2 ^ (prefixWord ++ tailWord_4044935).sum := by decide
  have hdescent : baseEnd_4044935 < baseStart_4044935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045023 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_4045023 : Nat := 118140960795 + 4045023 * 2 ^ 59
def prefixEnd_4045023 : Nat := 4983230072969 + 3 ^ 40 * 4045023 * 2
def baseEnd_4045023 : Nat := 1384694038327888375073189

theorem tailTrace_4045023 : CollatzResearch.WordTrace tailWord_4045023 prefixEnd_4045023 1384694038327888375073189 := by
  unfold tailWord_4045023
  simp only [CollatzResearch.WordTrace]
  refine ⟨147534109224579980773331723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98356072816386653848887815 147534109224579980773331723)
  ·
    refine ⟨221301163836869971159997585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147534109224579980773331723 221301163836869971159997585)
    ·
      refine ⟨165975872877652478369998189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221301163836869971159997585 165975872877652478369998189)
      ·
        refine ⟨62240952329119679388749321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165975872877652478369998189 62240952329119679388749321)
        ·
          refine ⟨46680714246839759541561991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62240952329119679388749321 46680714246839759541561991)
          ·
            refine ⟨70021071370259639312342987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46680714246839759541561991 70021071370259639312342987)
            ·
              refine ⟨105031607055389458968514481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70021071370259639312342987 105031607055389458968514481)
              ·
                refine ⟨78773705291542094226385861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105031607055389458968514481 78773705291542094226385861)
                ·
                  refine ⟨14770069742164142667447349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78773705291542094226385861 14770069742164142667447349)
                  ·
                    refine ⟨1384694038327888375073189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14770069742164142667447349 1384694038327888375073189)
                    ·
                      rfl

theorem cell22_4045023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_4045023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045023 prefixEnd_4045023 := by exact prefixLift 4045023
  have htrace : WordTrace (prefixWord ++ tailWord_4045023) baseStart_4045023 baseEnd_4045023 := by
    simpa [prefixWord, tailWord_4045023, baseEnd_4045023] using wordTrace_append hprefix tailTrace_4045023
  have hstable : (prefixWord ++ tailWord_4045023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045023).length < 2 ^ (prefixWord ++ tailWord_4045023).sum := by decide
  have hdescent : baseEnd_4045023 < baseStart_4045023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045042 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_4045042 : Nat := 118140960795 + 4045042 * 2 ^ 59
def prefixEnd_4045042 : Nat := 4983230072969 + 3 ^ 40 * 4045042 * 2
def baseEnd_4045042 : Nat := 461566847472059552949377

theorem tailTrace_4045042 : CollatzResearch.WordTrace tailWord_4045042 prefixEnd_4045042 461566847472059552949377 := by
  unfold tailWord_4045042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36883700552877786754568345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98356534807674098012182253 36883700552877786754568345)
  ·
    refine ⟨27662775414658340065926259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36883700552877786754568345 27662775414658340065926259)
    ·
      refine ⟨41494163121987510098889389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27662775414658340065926259 41494163121987510098889389)
      ·
        refine ⟨15560311170745316287083521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41494163121987510098889389 15560311170745316287083521)
        ·
          refine ⟨11670233378058987215312641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15560311170745316287083521 11670233378058987215312641)
          ·
            refine ⟨8752675033544240411484481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11670233378058987215312641 8752675033544240411484481)
            ·
              refine ⟨6564506275158180308613361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8752675033544240411484481 6564506275158180308613361)
              ·
                refine ⟨4923379706368635231460021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6564506275158180308613361 4923379706368635231460021)
                ·
                  refine ⟨461566847472059552949377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4923379706368635231460021 461566847472059552949377)
                  ·
                    rfl

theorem cell22_4045042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_4045042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045042 prefixEnd_4045042 := by exact prefixLift 4045042
  have htrace : WordTrace (prefixWord ++ tailWord_4045042) baseStart_4045042 baseEnd_4045042 := by
    simpa [prefixWord, tailWord_4045042, baseEnd_4045042] using wordTrace_append hprefix tailTrace_4045042
  have hstable : (prefixWord ++ tailWord_4045042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045042).length < 2 ^ (prefixWord ++ tailWord_4045042).sum := by decide
  have hdescent : baseEnd_4045042 < baseStart_4045042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045046 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_4045046 : Nat := 118140960795 + 4045046 * 2 ^ 59
def prefixEnd_4045046 : Nat := 4983230072969 + 3 ^ 40 * 4045046 * 2
def baseEnd_4045046 : Nat := 1384701911697923981748119

theorem tailTrace_4045046 : CollatzResearch.WordTrace tailWord_4045046 prefixEnd_4045046 1384701911697923981748119 := by
  unfold tailWord_4045046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220934256468540981338687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98356632068997770467612661 9220934256468540981338687)
  ·
    refine ⟨13831401384702811472008031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9220934256468540981338687 13831401384702811472008031)
    ·
      refine ⟨20747102077054217208012047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13831401384702811472008031 20747102077054217208012047)
      ·
        refine ⟨31120653115581325812018071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747102077054217208012047 31120653115581325812018071)
        ·
          refine ⟨46680979673371988718027107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31120653115581325812018071 46680979673371988718027107)
          ·
            refine ⟨70021469510057983077040661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46680979673371988718027107 70021469510057983077040661)
            ·
              refine ⟨3282256383283967956736281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70021469510057983077040661 3282256383283967956736281)
              ·
                refine ⟨2461692287462975967552211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282256383283967956736281 2461692287462975967552211)
                ·
                  refine ⟨3692538431194463951328317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461692287462975967552211 3692538431194463951328317)
                  ·
                    refine ⟨1384701911697923981748119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3692538431194463951328317 1384701911697923981748119)
                    ·
                      rfl

theorem cell22_4045046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_4045046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045046 prefixEnd_4045046 := by exact prefixLift 4045046
  have htrace : WordTrace (prefixWord ++ tailWord_4045046) baseStart_4045046 baseEnd_4045046 := by
    simpa [prefixWord, tailWord_4045046, baseEnd_4045046] using wordTrace_append hprefix tailTrace_4045046
  have hstable : (prefixWord ++ tailWord_4045046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045046).length < 2 ^ (prefixWord ++ tailWord_4045046).sum := by decide
  have hdescent : baseEnd_4045046 < baseStart_4045046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045053 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 10]
def baseStart_4045053 : Nat := 118140960795 + 4045053 * 2 ^ 59
def prefixEnd_4045053 : Nat := 4983230072969 + 3 ^ 40 * 4045053 * 2
def baseEnd_4045053 : Nat := 461568102646992765607699

theorem tailTrace_4045053 : CollatzResearch.WordTrace tailWord_4045053 prefixEnd_4045053 461568102646992765607699 := by
  unfold tailWord_4045053
  simp only [CollatzResearch.WordTrace]
  refine ⟨147535203414471295896923813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98356802276314197264615875 147535203414471295896923813)
  ·
    refine ⟨27662850640213367980673215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147535203414471295896923813 27662850640213367980673215)
    ·
      refine ⟨41494275960320051971009823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27662850640213367980673215 41494275960320051971009823)
      ·
        refine ⟨62241413940480077956514735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41494275960320051971009823 62241413940480077956514735)
        ·
          refine ⟨93362120910720116934772103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62241413940480077956514735 93362120910720116934772103)
          ·
            refine ⟨140043181366080175402158155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93362120910720116934772103 140043181366080175402158155)
            ·
              refine ⟨210064772049120263103237233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140043181366080175402158155 210064772049120263103237233)
              ·
                refine ⟨157548579036840197327427925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210064772049120263103237233 157548579036840197327427925)
                ·
                  refine ⟨461568102646992765607699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 157548579036840197327427925 461568102646992765607699)
                  ·
                    rfl

theorem cell22_4045053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_4045053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045053 prefixEnd_4045053 := by exact prefixLift 4045053
  have htrace : WordTrace (prefixWord ++ tailWord_4045053) baseStart_4045053 baseEnd_4045053 := by
    simpa [prefixWord, tailWord_4045053, baseEnd_4045053] using wordTrace_append hprefix tailTrace_4045053
  have hstable : (prefixWord ++ tailWord_4045053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045053).length < 2 ^ (prefixWord ++ tailWord_4045053).sum := by decide
  have hdescent : baseEnd_4045053 < baseStart_4045053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045070 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_4045070 : Nat := 118140960795 + 4045070 * 2 ^ 59
def prefixEnd_4045070 : Nat := 4983230072969 + 3 ^ 40 * 4045070 * 2
def baseEnd_4045070 : Nat := 461570042462798639716015

theorem tailTrace_4045070 : CollatzResearch.WordTrace tailWord_4045070 prefixEnd_4045070 461570042462798639716015 := by
  unfold tailWord_4045070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18441977931926213475036583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98357215636939805200195109 18441977931926213475036583)
  ·
    refine ⟨27662966897889320212554875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18441977931926213475036583 27662966897889320212554875)
    ·
      refine ⟨41494450346833980318832313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27662966897889320212554875 41494450346833980318832313)
      ·
        refine ⟨31120837760125485239124235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41494450346833980318832313 31120837760125485239124235)
        ·
          refine ⟨46681256640188227858686353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31120837760125485239124235 46681256640188227858686353)
          ·
            refine ⟨35010942480141170894014765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46681256640188227858686353 35010942480141170894014765)
            ·
              refine ⟨13129103430052939085255537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35010942480141170894014765 13129103430052939085255537)
              ·
                refine ⟨9846827572539704313941653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13129103430052939085255537 9846827572539704313941653)
                ·
                  refine ⟨461570042462798639716015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9846827572539704313941653 461570042462798639716015)
                  ·
                    rfl

theorem cell22_4045070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_4045070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045070 prefixEnd_4045070 := by exact prefixLift 4045070
  have htrace : WordTrace (prefixWord ++ tailWord_4045070) baseStart_4045070 baseEnd_4045070 := by
    simpa [prefixWord, tailWord_4045070, baseEnd_4045070] using wordTrace_append hprefix tailTrace_4045070
  have hstable : (prefixWord ++ tailWord_4045070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045070).length < 2 ^ (prefixWord ++ tailWord_4045070).sum := by decide
  have hdescent : baseEnd_4045070 < baseStart_4045070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045087 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 4]
def baseStart_4045087 : Nat := 118140960795 + 4045087 * 2 ^ 59
def prefixEnd_4045087 : Nat := 4983230072969 + 3 ^ 40 * 4045087 * 2
def baseEnd_4045087 : Nat := 461571982278604513824331

theorem tailTrace_4045087 : CollatzResearch.WordTrace tailWord_4045087 prefixEnd_4045087 461571982278604513824331 := by
  unfold tailWord_4045087
  simp only [CollatzResearch.WordTrace]
  refine ⟨147536443496348119703661515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98357628997565413135774343 147536443496348119703661515)
  ·
    refine ⟨221304665244522179555492273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147536443496348119703661515 221304665244522179555492273)
    ·
      refine ⟨165978498933391634666619205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221304665244522179555492273 165978498933391634666619205)
      ·
        refine ⟨31120968550010931499991101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165978498933391634666619205 31120968550010931499991101)
        ·
          refine ⟨11670363206254099312496663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31120968550010931499991101 11670363206254099312496663)
          ·
            refine ⟨17505544809381148968744995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670363206254099312496663 17505544809381148968744995)
            ·
              refine ⟨26258317214071723453117493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17505544809381148968744995 26258317214071723453117493)
              ·
                refine ⟨2461717238819224073729765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26258317214071723453117493 2461717238819224073729765)
                ·
                  refine ⟨461571982278604513824331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461717238819224073729765 461571982278604513824331)
                  ·
                    rfl

theorem cell22_4045087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 4].length) (baseStart_4045087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045087 prefixEnd_4045087 := by exact prefixLift 4045087
  have htrace : WordTrace (prefixWord ++ tailWord_4045087) baseStart_4045087 baseEnd_4045087 := by
    simpa [prefixWord, tailWord_4045087, baseEnd_4045087] using wordTrace_append hprefix tailTrace_4045087
  have hstable : (prefixWord ++ tailWord_4045087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045087).length < 2 ^ (prefixWord ++ tailWord_4045087).sum := by decide
  have hdescent : baseEnd_4045087 < baseStart_4045087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045100 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_4045100 : Nat := 118140960795 + 4045100 * 2 ^ 59
def prefixEnd_4045100 : Nat := 4983230072969 + 3 ^ 40 * 4045100 * 2
def baseEnd_4045100 : Nat := 1384720397001485840897953

theorem tailTrace_4045100 : CollatzResearch.WordTrace tailWord_4045100 prefixEnd_4045100 1384720397001485840897953 := by
  unfold tailWord_4045100
  simp only [CollatzResearch.WordTrace]
  refine ⟨73768458822650511461942377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98357945096867348615923169 73768458822650511461942377)
  ·
    refine ⟨55326344116987883596456783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73768458822650511461942377 55326344116987883596456783)
    ·
      refine ⟨82989516175481825394685175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55326344116987883596456783 82989516175481825394685175)
      ·
        refine ⟨124484274263222738092027763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82989516175481825394685175 124484274263222738092027763)
        ·
          refine ⟨186726411394834107138041645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124484274263222738092027763 186726411394834107138041645)
          ·
            refine ⟨70022404273062790176765617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186726411394834107138041645 70022404273062790176765617)
            ·
              refine ⟨52516803204797092632574213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70022404273062790176765617 52516803204797092632574213)
              ·
                refine ⟨9846900600899454868607665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52516803204797092632574213 9846900600899454868607665)
                ·
                  refine ⟨7385175450674591151455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9846900600899454868607665 7385175450674591151455749)
                  ·
                    refine ⟨1384720397001485840897953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7385175450674591151455749 1384720397001485840897953)
                    ·
                      rfl

theorem cell22_4045100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_4045100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045100 prefixEnd_4045100 := by exact prefixLift 4045100
  have htrace : WordTrace (prefixWord ++ tailWord_4045100) baseStart_4045100 baseEnd_4045100 := by
    simpa [prefixWord, tailWord_4045100, baseEnd_4045100] using wordTrace_append hprefix tailTrace_4045100
  have hstable : (prefixWord ++ tailWord_4045100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045100).length < 2 ^ (prefixWord ++ tailWord_4045100).sum := by decide
  have hdescent : baseEnd_4045100 < baseStart_4045100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045119 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 2, 3]
def baseStart_4045119 : Nat := 118140960795 + 4045119 * 2 ^ 59
def prefixEnd_4045119 : Nat := 4983230072969 + 3 ^ 40 * 4045119 * 2
def baseEnd_4045119 : Nat := 1384726901089776124672895

theorem tailTrace_4045119 : CollatzResearch.WordTrace tailWord_4045119 prefixEnd_4045119 1384726901089776124672895 := by
  unfold tailWord_4045119
  simp only [CollatzResearch.WordTrace]
  refine ⟨147537610632232189168826411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98358407088154792779217607 147537610632232189168826411)
  ·
    refine ⟨221306415948348283753239617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147537610632232189168826411 221306415948348283753239617)
    ·
      refine ⟨165979811961261212814929713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221306415948348283753239617 165979811961261212814929713)
      ·
        refine ⟨124484858970945909611197285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165979811961261212814929713 124484858970945909611197285)
        ·
          refine ⟨23340911057052358052099491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124484858970945909611197285 23340911057052358052099491)
          ·
            refine ⟨35011366585578537078149237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23340911057052358052099491 35011366585578537078149237)
            ·
              refine ⟨3282315617397987851076491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35011366585578537078149237 3282315617397987851076491)
              ·
                refine ⟨4923473426096981776614737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282315617397987851076491 4923473426096981776614737)
                ·
                  refine ⟨3692605069572736332461053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4923473426096981776614737 3692605069572736332461053)
                  ·
                    refine ⟨1384726901089776124672895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3692605069572736332461053 1384726901089776124672895)
                    ·
                      rfl

theorem cell22_4045119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_4045119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045119 prefixEnd_4045119 := by exact prefixLift 4045119
  have htrace : WordTrace (prefixWord ++ tailWord_4045119) baseStart_4045119 baseEnd_4045119 := by
    simpa [prefixWord, tailWord_4045119, baseEnd_4045119] using wordTrace_append hprefix tailTrace_4045119
  have hstable : (prefixWord ++ tailWord_4045119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045119).length < 2 ^ (prefixWord ++ tailWord_4045119).sum := by decide
  have hdescent : baseEnd_4045119 < baseStart_4045119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045207 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 1, 4]
def baseStart_4045207 : Nat := 118140960795 + 4045207 * 2 ^ 59
def prefixEnd_4045207 : Nat := 4983230072969 + 3 ^ 40 * 4045207 * 2
def baseEnd_4045207 : Nat := 1384757025288173228472625

theorem tailTrace_4045207 : CollatzResearch.WordTrace tailWord_4045207 prefixEnd_4045207 1384757025288173228472625 := by
  unfold tailWord_4045207
  simp only [CollatzResearch.WordTrace]
  refine ⟨147540820255913380198029875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98360546837275586798686583 147540820255913380198029875)
  ·
    refine ⟨221311230383870070297044813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147540820255913380198029875 221311230383870070297044813)
    ·
      refine ⟨82991711393951276361391805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221311230383870070297044813 82991711393951276361391805)
      ·
        refine ⟨31121891772731728635521927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82991711393951276361391805 31121891772731728635521927)
        ·
          refine ⟨46682837659097592953282891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31121891772731728635521927 46682837659097592953282891)
          ·
            refine ⟨70024256488646389429924337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46682837659097592953282891 70024256488646389429924337)
            ·
              refine ⟨52518192366484792072443253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70024256488646389429924337 52518192366484792072443253)
              ·
                refine ⟨4923580534357949256791555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52518192366484792072443253 4923580534357949256791555)
                ·
                  refine ⟨7385370801536923885187333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923580534357949256791555 7385370801536923885187333)
                  ·
                    refine ⟨1384757025288173228472625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7385370801536923885187333 1384757025288173228472625)
                    ·
                      rfl

theorem cell22_4045207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_4045207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045207 prefixEnd_4045207 := by exact prefixLift 4045207
  have htrace : WordTrace (prefixWord ++ tailWord_4045207) baseStart_4045207 baseEnd_4045207 := by
    simpa [prefixWord, tailWord_4045207, baseEnd_4045207] using wordTrace_append hprefix tailTrace_4045207
  have hstable : (prefixWord ++ tailWord_4045207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045207).length < 2 ^ (prefixWord ++ tailWord_4045207).sum := by decide
  have hdescent : baseEnd_4045207 < baseStart_4045207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045224 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4045224 : Nat := 118140960795 + 4045224 * 2 ^ 59
def prefixEnd_4045224 : Nat := 4983230072969 + 3 ^ 40 * 4045224 * 2
def baseEnd_4045224 : Nat := 1384762844735590850797573

theorem tailTrace_4045224 : CollatzResearch.WordTrace tailWord_4045224 prefixEnd_4045224 1384762844735590850797573 := by
  unfold tailWord_4045224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73770720148425896050699363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98360960197901194734265817 73770720148425896050699363)
  ·
    refine ⟨110656080222638844076049045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73770720148425896050699363 110656080222638844076049045)
    ·
      refine ⟨5187003760436195816064799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110656080222638844076049045 5187003760436195816064799)
      ·
        refine ⟨7780505640654293724097199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187003760436195816064799 7780505640654293724097199)
        ·
          refine ⟨11670758460981440586145799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780505640654293724097199 11670758460981440586145799)
          ·
            refine ⟨17506137691472160879218699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670758460981440586145799 17506137691472160879218699)
            ·
              refine ⟨26259206537208241318828049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17506137691472160879218699 26259206537208241318828049)
              ·
                refine ⟨19694404902906180989121037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26259206537208241318828049 19694404902906180989121037)
                ·
                  refine ⟨7385401838589817870920389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19694404902906180989121037 7385401838589817870920389)
                  ·
                    refine ⟨1384762844735590850797573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7385401838589817870920389 1384762844735590850797573)
                    ·
                      rfl

theorem cell22_4045224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4045224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045224 prefixEnd_4045224 := by exact prefixLift 4045224
  have htrace : WordTrace (prefixWord ++ tailWord_4045224) baseStart_4045224 baseEnd_4045224 := by
    simpa [prefixWord, tailWord_4045224, baseEnd_4045224] using wordTrace_append hprefix tailTrace_4045224
  have hstable : (prefixWord ++ tailWord_4045224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045224).length < 2 ^ (prefixWord ++ tailWord_4045224).sum := by decide
  have hdescent : baseEnd_4045224 < baseStart_4045224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045265 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_4045265 : Nat := 118140960795 + 4045265 * 2 ^ 59
def prefixEnd_4045265 : Nat := 4983230072969 + 3 ^ 40 * 4045265 * 2
def baseEnd_4045265 : Nat := 1384776879873480410522447

theorem tailTrace_4045265 : CollatzResearch.WordTrace tailWord_4045265 prefixEnd_4045265 1384776879873480410522447 := by
  unfold tailWord_4045265
  simp only [CollatzResearch.WordTrace]
  refine ⟨147542935689703256103641249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98361957126468837402427499 147542935689703256103641249)
  ·
    refine ⟨110657201767277442077730937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147542935689703256103641249 110657201767277442077730937)
    ·
      refine ⟨82992901325458081558298203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110657201767277442077730937 82992901325458081558298203)
      ·
        refine ⟨124489351988187122337447305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82992901325458081558298203 124489351988187122337447305)
        ·
          refine ⟨93367013991140341753085479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124489351988187122337447305 93367013991140341753085479)
          ·
            refine ⟨140050520986710512629628219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93367013991140341753085479 140050520986710512629628219)
            ·
              refine ⟨210075781480065768944442329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140050520986710512629628219 210075781480065768944442329)
              ·
                refine ⟨157556836110049326708331747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210075781480065768944442329 157556836110049326708331747)
                ·
                  refine ⟨236335254165073990062497621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157556836110049326708331747 236335254165073990062497621)
                  ·
                    refine ⟨1384776879873480410522447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236335254165073990062497621 1384776879873480410522447)
                    ·
                      rfl

theorem cell22_4045265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_4045265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045265 prefixEnd_4045265 := by exact prefixLift 4045265
  have htrace : WordTrace (prefixWord ++ tailWord_4045265) baseStart_4045265 baseEnd_4045265 := by
    simpa [prefixWord, tailWord_4045265, baseEnd_4045265] using wordTrace_append hprefix tailTrace_4045265
  have hstable : (prefixWord ++ tailWord_4045265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045265).length < 2 ^ (prefixWord ++ tailWord_4045265).sum := by decide
  have hdescent : baseEnd_4045265 < baseStart_4045265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045318 : List Nat := [6, 2, 1, 1, 1, 3, 8]
def baseStart_4045318 : Nat := 118140960795 + 4045318 * 2 ^ 59
def prefixEnd_4045318 : Nat := 4983230072969 + 3 ^ 40 * 4045318 * 2
def baseEnd_4045318 : Nat := 51288704550244664405455

theorem tailTrace_4045318 : CollatzResearch.WordTrace tailWord_4045318 prefixEnd_4045318 51288704550244664405455 := by
  unfold tailWord_4045318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4610777148703476442353769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98363245839007497436880405 4610777148703476442353769)
  ·
    refine ⟨3458082861527607331765327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4610777148703476442353769 3458082861527607331765327)
    ·
      refine ⟨5187124292291410997647991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458082861527607331765327 5187124292291410997647991)
      ·
        refine ⟨7780686438437116496471987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187124292291410997647991 7780686438437116496471987)
        ·
          refine ⟨11671029657655674744707981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780686438437116496471987 11671029657655674744707981)
          ·
            refine ⟨4376636121620878029265493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11671029657655674744707981 4376636121620878029265493)
            ·
              refine ⟨51288704550244664405455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4376636121620878029265493 51288704550244664405455)
              ·
                rfl

theorem cell22_4045318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 8].length) (baseStart_4045318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045318 prefixEnd_4045318 := by exact prefixLift 4045318
  have htrace : WordTrace (prefixWord ++ tailWord_4045318) baseStart_4045318 baseEnd_4045318 := by
    simpa [prefixWord, tailWord_4045318, baseEnd_4045318] using wordTrace_append hprefix tailTrace_4045318
  have hstable : (prefixWord ++ tailWord_4045318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045318).length < 2 ^ (prefixWord ++ tailWord_4045318).sum := by decide
  have hdescent : baseEnd_4045318 < baseStart_4045318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045333 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_4045333 : Nat := 118140960795 + 4045333 * 2 ^ 59
def prefixEnd_4045333 : Nat := 4983230072969 + 3 ^ 40 * 4045333 * 2
def baseEnd_4045333 : Nat := 1384800157663150899822239

theorem tailTrace_4045333 : CollatzResearch.WordTrace tailWord_4045333 prefixEnd_4045333 1384800157663150899822239 := by
  unfold tailWord_4045333
  simp only [CollatzResearch.WordTrace]
  refine ⟨147545415853456903717116653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98363610568971269144744435 147545415853456903717116653)
  ·
    refine ⟨55329530945046338893918745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147545415853456903717116653 55329530945046338893918745)
    ·
      refine ⟨41497148208784754170439059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55329530945046338893918745 41497148208784754170439059)
      ·
        refine ⟨62245722313177131255658589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41497148208784754170439059 62245722313177131255658589)
        ·
          refine ⟨23342145867441424220871971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62245722313177131255658589 23342145867441424220871971)
          ·
            refine ⟨35013218801162136331307957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23342145867441424220871971 35013218801162136331307957)
            ·
              refine ⟨3282489262608950281060121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35013218801162136331307957 3282489262608950281060121)
              ·
                refine ⟨2461866946956712710795091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282489262608950281060121 2461866946956712710795091)
                ·
                  refine ⟨3692800420435069066192637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461866946956712710795091 3692800420435069066192637)
                  ·
                    refine ⟨1384800157663150899822239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3692800420435069066192637 1384800157663150899822239)
                    ·
                      rfl

theorem cell22_4045333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_4045333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045333 prefixEnd_4045333 := by exact prefixLift 4045333
  have htrace : WordTrace (prefixWord ++ tailWord_4045333) baseStart_4045333 baseEnd_4045333 := by
    simpa [prefixWord, tailWord_4045333, baseEnd_4045333] using wordTrace_append hprefix tailTrace_4045333
  have hstable : (prefixWord ++ tailWord_4045333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045333).length < 2 ^ (prefixWord ++ tailWord_4045333).sum := by decide
  have hdescent : baseEnd_4045333 < baseStart_4045333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045380 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 5]
def baseStart_4045380 : Nat := 118140960795 + 4045380 * 2 ^ 59
def prefixEnd_4045380 : Nat := 4983230072969 + 3 ^ 40 * 4045380 * 2
def baseEnd_4045380 : Nat := 461605415574552814632365

theorem tailTrace_4045380 : CollatzResearch.WordTrace tailWord_4045380 prefixEnd_4045380 461605415574552814632365 := by
  unfold tailWord_4045380
  simp only [CollatzResearch.WordTrace]
  refine ⟨73773565042143315372038797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98364753389524420496051729 73773565042143315372038797)
  ·
    refine ⟨27665086890803743264514549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73773565042143315372038797 27665086890803743264514549)
    ·
      refine ⟨2593601896012850931048239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27665086890803743264514549 2593601896012850931048239)
      ·
        refine ⟨3890402844019276396572359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593601896012850931048239 3890402844019276396572359)
        ·
          refine ⟨5835604266028914594858539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890402844019276396572359 5835604266028914594858539)
          ·
            refine ⟨8753406399043371892287809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5835604266028914594858539 8753406399043371892287809)
            ·
              refine ⟨6565054799282528919215857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8753406399043371892287809 6565054799282528919215857)
              ·
                refine ⟨4923791099461896689411893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565054799282528919215857 4923791099461896689411893)
                ·
                  refine ⟨461605415574552814632365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4923791099461896689411893 461605415574552814632365)
                  ·
                    rfl

theorem cell22_4045380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_4045380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045380 prefixEnd_4045380 := by exact prefixLift 4045380
  have htrace : WordTrace (prefixWord ++ tailWord_4045380) baseStart_4045380 baseEnd_4045380 := by
    simpa [prefixWord, tailWord_4045380, baseEnd_4045380] using wordTrace_append hprefix tailTrace_4045380
  have hstable : (prefixWord ++ tailWord_4045380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045380).length < 2 ^ (prefixWord ++ tailWord_4045380).sum := by decide
  have hdescent : baseEnd_4045380 < baseStart_4045380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045391 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 4]
def baseStart_4045391 : Nat := 118140960795 + 4045391 * 2 ^ 59
def prefixEnd_4045391 : Nat := 4983230072969 + 3 ^ 40 * 4045391 * 2
def baseEnd_4045391 : Nat := 461606670749486027290687

theorem tailTrace_4045391 : CollatzResearch.WordTrace tailWord_4045391 prefixEnd_4045391 461606670749486027290687 := by
  unfold tailWord_4045391
  simp only [CollatzResearch.WordTrace]
  refine ⟨147547531287246779622728027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98365020858164519748485351 147547531287246779622728027)
  ·
    refine ⟨221321296930870169434092041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147547531287246779622728027 221321296930870169434092041)
    ·
      refine ⟨165990972698152627075569031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221321296930870169434092041 165990972698152627075569031)
      ·
        refine ⟨248986459047228940613353547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165990972698152627075569031 248986459047228940613353547)
        ·
          refine ⟨373479688570843410920030321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248986459047228940613353547 373479688570843410920030321)
          ·
            refine ⟨280109766428132558190022741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373479688570843410920030321 280109766428132558190022741)
            ·
              refine ⟨3282536325329678416289329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 280109766428132558190022741 3282536325329678416289329)
              ·
                refine ⟨2461902243997258812216997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282536325329678416289329 2461902243997258812216997)
                ·
                  refine ⟨461606670749486027290687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461902243997258812216997 461606670749486027290687)
                  ·
                    rfl

theorem cell22_4045391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 4].length) (baseStart_4045391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045391 prefixEnd_4045391 := by exact prefixLift 4045391
  have htrace : WordTrace (prefixWord ++ tailWord_4045391) baseStart_4045391 baseEnd_4045391 := by
    simpa [prefixWord, tailWord_4045391, baseEnd_4045391] using wordTrace_append hprefix tailTrace_4045391
  have hstable : (prefixWord ++ tailWord_4045391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045391).length < 2 ^ (prefixWord ++ tailWord_4045391).sum := by decide
  have hdescent : baseEnd_4045391 < baseStart_4045391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045421 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4045421 : Nat := 118140960795 + 4045421 * 2 ^ 59
def prefixEnd_4045421 : Nat := 4983230072969 + 3 ^ 40 * 4045421 * 2
def baseEnd_4045421 : Nat := 1384830281861548003621969

theorem tailTrace_4045421 : CollatzResearch.WordTrace tailWord_4045421 prefixEnd_4045421 1384830281861548003621969 := by
  unfold tailWord_4045421
  simp only [CollatzResearch.WordTrace]
  refine ⟨147548625477138094746320117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98365750318092063164213411 147548625477138094746320117)
  ·
    refine ⟨13832683638481696382467511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147548625477138094746320117 13832683638481696382467511)
    ·
      refine ⟨20749025457722544573701267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13832683638481696382467511 20749025457722544573701267)
      ·
        refine ⟨31123538186583816860551901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20749025457722544573701267 31123538186583816860551901)
        ·
          refine ⟨11671326819968931322706963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31123538186583816860551901 11671326819968931322706963)
          ·
            refine ⟨17506990229953396984060445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11671326819968931322706963 17506990229953396984060445)
            ·
              refine ⟨6565121336232523869022667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17506990229953396984060445 6565121336232523869022667)
              ·
                refine ⟨9847682004348785803534001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6565121336232523869022667 9847682004348785803534001)
                ·
                  refine ⟨7385761503261589352650501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9847682004348785803534001 7385761503261589352650501)
                  ·
                    refine ⟨1384830281861548003621969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7385761503261589352650501 1384830281861548003621969)
                    ·
                      rfl

theorem cell22_4045421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4045421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045421 prefixEnd_4045421 := by exact prefixLift 4045421
  have htrace : WordTrace (prefixWord ++ tailWord_4045421) baseStart_4045421 baseEnd_4045421 := by
    simpa [prefixWord, tailWord_4045421, baseEnd_4045421] using wordTrace_append hprefix tailTrace_4045421
  have hstable : (prefixWord ++ tailWord_4045421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045421).length < 2 ^ (prefixWord ++ tailWord_4045421).sum := by decide
  have hdescent : baseEnd_4045421 < baseStart_4045421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045432 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_4045432 : Nat := 118140960795 + 4045432 * 2 ^ 59
def prefixEnd_4045432 : Nat := 4983230072969 + 3 ^ 40 * 4045432 * 2
def baseEnd_4045432 : Nat := 1384834047386347641596935

theorem tailTrace_4045432 : CollatzResearch.WordTrace tailWord_4045432 prefixEnd_4045432 1384834047386347641596935 := by
  unfold tailWord_4045432
  simp only [CollatzResearch.WordTrace]
  refine ⟨73774513340049121812485275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98366017786732162416647033 73774513340049121812485275)
  ·
    refine ⟨110661770010073682718727913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73774513340049121812485275 110661770010073682718727913)
    ·
      refine ⟨82996327507555262039045935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110661770010073682718727913 82996327507555262039045935)
      ·
        refine ⟨124494491261332893058568903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82996327507555262039045935 124494491261332893058568903)
        ·
          refine ⟨186741736891999339587853355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124494491261332893058568903 186741736891999339587853355)
          ·
            refine ⟨280112605337999009381780033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186741736891999339587853355 280112605337999009381780033)
            ·
              refine ⟨210084454003499257036335025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280112605337999009381780033 210084454003499257036335025)
              ·
                refine ⟨157563340502624442777251269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210084454003499257036335025 157563340502624442777251269)
                ·
                  refine ⟨29543126344242083020734613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157563340502624442777251269 29543126344242083020734613)
                  ·
                    refine ⟨1384834047386347641596935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29543126344242083020734613 1384834047386347641596935)
                    ·
                      rfl

theorem cell22_4045432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_4045432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045432 prefixEnd_4045432 := by exact prefixLift 4045432
  have htrace : WordTrace (prefixWord ++ tailWord_4045432) baseStart_4045432 baseEnd_4045432 := by
    simpa [prefixWord, tailWord_4045432, baseEnd_4045432] using wordTrace_append hprefix tailTrace_4045432
  have hstable : (prefixWord ++ tailWord_4045432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045432).length < 2 ^ (prefixWord ++ tailWord_4045432).sum := by decide
  have hdescent : baseEnd_4045432 < baseStart_4045432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045485 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_4045485 : Nat := 118140960795 + 4045485 * 2 ^ 59
def prefixEnd_4045485 : Nat := 4983230072969 + 3 ^ 40 * 4045485 * 2
def baseEnd_4045485 : Nat := 1384852190369473170021773

theorem tailTrace_4045485 : CollatzResearch.WordTrace tailWord_4045485 prefixEnd_4045485 1384852190369473170021773 := by
  unfold tailWord_4045485
  simp only [CollatzResearch.WordTrace]
  refine ⟨147550959748906233676649909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98367306499270822451099939 147550959748906233676649909)
  ·
    refine ⟨13832902476459959407185929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147550959748906233676649909 13832902476459959407185929)
    ·
      refine ⟨10374676857344969555389447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13832902476459959407185929 10374676857344969555389447)
      ·
        refine ⟨15562015286017454333084171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10374676857344969555389447 15562015286017454333084171)
        ·
          refine ⟨23343022929026181499626257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15562015286017454333084171 23343022929026181499626257)
          ·
            refine ⟨17507267196769636124719693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23343022929026181499626257 17507267196769636124719693)
            ·
              refine ⟨6565225198788613546769885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17507267196769636124719693 6565225198788613546769885)
              ·
                refine ⟨2461959449545730080038707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6565225198788613546769885 2461959449545730080038707)
                ·
                  refine ⟨3692939174318595120058061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461959449545730080038707 3692939174318595120058061)
                  ·
                    refine ⟨1384852190369473170021773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3692939174318595120058061 1384852190369473170021773)
                    ·
                      rfl

theorem cell22_4045485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_4045485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045485 prefixEnd_4045485 := by exact prefixLift 4045485
  have htrace : WordTrace (prefixWord ++ tailWord_4045485) baseStart_4045485 baseEnd_4045485 := by
    simpa [prefixWord, tailWord_4045485, baseEnd_4045485] using wordTrace_append hprefix tailTrace_4045485
  have hstable : (prefixWord ++ tailWord_4045485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045485).length < 2 ^ (prefixWord ++ tailWord_4045485).sum := by decide
  have hdescent : baseEnd_4045485 < baseStart_4045485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045528 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_4045528 : Nat := 118140960795 + 4045528 * 2 ^ 59
def prefixEnd_4045528 : Nat := 4983230072969 + 3 ^ 40 * 4045528 * 2
def baseEnd_4045528 : Nat := 1384866910148235391196641

theorem tailTrace_4045528 : CollatzResearch.WordTrace tailWord_4045528 prefixEnd_4045528 1384866910148235391196641 := by
  unfold tailWord_4045528
  simp only [CollatzResearch.WordTrace]
  refine ⟨73776264043875226010232619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98368352058500301346976825 73776264043875226010232619)
  ·
    refine ⟨110664396065812839015348929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73776264043875226010232619 110664396065812839015348929)
    ·
      refine ⟨82998297049359629261511697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110664396065812839015348929 82998297049359629261511697)
      ·
        refine ⟨62248722787019721946133773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82998297049359629261511697 62248722787019721946133773)
        ·
          refine ⟨23343271045132395729800165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62248722787019721946133773 23343271045132395729800165)
          ·
            refine ⟨4376863320962324199337531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23343271045132395729800165 4376863320962324199337531)
            ·
              refine ⟨6565294981443486299006297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376863320962324199337531 6565294981443486299006297)
              ·
                refine ⟨4923971236082614724254723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565294981443486299006297 4923971236082614724254723)
                ·
                  refine ⟨7385956854123922086382085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923971236082614724254723 7385956854123922086382085)
                  ·
                    refine ⟨1384866910148235391196641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7385956854123922086382085 1384866910148235391196641)
                    ·
                      rfl

theorem cell22_4045528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_4045528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045528 prefixEnd_4045528 := by exact prefixLift 4045528
  have htrace : WordTrace (prefixWord ++ tailWord_4045528) baseStart_4045528 baseEnd_4045528 := by
    simpa [prefixWord, tailWord_4045528, baseEnd_4045528] using wordTrace_append hprefix tailTrace_4045528
  have hstable : (prefixWord ++ tailWord_4045528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045528).length < 2 ^ (prefixWord ++ tailWord_4045528).sum := by decide
  have hdescent : baseEnd_4045528 < baseStart_4045528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045541 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_4045541 : Nat := 118140960795 + 4045541 * 2 ^ 59
def prefixEnd_4045541 : Nat := 4983230072969 + 3 ^ 40 * 4045541 * 2
def baseEnd_4045541 : Nat := 1384871360313907690621601

theorem tailTrace_4045541 : CollatzResearch.WordTrace tailWord_4045541 prefixEnd_4045541 1384871360313907690621601 := by
  unfold tailWord_4045541
  simp only [CollatzResearch.WordTrace]
  refine ⟨147553002236703355240688477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98368668157802236827125651 147553002236703355240688477)
  ·
    refine ⟨55332375838763758215258179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147553002236703355240688477 55332375838763758215258179)
    ·
      refine ⟨82998563758145637322887269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55332375838763758215258179 82998563758145637322887269)
      ·
        refine ⟨15562230704652306998041363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82998563758145637322887269 15562230704652306998041363)
        ·
          refine ⟨23343346056978460497062045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15562230704652306998041363 23343346056978460497062045)
          ·
            refine ⟨8753754771366922686398267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23343346056978460497062045 8753754771366922686398267)
            ·
              refine ⟨13130632157050384029597401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8753754771366922686398267 13130632157050384029597401)
              ·
                refine ⟨9847974117787788022198051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13130632157050384029597401 9847974117787788022198051)
                ·
                  refine ⟨14771961176681682033297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9847974117787788022198051 14771961176681682033297077)
                  ·
                    refine ⟨1384871360313907690621601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14771961176681682033297077 1384871360313907690621601)
                    ·
                      rfl

theorem cell22_4045541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_4045541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045541 prefixEnd_4045541 := by exact prefixLift 4045541
  have htrace : WordTrace (prefixWord ++ tailWord_4045541) baseStart_4045541 baseEnd_4045541 := by
    simpa [prefixWord, tailWord_4045541, baseEnd_4045541] using wordTrace_append hprefix tailTrace_4045541
  have hstable : (prefixWord ++ tailWord_4045541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045541).length < 2 ^ (prefixWord ++ tailWord_4045541).sum := by decide
  have hdescent : baseEnd_4045541 < baseStart_4045541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045554 : List Nat := [3, 2, 1, 3, 1, 12]
def baseStart_4045554 : Nat := 118140960795 + 4045554 * 2 ^ 59
def prefixEnd_4045554 : Nat := 4983230072969 + 3 ^ 40 * 4045554 * 2
def baseEnd_4045554 : Nat := 17097232228142962840081

theorem tailTrace_4045554 : CollatzResearch.WordTrace tailWord_4045554 prefixEnd_4045554 17097232228142962840081 := by
  unfold tailWord_4045554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36888369096414064615227929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98368984257104172307274477 36888369096414064615227929)
  ·
    refine ⟨27666276822310548461420947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36888369096414064615227929 27666276822310548461420947)
    ·
      refine ⟨41499415233465822692131421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27666276822310548461420947 41499415233465822692131421)
      ·
        refine ⟨15562280712549683509549283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41499415233465822692131421 15562280712549683509549283)
        ·
          refine ⟨23343421068824525264323925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15562280712549683509549283 23343421068824525264323925)
          ·
            refine ⟨17097232228142962840081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23343421068824525264323925 17097232228142962840081)
            ·
              rfl

theorem cell22_4045554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 12].length) (baseStart_4045554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045554 prefixEnd_4045554 := by exact prefixLift 4045554
  have htrace : WordTrace (prefixWord ++ tailWord_4045554) baseStart_4045554 baseEnd_4045554 := by
    simpa [prefixWord, tailWord_4045554, baseEnd_4045554] using wordTrace_append hprefix tailTrace_4045554
  have hstable : (prefixWord ++ tailWord_4045554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045554).length < 2 ^ (prefixWord ++ tailWord_4045554).sum := by decide
  have hdescent : baseEnd_4045554 < baseStart_4045554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045569 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4045569 : Nat := 118140960795 + 4045569 * 2 ^ 59
def prefixEnd_4045569 : Nat := 4983230072969 + 3 ^ 40 * 4045569 * 2
def baseEnd_4045569 : Nat := 1384880945286124950921515

theorem tailTrace_4045569 : CollatzResearch.WordTrace tailWord_4045569 prefixEnd_4045569 1384880945286124950921515 := by
  unfold tailWord_4045569
  simp only [CollatzResearch.WordTrace]
  refine ⟨147554023480601916022707761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98369348987067944015138507 147554023480601916022707761)
  ·
    refine ⟨110665517610451437017030821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147554023480601916022707761 110665517610451437017030821)
    ·
      refine ⟨20749784551959644440693279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110665517610451437017030821 20749784551959644440693279)
      ·
        refine ⟨31124676827939466661039919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20749784551959644440693279 31124676827939466661039919)
        ·
          refine ⟨46687015241909199991559879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31124676827939466661039919 46687015241909199991559879)
          ·
            refine ⟨70030522862863799987339819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46687015241909199991559879 70030522862863799987339819)
            ·
              refine ⟨105045784294295699981009729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70030522862863799987339819 105045784294295699981009729)
              ·
                refine ⟨78784338220721774985757297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105045784294295699981009729 78784338220721774985757297)
                ·
                  refine ⟨59088253665541331239317973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78784338220721774985757297 59088253665541331239317973)
                  ·
                    refine ⟨1384880945286124950921515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59088253665541331239317973 1384880945286124950921515)
                    ·
                      rfl

theorem cell22_4045569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4045569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045569 prefixEnd_4045569 := by exact prefixLift 4045569
  have htrace : WordTrace (prefixWord ++ tailWord_4045569) baseStart_4045569 baseEnd_4045569 := by
    simpa [prefixWord, tailWord_4045569, baseEnd_4045569] using wordTrace_append hprefix tailTrace_4045569
  have hstable : (prefixWord ++ tailWord_4045569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045569).length < 2 ^ (prefixWord ++ tailWord_4045569).sum := by decide
  have hdescent : baseEnd_4045569 < baseStart_4045569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045631 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 2, 5]
def baseStart_4045631 : Nat := 118140960795 + 4045631 * 2 ^ 59
def prefixEnd_4045631 : Nat := 4983230072969 + 3 ^ 40 * 4045631 * 2
def baseEnd_4045631 : Nat := 1384902169153177455871325

theorem tailTrace_4045631 : CollatzResearch.WordTrace tailWord_4045631 prefixEnd_4045631 1384902169153177455871325 := by
  unfold tailWord_4045631
  simp only [CollatzResearch.WordTrace]
  refine ⟨147556284806377300611464747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98370856537584867074309831 147556284806377300611464747)
  ·
    refine ⟨221334427209565950917197121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147556284806377300611464747 221334427209565950917197121)
    ·
      refine ⟨166000820407174463187897841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221334427209565950917197121 166000820407174463187897841)
      ·
        refine ⟨124500615305380847390923381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166000820407174463187897841 124500615305380847390923381)
        ·
          refine ⟨11671932684879454442899067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124500615305380847390923381 11671932684879454442899067)
          ·
            refine ⟨17507899027319181664348601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11671932684879454442899067 17507899027319181664348601)
            ·
              refine ⟨13130924270489386248261451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17507899027319181664348601 13130924270489386248261451)
              ·
                refine ⟨19696386405734079372392177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13130924270489386248261451 19696386405734079372392177)
                ·
                  refine ⟨14772289804300559529294133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19696386405734079372392177 14772289804300559529294133)
                  ·
                    refine ⟨1384902169153177455871325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14772289804300559529294133 1384902169153177455871325)
                    ·
                      rfl

theorem cell22_4045631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_4045631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045631 prefixEnd_4045631 := by exact prefixLift 4045631
  have htrace : WordTrace (prefixWord ++ tailWord_4045631) baseStart_4045631 baseEnd_4045631 := by
    simpa [prefixWord, tailWord_4045631, baseEnd_4045631] using wordTrace_append hprefix tailTrace_4045631
  have hstable : (prefixWord ++ tailWord_4045631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045631).length < 2 ^ (prefixWord ++ tailWord_4045631).sum := by decide
  have hdescent : baseEnd_4045631 < baseStart_4045631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045646 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_4045646 : Nat := 118140960795 + 4045646 * 2 ^ 59
def prefixEnd_4045646 : Nat := 4983230072969 + 3 ^ 40 * 4045646 * 2
def baseEnd_4045646 : Nat := 1384907303959722416746279

theorem tailTrace_4045646 : CollatzResearch.WordTrace tailWord_4045646 prefixEnd_4045646 1384907303959722416746279 := by
  unfold tailWord_4045646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18444603987665369771657599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98371221267548638782173861 18444603987665369771657599)
  ·
    refine ⟨27666905981498054657486399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18444603987665369771657599 27666905981498054657486399)
    ·
      refine ⟨41500358972247081986229599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27666905981498054657486399 41500358972247081986229599)
      ·
        refine ⟨62250538458370622979344399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41500358972247081986229599 62250538458370622979344399)
        ·
          refine ⟨93375807687555934469016599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62250538458370622979344399 93375807687555934469016599)
          ·
            refine ⟨140063711531333901703524899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93375807687555934469016599 140063711531333901703524899)
            ·
              refine ⟨210095567297000852555287349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140063711531333901703524899 210095567297000852555287349)
              ·
                refine ⟨19696459434093829927058189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210095567297000852555287349 19696459434093829927058189)
                ·
                  refine ⟨7386172287785186222646821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19696459434093829927058189 7386172287785186222646821)
                  ·
                    refine ⟨1384907303959722416746279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386172287785186222646821 1384907303959722416746279)
                    ·
                      rfl

theorem cell22_4045646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_4045646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045646 prefixEnd_4045646 := by exact prefixLift 4045646
  have htrace : WordTrace (prefixWord ++ tailWord_4045646) baseStart_4045646 baseEnd_4045646 := by
    simpa [prefixWord, tailWord_4045646, baseEnd_4045646] using wordTrace_append hprefix tailTrace_4045646
  have hstable : (prefixWord ++ tailWord_4045646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045646).length < 2 ^ (prefixWord ++ tailWord_4045646).sum := by decide
  have hdescent : baseEnd_4045646 < baseStart_4045646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045772 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_4045772 : Nat := 118140960795 + 4045772 * 2 ^ 59
def prefixEnd_4045772 : Nat := 4983230072969 + 3 ^ 40 * 4045772 * 2
def baseEnd_4045772 : Nat := 1384950436334700088095893

theorem tailTrace_4045772 : CollatzResearch.WordTrace tailWord_4045772 prefixEnd_4045772 1384950436334700088095893 := by
  unfold tailWord_4045772
  simp only [CollatzResearch.WordTrace]
  refine ⟨73780713749433240846173785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98374284999244321128231713 73780713749433240846173785)
  ·
    refine ⟨55335535312074930634630339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73780713749433240846173785 55335535312074930634630339)
    ·
      refine ⟨83003302968112395951945509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55335535312074930634630339 83003302968112395951945509)
      ·
        refine ⟨15563119306521074240989783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83003302968112395951945509 15563119306521074240989783)
        ·
          refine ⟨23344678959781611361484675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15563119306521074240989783 23344678959781611361484675)
          ·
            refine ⟨35017018439672417042227013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23344678959781611361484675 35017018439672417042227013)
            ·
              refine ⟨6565690957438578195417565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35017018439672417042227013 6565690957438578195417565)
              ·
                refine ⟨2462134109039466823281587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6565690957438578195417565 2462134109039466823281587)
                ·
                  refine ⟨3693201163559200234922381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462134109039466823281587 3693201163559200234922381)
                  ·
                    refine ⟨1384950436334700088095893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693201163559200234922381 1384950436334700088095893)
                    ·
                      rfl

theorem cell22_4045772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_4045772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045772 prefixEnd_4045772 := by exact prefixLift 4045772
  have htrace : WordTrace (prefixWord ++ tailWord_4045772) baseStart_4045772 baseEnd_4045772 := by
    simpa [prefixWord, tailWord_4045772, baseEnd_4045772] using wordTrace_append hprefix tailTrace_4045772
  have hstable : (prefixWord ++ tailWord_4045772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045772).length < 2 ^ (prefixWord ++ tailWord_4045772).sum := by decide
  have hdescent : baseEnd_4045772 < baseStart_4045772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045785 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 5]
def baseStart_4045785 : Nat := 118140960795 + 4045785 * 2 ^ 59
def prefixEnd_4045785 : Nat := 4983230072969 + 3 ^ 40 * 4045785 * 2
def baseEnd_4045785 : Nat := 461651628833457462506951

theorem tailTrace_4045785 : CollatzResearch.WordTrace tailWord_4045785 prefixEnd_4045785 461651628833457462506951 := by
  unfold tailWord_4045785
  simp only [CollatzResearch.WordTrace]
  refine ⟨147561901647819384912570809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98374601098546256608380539 147561901647819384912570809)
  ·
    refine ⟨110671426235864538684428107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147561901647819384912570809 110671426235864538684428107)
    ·
      refine ⟨166007139353796808026642161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110671426235864538684428107 166007139353796808026642161)
      ·
        refine ⟨124505354515347606019981621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166007139353796808026642161 124505354515347606019981621)
        ·
          refine ⟨11672376985813838064373277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124505354515347606019981621 11672376985813838064373277)
          ·
            refine ⟨4377141369680189274139979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11672376985813838064373277 4377141369680189274139979)
            ·
              refine ⟨6565712054520283911209969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4377141369680189274139979 6565712054520283911209969)
              ·
                refine ⟨4924284040890212933407477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565712054520283911209969 4924284040890212933407477)
                ·
                  refine ⟨461651628833457462506951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4924284040890212933407477 461651628833457462506951)
                  ·
                    rfl

theorem cell22_4045785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_4045785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045785 prefixEnd_4045785 := by exact prefixLift 4045785
  have htrace : WordTrace (prefixWord ++ tailWord_4045785) baseStart_4045785 baseEnd_4045785 := by
    simpa [prefixWord, tailWord_4045785, baseEnd_4045785] using wordTrace_append hprefix tailTrace_4045785
  have hstable : (prefixWord ++ tailWord_4045785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045785).length < 2 ^ (prefixWord ++ tailWord_4045785).sum := by decide
  have hdescent : baseEnd_4045785 < baseStart_4045785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045845 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_4045845 : Nat := 118140960795 + 4045845 * 2 ^ 59
def prefixEnd_4045845 : Nat := 4983230072969 + 3 ^ 40 * 4045845 * 2
def baseEnd_4045845 : Nat := 1384975425726552231020669

theorem tailTrace_4045845 : CollatzResearch.WordTrace tailWord_4045845 prefixEnd_4045845 1384975425726552231020669 := by
  unfold tailWord_4045845
  simp only [CollatzResearch.WordTrace]
  refine ⟨147564090027602015159754989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98376060018401343439836659 147564090027602015159754989)
  ·
    refine ⟨55336533760350755684908121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147564090027602015159754989 55336533760350755684908121)
    ·
      refine ⟨41502400320263066763681091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55336533760350755684908121 41502400320263066763681091)
      ·
        refine ⟨62253600480394600145521637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41502400320263066763681091 62253600480394600145521637)
        ·
          refine ⟨11672550090073987527285307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62253600480394600145521637 11672550090073987527285307)
          ·
            refine ⟨17508825135110981290927961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672550090073987527285307 17508825135110981290927961)
            ·
              refine ⟨13131618851333235968195971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17508825135110981290927961 13131618851333235968195971)
              ·
                refine ⟨19697428276999853952293957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13131618851333235968195971 19697428276999853952293957)
                ·
                  refine ⟨3693267801937472616055117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19697428276999853952293957 3693267801937472616055117)
                  ·
                    refine ⟨1384975425726552231020669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693267801937472616055117 1384975425726552231020669)
                    ·
                      rfl

theorem cell22_4045845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_4045845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045845 prefixEnd_4045845 := by exact prefixLift 4045845
  have htrace : WordTrace (prefixWord ++ tailWord_4045845) baseStart_4045845 baseEnd_4045845 := by
    simpa [prefixWord, tailWord_4045845, baseEnd_4045845] using wordTrace_append hprefix tailTrace_4045845
  have hstable : (prefixWord ++ tailWord_4045845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045845).length < 2 ^ (prefixWord ++ tailWord_4045845).sum := by decide
  have hdescent : baseEnd_4045845 < baseStart_4045845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045858 : List Nat := [3, 3, 1, 1, 1, 3, 1, 9]
def baseStart_4045858 : Nat := 118140960795 + 4045858 * 2 ^ 59
def prefixEnd_4045858 : Nat := 4983230072969 + 3 ^ 40 * 4045858 * 2
def baseEnd_4045858 : Nat := 153886652876913836716181

theorem tailTrace_4045858 : CollatzResearch.WordTrace tailWord_4045858 prefixEnd_4045858 153886652876913836716181 := by
  unfold tailWord_4045858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36891141044138729594994557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98376376117703278919985485 36891141044138729594994557)
  ·
    refine ⟨13834177891552023598122959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36891141044138729594994557 13834177891552023598122959)
    ·
      refine ⟨20751266837328035397184439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13834177891552023598122959 20751266837328035397184439)
      ·
        refine ⟨31126900255992053095776659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20751266837328035397184439 31126900255992053095776659)
        ·
          refine ⟨46690350383988079643664989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31126900255992053095776659 46690350383988079643664989)
          ·
            refine ⟨17508881393995529866374371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46690350383988079643664989 17508881393995529866374371)
            ·
              refine ⟨26263322090993294799561557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508881393995529866374371 26263322090993294799561557)
              ·
                refine ⟨153886652876913836716181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26263322090993294799561557 153886652876913836716181)
                ·
                  rfl

theorem cell22_4045858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_4045858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045858 prefixEnd_4045858 := by exact prefixLift 4045858
  have htrace : WordTrace (prefixWord ++ tailWord_4045858) baseStart_4045858 baseEnd_4045858 := by
    simpa [prefixWord, tailWord_4045858, baseEnd_4045858] using wordTrace_append hprefix tailTrace_4045858
  have hstable : (prefixWord ++ tailWord_4045858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045858).length < 2 ^ (prefixWord ++ tailWord_4045858).sum := by decide
  have hdescent : baseEnd_4045858 < baseStart_4045858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045948 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_4045948 : Nat := 118140960795 + 4045948 * 2 ^ 59
def prefixEnd_4045948 : Nat := 4983230072969 + 3 ^ 40 * 4045948 * 2
def baseEnd_4045948 : Nat := 461670228243831431898451

theorem tailTrace_4045948 : CollatzResearch.WordTrace tailWord_4045948 prefixEnd_4045948 461670228243831431898451 := by
  unfold tailWord_4045948
  simp only [CollatzResearch.WordTrace]
  refine ⟨73783923373114431875377249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98378564497485909167169665 73783923373114431875377249)
  ·
    refine ⟨55337942529835823906532937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73783923373114431875377249 55337942529835823906532937)
    ·
      refine ⟨41503456897376867929899703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55337942529835823906532937 41503456897376867929899703)
      ·
        refine ⟨62255185346065301894849555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41503456897376867929899703 62255185346065301894849555)
        ·
          refine ⟨93382778019097952842274333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62255185346065301894849555 93382778019097952842274333)
          ·
            refine ⟨35018541757161732315852875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93382778019097952842274333 35018541757161732315852875)
            ·
              refine ⟨52527812635742598473779313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35018541757161732315852875 52527812635742598473779313)
              ·
                refine ⟨39395859476806948855334485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52527812635742598473779313 39395859476806948855334485)
                ·
                  refine ⟨461670228243831431898451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39395859476806948855334485 461670228243831431898451)
                  ·
                    rfl

theorem cell22_4045948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_4045948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045948 prefixEnd_4045948 := by exact prefixLift 4045948
  have htrace : WordTrace (prefixWord ++ tailWord_4045948) baseStart_4045948 baseEnd_4045948 := by
    simpa [prefixWord, tailWord_4045948, baseEnd_4045948] using wordTrace_append hprefix tailTrace_4045948
  have hstable : (prefixWord ++ tailWord_4045948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045948).length < 2 ^ (prefixWord ++ tailWord_4045948).sum := by decide
  have hdescent : baseEnd_4045948 < baseStart_4045948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045963 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_4045963 : Nat := 118140960795 + 4045963 * 2 ^ 59
def prefixEnd_4045963 : Nat := 4983230072969 + 3 ^ 40 * 4045963 * 2
def baseEnd_4045963 : Nat := 1385015819538039256570307

theorem tailTrace_4045963 : CollatzResearch.WordTrace tailWord_4045963 prefixEnd_4045963 1385015819538039256570307 := by
  unfold tailWord_4045963
  simp only [CollatzResearch.WordTrace]
  refine ⟨147568393841174521312550543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98378929227449680875033695 147568393841174521312550543)
  ·
    refine ⟨221352590761761781968825815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147568393841174521312550543 221352590761761781968825815)
    ·
      refine ⟨332028886142642672953238723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221352590761761781968825815 332028886142642672953238723)
      ·
        refine ⟨498043329213964009429858085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332028886142642672953238723 498043329213964009429858085)
        ·
          refine ⟨93383124227618251768098391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498043329213964009429858085 93383124227618251768098391)
          ·
            refine ⟨140074686341427377652147587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93383124227618251768098391 140074686341427377652147587)
            ·
              refine ⟨210112029512141066478221381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140074686341427377652147587 210112029512141066478221381)
              ·
                refine ⟨39396005533526449964666509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210112029512141066478221381 39396005533526449964666509)
                ·
                  refine ⟨14773502075072418736749941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39396005533526449964666509 14773502075072418736749941)
                  ·
                    refine ⟨1385015819538039256570307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14773502075072418736749941 1385015819538039256570307)
                    ·
                      rfl

theorem cell22_4045963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_4045963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045963 prefixEnd_4045963 := by exact prefixLift 4045963
  have htrace : WordTrace (prefixWord ++ tailWord_4045963) baseStart_4045963 baseEnd_4045963 := by
    simpa [prefixWord, tailWord_4045963, baseEnd_4045963] using wordTrace_append hprefix tailTrace_4045963
  have hstable : (prefixWord ++ tailWord_4045963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045963).length < 2 ^ (prefixWord ++ tailWord_4045963).sum := by decide
  have hdescent : baseEnd_4045963 < baseStart_4045963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045982 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_4045982 : Nat := 118140960795 + 4045982 * 2 ^ 59
def prefixEnd_4045982 : Nat := 4983230072969 + 3 ^ 40 * 4045982 * 2
def baseEnd_4045982 : Nat := 461674107875443180115083

theorem tailTrace_4045982 : CollatzResearch.WordTrace tailWord_4045982 prefixEnd_4045982 461674107875443180115083 := by
  unfold tailWord_4045982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446135853513210944686525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98379391218737125038328133 18446135853513210944686525)
  ·
    refine ⟨6917300945067454104257447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18446135853513210944686525 6917300945067454104257447)
    ·
      refine ⟨10375951417601181156386171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917300945067454104257447 10375951417601181156386171)
      ·
        refine ⟨15563927126401771734579257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10375951417601181156386171 15563927126401771734579257)
        ·
          refine ⟨11672945344801328800934443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15563927126401771734579257 11672945344801328800934443)
          ·
            refine ⟨17509418017201993201401665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672945344801328800934443 17509418017201993201401665)
            ·
              refine ⟨13132063512901494901051249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17509418017201993201401665 13132063512901494901051249)
              ·
                refine ⟨9849047634676121175788437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13132063512901494901051249 9849047634676121175788437)
                ·
                  refine ⟨461674107875443180115083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9849047634676121175788437 461674107875443180115083)
                  ·
                    rfl

theorem cell22_4045982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_4045982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4045982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4045982 prefixEnd_4045982 := by exact prefixLift 4045982
  have htrace : WordTrace (prefixWord ++ tailWord_4045982) baseStart_4045982 baseEnd_4045982 := by
    simpa [prefixWord, tailWord_4045982, baseEnd_4045982] using wordTrace_append hprefix tailTrace_4045982
  have hstable : (prefixWord ++ tailWord_4045982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045982).length < 2 ^ (prefixWord ++ tailWord_4045982).sum := by decide
  have hdescent : baseEnd_4045982 < baseStart_4045982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046012 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_4046012 : Nat := 118140960795 + 4046012 * 2 ^ 59
def prefixEnd_4046012 : Nat := 4983230072969 + 3 ^ 40 * 4046012 * 2
def baseEnd_4046012 : Nat := 1385032593239419462095157

theorem tailTrace_4046012 : CollatzResearch.WordTrace tailWord_4046012 prefixEnd_4046012 1385032593239419462095157 := by
  unfold tailWord_4046012
  simp only [CollatzResearch.WordTrace]
  refine ⟨73785090508998501340542145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98380120678664668454056193 73785090508998501340542145)
  ·
    refine ⟨55338817881748876005406609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73785090508998501340542145 55338817881748876005406609)
    ·
      refine ⟨41504113411311657004054957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55338817881748876005406609 41504113411311657004054957)
      ·
        refine ⟨15564042529241871376520609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41504113411311657004054957 15564042529241871376520609)
        ·
          refine ⟨11673031896931403532390457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15564042529241871376520609 11673031896931403532390457)
          ·
            refine ⟨8754773922698552649292843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11673031896931403532390457 8754773922698552649292843)
            ·
              refine ⟨13132160884047828973939265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754773922698552649292843 13132160884047828973939265)
              ·
                refine ⟨9849120663035871730454449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13132160884047828973939265 9849120663035871730454449)
                ·
                  refine ⟨7386840497276903797840837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9849120663035871730454449 7386840497276903797840837)
                  ·
                    refine ⟨1385032593239419462095157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386840497276903797840837 1385032593239419462095157)
                    ·
                      rfl

theorem cell22_4046012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_4046012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046012 prefixEnd_4046012 := by exact prefixLift 4046012
  have htrace : WordTrace (prefixWord ++ tailWord_4046012) baseStart_4046012 baseEnd_4046012 := by
    simpa [prefixWord, tailWord_4046012, baseEnd_4046012] using wordTrace_append hprefix tailTrace_4046012
  have hstable : (prefixWord ++ tailWord_4046012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046012).length < 2 ^ (prefixWord ++ tailWord_4046012).sum := by decide
  have hdescent : baseEnd_4046012 < baseStart_4046012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046076 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_4046076 : Nat := 118140960795 + 4046076 * 2 ^ 59
def prefixEnd_4046076 : Nat := 4983230072969 + 3 ^ 40 * 4046076 * 2
def baseEnd_4046076 : Nat := 1385054501747344628494961

theorem tailTrace_4046076 : CollatzResearch.WordTrace tailWord_4046076 prefixEnd_4046076 1385054501747344628494961 := by
  unfold tailWord_4046076
  simp only [CollatzResearch.WordTrace]
  refine ⟨73786257644882570805707041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98381676859843427740942721 73786257644882570805707041)
  ·
    refine ⟨55339693233661928104280281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73786257644882570805707041 55339693233661928104280281)
    ·
      refine ⟨41504769925246446078210211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55339693233661928104280281 41504769925246446078210211)
      ·
        refine ⟨62257154887869669117315317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41504769925246446078210211 62257154887869669117315317)
        ·
          refine ⟨5836608270737781479748311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62257154887869669117315317 5836608270737781479748311)
          ·
            refine ⟨8754912406106672219622467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836608270737781479748311 8754912406106672219622467)
            ·
              refine ⟨13132368609160008329433701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754912406106672219622467 13132368609160008329433701)
              ·
                refine ⟨2462319114217501561768819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13132368609160008329433701 2462319114217501561768819)
                ·
                  refine ⟨3693478671326252342653229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462319114217501561768819 3693478671326252342653229)
                  ·
                    refine ⟨1385054501747344628494961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693478671326252342653229 1385054501747344628494961)
                    ·
                      rfl

theorem cell22_4046076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_4046076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046076 prefixEnd_4046076 := by exact prefixLift 4046076
  have htrace : WordTrace (prefixWord ++ tailWord_4046076) baseStart_4046076 baseEnd_4046076 := by
    simpa [prefixWord, tailWord_4046076, baseEnd_4046076] using wordTrace_append hprefix tailTrace_4046076
  have hstable : (prefixWord ++ tailWord_4046076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046076).length < 2 ^ (prefixWord ++ tailWord_4046076).sum := by decide
  have hdescent : baseEnd_4046076 < baseStart_4046076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046085 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_4046085 : Nat := 118140960795 + 4046085 * 2 ^ 59
def prefixEnd_4046085 : Nat := 4983230072969 + 3 ^ 40 * 4046085 * 2
def baseEnd_4046085 : Nat := 1385057582631271605019933

theorem tailTrace_4046085 : CollatzResearch.WordTrace tailWord_4046085 prefixEnd_4046085 1385057582631271605019933 := by
  unfold tailWord_4046085
  simp only [CollatzResearch.WordTrace]
  refine ⟨147572843546732536148491709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98381895697821690765661139 147572843546732536148491709)
  ·
    refine ⟨55339816330024701055684391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147572843546732536148491709 55339816330024701055684391)
    ·
      refine ⟨83009724495037051583526587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55339816330024701055684391 83009724495037051583526587)
      ·
        refine ⟨124514586742555577375289881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83009724495037051583526587 124514586742555577375289881)
        ·
          refine ⟨93385940056916683031467411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124514586742555577375289881 93385940056916683031467411)
          ·
            refine ⟨140078910085375024547201117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93385940056916683031467411 140078910085375024547201117)
            ·
              refine ⟨52529591282015634205200419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140078910085375024547201117 52529591282015634205200419)
              ·
                refine ⟨78794386923023451307800629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52529591282015634205200419 78794386923023451307800629)
                ·
                  refine ⟨7386973774033448560106309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78794386923023451307800629 7386973774033448560106309)
                  ·
                    refine ⟨1385057582631271605019933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386973774033448560106309 1385057582631271605019933)
                    ·
                      rfl

theorem cell22_4046085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_4046085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046085 prefixEnd_4046085 := by exact prefixLift 4046085
  have htrace : WordTrace (prefixWord ++ tailWord_4046085) baseStart_4046085 baseEnd_4046085 := by
    simpa [prefixWord, tailWord_4046085, baseEnd_4046085] using wordTrace_append hprefix tailTrace_4046085
  have hstable : (prefixWord ++ tailWord_4046085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046085).length < 2 ^ (prefixWord ++ tailWord_4046085).sum := by decide
  have hdescent : baseEnd_4046085 < baseStart_4046085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046110 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4046110 : Nat := 118140960795 + 4046110 * 2 ^ 59
def prefixEnd_4046110 : Nat := 4983230072969 + 3 ^ 40 * 4046110 * 2
def baseEnd_4046110 : Nat := 1385066140642179873144857

theorem tailTrace_4046110 : CollatzResearch.WordTrace tailWord_4046110 prefixEnd_4046110 1385066140642179873144857 := by
  unfold tailWord_4046110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446719421455245677268973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98382503581094643612101189 18446719421455245677268973)
  ·
    refine ⟨6917519783045717128975865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18446719421455245677268973 6917519783045717128975865)
    ·
      refine ⟨5188139837284287846731899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6917519783045717128975865 5188139837284287846731899)
      ·
        refine ⟨7782209755926431770097849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188139837284287846731899 7782209755926431770097849)
        ·
          refine ⟨5836657316944823827573387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7782209755926431770097849 5836657316944823827573387)
          ·
            refine ⟨8754985975417235741360081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836657316944823827573387 8754985975417235741360081)
            ·
              refine ⟨6566239481562926806020061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8754985975417235741360081 6566239481562926806020061)
              ·
                refine ⟨2462339805586097552257523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6566239481562926806020061 2462339805586097552257523)
                ·
                  refine ⟨3693509708379146328386285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462339805586097552257523 3693509708379146328386285)
                  ·
                    refine ⟨1385066140642179873144857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693509708379146328386285 1385066140642179873144857)
                    ·
                      rfl

theorem cell22_4046110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4046110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046110 prefixEnd_4046110 := by exact prefixLift 4046110
  have htrace : WordTrace (prefixWord ++ tailWord_4046110) baseStart_4046110 baseEnd_4046110 := by
    simpa [prefixWord, tailWord_4046110, baseEnd_4046110] using wordTrace_append hprefix tailTrace_4046110
  have hstable : (prefixWord ++ tailWord_4046110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046110).length < 2 ^ (prefixWord ++ tailWord_4046110).sum := by decide
  have hdescent : baseEnd_4046110 < baseStart_4046110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046160 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_4046160 : Nat := 118140960795 + 4046160 * 2 ^ 59
def prefixEnd_4046160 : Nat := 4983230072969 + 3 ^ 40 * 4046160 * 2
def baseEnd_4046160 : Nat := 1385083256663996409394703

theorem tailTrace_4046160 : CollatzResearch.WordTrace tailWord_4046160 prefixEnd_4046160 1385083256663996409394703 := by
  unfold tailWord_4046160
  simp only [CollatzResearch.WordTrace]
  refine ⟨73787789510730411978735967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98383719347640549304981289 73787789510730411978735967)
  ·
    refine ⟨110681684266095617968103951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73787789510730411978735967 110681684266095617968103951)
    ·
      refine ⟨166022526399143426952155927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110681684266095617968103951 166022526399143426952155927)
      ·
        refine ⟨249033789598715140428233891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166022526399143426952155927 249033789598715140428233891)
        ·
          refine ⟨373550684398072710642350837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249033789598715140428233891 373550684398072710642350837)
          ·
            refine ⟨35020376662319316622720391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373550684398072710642350837 35020376662319316622720391)
            ·
              refine ⟨52530564993478974934080587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35020376662319316622720391 52530564993478974934080587)
              ·
                refine ⟨78795847490218462401120881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52530564993478974934080587 78795847490218462401120881)
                ·
                  refine ⟨59096885617663846800840661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78795847490218462401120881 59096885617663846800840661)
                  ·
                    refine ⟨1385083256663996409394703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59096885617663846800840661 1385083256663996409394703)
                    ·
                      rfl

theorem cell22_4046160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_4046160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046160 prefixEnd_4046160 := by exact prefixLift 4046160
  have htrace : WordTrace (prefixWord ++ tailWord_4046160) baseStart_4046160 baseEnd_4046160 := by
    simpa [prefixWord, tailWord_4046160, baseEnd_4046160] using wordTrace_append hprefix tailTrace_4046160
  have hstable : (prefixWord ++ tailWord_4046160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046160).length < 2 ^ (prefixWord ++ tailWord_4046160).sum := by decide
  have hdescent : baseEnd_4046160 < baseStart_4046160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046175 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_4046175 : Nat := 118140960795 + 4046175 * 2 ^ 59
def prefixEnd_4046175 : Nat := 4983230072969 + 3 ^ 40 * 4046175 * 2
def baseEnd_4046175 : Nat := 1385088391470541370269657

theorem tailTrace_4046175 : CollatzResearch.WordTrace tailWord_4046175 prefixEnd_4046175 1385088391470541370269657 := by
  unfold tailWord_4046175
  simp only [CollatzResearch.WordTrace]
  refine ⟨147576126116406481519267979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98384084077604321012845319 147576126116406481519267979)
  ·
    refine ⟨221364189174609722278901969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147576126116406481519267979 221364189174609722278901969)
    ·
      refine ⟨166023141880957291709176477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221364189174609722278901969 166023141880957291709176477)
      ·
        refine ⟨62258678205358984390941179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166023141880957291709176477 62258678205358984390941179)
        ·
          refine ⟨93388017308038476586411769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62258678205358984390941179 93388017308038476586411769)
          ·
            refine ⟨70041012981028857439808827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93388017308038476586411769 70041012981028857439808827)
            ·
              refine ⟨105061519471543286159713241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70041012981028857439808827 105061519471543286159713241)
              ·
                refine ⟨78796139603657464619784931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105061519471543286159713241 78796139603657464619784931)
                ·
                  refine ⟨118194209405486196929677397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78796139603657464619784931 118194209405486196929677397)
                  ·
                    refine ⟨1385088391470541370269657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118194209405486196929677397 1385088391470541370269657)
                    ·
                      rfl

theorem cell22_4046175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_4046175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046175 prefixEnd_4046175 := by exact prefixLift 4046175
  have htrace : WordTrace (prefixWord ++ tailWord_4046175) baseStart_4046175 baseEnd_4046175 := by
    simpa [prefixWord, tailWord_4046175, baseEnd_4046175] using wordTrace_append hprefix tailTrace_4046175
  have hstable : (prefixWord ++ tailWord_4046175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046175).length < 2 ^ (prefixWord ++ tailWord_4046175).sum := by decide
  have hdescent : baseEnd_4046175 < baseStart_4046175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046177 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_4046177 : Nat := 118140960795 + 4046177 * 2 ^ 59
def prefixEnd_4046177 : Nat := 4983230072969 + 3 ^ 40 * 4046177 * 2
def baseEnd_4046177 : Nat := 1385089076111414031719651

theorem tailTrace_4046177 : CollatzResearch.WordTrace tailWord_4046177 prefixEnd_4046177 1385089076111414031719651 := by
  unfold tailWord_4046177
  simp only [CollatzResearch.WordTrace]
  refine ⟨147576199062399235860840785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98384132708266157240560523 147576199062399235860840785)
  ·
    refine ⟨110682149296799426895630589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147576199062399235860840785 110682149296799426895630589)
    ·
      refine ⟨41505805986299785085861471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110682149296799426895630589 41505805986299785085861471)
      ·
        refine ⟨62258708979449677628792207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41505805986299785085861471 62258708979449677628792207)
        ·
          refine ⟨93388063469174516443188311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62258708979449677628792207 93388063469174516443188311)
          ·
            refine ⟨140082095203761774664782467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93388063469174516443188311 140082095203761774664782467)
            ·
              refine ⟨210123142805642661997173701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140082095203761774664782467 210123142805642661997173701)
              ·
                refine ⟨39398089276057999124470069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210123142805642661997173701 39398089276057999124470069)
                ·
                  refine ⟨3693570869630437417919069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39398089276057999124470069 3693570869630437417919069)
                  ·
                    refine ⟨1385089076111414031719651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693570869630437417919069 1385089076111414031719651)
                    ·
                      rfl

theorem cell22_4046177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_4046177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046177 prefixEnd_4046177 := by exact prefixLift 4046177
  have htrace : WordTrace (prefixWord ++ tailWord_4046177) baseStart_4046177 baseEnd_4046177 := by
    simpa [prefixWord, tailWord_4046177, baseEnd_4046177] using wordTrace_append hprefix tailTrace_4046177
  have hstable : (prefixWord ++ tailWord_4046177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046177).length < 2 ^ (prefixWord ++ tailWord_4046177).sum := by decide
  have hdescent : baseEnd_4046177 < baseStart_4046177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046284 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_4046284 : Nat := 118140960795 + 4046284 * 2 ^ 59
def prefixEnd_4046284 : Nat := 4983230072969 + 3 ^ 40 * 4046284 * 2
def baseEnd_4046284 : Nat := 1385125704398101419294323

theorem tailTrace_4046284 : CollatzResearch.WordTrace tailWord_4046284 prefixEnd_4046284 1385125704398101419294323 := by
  unfold tailWord_4046284
  simp only [CollatzResearch.WordTrace]
  refine ⟨73790050836505796567492953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98386734448674395423323937 73790050836505796567492953)
  ·
    refine ⟨55342538127379347425619715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73790050836505796567492953 55342538127379347425619715)
    ·
      refine ⟨83013807191069021138429573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55342538127379347425619715 83013807191069021138429573)
      ·
        refine ⟨15565088848325441463455545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83013807191069021138429573 15565088848325441463455545)
        ·
          refine ⟨11673816636244081097591659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15565088848325441463455545 11673816636244081097591659)
          ·
            refine ⟨17510724954366121646387489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673816636244081097591659 17510724954366121646387489)
            ·
              refine ⟨13133043715774591234790617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17510724954366121646387489 13133043715774591234790617)
              ·
                refine ⟨9849782786830943426092963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13133043715774591234790617 9849782786830943426092963)
                ·
                  refine ⟨14774674180246415139139445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9849782786830943426092963 14774674180246415139139445)
                  ·
                    refine ⟨1385125704398101419294323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14774674180246415139139445 1385125704398101419294323)
                    ·
                      rfl

theorem cell22_4046284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_4046284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046284 prefixEnd_4046284 := by exact prefixLift 4046284
  have htrace : WordTrace (prefixWord ++ tailWord_4046284) baseStart_4046284 baseEnd_4046284 := by
    simpa [prefixWord, tailWord_4046284, baseEnd_4046284] using wordTrace_append hprefix tailTrace_4046284
  have hstable : (prefixWord ++ tailWord_4046284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046284).length < 2 ^ (prefixWord ++ tailWord_4046284).sum := by decide
  have hdescent : baseEnd_4046284 < baseStart_4046284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046297 : List Nat := [1, 2, 1, 2, 4, 3, 9]
def baseStart_4046297 : Nat := 118140960795 + 4046297 * 2 ^ 59
def prefixEnd_4046297 : Nat := 4983230072969 + 3 ^ 40 * 4046297 * 2
def baseEnd_4046297 : Nat := 51301116835695322915529

theorem tailTrace_4046297 : CollatzResearch.WordTrace tailWord_4046297 prefixEnd_4046297 51301116835695322915529 := by
  unfold tailWord_4046297
  simp only [CollatzResearch.WordTrace]
  refine ⟨147580575821964496355209145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98387050547976330903472763 147580575821964496355209145)
  ·
    refine ⟨110685431866473372266406859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147580575821964496355209145 110685431866473372266406859)
    ·
      refine ⟨166028147799710058399610289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110685431866473372266406859 166028147799710058399610289)
      ·
        refine ⟨124521110849782543799707717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166028147799710058399610289 124521110849782543799707717)
        ·
          refine ⟨23347708284334226962445197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124521110849782543799707717 23347708284334226962445197)
          ·
            refine ⟨8755390606625335110916949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23347708284334226962445197 8755390606625335110916949)
            ·
              refine ⟨51301116835695322915529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8755390606625335110916949 51301116835695322915529)
              ·
                rfl

theorem cell22_4046297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 9].length) (baseStart_4046297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046297 prefixEnd_4046297 := by exact prefixLift 4046297
  have htrace : WordTrace (prefixWord ++ tailWord_4046297) baseStart_4046297 baseEnd_4046297 := by
    simpa [prefixWord, tailWord_4046297, baseEnd_4046297] using wordTrace_append hprefix tailTrace_4046297
  have hstable : (prefixWord ++ tailWord_4046297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046297).length < 2 ^ (prefixWord ++ tailWord_4046297).sum := by decide
  have hdescent : baseEnd_4046297 < baseStart_4046297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046301 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4046301 : Nat := 118140960795 + 4046301 * 2 ^ 59
def prefixEnd_4046301 : Nat := 4983230072969 + 3 ^ 40 * 4046301 * 2
def baseEnd_4046301 : Nat := 1385131523845519041619271

theorem tailTrace_4046301 : CollatzResearch.WordTrace tailWord_4046301 prefixEnd_4046301 1385131523845519041619271 := by
  unfold tailWord_4046301
  simp only [CollatzResearch.WordTrace]
  refine ⟨147580721713950005038354757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98387147809300003358903171 147580721713950005038354757)
  ·
    refine ⟨27671385321365625944691517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147580721713950005038354757 27671385321365625944691517)
    ·
      refine ⟨10376769495512109729259319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27671385321365625944691517 10376769495512109729259319)
      ·
        refine ⟨15565154243268164593888979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10376769495512109729259319 15565154243268164593888979)
        ·
          refine ⟨23347731364902246890833469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565154243268164593888979 23347731364902246890833469)
          ·
            refine ⟨8755399261838342584062551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23347731364902246890833469 8755399261838342584062551)
            ·
              refine ⟨13133098892757513876093827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755399261838342584062551 13133098892757513876093827)
              ·
                refine ⟨19699648339136270814140741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133098892757513876093827 19699648339136270814140741)
                ·
                  refine ⟨3693684063588050777651389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19699648339136270814140741 3693684063588050777651389)
                  ·
                    refine ⟨1385131523845519041619271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693684063588050777651389 1385131523845519041619271)
                    ·
                      rfl

theorem cell22_4046301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4046301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046301 prefixEnd_4046301 := by exact prefixLift 4046301
  have htrace : WordTrace (prefixWord ++ tailWord_4046301) baseStart_4046301 baseEnd_4046301 := by
    simpa [prefixWord, tailWord_4046301, baseEnd_4046301] using wordTrace_append hprefix tailTrace_4046301
  have hstable : (prefixWord ++ tailWord_4046301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046301).length < 2 ^ (prefixWord ++ tailWord_4046301).sum := by decide
  have hdescent : baseEnd_4046301 < baseStart_4046301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046318 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_4046318 : Nat := 118140960795 + 4046318 * 2 ^ 59
def prefixEnd_4046318 : Nat := 4983230072969 + 3 ^ 40 * 4046318 * 2
def baseEnd_4046318 : Nat := 1385137343292936663944219

theorem tailTrace_4046318 : CollatzResearch.WordTrace tailWord_4046318 prefixEnd_4046318 1385137343292936663944219 := by
  unfold tailWord_4046318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18447667719361052117715451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98387561169925611294482405 18447667719361052117715451)
  ·
    refine ⟨27671501579041578176573177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18447667719361052117715451 27671501579041578176573177)
    ·
      refine ⟨20753626184281183632429883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27671501579041578176573177 20753626184281183632429883)
      ·
        refine ⟨31130439276421775448644825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20753626184281183632429883 31130439276421775448644825)
        ·
          refine ⟨23347829457316331586483619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31130439276421775448644825 23347829457316331586483619)
          ·
            refine ⟨35021744185974497379725429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23347829457316331586483619 35021744185974497379725429)
            ·
              refine ⟨3283288517435109129349259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35021744185974497379725429 3283288517435109129349259)
              ·
                refine ⟨4924932776152663694023889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283288517435109129349259 4924932776152663694023889)
                ·
                  refine ⟨3693699582114497770517917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924932776152663694023889 3693699582114497770517917)
                  ·
                    refine ⟨1385137343292936663944219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693699582114497770517917 1385137343292936663944219)
                    ·
                      rfl

theorem cell22_4046318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_4046318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046318 prefixEnd_4046318 := by exact prefixLift 4046318
  have htrace : WordTrace (prefixWord ++ tailWord_4046318) baseStart_4046318 baseEnd_4046318 := by
    simpa [prefixWord, tailWord_4046318, baseEnd_4046318] using wordTrace_append hprefix tailTrace_4046318
  have hstable : (prefixWord ++ tailWord_4046318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046318).length < 2 ^ (prefixWord ++ tailWord_4046318).sum := by decide
  have hdescent : baseEnd_4046318 < baseStart_4046318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046436 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_4046436 : Nat := 118140960795 + 4046436 * 2 ^ 59
def prefixEnd_4046436 : Nat := 4983230072969 + 3 ^ 40 * 4046436 * 2
def baseEnd_4046436 : Nat := 1385177737104423689493857

theorem tailTrace_4046436 : CollatzResearch.WordTrace tailWord_4046436 prefixEnd_4046436 1385177737104423689493857 := by
  unfold tailWord_4046436
  simp only [CollatzResearch.WordTrace]
  refine ⟨73792822784230461547259581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98390430378973948729679441 73792822784230461547259581)
  ·
    refine ⟨27672308544086423080222343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73792822784230461547259581 27672308544086423080222343)
    ·
      refine ⟨41508462816129634620333515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27672308544086423080222343 41508462816129634620333515)
      ·
        refine ⟨62262694224194451930500273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41508462816129634620333515 62262694224194451930500273)
        ·
          refine ⟨46697020668145838947875205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62262694224194451930500273 46697020668145838947875205)
          ·
            refine ⟨8755691375277344802726601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46697020668145838947875205 8755691375277344802726601)
            ·
              refine ⟨6566768531458008602044951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8755691375277344802726601 6566768531458008602044951)
              ·
                refine ⟨9850152797187012903067427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6566768531458008602044951 9850152797187012903067427)
                ·
                  refine ⟨14775229195780519354601141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850152797187012903067427 14775229195780519354601141)
                  ·
                    refine ⟨1385177737104423689493857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14775229195780519354601141 1385177737104423689493857)
                    ·
                      rfl

theorem cell22_4046436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_4046436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046436 prefixEnd_4046436 := by exact prefixLift 4046436
  have htrace : WordTrace (prefixWord ++ tailWord_4046436) baseStart_4046436 baseEnd_4046436 := by
    simpa [prefixWord, tailWord_4046436, baseEnd_4046436] using wordTrace_append hprefix tailTrace_4046436
  have hstable : (prefixWord ++ tailWord_4046436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046436).length < 2 ^ (prefixWord ++ tailWord_4046436).sum := by decide
  have hdescent : baseEnd_4046436 < baseStart_4046436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046532 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_4046532 : Nat := 118140960795 + 4046532 * 2 ^ 59
def prefixEnd_4046532 : Nat := 4983230072969 + 3 ^ 40 * 4046532 * 2
def baseEnd_4046532 : Nat := 1385210599866311439093563

theorem tailTrace_4046532 : CollatzResearch.WordTrace tailWord_4046532 prefixEnd_4046532 1385210599866311439093563 := by
  unfold tailWord_4046532
  simp only [CollatzResearch.WordTrace]
  refine ⟨73794573488056565745006925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98392764650742087660009233 73794573488056565745006925)
  ·
    refine ⟨27672965058021212154377597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73794573488056565745006925 27672965058021212154377597)
    ·
      refine ⟨10377361896757954557891599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27672965058021212154377597 10377361896757954557891599)
      ·
        refine ⟨15566042845136931836837399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377361896757954557891599 15566042845136931836837399)
        ·
          refine ⟨23349064267705397755256099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15566042845136931836837399 23349064267705397755256099)
          ·
            refine ⟨35023596401558096632884149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23349064267705397755256099 35023596401558096632884149)
            ·
              refine ⟨3283462162646071559332889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35023596401558096632884149 3283462162646071559332889)
              ·
                refine ⟨2462596621984553669499667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283462162646071559332889 2462596621984553669499667)
                ·
                  refine ⟨3693894932976830504249501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462596621984553669499667 3693894932976830504249501)
                  ·
                    refine ⟨1385210599866311439093563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693894932976830504249501 1385210599866311439093563)
                    ·
                      rfl

theorem cell22_4046532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_4046532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046532 prefixEnd_4046532 := by exact prefixLift 4046532
  have htrace : WordTrace (prefixWord ++ tailWord_4046532) baseStart_4046532 baseEnd_4046532 := by
    simpa [prefixWord, tailWord_4046532, baseEnd_4046532] using wordTrace_append hprefix tailTrace_4046532
  have hstable : (prefixWord ++ tailWord_4046532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046532).length < 2 ^ (prefixWord ++ tailWord_4046532).sum := by decide
  have hdescent : baseEnd_4046532 < baseStart_4046532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046571 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 6, 3]
def baseStart_4046571 : Nat := 118140960795 + 4046571 * 2 ^ 59
def prefixEnd_4046571 : Nat := 4983230072969 + 3 ^ 40 * 4046571 * 2
def baseEnd_4046571 : Nat := 1385223950363328337368443

theorem tailTrace_4046571 : CollatzResearch.WordTrace tailWord_4046571 prefixEnd_4046571 1385223950363328337368443 := by
  unfold tailWord_4046571
  simp only [CollatzResearch.WordTrace]
  refine ⟨147590569422971841150683567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98393712948647894100455711 147590569422971841150683567)
  ·
    refine ⟨221385854134457761726025351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147590569422971841150683567 221385854134457761726025351)
    ·
      refine ⟨332078781201686642589038027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221385854134457761726025351 332078781201686642589038027)
      ·
        refine ⟨498118171802529963883557041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332078781201686642589038027 498118171802529963883557041)
        ·
          refine ⟨373588628851897472912667781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498118171802529963883557041 373588628851897472912667781)
          ·
            refine ⟨70047867909730776171125209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373588628851897472912667781 70047867909730776171125209)
            ·
              refine ⟨52535900932298082128343907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70047867909730776171125209 52535900932298082128343907)
              ·
                refine ⟨78803851398447123192515861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52535900932298082128343907 78803851398447123192515861)
                ·
                  refine ⟨3693930534302208899649181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78803851398447123192515861 3693930534302208899649181)
                  ·
                    refine ⟨1385223950363328337368443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693930534302208899649181 1385223950363328337368443)
                    ·
                      rfl

theorem cell22_4046571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 3].length) (baseStart_4046571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046571 prefixEnd_4046571 := by exact prefixLift 4046571
  have htrace : WordTrace (prefixWord ++ tailWord_4046571) baseStart_4046571 baseEnd_4046571 := by
    simpa [prefixWord, tailWord_4046571, baseEnd_4046571] using wordTrace_append hprefix tailTrace_4046571
  have hstable : (prefixWord ++ tailWord_4046571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046571).length < 2 ^ (prefixWord ++ tailWord_4046571).sum := by decide
  have hdescent : baseEnd_4046571 < baseStart_4046571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046618 : List Nat := [3, 1, 1, 3, 2, 3, 3, 6]
def baseStart_4046618 : Nat := 118140960795 + 4046618 * 2 ^ 59
def prefixEnd_4046618 : Nat := 4983230072969 + 3 ^ 40 * 4046618 * 2
def baseEnd_4046618 : Nat := 153915559935981764604811

theorem tailTrace_4046618 : CollatzResearch.WordTrace tailWord_4046618 prefixEnd_4046618 153915559935981764604811 := by
  unfold tailWord_4046618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36898070913450392044411127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98394855769201045451763005 36898070913450392044411127)
  ·
    refine ⟨55347106370175588066616691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36898070913450392044411127 55347106370175588066616691)
    ·
      refine ⟨83020659555263382099925037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55347106370175588066616691 83020659555263382099925037)
      ·
        refine ⟨31132747333223768287471889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83020659555263382099925037 31132747333223768287471889)
        ·
          refine ⟨23349560499917826215603917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31132747333223768287471889 23349560499917826215603917)
          ·
            refine ⟨8756085187469184830851469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23349560499917826215603917 8756085187469184830851469)
            ·
              refine ⟨3283531945300944311569301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8756085187469184830851469 3283531945300944311569301)
              ·
                refine ⟨153915559935981764604811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3283531945300944311569301 153915559935981764604811)
                ·
                  rfl

theorem cell22_4046618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_4046618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046618 prefixEnd_4046618 := by exact prefixLift 4046618
  have htrace : WordTrace (prefixWord ++ tailWord_4046618) baseStart_4046618 baseEnd_4046618 := by
    simpa [prefixWord, tailWord_4046618, baseEnd_4046618] using wordTrace_append hprefix tailTrace_4046618
  have hstable : (prefixWord ++ tailWord_4046618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046618).length < 2 ^ (prefixWord ++ tailWord_4046618).sum := by decide
  have hdescent : baseEnd_4046618 < baseStart_4046618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046650 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_4046650 : Nat := 118140960795 + 4046650 * 2 ^ 59
def prefixEnd_4046650 : Nat := 4983230072969 + 3 ^ 40 * 4046650 * 2
def baseEnd_4046650 : Nat := 1385250993677798464643201

theorem tailTrace_4046650 : CollatzResearch.WordTrace tailWord_4046650 prefixEnd_4046650 1385250993677798464643201 := by
  unfold tailWord_4046650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36898362697421409410702351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98395633859790425095206269 36898362697421409410702351)
  ·
    refine ⟨55347544046132114116053527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36898362697421409410702351 55347544046132114116053527)
    ·
      refine ⟨83021316069198171174080291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55347544046132114116053527 83021316069198171174080291)
      ·
        refine ⟨124531974103797256761120437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83021316069198171174080291 124531974103797256761120437)
        ·
          refine ⟨11674872572230992821355041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124531974103797256761120437 11674872572230992821355041)
          ·
            refine ⟨8756154429173244616016281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11674872572230992821355041 8756154429173244616016281)
            ·
              refine ⟨6567115821879933462012211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8756154429173244616016281 6567115821879933462012211)
              ·
                refine ⟨9850673732819900193018317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567115821879933462012211 9850673732819900193018317)
                ·
                  refine ⟨3694002649807462572381869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9850673732819900193018317 3694002649807462572381869)
                  ·
                    refine ⟨1385250993677798464643201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694002649807462572381869 1385250993677798464643201)
                    ·
                      rfl

theorem cell22_4046650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_4046650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046650 prefixEnd_4046650 := by exact prefixLift 4046650
  have htrace : WordTrace (prefixWord ++ tailWord_4046650) baseStart_4046650 baseEnd_4046650 := by
    simpa [prefixWord, tailWord_4046650, baseEnd_4046650] using wordTrace_append hprefix tailTrace_4046650
  have hstable : (prefixWord ++ tailWord_4046650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046650).length < 2 ^ (prefixWord ++ tailWord_4046650).sum := by decide
  have hdescent : baseEnd_4046650 < baseStart_4046650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046661 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_4046661 : Nat := 118140960795 + 4046661 * 2 ^ 59
def prefixEnd_4046661 : Nat := 4983230072969 + 3 ^ 40 * 4046661 * 2
def baseEnd_4046661 : Nat := 1385254759202598102618167

theorem tailTrace_4046661 : CollatzResearch.WordTrace tailWord_4046661 prefixEnd_4046661 1385254759202598102618167 := by
  unfold tailWord_4046661
  simp only [CollatzResearch.WordTrace]
  refine ⟨147593851992645786521459837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98395901328430524347639891 147593851992645786521459837)
  ·
    refine ⟨55347694497242169945547439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147593851992645786521459837 55347694497242169945547439)
    ·
      refine ⟨83021541745863254918321159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55347694497242169945547439 83021541745863254918321159)
      ·
        refine ⟨124532312618794882377481739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83021541745863254918321159 124532312618794882377481739)
        ·
          refine ⟨186798468928192323566222609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124532312618794882377481739 186798468928192323566222609)
          ·
            refine ⟨140098851696144242674666957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186798468928192323566222609 140098851696144242674666957)
            ·
              refine ⟨52537069386054091003000109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140098851696144242674666957 52537069386054091003000109)
              ·
                refine ⟨19701401019770284126125041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52537069386054091003000109 19701401019770284126125041)
                ·
                  refine ⟨14776050764827713094593781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19701401019770284126125041 14776050764827713094593781)
                  ·
                    refine ⟨1385254759202598102618167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14776050764827713094593781 1385254759202598102618167)
                    ·
                      rfl

theorem cell22_4046661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_4046661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046661 prefixEnd_4046661 := by exact prefixLift 4046661
  have htrace : WordTrace (prefixWord ++ tailWord_4046661) baseStart_4046661 baseEnd_4046661 := by
    simpa [prefixWord, tailWord_4046661, baseEnd_4046661] using wordTrace_append hprefix tailTrace_4046661
  have hstable : (prefixWord ++ tailWord_4046661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046661).length < 2 ^ (prefixWord ++ tailWord_4046661).sum := by decide
  have hdescent : baseEnd_4046661 < baseStart_4046661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046727 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 1, 4]
def baseStart_4046727 : Nat := 118140960795 + 4046727 * 2 ^ 59
def prefixEnd_4046727 : Nat := 4983230072969 + 3 ^ 40 * 4046727 * 2
def baseEnd_4046727 : Nat := 1385277352351395930467965

theorem tailTrace_4046727 : CollatzResearch.WordTrace tailWord_4046727 prefixEnd_4046727 1385277352351395930467965 := by
  unfold tailWord_4046727
  simp only [CollatzResearch.WordTrace]
  refine ⟨147596259210406679793362435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98397506140271119862241623 147596259210406679793362435)
  ·
    refine ⟨221394388815610019690043653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147596259210406679793362435 221394388815610019690043653)
    ·
      refine ⟨41511447902926878691883185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221394388815610019690043653 41511447902926878691883185)
      ·
        refine ⟨31133585927195159018912389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41511447902926878691883185 31133585927195159018912389)
        ·
          refine ⟨5837547361349092316046073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31133585927195159018912389 5837547361349092316046073)
          ·
            refine ⟨4378160521011819237034555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5837547361349092316046073 4378160521011819237034555)
            ·
              refine ⟨6567240781517728855551833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378160521011819237034555 6567240781517728855551833)
              ·
                refine ⟨4925430586138296641663875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6567240781517728855551833 4925430586138296641663875)
                ·
                  refine ⟨7388145879207444962495813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925430586138296641663875 7388145879207444962495813)
                  ·
                    refine ⟨1385277352351395930467965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388145879207444962495813 1385277352351395930467965)
                    ·
                      rfl

theorem cell22_4046727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_4046727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046727 prefixEnd_4046727 := by exact prefixLift 4046727
  have htrace : WordTrace (prefixWord ++ tailWord_4046727) baseStart_4046727 baseEnd_4046727 := by
    simpa [prefixWord, tailWord_4046727, baseEnd_4046727] using wordTrace_append hprefix tailTrace_4046727
  have hstable : (prefixWord ++ tailWord_4046727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046727).length < 2 ^ (prefixWord ++ tailWord_4046727).sum := by decide
  have hdescent : baseEnd_4046727 < baseStart_4046727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046740 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4046740 : Nat := 118140960795 + 4046740 * 2 ^ 59
def prefixEnd_4046740 : Nat := 4983230072969 + 3 ^ 40 * 4046740 * 2
def baseEnd_4046740 : Nat := 1385281802517068229892925

theorem tailTrace_4046740 : CollatzResearch.WordTrace tailWord_4046740 prefixEnd_4046740 1385281802517068229892925 := by
  unfold tailWord_4046740
  simp only [CollatzResearch.WordTrace]
  refine ⟨73798366679679791506792837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98397822239573055342390449 73798366679679791506792837)
  ·
    refine ⟨13837193752439960907523657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73798366679679791506792837 13837193752439960907523657)
    ·
      refine ⟨10377895314329970680642743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13837193752439960907523657 10377895314329970680642743)
      ·
        refine ⟨15566842971494956020964115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377895314329970680642743 15566842971494956020964115)
        ·
          refine ⟨23350264457242434031446173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15566842971494956020964115 23350264457242434031446173)
          ·
            refine ⟨8756349171465912761792315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23350264457242434031446173 8756349171465912761792315)
            ·
              refine ⟨13134523757198869142688473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756349171465912761792315 13134523757198869142688473)
              ·
                refine ⟨9850892817899151857016355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13134523757198869142688473 9850892817899151857016355)
                ·
                  refine ⟨14776339226848727785524533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850892817899151857016355 14776339226848727785524533)
                  ·
                    refine ⟨1385281802517068229892925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14776339226848727785524533 1385281802517068229892925)
                    ·
                      rfl

theorem cell22_4046740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4046740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046740 prefixEnd_4046740 := by exact prefixLift 4046740
  have htrace : WordTrace (prefixWord ++ tailWord_4046740) baseStart_4046740 baseEnd_4046740 := by
    simpa [prefixWord, tailWord_4046740, baseEnd_4046740] using wordTrace_append hprefix tailTrace_4046740
  have hstable : (prefixWord ++ tailWord_4046740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046740).length < 2 ^ (prefixWord ++ tailWord_4046740).sum := by decide
  have hdescent : baseEnd_4046740 < baseStart_4046740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046744 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 1, 4]
def baseStart_4046744 : Nat := 118140960795 + 4046744 * 2 ^ 59
def prefixEnd_4046744 : Nat := 4983230072969 + 3 ^ 40 * 4046744 * 2
def baseEnd_4046744 : Nat := 1385283171798813552792913

theorem tailTrace_4046744 : CollatzResearch.WordTrace tailWord_4046744 prefixEnd_4046744 1385283171798813552792913 := by
  unfold tailWord_4046744
  simp only [CollatzResearch.WordTrace]
  refine ⟨73798439625672545848365643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98397919500896727797820857 73798439625672545848365643)
  ·
    refine ⟨110697659438508818772548465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73798439625672545848365643 110697659438508818772548465)
    ·
      refine ⟨83023244578881614079411349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110697659438508818772548465 83023244578881614079411349)
      ·
        refine ⟨3891714589635075659972407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83023244578881614079411349 3891714589635075659972407)
        ·
          refine ⟨5837571884452613489958611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891714589635075659972407 5837571884452613489958611)
          ·
            refine ⟨8756357826678920234937917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837571884452613489958611 8756357826678920234937917)
            ·
              refine ⟨3283634185004595088101719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8756357826678920234937917 3283634185004595088101719)
              ·
                refine ⟨4925451277506892632152579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283634185004595088101719 4925451277506892632152579)
                ·
                  refine ⟨7388176916260338948228869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925451277506892632152579 7388176916260338948228869)
                  ·
                    refine ⟨1385283171798813552792913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388176916260338948228869 1385283171798813552792913)
                    ·
                      rfl

theorem cell22_4046744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_4046744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046744 prefixEnd_4046744 := by exact prefixLift 4046744
  have htrace : WordTrace (prefixWord ++ tailWord_4046744) baseStart_4046744 baseEnd_4046744 := by
    simpa [prefixWord, tailWord_4046744, baseEnd_4046744] using wordTrace_append hprefix tailTrace_4046744
  have hstable : (prefixWord ++ tailWord_4046744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046744).length < 2 ^ (prefixWord ++ tailWord_4046744).sum := by decide
  have hdescent : baseEnd_4046744 < baseStart_4046744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046753 : List Nat := [1, 2, 3, 4, 2, 10]
def baseStart_4046753 : Nat := 118140960795 + 4046753 * 2 ^ 59
def prefixEnd_4046753 : Nat := 4983230072969 + 3 ^ 40 * 4046753 * 2
def baseEnd_4046753 : Nat := 17102299415836302831085

theorem tailTrace_4046753 : CollatzResearch.WordTrace tailWord_4046753 prefixEnd_4046753 17102299415836302831085 := by
  unfold tailWord_4046753
  simp only [CollatzResearch.WordTrace]
  refine ⟨147597207508312486233808913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98398138338874990822539275 147597207508312486233808913)
  ·
    refine ⟨110697905631234364675356685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147597207508312486233808913 110697905631234364675356685)
    ·
      refine ⟨41511714611712886753258757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110697905631234364675356685 41511714611712886753258757)
      ·
        refine ⟨7783446489696166266236017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41511714611712886753258757 7783446489696166266236017)
        ·
          refine ⟨5837584867272124699677013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783446489696166266236017 5837584867272124699677013)
          ·
            refine ⟨17102299415836302831085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5837584867272124699677013 17102299415836302831085)
            ·
              rfl

theorem cell22_4046753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 10].length) (baseStart_4046753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046753 prefixEnd_4046753 := by exact prefixLift 4046753
  have htrace : WordTrace (prefixWord ++ tailWord_4046753) baseStart_4046753 baseEnd_4046753 := by
    simpa [prefixWord, tailWord_4046753, baseEnd_4046753] using wordTrace_append hprefix tailTrace_4046753
  have hstable : (prefixWord ++ tailWord_4046753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046753).length < 2 ^ (prefixWord ++ tailWord_4046753).sum := by decide
  have hdescent : baseEnd_4046753 < baseStart_4046753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046759 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 4]
def baseStart_4046759 : Nat := 118140960795 + 4046759 * 2 ^ 59
def prefixEnd_4046759 : Nat := 4983230072969 + 3 ^ 40 * 4046759 * 2
def baseEnd_4046759 : Nat := 461762768868452837889289

theorem tailTrace_4046759 : CollatzResearch.WordTrace tailWord_4046759 prefixEnd_4046759 461762768868452837889289 := by
  unfold tailWord_4046759
  simp only [CollatzResearch.WordTrace]
  refine ⟨147597426346290749258527331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98398284230860499505684887 147597426346290749258527331)
  ·
    refine ⟨221396139519436123887790997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147597426346290749258527331 221396139519436123887790997)
    ·
      refine ⟨10377944039973568307240203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221396139519436123887790997 10377944039973568307240203)
      ·
        refine ⟨15566916059960352460860305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377944039973568307240203 15566916059960352460860305)
        ·
          refine ⟨11675187044970264345645229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15566916059960352460860305 11675187044970264345645229)
          ·
            refine ⟨4378195141863849129616961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11675187044970264345645229 4378195141863849129616961)
            ·
              refine ⟨3283646356397886847212721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378195141863849129616961 3283646356397886847212721)
              ·
                refine ⟨2462734767298415135409541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283646356397886847212721 2462734767298415135409541)
                ·
                  refine ⟨461762768868452837889289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2462734767298415135409541 461762768868452837889289)
                  ·
                    rfl

theorem cell22_4046759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 4].length) (baseStart_4046759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046759 prefixEnd_4046759 := by exact prefixLift 4046759
  have htrace : WordTrace (prefixWord ++ tailWord_4046759) baseStart_4046759 baseEnd_4046759 := by
    simpa [prefixWord, tailWord_4046759, baseEnd_4046759] using wordTrace_append hprefix tailTrace_4046759
  have hstable : (prefixWord ++ tailWord_4046759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046759).length < 2 ^ (prefixWord ++ tailWord_4046759).sum := by decide
  have hdescent : baseEnd_4046759 < baseStart_4046759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046768 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_4046768 : Nat := 118140960795 + 4046768 * 2 ^ 59
def prefixEnd_4046768 : Nat := 4983230072969 + 3 ^ 40 * 4046768 * 2
def baseEnd_4046768 : Nat := 1385291387489285490192839

theorem tailTrace_4046768 : CollatzResearch.WordTrace tailWord_4046768 prefixEnd_4046768 1385291387489285490192839 := by
  unfold tailWord_4046768
  simp only [CollatzResearch.WordTrace]
  refine ⟨73798877301629071897802479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98398503068838762530403305 73798877301629071897802479)
  ·
    refine ⟨110698315952443607846703719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73798877301629071897802479 110698315952443607846703719)
    ·
      refine ⟨166047473928665411770055579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110698315952443607846703719 166047473928665411770055579)
      ·
        refine ⟨249071210892998117655083369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166047473928665411770055579 249071210892998117655083369)
        ·
          refine ⟨186803408169748588241312527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249071210892998117655083369 186803408169748588241312527)
          ·
            refine ⟨280205112254622882361968791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186803408169748588241312527 280205112254622882361968791)
            ·
              refine ⟨420307668381934323542953187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280205112254622882361968791 420307668381934323542953187)
              ·
                refine ⟨630461502572901485314429781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420307668381934323542953187 630461502572901485314429781)
                ·
                  refine ⟨3694110366638094640514237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 630461502572901485314429781 3694110366638094640514237)
                  ·
                    refine ⟨1385291387489285490192839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694110366638094640514237 1385291387489285490192839)
                    ·
                      rfl

theorem cell22_4046768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_4046768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046768 prefixEnd_4046768 := by exact prefixLift 4046768
  have htrace : WordTrace (prefixWord ++ tailWord_4046768) baseStart_4046768 baseEnd_4046768 := by
    simpa [prefixWord, tailWord_4046768, baseEnd_4046768] using wordTrace_append hprefix tailTrace_4046768
  have hstable : (prefixWord ++ tailWord_4046768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046768).length < 2 ^ (prefixWord ++ tailWord_4046768).sum := by decide
  have hdescent : baseEnd_4046768 < baseStart_4046768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046798 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_4046798 : Nat := 118140960795 + 4046798 * 2 ^ 59
def prefixEnd_4046798 : Nat := 4983230072969 + 3 ^ 40 * 4046798 * 2
def baseEnd_4046798 : Nat := 461767219034125137314249

theorem tailTrace_4046798 : CollatzResearch.WordTrace tailWord_4046798 prefixEnd_4046798 461767219034125137314249 := by
  unfold tailWord_4046798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449856099143682364899631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98399232528766305946131365 18449856099143682364899631)
  ·
    refine ⟨27674784148715523547349447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18449856099143682364899631 27674784148715523547349447)
    ·
      refine ⟨41512176223073285321024171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27674784148715523547349447 41512176223073285321024171)
      ·
        refine ⟨62268264334609927981536257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41512176223073285321024171 62268264334609927981536257)
        ·
          refine ⟨46701198250957445986152193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62268264334609927981536257 46701198250957445986152193)
          ·
            refine ⟨35025898688218084489614145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46701198250957445986152193 35025898688218084489614145)
            ·
              refine ⟨26269424016163563367210609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35025898688218084489614145 26269424016163563367210609)
              ·
                refine ⟨19702068012122672525407957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26269424016163563367210609 19702068012122672525407957)
                ·
                  refine ⟨461767219034125137314249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19702068012122672525407957 461767219034125137314249)
                  ·
                    rfl

theorem cell22_4046798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_4046798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046798 prefixEnd_4046798 := by exact prefixLift 4046798
  have htrace : WordTrace (prefixWord ++ tailWord_4046798) baseStart_4046798 baseEnd_4046798 := by
    simpa [prefixWord, tailWord_4046798, baseEnd_4046798] using wordTrace_append hprefix tailTrace_4046798
  have hstable : (prefixWord ++ tailWord_4046798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046798).length < 2 ^ (prefixWord ++ tailWord_4046798).sum := by decide
  have hdescent : baseEnd_4046798 < baseStart_4046798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046815 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 5]
def baseStart_4046815 : Nat := 118140960795 + 4046815 * 2 ^ 59
def prefixEnd_4046815 : Nat := 4983230072969 + 3 ^ 40 * 4046815 * 2
def baseEnd_4046815 : Nat := 461769158849931011422565

theorem tailTrace_4046815 : CollatzResearch.WordTrace tailWord_4046815 prefixEnd_4046815 461769158849931011422565 := by
  unfold tailWord_4046815
  simp only [CollatzResearch.WordTrace]
  refine ⟨147599468834087870822565899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98399645889391913881710599 147599468834087870822565899)
  ·
    refine ⟨221399203251131806233848849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147599468834087870822565899 221399203251131806233848849)
    ·
      refine ⟨166049402438348854675386637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221399203251131806233848849 166049402438348854675386637)
      ·
        refine ⟨62268525914380820503269989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166049402438348854675386637 62268525914380820503269989)
        ·
          refine ⟨11675348608946403844363123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62268525914380820503269989 11675348608946403844363123)
          ·
            refine ⟨17513022913419605766544685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11675348608946403844363123 17513022913419605766544685)
            ·
              refine ⟨6567383592532352162454257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17513022913419605766544685 6567383592532352162454257)
              ·
                refine ⟨4925537694399264121840693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6567383592532352162454257 4925537694399264121840693)
                ·
                  refine ⟨461769158849931011422565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4925537694399264121840693 461769158849931011422565)
                  ·
                    rfl

theorem cell22_4046815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 5].length) (baseStart_4046815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046815 prefixEnd_4046815 := by exact prefixLift 4046815
  have htrace : WordTrace (prefixWord ++ tailWord_4046815) baseStart_4046815 baseEnd_4046815 := by
    simpa [prefixWord, tailWord_4046815, baseEnd_4046815] using wordTrace_append hprefix tailTrace_4046815
  have hstable : (prefixWord ++ tailWord_4046815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046815).length < 2 ^ (prefixWord ++ tailWord_4046815).sum := by decide
  have hdescent : baseEnd_4046815 < baseStart_4046815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046828 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_4046828 : Nat := 118140960795 + 4046828 * 2 ^ 59
def prefixEnd_4046828 : Nat := 4983230072969 + 3 ^ 40 * 4046828 * 2
def baseEnd_4046828 : Nat := 1385311926715465333692655

theorem tailTrace_4046828 : CollatzResearch.WordTrace tailWord_4046828 prefixEnd_4046828 1385311926715465333692655 := by
  unfold tailWord_4046828
  simp only [CollatzResearch.WordTrace]
  refine ⟨73799971491520387021394569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98399961988693849361859425 73799971491520387021394569)
  ·
    refine ⟨55349978618640290266045927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73799971491520387021394569 55349978618640290266045927)
    ·
      refine ⟨83024967927960435399068891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55349978618640290266045927 83024967927960435399068891)
      ·
        refine ⟨124537451891940653098603337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83024967927960435399068891 124537451891940653098603337)
        ·
          refine ⟨93403088918955489823952503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124537451891940653098603337 93403088918955489823952503)
          ·
            refine ⟨140104633378433234735928755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93403088918955489823952503 140104633378433234735928755)
            ·
              refine ⟨210156950067649852103893133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140104633378433234735928755 210156950067649852103893133)
              ·
                refine ⟨78808856275368694538959925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210156950067649852103893133 78808856275368694538959925)
                ·
                  refine ⟨7388330275815815113027493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78808856275368694538959925 7388330275815815113027493)
                  ·
                    refine ⟨1385311926715465333692655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388330275815815113027493 1385311926715465333692655)
                    ·
                      rfl

theorem cell22_4046828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_4046828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046828 prefixEnd_4046828 := by exact prefixLift 4046828
  have htrace : WordTrace (prefixWord ++ tailWord_4046828) baseStart_4046828 baseEnd_4046828 := by
    simpa [prefixWord, tailWord_4046828, baseEnd_4046828] using wordTrace_append hprefix tailTrace_4046828
  have hstable : (prefixWord ++ tailWord_4046828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046828).length < 2 ^ (prefixWord ++ tailWord_4046828).sum := by decide
  have hdescent : baseEnd_4046828 < baseStart_4046828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046830 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4046830 : Nat := 118140960795 + 4046830 * 2 ^ 59
def prefixEnd_4046830 : Nat := 4983230072969 + 3 ^ 40 * 4046830 * 2
def baseEnd_4046830 : Nat := 1385312611356337995142649

theorem tailTrace_4046830 : CollatzResearch.WordTrace tailWord_4046830 prefixEnd_4046830 1385312611356337995142649 := by
  unfold tailWord_4046830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18450001991129191048045243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98400010619355685589574629 18450001991129191048045243)
  ·
    refine ⟨27675002986693786572067865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18450001991129191048045243 27675002986693786572067865)
    ·
      refine ⟨20756252240020339929050899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27675002986693786572067865 20756252240020339929050899)
      ·
        refine ⟨31134378360030509893576349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20756252240020339929050899 31134378360030509893576349)
        ·
          refine ⟨11675391885011441210091131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31134378360030509893576349 11675391885011441210091131)
          ·
            refine ⟨17513087827517161815136697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11675391885011441210091131 17513087827517161815136697)
            ·
              refine ⟨13134815870637871361352523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17513087827517161815136697 13134815870637871361352523)
              ·
                refine ⟨19702223805956807042028785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134815870637871361352523 19702223805956807042028785)
                ·
                  refine ⟨14776667854467605281521589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19702223805956807042028785 14776667854467605281521589)
                  ·
                    refine ⟨1385312611356337995142649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14776667854467605281521589 1385312611356337995142649)
                    ·
                      rfl

theorem cell22_4046830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4046830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046830 prefixEnd_4046830 := by exact prefixLift 4046830
  have htrace : WordTrace (prefixWord ++ tailWord_4046830) baseStart_4046830 baseEnd_4046830 := by
    simpa [prefixWord, tailWord_4046830, baseEnd_4046830] using wordTrace_append hprefix tailTrace_4046830
  have hstable : (prefixWord ++ tailWord_4046830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046830).length < 2 ^ (prefixWord ++ tailWord_4046830).sum := by decide
  have hdescent : baseEnd_4046830 < baseStart_4046830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046843 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 6]
def baseStart_4046843 : Nat := 118140960795 + 4046843 * 2 ^ 59
def prefixEnd_4046843 : Nat := 4983230072969 + 3 ^ 40 * 4046843 * 2
def baseEnd_4046843 : Nat := 461772353840670098189203

theorem tailTrace_4046843 : CollatzResearch.WordTrace tailWord_4046843 prefixEnd_4046843 461772353840670098189203 := by
  unfold tailWord_4046843
  simp only [CollatzResearch.WordTrace]
  refine ⟨147600490077986431604585183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98400326718657621069723455 147600490077986431604585183)
  ·
    refine ⟨221400735116979647406877775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147600490077986431604585183 221400735116979647406877775)
    ·
      refine ⟨332101102675469471110316663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221400735116979647406877775 332101102675469471110316663)
      ·
        refine ⟨498151654013204206665474995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332101102675469471110316663 498151654013204206665474995)
        ·
          refine ⟨747227481019806309998212493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498151654013204206665474995 747227481019806309998212493)
          ·
            refine ⟨280210305382427366249329685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747227481019806309998212493 280210305382427366249329685)
            ·
              refine ⟨13134858064801282792937329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 280210305382427366249329685 13134858064801282792937329)
              ·
                refine ⟨9851143548600962094702997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13134858064801282792937329 9851143548600962094702997)
                ·
                  refine ⟨461772353840670098189203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9851143548600962094702997 461772353840670098189203)
                  ·
                    rfl

theorem cell22_4046843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_4046843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046843 prefixEnd_4046843 := by exact prefixLift 4046843
  have htrace : WordTrace (prefixWord ++ tailWord_4046843) baseStart_4046843 baseEnd_4046843 := by
    simpa [prefixWord, tailWord_4046843, baseEnd_4046843] using wordTrace_append hprefix tailTrace_4046843
  have hstable : (prefixWord ++ tailWord_4046843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046843).length < 2 ^ (prefixWord ++ tailWord_4046843).sum := by decide
  have hdescent : baseEnd_4046843 < baseStart_4046843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046845 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_4046845 : Nat := 118140960795 + 4046845 * 2 ^ 59
def prefixEnd_4046845 : Nat := 4983230072969 + 3 ^ 40 * 4046845 * 2
def baseEnd_4046845 : Nat := 1385317746162882956017603

theorem tailTrace_4046845 : CollatzResearch.WordTrace tailWord_4046845 prefixEnd_4046845 1385317746162882956017603 := by
  unfold tailWord_4046845
  simp only [CollatzResearch.WordTrace]
  refine ⟨147600563023979185946157989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98400375349319457297438659 147600563023979185946157989)
  ·
    refine ⟨27675105566996097364904623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147600563023979185946157989 27675105566996097364904623)
    ·
      refine ⟨41512658350494146047356935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27675105566996097364904623 41512658350494146047356935)
      ·
        refine ⟨62268987525741219071035403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41512658350494146047356935 62268987525741219071035403)
        ·
          refine ⟨93403481288611828606553105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62268987525741219071035403 93403481288611828606553105)
          ·
            refine ⟨70052610966458871454914829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93403481288611828606553105 70052610966458871454914829)
            ·
              refine ⟨26269729112422076795593061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70052610966458871454914829 26269729112422076795593061)
              ·
                refine ⟨4925574208579139399173699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26269729112422076795593061 4925574208579139399173699)
                ·
                  refine ⟨7388361312868709098760549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925574208579139399173699 7388361312868709098760549)
                  ·
                    refine ⟨1385317746162882956017603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388361312868709098760549 1385317746162882956017603)
                    ·
                      rfl

theorem cell22_4046845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_4046845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046845 prefixEnd_4046845 := by exact prefixLift 4046845
  have htrace : WordTrace (prefixWord ++ tailWord_4046845) baseStart_4046845 baseEnd_4046845 := by
    simpa [prefixWord, tailWord_4046845, baseEnd_4046845] using wordTrace_append hprefix tailTrace_4046845
  have hstable : (prefixWord ++ tailWord_4046845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046845).length < 2 ^ (prefixWord ++ tailWord_4046845).sum := by decide
  have hdescent : baseEnd_4046845 < baseStart_4046845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046877 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 6]
def baseStart_4046877 : Nat := 118140960795 + 4046877 * 2 ^ 59
def prefixEnd_4046877 : Nat := 4983230072969 + 3 ^ 40 * 4046877 * 2
def baseEnd_4046877 : Nat := 461776233472281846405835

theorem tailTrace_4046877 : CollatzResearch.WordTrace tailWord_4046877 prefixEnd_4046877 461776233472281846405835 := by
  unfold tailWord_4046877
  simp only [CollatzResearch.WordTrace]
  refine ⟨147601730159863255411322885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98401153439908836940881923 147601730159863255411322885)
  ·
    refine ⟨27675324404974360389623041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147601730159863255411322885 27675324404974360389623041)
    ·
      refine ⟨20756493303730770292217281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27675324404974360389623041 20756493303730770292217281)
      ·
        refine ⟨15567369977798077719162961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20756493303730770292217281 15567369977798077719162961)
        ·
          refine ⟨11675527483348558289372221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15567369977798077719162961 11675527483348558289372221)
          ·
            refine ⟨4378322806255709358514583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11675527483348558289372221 4378322806255709358514583)
            ·
              refine ⟨6567484209383564037771875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378322806255709358514583 6567484209383564037771875)
              ·
                refine ⟨9851226314075346056657813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567484209383564037771875 9851226314075346056657813)
                ·
                  refine ⟨461776233472281846405835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9851226314075346056657813 461776233472281846405835)
                  ·
                    rfl

theorem cell22_4046877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_4046877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046877 prefixEnd_4046877 := by exact prefixLift 4046877
  have htrace : WordTrace (prefixWord ++ tailWord_4046877) baseStart_4046877 baseEnd_4046877 := by
    simpa [prefixWord, tailWord_4046877, baseEnd_4046877] using wordTrace_append hprefix tailTrace_4046877
  have hstable : (prefixWord ++ tailWord_4046877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046877).length < 2 ^ (prefixWord ++ tailWord_4046877).sum := by decide
  have hdescent : baseEnd_4046877 < baseStart_4046877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046903 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_4046903 : Nat := 118140960795 + 4046903 * 2 ^ 59
def prefixEnd_4046903 : Nat := 4983230072969 + 3 ^ 40 * 4046903 * 2
def baseEnd_4046903 : Nat := 1385337600748190138067425

theorem tailTrace_4046903 : CollatzResearch.WordTrace tailWord_4046903 prefixEnd_4046903 1385337600748190138067425 := by
  unfold tailWord_4046903
  simp only [CollatzResearch.WordTrace]
  refine ⟨147602678457769061851769363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98401785638512707901179575 147602678457769061851769363)
  ·
    refine ⟨221404017686653592777654045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147602678457769061851769363 221404017686653592777654045)
    ·
      refine ⟨83026506632495097291620267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221404017686653592777654045 83026506632495097291620267)
      ·
        refine ⟨124539759948742645937430401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83026506632495097291620267 124539759948742645937430401)
        ·
          refine ⟨93404819961556984453072801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124539759948742645937430401 93404819961556984453072801)
          ·
            refine ⟨70053614971167738339804601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93404819961556984453072801 70053614971167738339804601)
            ·
              refine ⟨52540211228375803754853451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70053614971167738339804601 52540211228375803754853451)
              ·
                refine ⟨78810316842563705632280177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52540211228375803754853451 78810316842563705632280177)
                ·
                  refine ⟨59107737631922779224210133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78810316842563705632280177 59107737631922779224210133)
                  ·
                    refine ⟨1385337600748190138067425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59107737631922779224210133 1385337600748190138067425)
                    ·
                      rfl

theorem cell22_4046903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_4046903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046903 prefixEnd_4046903 := by exact prefixLift 4046903
  have htrace : WordTrace (prefixWord ++ tailWord_4046903) baseStart_4046903 baseEnd_4046903 := by
    simpa [prefixWord, tailWord_4046903, baseEnd_4046903] using wordTrace_append hprefix tailTrace_4046903
  have hstable : (prefixWord ++ tailWord_4046903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046903).length < 2 ^ (prefixWord ++ tailWord_4046903).sum := by decide
  have hdescent : baseEnd_4046903 < baseStart_4046903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046920 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_4046920 : Nat := 118140960795 + 4046920 * 2 ^ 59
def prefixEnd_4046920 : Nat := 4983230072969 + 3 ^ 40 * 4046920 * 2
def baseEnd_4046920 : Nat := 1385343420195607760392373

theorem tailTrace_4046920 : CollatzResearch.WordTrace tailWord_4046920 prefixEnd_4046920 1385343420195607760392373 := by
  unfold tailWord_4046920
  simp only [CollatzResearch.WordTrace]
  refine ⟨73801649249353736877569107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98402198999138315836758809 73801649249353736877569107)
  ·
    refine ⟨110702473874030605316353661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73801649249353736877569107 110702473874030605316353661)
    ·
      refine ⟨41513427702761476993632623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110702473874030605316353661 41513427702761476993632623)
      ·
        refine ⟨62270141554142215490448935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41513427702761476993632623 62270141554142215490448935)
        ·
          refine ⟨93405212331213323235673403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62270141554142215490448935 93405212331213323235673403)
          ·
            refine ⟨140107818496819984853510105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93405212331213323235673403 140107818496819984853510105)
            ·
              refine ⟨105080863872614988640132579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140107818496819984853510105 105080863872614988640132579)
              ·
                refine ⟨157621295808922482960198869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105080863872614988640132579 157621295808922482960198869)
                ·
                  refine ⟨3694249120521620694379661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 157621295808922482960198869 3694249120521620694379661)
                  ·
                    refine ⟨1385343420195607760392373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694249120521620694379661 1385343420195607760392373)
                    ·
                      rfl

theorem cell22_4046920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_4046920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046920 prefixEnd_4046920 := by exact prefixLift 4046920
  have htrace : WordTrace (prefixWord ++ tailWord_4046920) baseStart_4046920 baseEnd_4046920 := by
    simpa [prefixWord, tailWord_4046920, baseEnd_4046920] using wordTrace_append hprefix tailTrace_4046920
  have hstable : (prefixWord ++ tailWord_4046920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046920).length < 2 ^ (prefixWord ++ tailWord_4046920).sum := by decide
  have hdescent : baseEnd_4046920 < baseStart_4046920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046954 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4046954 : Nat := 118140960795 + 4046954 * 2 ^ 59
def prefixEnd_4046954 : Nat := 4983230072969 + 3 ^ 40 * 4046954 * 2
def baseEnd_4046954 : Nat := 1385355059090443005042269

theorem tailTrace_4046954 : CollatzResearch.WordTrace tailWord_4046954 prefixEnd_4046954 1385355059090443005042269 := by
  unfold tailWord_4046954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901134645146074390468979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98403025720389531707917277 36901134645146074390468979)
  ·
    refine ⟨55351701967719111585703469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36901134645146074390468979 55351701967719111585703469)
    ·
      refine ⟨20756888237894666844638801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55351701967719111585703469 20756888237894666844638801)
      ·
        refine ⟨15567666178421000133479101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20756888237894666844638801 15567666178421000133479101)
        ·
          refine ⟨5837874816907875050054663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15567666178421000133479101 5837874816907875050054663)
          ·
            refine ⟨8756812225361812575081995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837874816907875050054663 8756812225361812575081995)
            ·
              refine ⟨13135218338042718862622993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756812225361812575081995 13135218338042718862622993)
              ·
                refine ⟨9851413753532039146967245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13135218338042718862622993 9851413753532039146967245)
                ·
                  refine ⟨3694280157574514680112717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9851413753532039146967245 3694280157574514680112717)
                  ·
                    refine ⟨1385355059090443005042269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694280157574514680112717 1385355059090443005042269)
                    ·
                      rfl

theorem cell22_4046954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4046954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046954 prefixEnd_4046954 := by exact prefixLift 4046954
  have htrace : WordTrace (prefixWord ++ tailWord_4046954) baseStart_4046954 baseEnd_4046954 := by
    simpa [prefixWord, tailWord_4046954, baseEnd_4046954] using wordTrace_append hprefix tailTrace_4046954
  have hstable : (prefixWord ++ tailWord_4046954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046954).length < 2 ^ (prefixWord ++ tailWord_4046954).sum := by decide
  have hdescent : baseEnd_4046954 < baseStart_4046954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046984 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 5]
def baseStart_4046984 : Nat := 118140960795 + 4046984 * 2 ^ 59
def prefixEnd_4046984 : Nat := 4983230072969 + 3 ^ 40 * 4046984 * 2
def baseEnd_4046984 : Nat := 461788442901177642264059

theorem tailTrace_4046984 : CollatzResearch.WordTrace tailWord_4046984 prefixEnd_4046984 461788442901177642264059 := by
  unfold tailWord_4046984
  simp only [CollatzResearch.WordTrace]
  refine ⟨73802816385237806342734003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98403755180317075123645337 73802816385237806342734003)
  ·
    refine ⟨110704224577856709514101005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73802816385237806342734003 110704224577856709514101005)
    ·
      refine ⟨41514084216696266067787877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110704224577856709514101005 41514084216696266067787877)
      ·
        refine ⟨7783890790630549887710227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41514084216696266067787877 7783890790630549887710227)
        ·
          refine ⟨11675836185945824831565341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783890790630549887710227 11675836185945824831565341)
          ·
            refine ⟨4378438569729684311837003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11675836185945824831565341 4378438569729684311837003)
            ·
              refine ⟨6567657854594526467755505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378438569729684311837003 6567657854594526467755505)
              ·
                refine ⟨4925743390945894850816629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6567657854594526467755505 4925743390945894850816629)
                ·
                  refine ⟨461788442901177642264059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4925743390945894850816629 461788442901177642264059)
                  ·
                    rfl

theorem cell22_4046984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_4046984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4046984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4046984 prefixEnd_4046984 := by exact prefixLift 4046984
  have htrace : WordTrace (prefixWord ++ tailWord_4046984) baseStart_4046984 baseEnd_4046984 := by
    simpa [prefixWord, tailWord_4046984, baseEnd_4046984] using wordTrace_append hprefix tailTrace_4046984
  have hstable : (prefixWord ++ tailWord_4046984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046984).length < 2 ^ (prefixWord ++ tailWord_4046984).sum := by decide
  have hdescent : baseEnd_4046984 < baseStart_4046984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047022 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4047022 : Nat := 118140960795 + 4047022 * 2 ^ 59
def prefixEnd_4047022 : Nat := 4983230072969 + 3 ^ 40 * 4047022 * 2
def baseEnd_4047022 : Nat := 1385378336880113494342061

theorem tailTrace_4047022 : CollatzResearch.WordTrace tailWord_4047022 prefixEnd_4047022 1385378336880113494342061 := by
  unfold tailWord_4047022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18450877343042243146918915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98404679162891963450234213 18450877343042243146918915)
  ·
    refine ⟨27676316014563364720378373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18450877343042243146918915 27676316014563364720378373)
    ·
      refine ⟨5189309252730630885070945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27676316014563364720378373 5189309252730630885070945)
      ·
        refine ⟨3891981939547973163803209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189309252730630885070945 3891981939547973163803209)
        ·
          refine ⟨2918986454660979872852407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891981939547973163803209 2918986454660979872852407)
          ·
            refine ⟨4378479681991469809278611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918986454660979872852407 4378479681991469809278611)
            ·
              refine ⟨6567719522987204713917917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378479681991469809278611 6567719522987204713917917)
              ·
                refine ⟨2462894821120201767719219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6567719522987204713917917 2462894821120201767719219)
                ·
                  refine ⟨3694342231680302651578829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462894821120201767719219 3694342231680302651578829)
                  ·
                    refine ⟨1385378336880113494342061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694342231680302651578829 1385378336880113494342061)
                    ·
                      rfl

theorem cell22_4047022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4047022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047022 prefixEnd_4047022 := by exact prefixLift 4047022
  have htrace : WordTrace (prefixWord ++ tailWord_4047022) baseStart_4047022 baseEnd_4047022 := by
    simpa [prefixWord, tailWord_4047022, baseEnd_4047022] using wordTrace_append hprefix tailTrace_4047022
  have hstable : (prefixWord ++ tailWord_4047022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047022).length < 2 ^ (prefixWord ++ tailWord_4047022).sum := by decide
  have hdescent : baseEnd_4047022 < baseStart_4047022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047040 : List Nat := [2, 1, 1, 2, 5, 1, 10]
def baseStart_4047040 : Nat := 118140960795 + 4047040 * 2 ^ 59
def prefixEnd_4047040 : Nat := 4983230072969 + 3 ^ 40 * 4047040 * 2
def baseEnd_4047040 : Nat := 51310536986961757310815

theorem tailTrace_4047040 : CollatzResearch.WordTrace tailWord_4047040 prefixEnd_4047040 51310536986961757310815 := by
  unfold tailWord_4047040
  simp only [CollatzResearch.WordTrace]
  refine ⟨73803837629136367124753287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98405116838848489499671049 73803837629136367124753287)
  ·
    refine ⟨110705756443704550687129931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73803837629136367124753287 110705756443704550687129931)
    ·
      refine ⟨166058634665556826030694897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110705756443704550687129931 166058634665556826030694897)
      ·
        refine ⟨124543975999167619523021173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166058634665556826030694897 124543975999167619523021173)
        ·
          refine ⟨11675997749921964330283235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124543975999167619523021173 11675997749921964330283235)
          ·
            refine ⟨17513996624882946495424853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11675997749921964330283235 17513996624882946495424853)
            ·
              refine ⟨51310536986961757310815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17513996624882946495424853 51310536986961757310815)
              ·
                rfl

theorem cell22_4047040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 10].length) (baseStart_4047040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047040 prefixEnd_4047040 := by exact prefixLift 4047040
  have htrace : WordTrace (prefixWord ++ tailWord_4047040) baseStart_4047040 baseEnd_4047040 := by
    simpa [prefixWord, tailWord_4047040, baseEnd_4047040] using wordTrace_append hprefix tailTrace_4047040
  have hstable : (prefixWord ++ tailWord_4047040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047040).length < 2 ^ (prefixWord ++ tailWord_4047040).sum := by decide
  have hdescent : baseEnd_4047040 < baseStart_4047040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047044 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4047044 : Nat := 118140960795 + 4047044 * 2 ^ 59
def prefixEnd_4047044 : Nat := 4983230072969 + 3 ^ 40 * 4047044 * 2
def baseEnd_4047044 : Nat := 1385385867929712770291993

theorem tailTrace_4047044 : CollatzResearch.WordTrace tailWord_4047044 prefixEnd_4047044 1385385867929712770291993 := by
  unfold tailWord_4047044
  simp only [CollatzResearch.WordTrace]
  refine ⟨73803910575129121466326093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98405214100172161955101457 73803910575129121466326093)
  ·
    refine ⟨27676466465673420549872285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73803910575129121466326093 27676466465673420549872285)
    ·
      refine ⟨10378674924627532706202107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27676466465673420549872285 10378674924627532706202107)
      ·
        refine ⟨15568012386941299059303161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10378674924627532706202107 15568012386941299059303161)
        ·
          refine ⟨11676009290205974294477371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15568012386941299059303161 11676009290205974294477371)
          ·
            refine ⟨17514013935308961441716057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676009290205974294477371 17514013935308961441716057)
            ·
              refine ⟨13135510451481721081287043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17514013935308961441716057 13135510451481721081287043)
              ·
                refine ⟨19703265677222581621930565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13135510451481721081287043 19703265677222581621930565)
                ·
                  refine ⟨3694362314479234054111981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19703265677222581621930565 3694362314479234054111981)
                  ·
                    refine ⟨1385385867929712770291993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694362314479234054111981 1385385867929712770291993)
                    ·
                      rfl

theorem cell22_4047044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4047044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047044 prefixEnd_4047044 := by exact prefixLift 4047044
  have htrace : WordTrace (prefixWord ++ tailWord_4047044) baseStart_4047044 baseEnd_4047044 := by
    simpa [prefixWord, tailWord_4047044, baseEnd_4047044] using wordTrace_append hprefix tailTrace_4047044
  have hstable : (prefixWord ++ tailWord_4047044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047044).length < 2 ^ (prefixWord ++ tailWord_4047044).sum := by decide
  have hdescent : baseEnd_4047044 < baseStart_4047044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047061 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_4047061 : Nat := 118140960795 + 4047061 * 2 ^ 59
def prefixEnd_4047061 : Nat := 4983230072969 + 3 ^ 40 * 4047061 * 2
def baseEnd_4047061 : Nat := 1385391687377130392616941

theorem tailTrace_4047061 : CollatzResearch.WordTrace tailWord_4047061 prefixEnd_4047061 1385391687377130392616941 := by
  unfold tailWord_4047061
  simp only [CollatzResearch.WordTrace]
  refine ⟨147608441191196654836021037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98405627460797769890680691 147608441191196654836021037)
  ·
    refine ⟨55353165446698745563507889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147608441191196654836021037 55353165446698745563507889)
    ·
      refine ⟨41514874085024059172630917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55353165446698745563507889 41514874085024059172630917)
      ·
        refine ⟨7784038890942011094868297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41514874085024059172630917 7784038890942011094868297)
        ·
          refine ⟨5838029168206508321151223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7784038890942011094868297 5838029168206508321151223)
          ·
            refine ⟨8757043752309762481726835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838029168206508321151223 8757043752309762481726835)
            ·
              refine ⟨13135565628464643722590253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757043752309762481726835 13135565628464643722590253)
              ·
                refine ⟨4925837110674241395971345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13135565628464643722590253 4925837110674241395971345)
                ·
                  refine ⟨3694377833005681046978509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4925837110674241395971345 3694377833005681046978509)
                  ·
                    refine ⟨1385391687377130392616941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694377833005681046978509 1385391687377130392616941)
                    ·
                      rfl

theorem cell22_4047061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_4047061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047061 prefixEnd_4047061 := by exact prefixLift 4047061
  have htrace : WordTrace (prefixWord ++ tailWord_4047061) baseStart_4047061 baseEnd_4047061 := by
    simpa [prefixWord, tailWord_4047061, baseEnd_4047061] using wordTrace_append hprefix tailTrace_4047061
  have hstable : (prefixWord ++ tailWord_4047061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047061).length < 2 ^ (prefixWord ++ tailWord_4047061).sum := by decide
  have hdescent : baseEnd_4047061 < baseStart_4047061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047072 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_4047072 : Nat := 118140960795 + 4047072 * 2 ^ 59
def prefixEnd_4047072 : Nat := 4983230072969 + 3 ^ 40 * 4047072 * 2
def baseEnd_4047072 : Nat := 1385395452901930030591907

theorem tailTrace_4047072 : CollatzResearch.WordTrace tailWord_4047072 prefixEnd_4047072 1385395452901930030591907 := by
  unfold tailWord_4047072
  simp only [CollatzResearch.WordTrace]
  refine ⟨73804421197078401857335735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98405894929437869143114313 73804421197078401857335735)
  ·
    refine ⟨110706631795617602786003603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73804421197078401857335735 110706631795617602786003603)
    ·
      refine ⟨166059947693426404179005405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110706631795617602786003603 166059947693426404179005405)
      ·
        refine ⟨62272480385034901567127027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166059947693426404179005405 62272480385034901567127027)
        ·
          refine ⟨93408720577552352350690541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62272480385034901567127027 93408720577552352350690541)
          ·
            refine ⟨35028270216582132131508953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93408720577552352350690541 35028270216582132131508953)
            ·
              refine ⟨26271202662436599098631715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35028270216582132131508953 26271202662436599098631715)
              ·
                refine ⟨39406803993654898647947573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26271202662436599098631715 39406803993654898647947573)
                ·
                  refine ⟨3694387874405146748245085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39406803993654898647947573 3694387874405146748245085)
                  ·
                    refine ⟨1385395452901930030591907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694387874405146748245085 1385395452901930030591907)
                    ·
                      rfl

theorem cell22_4047072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_4047072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047072 prefixEnd_4047072 := by exact prefixLift 4047072
  have htrace : WordTrace (prefixWord ++ tailWord_4047072) baseStart_4047072 baseEnd_4047072 := by
    simpa [prefixWord, tailWord_4047072, baseEnd_4047072] using wordTrace_append hprefix tailTrace_4047072
  have hstable : (prefixWord ++ tailWord_4047072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047072).length < 2 ^ (prefixWord ++ tailWord_4047072).sum := by decide
  have hdescent : baseEnd_4047072 < baseStart_4047072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047164 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 4]
def baseStart_4047164 : Nat := 118140960795 + 4047164 * 2 ^ 59
def prefixEnd_4047164 : Nat := 4983230072969 + 3 ^ 40 * 4047164 * 2
def baseEnd_4047164 : Nat := 461808982127357485763875

theorem tailTrace_4047164 : CollatzResearch.WordTrace tailWord_4047164 prefixEnd_4047164 461808982127357485763875 := by
  unfold tailWord_4047164
  simp only [CollatzResearch.WordTrace]
  refine ⟨73806098954911751713510273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98408131939882335618013697 73806098954911751713510273)
  ·
    refine ⟨55354574216183813785132705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73806098954911751713510273 55354574216183813785132705)
    ·
      refine ⟨41515930662137860338849529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55354574216183813785132705 41515930662137860338849529)
      ·
        refine ⟨31136947996603395254137147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41515930662137860338849529 31136947996603395254137147)
        ·
          refine ⟨46705421994905092881205721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31136947996603395254137147 46705421994905092881205721)
          ·
            refine ⟨35029066496178819660904291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46705421994905092881205721 35029066496178819660904291)
            ·
              refine ⟨52543599744268229491356437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35029066496178819660904291 52543599744268229491356437)
              ·
                refine ⟨2462981238012573257407333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52543599744268229491356437 2462981238012573257407333)
                ·
                  refine ⟨461808982127357485763875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2462981238012573257407333 461808982127357485763875)
                  ·
                    rfl

theorem cell22_4047164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_4047164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047164 prefixEnd_4047164 := by exact prefixLift 4047164
  have htrace : WordTrace (prefixWord ++ tailWord_4047164) baseStart_4047164 baseEnd_4047164 := by
    simpa [prefixWord, tailWord_4047164, baseEnd_4047164] using wordTrace_append hprefix tailTrace_4047164
  have hstable : (prefixWord ++ tailWord_4047164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047164).length < 2 ^ (prefixWord ++ tailWord_4047164).sum := by decide
  have hdescent : baseEnd_4047164 < baseStart_4047164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047271 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 5]
def baseStart_4047271 : Nat := 118140960795 + 4047271 * 2 ^ 59
def prefixEnd_4047271 : Nat := 4983230072969 + 3 ^ 40 * 4047271 * 2
def baseEnd_4047271 : Nat := 461821191556253281622099

theorem tailTrace_4047271 : CollatzResearch.WordTrace tailWord_4047271 prefixEnd_4047271 461821191556253281622099 := by
  unfold tailWord_4047271
  simp only [CollatzResearch.WordTrace]
  refine ⟨147616100520435860701165667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98410733680290573800777111 147616100520435860701165667)
  ·
    refine ⟨221424150780653791051748501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147616100520435860701165667 221424150780653791051748501)
    ·
      refine ⟨10379257067843146455550711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221424150780653791051748501 10379257067843146455550711)
      ·
        refine ⟨15568885601764719683326067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10379257067843146455550711 15568885601764719683326067)
        ·
          refine ⟨23353328402647079524989101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15568885601764719683326067 23353328402647079524989101)
          ·
            refine ⟨8757498150992654821870913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23353328402647079524989101 8757498150992654821870913)
            ·
              refine ⟨6568123613244491116403185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8757498150992654821870913 6568123613244491116403185)
              ·
                refine ⟨4926092709933368337302389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6568123613244491116403185 4926092709933368337302389)
                ·
                  refine ⟨461821191556253281622099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4926092709933368337302389 461821191556253281622099)
                  ·
                    rfl

theorem cell22_4047271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 5].length) (baseStart_4047271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047271 prefixEnd_4047271 := by exact prefixLift 4047271
  have htrace : WordTrace (prefixWord ++ tailWord_4047271) baseStart_4047271 baseEnd_4047271 := by
    simpa [prefixWord, tailWord_4047271, baseEnd_4047271] using wordTrace_append hprefix tailTrace_4047271
  have hstable : (prefixWord ++ tailWord_4047271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047271).length < 2 ^ (prefixWord ++ tailWord_4047271).sum := by decide
  have hdescent : baseEnd_4047271 < baseStart_4047271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047318 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4047318 : Nat := 118140960795 + 4047318 * 2 ^ 59
def prefixEnd_4047318 : Nat := 4983230072969 + 3 ^ 40 * 4047318 * 2
def baseEnd_4047318 : Nat := 1385479663729267388941153

theorem tailTrace_4047318 : CollatzResearch.WordTrace tailWord_4047318 prefixEnd_4047318 1385479663729267388941153 := by
  unfold tailWord_4047318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226113421954099233007913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98411876500843725152084405 9226113421954099233007913)
  ·
    refine ⟨6919585066465574424755935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9226113421954099233007913 6919585066465574424755935)
    ·
      refine ⟨10379377599698361637133903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6919585066465574424755935 10379377599698361637133903)
      ·
        refine ⟨15569066399547542455700855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10379377599698361637133903 15569066399547542455700855)
        ·
          refine ⟨23353599599321313683551283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15569066399547542455700855 23353599599321313683551283)
          ·
            refine ⟨35030399398981970525326925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23353599599321313683551283 35030399398981970525326925)
            ·
              refine ⟨13136399774618238946997597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35030399398981970525326925 13136399774618238946997597)
              ·
                refine ⟨4926149915481839605124099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13136399774618238946997597 4926149915481839605124099)
                ·
                  refine ⟨7389224873222759407686149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926149915481839605124099 7389224873222759407686149)
                  ·
                    refine ⟨1385479663729267388941153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7389224873222759407686149 1385479663729267388941153)
                    ·
                      rfl

theorem cell22_4047318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4047318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047318 prefixEnd_4047318 := by exact prefixLift 4047318
  have htrace : WordTrace (prefixWord ++ tailWord_4047318) baseStart_4047318 baseEnd_4047318 := by
    simpa [prefixWord, tailWord_4047318, baseEnd_4047318] using wordTrace_append hprefix tailTrace_4047318
  have hstable : (prefixWord ++ tailWord_4047318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047318).length < 2 ^ (prefixWord ++ tailWord_4047318).sum := by decide
  have hdescent : baseEnd_4047318 < baseStart_4047318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047329 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_4047329 : Nat := 118140960795 + 4047329 * 2 ^ 59
def prefixEnd_4047329 : Nat := 4983230072969 + 3 ^ 40 * 4047329 * 2
def baseEnd_4047329 : Nat := 1385483429254067026916119

theorem tailTrace_4047329 : CollatzResearch.WordTrace tailWord_4047329 prefixEnd_4047329 1385483429254067026916119 := by
  unfold tailWord_4047329
  simp only [CollatzResearch.WordTrace]
  refine ⟨147618215954225736606777041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98412143969483824404518027 147618215954225736606777041)
  ·
    refine ⟨110713661965669302455082781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147618215954225736606777041 110713661965669302455082781)
    ·
      refine ⟨41517623237125988420656043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110713661965669302455082781 41517623237125988420656043)
      ·
        refine ⟨62276434855688982630984065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41517623237125988420656043 62276434855688982630984065)
        ·
          refine ⟨46707326141766736973238049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62276434855688982630984065 46707326141766736973238049)
          ·
            refine ⟨35030494606325052729928537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46707326141766736973238049 35030494606325052729928537)
            ·
              refine ⟨26272870954743789547446403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35030494606325052729928537 26272870954743789547446403)
              ·
                refine ⟨39409306432115684321169605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26272870954743789547446403 39409306432115684321169605)
                ·
                  refine ⟨7389244956021690810219301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39409306432115684321169605 7389244956021690810219301)
                  ·
                    refine ⟨1385483429254067026916119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7389244956021690810219301 1385483429254067026916119)
                    ·
                      rfl

theorem cell22_4047329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_4047329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047329 prefixEnd_4047329 := by exact prefixLift 4047329
  have htrace : WordTrace (prefixWord ++ tailWord_4047329) baseStart_4047329 baseEnd_4047329 := by
    simpa [prefixWord, tailWord_4047329, baseEnd_4047329] using wordTrace_append hprefix tailTrace_4047329
  have hstable : (prefixWord ++ tailWord_4047329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047329).length < 2 ^ (prefixWord ++ tailWord_4047329).sum := by decide
  have hdescent : baseEnd_4047329 < baseStart_4047329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047361 : List Nat := [1, 2, 4, 1, 3, 1, 4, 6]
def baseStart_4047361 : Nat := 118140960795 + 4047361 * 2 ^ 59
def prefixEnd_4047361 : Nat := 4983230072969 + 3 ^ 40 * 4047361 * 2
def baseEnd_4047361 : Nat := 153943820389781067790669

theorem tailTrace_4047361 : CollatzResearch.WordTrace tailWord_4047361 prefixEnd_4047361 153943820389781067790669 := by
  unfold tailWord_4047361
  simp only [CollatzResearch.WordTrace]
  refine ⟨147619383090109806071941937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98412922060073204047961291 147619383090109806071941937)
  ·
    refine ⟨110714537317582354553956453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147619383090109806071941937 110714537317582354553956453)
    ·
      refine ⟨20758975747046691478866835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110714537317582354553956453 20758975747046691478866835)
      ·
        refine ⟨31138463620570037218300253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20758975747046691478866835 31138463620570037218300253)
        ·
          refine ⟨11676923857713763956862595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31138463620570037218300253 11676923857713763956862595)
          ·
            refine ⟨17515385786570645935293893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676923857713763956862595 17515385786570645935293893)
            ·
              refine ⟨3284134834981996112867605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17515385786570645935293893 3284134834981996112867605)
              ·
                refine ⟨153943820389781067790669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3284134834981996112867605 153943820389781067790669)
                ·
                  rfl

theorem cell22_4047361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 6].length) (baseStart_4047361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047361 prefixEnd_4047361 := by exact prefixLift 4047361
  have htrace : WordTrace (prefixWord ++ tailWord_4047361) baseStart_4047361 baseEnd_4047361 := by
    simpa [prefixWord, tailWord_4047361, baseEnd_4047361] using wordTrace_append hprefix tailTrace_4047361
  have hstable : (prefixWord ++ tailWord_4047361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047361).length < 2 ^ (prefixWord ++ tailWord_4047361).sum := by decide
  have hdescent : baseEnd_4047361 < baseStart_4047361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
