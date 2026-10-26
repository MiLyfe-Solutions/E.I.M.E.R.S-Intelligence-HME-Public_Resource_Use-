import V185TrunkScan22Chunk408

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3647068 : List Nat := [2, 2, 4, 1, 2, 2, 2, 7]
def baseStart_3647068 : Nat := 118140960795 + 3647068 * 2 ^ 59
def prefixEnd_3647068 : Nat := 4983230072969 + 3 ^ 40 * 3647068 * 2
def baseEnd_3647068 : Nat := 138718434343099412102033

theorem tailTrace_3647068 : CollatzResearch.WordTrace tailWord_3647068 prefixEnd_3647068 138718434343099412102033 := by
  unfold tailWord_3647068
  simp only [CollatzResearch.WordTrace]
  refine ⟨66509748975651490235162929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88679665300868653646883905 66509748975651490235162929)
  ·
    refine ⟨49882311731738617676372197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66509748975651490235162929 49882311731738617676372197)
    ·
      refine ⟨9352933449700990814319787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49882311731738617676372197 9352933449700990814319787)
      ·
        refine ⟨14029400174551486221479681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9352933449700990814319787 14029400174551486221479681)
        ·
          refine ⟨10522050130913614666109761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14029400174551486221479681 10522050130913614666109761)
          ·
            refine ⟨7891537598185210999582321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10522050130913614666109761 7891537598185210999582321)
            ·
              refine ⟨5918653198638908249686741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7891537598185210999582321 5918653198638908249686741)
              ·
                refine ⟨138718434343099412102033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5918653198638908249686741 138718434343099412102033)
                ·
                  rfl

theorem cell22_3647068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_3647068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647068 prefixEnd_3647068 := by exact prefixLift 3647068
  have htrace : WordTrace (prefixWord ++ tailWord_3647068) baseStart_3647068 baseEnd_3647068 := by
    simpa [prefixWord, tailWord_3647068, baseEnd_3647068] using wordTrace_append hprefix tailTrace_3647068
  have hstable : (prefixWord ++ tailWord_3647068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647068).length < 2 ^ (prefixWord ++ tailWord_3647068).sum := by decide
  have hdescent : baseEnd_3647068 < baseStart_3647068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647100 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_3647100 : Nat := 118140960795 + 3647100 * 2 ^ 59
def prefixEnd_3647100 : Nat := 4983230072969 + 3 ^ 40 * 3647100 * 2
def baseEnd_3647100 : Nat := 1248476863341857292118199

theorem tailTrace_3647100 : CollatzResearch.WordTrace tailWord_3647100 prefixEnd_3647100 1248476863341857292118199 := by
  unfold tailWord_3647100
  simp only [CollatzResearch.WordTrace]
  refine ⟨66510332543593524967745377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88680443391458033290327169 66510332543593524967745377)
  ·
    refine ⟨49882749407695143725809033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66510332543593524967745377 49882749407695143725809033)
    ·
      refine ⟨37412062055771357794356775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49882749407695143725809033 37412062055771357794356775)
      ·
        refine ⟨56118093083657036691535163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37412062055771357794356775 56118093083657036691535163)
        ·
          refine ⟨84177139625485555037302745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56118093083657036691535163 84177139625485555037302745)
          ·
            refine ⟨63132854719114166277977059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84177139625485555037302745 63132854719114166277977059)
            ·
              refine ⟨94699282078671249416965589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63132854719114166277977059 94699282078671249416965589)
              ·
                refine ⟨2219514423718857408210131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94699282078671249416965589 2219514423718857408210131)
                ·
                  refine ⟨3329271635578286112315197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219514423718857408210131 3329271635578286112315197)
                  ·
                    refine ⟨1248476863341857292118199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329271635578286112315197 1248476863341857292118199)
                    ·
                      rfl

theorem cell22_3647100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_3647100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647100 prefixEnd_3647100 := by exact prefixLift 3647100
  have htrace : WordTrace (prefixWord ++ tailWord_3647100) baseStart_3647100 baseEnd_3647100 := by
    simpa [prefixWord, tailWord_3647100, baseEnd_3647100] using wordTrace_append hprefix tailTrace_3647100
  have hstable : (prefixWord ++ tailWord_3647100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647100).length < 2 ^ (prefixWord ++ tailWord_3647100).sum := by decide
  have hdescent : baseEnd_3647100 < baseStart_3647100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647128 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_3647128 : Nat := 118140960795 + 3647128 * 2 ^ 59
def prefixEnd_3647128 : Nat := 4983230072969 + 3 ^ 40 * 3647128 * 2
def baseEnd_3647128 : Nat := 1248486448314074552418113

theorem tailTrace_3647128 : CollatzResearch.WordTrace tailWord_3647128 prefixEnd_3647128 1248486448314074552418113 := by
  unfold tailWord_3647128
  simp only [CollatzResearch.WordTrace]
  refine ⟨66510843165542805358755019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88681124220723740478340025 66510843165542805358755019)
  ·
    refine ⟨99766264748314208038132529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66510843165542805358755019 99766264748314208038132529)
    ·
      refine ⟨74824698561235656028599397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99766264748314208038132529 74824698561235656028599397)
      ·
        refine ⟨14029630980231685505362387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74824698561235656028599397 14029630980231685505362387)
        ·
          refine ⟨21044446470347528258043581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14029630980231685505362387 21044446470347528258043581)
          ·
            refine ⟨7891667426380323096766343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21044446470347528258043581 7891667426380323096766343)
            ·
              refine ⟨11837501139570484645149515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891667426380323096766343 11837501139570484645149515)
              ·
                refine ⟨17756251709355726967724273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11837501139570484645149515 17756251709355726967724273)
                ·
                  refine ⟨13317188782016795225793205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17756251709355726967724273 13317188782016795225793205)
                  ·
                    refine ⟨1248486448314074552418113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13317188782016795225793205 1248486448314074552418113)
                    ·
                      rfl

theorem cell22_3647128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_3647128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647128 prefixEnd_3647128 := by exact prefixLift 3647128
  have htrace : WordTrace (prefixWord ++ tailWord_3647128) baseStart_3647128 baseEnd_3647128 := by
    simpa [prefixWord, tailWord_3647128, baseEnd_3647128] using wordTrace_append hprefix tailTrace_3647128
  have hstable : (prefixWord ++ tailWord_3647128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647128).length < 2 ^ (prefixWord ++ tailWord_3647128).sum := by decide
  have hdescent : baseEnd_3647128 < baseStart_3647128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647141 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 8]
def baseStart_3647141 : Nat := 118140960795 + 3647141 * 2 ^ 59
def prefixEnd_3647141 : Nat := 4983230072969 + 3 ^ 40 * 3647141 * 2
def baseEnd_3647141 : Nat := 416163632826582283947691

theorem tailTrace_3647141 : CollatzResearch.WordTrace tailWord_3647141 prefixEnd_3647141 416163632826582283947691 := by
  unfold tailWord_3647141
  simp only [CollatzResearch.WordTrace]
  refine ⟨133022160480038513937733277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88681440320025675958488851 133022160480038513937733277)
  ·
    refine ⟨49883310180014442726649979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133022160480038513937733277 49883310180014442726649979)
    ·
      refine ⟨74824965270021664089974969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49883310180014442726649979 74824965270021664089974969)
      ·
        refine ⟨56118723952516248067481227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74824965270021664089974969 56118723952516248067481227)
        ·
          refine ⟨84178085928774372101221841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56118723952516248067481227 84178085928774372101221841)
          ·
            refine ⟨63133564446580779075916381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84178085928774372101221841 63133564446580779075916381)
            ·
              refine ⟨23675086667467792153468643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63133564446580779075916381 23675086667467792153468643)
              ·
                refine ⟨35512630001201688230202965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23675086667467792153468643 35512630001201688230202965)
                ·
                  refine ⟨416163632826582283947691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35512630001201688230202965 416163632826582283947691)
                  ·
                    rfl

theorem cell22_3647141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_3647141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647141 prefixEnd_3647141 := by exact prefixLift 3647141
  have htrace : WordTrace (prefixWord ++ tailWord_3647141) baseStart_3647141 baseEnd_3647141 := by
    simpa [prefixWord, tailWord_3647141, baseEnd_3647141] using wordTrace_append hprefix tailTrace_3647141
  have hstable : (prefixWord ++ tailWord_3647141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647141).length < 2 ^ (prefixWord ++ tailWord_3647141).sum := by decide
  have hdescent : baseEnd_3647141 < baseStart_3647141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647173 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_3647173 : Nat := 118140960795 + 3647173 * 2 ^ 59
def prefixEnd_3647173 : Nat := 4983230072969 + 3 ^ 40 * 3647173 * 2
def baseEnd_3647173 : Nat := 1248501852733709435042975

theorem tailTrace_3647173 : CollatzResearch.WordTrace tailWord_3647173 prefixEnd_3647173 1248501852733709435042975 := by
  unfold tailWord_3647173
  simp only [CollatzResearch.WordTrace]
  refine ⟨133023327615922583402898173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88682218410615055601932115 133023327615922583402898173)
  ·
    refine ⟨49883747855970968776086815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133023327615922583402898173 49883747855970968776086815)
    ·
      refine ⟨74825621783956453164130223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49883747855970968776086815 74825621783956453164130223)
      ·
        refine ⟨112238432675934679746195335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74825621783956453164130223 112238432675934679746195335)
        ·
          refine ⟨168357649013902019619293003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112238432675934679746195335 168357649013902019619293003)
          ·
            refine ⟨252536473520853029428939505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168357649013902019619293003 252536473520853029428939505)
            ·
              refine ⟨189402355140639772071704629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252536473520853029428939505 189402355140639772071704629)
              ·
                refine ⟨17756470794434978631722309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189402355140639772071704629 17756470794434978631722309)
                ·
                  refine ⟨3329338273956558493447933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17756470794434978631722309 3329338273956558493447933)
                  ·
                    refine ⟨1248501852733709435042975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329338273956558493447933 1248501852733709435042975)
                    ·
                      rfl

theorem cell22_3647173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_3647173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647173 prefixEnd_3647173 := by exact prefixLift 3647173
  have htrace : WordTrace (prefixWord ++ tailWord_3647173) baseStart_3647173 baseEnd_3647173 := by
    simpa [prefixWord, tailWord_3647173, baseEnd_3647173] using wordTrace_append hprefix tailTrace_3647173
  have hstable : (prefixWord ++ tailWord_3647173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647173).length < 2 ^ (prefixWord ++ tailWord_3647173).sum := by decide
  have hdescent : baseEnd_3647173 < baseStart_3647173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647235 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 3, 3]
def baseStart_3647235 : Nat := 118140960795 + 3647235 * 2 ^ 59
def prefixEnd_3647235 : Nat := 4983230072969 + 3 ^ 40 * 3647235 * 2
def baseEnd_3647235 : Nat := 1248523076600761939992785

theorem tailTrace_3647235 : CollatzResearch.WordTrace tailWord_3647235 prefixEnd_3647235 1248523076600761939992785 := by
  unfold tailWord_3647235
  simp only [CollatzResearch.WordTrace]
  refine ⟨133025588941697967991655159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88683725961131978661103439 133025588941697967991655159)
  ·
    refine ⟨199538383412546951987482739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133025588941697967991655159 199538383412546951987482739)
    ·
      refine ⟨299307575118820427981224109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199538383412546951987482739 299307575118820427981224109)
      ·
        refine ⟨112240340669557660492959041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299307575118820427981224109 112240340669557660492959041)
        ·
          refine ⟨84180255502168245369719281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112240340669557660492959041 84180255502168245369719281)
          ·
            refine ⟨63135191626626184027289461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84180255502168245369719281 63135191626626184027289461)
            ·
              refine ⟨5918924214996204752558387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63135191626626184027289461 5918924214996204752558387)
              ·
                refine ⟨8878386322494307128837581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918924214996204752558387 8878386322494307128837581)
                ·
                  refine ⟨3329394870935365173314093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8878386322494307128837581 3329394870935365173314093)
                  ·
                    refine ⟨1248523076600761939992785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329394870935365173314093 1248523076600761939992785)
                    ·
                      rfl

theorem cell22_3647235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 3].length) (baseStart_3647235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647235 prefixEnd_3647235 := by exact prefixLift 3647235
  have htrace : WordTrace (prefixWord ++ tailWord_3647235) baseStart_3647235 baseEnd_3647235 := by
    simpa [prefixWord, tailWord_3647235, baseEnd_3647235] using wordTrace_append hprefix tailTrace_3647235
  have hstable : (prefixWord ++ tailWord_3647235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647235).length < 2 ^ (prefixWord ++ tailWord_3647235).sum := by decide
  have hdescent : baseEnd_3647235 < baseStart_3647235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647245 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3647245 : Nat := 118140960795 + 3647245 * 2 ^ 59
def prefixEnd_3647245 : Nat := 4983230072969 + 3 ^ 40 * 3647245 * 2
def baseEnd_3647245 : Nat := 1248526499805125247242755

theorem tailTrace_3647245 : CollatzResearch.WordTrace tailWord_3647245 prefixEnd_3647245 1248526499805125247242755 := by
  unfold tailWord_3647245
  simp only [CollatzResearch.WordTrace]
  refine ⟨133025953671661739699519189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88683969114441159799679459 133025953671661739699519189)
  ·
    refine ⟨3117795789179572024207481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 133025953671661739699519189 3117795789179572024207481)
    ·
      refine ⟨2338346841884679018155611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3117795789179572024207481 2338346841884679018155611)
      ·
        refine ⟨3507520262827018527233417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338346841884679018155611 3507520262827018527233417)
        ·
          refine ⟨2630640197120263895425063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3507520262827018527233417 2630640197120263895425063)
          ·
            refine ⟨3945960295680395843137595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630640197120263895425063 3945960295680395843137595)
            ·
              refine ⟨5918940443520593764706393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945960295680395843137595 5918940443520593764706393)
              ·
                refine ⟨4439205332640445323529795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5918940443520593764706393 4439205332640445323529795)
                ·
                  refine ⟨6658807998960667985294693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439205332640445323529795 6658807998960667985294693)
                  ·
                    refine ⟨1248526499805125247242755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6658807998960667985294693 1248526499805125247242755)
                    ·
                      rfl

theorem cell22_3647245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3647245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647245 prefixEnd_3647245 := by exact prefixLift 3647245
  have htrace : WordTrace (prefixWord ++ tailWord_3647245) baseStart_3647245 baseEnd_3647245 := by
    simpa [prefixWord, tailWord_3647245, baseEnd_3647245] using wordTrace_append hprefix tailTrace_3647245
  have hstable : (prefixWord ++ tailWord_3647245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647245).length < 2 ^ (prefixWord ++ tailWord_3647245).sum := by decide
  have hdescent : baseEnd_3647245 < baseStart_3647245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647286 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3647286 : Nat := 118140960795 + 3647286 * 2 ^ 59
def prefixEnd_3647286 : Nat := 4983230072969 + 3 ^ 40 * 3647286 * 2
def baseEnd_3647286 : Nat := 1248540534943014806967629

theorem tailTrace_3647286 : CollatzResearch.WordTrace tailWord_3647286 prefixEnd_3647286 1248540534943014806967629 := by
  unfold tailWord_3647286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8314215566532075231360107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88684966043008802467841141 8314215566532075231360107)
  ·
    refine ⟨12471323349798112847040161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8314215566532075231360107 12471323349798112847040161)
    ·
      refine ⟨9353492512348584635280121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12471323349798112847040161 9353492512348584635280121)
      ·
        refine ⟨7015119384261438476460091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9353492512348584635280121 7015119384261438476460091)
        ·
          refine ⟨10522679076392157714690137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015119384261438476460091 10522679076392157714690137)
          ·
            refine ⟨7892009307294118286017603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10522679076392157714690137 7892009307294118286017603)
            ·
              refine ⟨11838013960941177429026405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7892009307294118286017603 11838013960941177429026405)
              ·
                refine ⟨2219627617676470767942451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11838013960941177429026405 2219627617676470767942451)
                ·
                  refine ⟨3329441426514706151913677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219627617676470767942451 3329441426514706151913677)
                  ·
                    refine ⟨1248540534943014806967629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329441426514706151913677 1248540534943014806967629)
                    ·
                      rfl

theorem cell22_3647286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3647286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647286 prefixEnd_3647286 := by exact prefixLift 3647286
  have htrace : WordTrace (prefixWord ++ tailWord_3647286) baseStart_3647286 baseEnd_3647286 := by
    simpa [prefixWord, tailWord_3647286, baseEnd_3647286] using wordTrace_append hprefix tailTrace_3647286
  have hstable : (prefixWord ++ tailWord_3647286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647286).length < 2 ^ (prefixWord ++ tailWord_3647286).sum := by decide
  have hdescent : baseEnd_3647286 < baseStart_3647286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647327 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 4]
def baseStart_3647327 : Nat := 118140960795 + 3647327 * 2 ^ 59
def prefixEnd_3647327 : Nat := 4983230072969 + 3 ^ 40 * 3647327 * 2
def baseEnd_3647327 : Nat := 416184856693634788897501

theorem tailTrace_3647327 : CollatzResearch.WordTrace tailWord_3647327 prefixEnd_3647327 416184856693634788897501 := by
  unfold tailWord_3647327
  simp only [CollatzResearch.WordTrace]
  refine ⟨133028944457364667704004235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88685962971576445136002823 133028944457364667704004235)
  ·
    refine ⟨199543416686047001556006353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133028944457364667704004235 199543416686047001556006353)
    ·
      refine ⟨149657562514535251167004765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199543416686047001556006353 149657562514535251167004765)
      ·
        refine ⟨56121585942950719187626787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149657562514535251167004765 56121585942950719187626787)
        ·
          refine ⟨84182378914426078781440181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56121585942950719187626787 84182378914426078781440181)
          ·
            refine ⟨7892098023227444885760017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84182378914426078781440181 7892098023227444885760017)
            ·
              refine ⟨5919073517420583664320013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7892098023227444885760017 5919073517420583664320013)
              ·
                refine ⟨2219652569032718874120005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5919073517420583664320013 2219652569032718874120005)
                ·
                  refine ⟨416184856693634788897501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219652569032718874120005 416184856693634788897501)
                  ·
                    rfl

theorem cell22_3647327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 4].length) (baseStart_3647327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647327 prefixEnd_3647327 := by exact prefixLift 3647327
  have htrace : WordTrace (prefixWord ++ tailWord_3647327) baseStart_3647327 baseEnd_3647327 := by
    simpa [prefixWord, tailWord_3647327, baseEnd_3647327] using wordTrace_append hprefix tailTrace_3647327
  have hstable : (prefixWord ++ tailWord_3647327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647327).length < 2 ^ (prefixWord ++ tailWord_3647327).sum := by decide
  have hdescent : baseEnd_3647327 < baseStart_3647327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647406 : List Nat := [4, 1, 5, 1, 1, 1, 2, 7]
def baseStart_3647406 : Nat := 118140960795 + 3647406 * 2 ^ 59
def prefixEnd_3647406 : Nat := 4983230072969 + 3 ^ 40 * 3647406 * 2
def baseEnd_3647406 : Nat := 138731290377263832663029

theorem tailTrace_3647406 : CollatzResearch.WordTrace tailWord_3647406 prefixEnd_3647406 138731290377263832663029 := by
  unfold tailWord_3647406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16628978228009808024516259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88687883882718976130753381 16628978228009808024516259)
  ·
    refine ⟨24943467342014712036774389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16628978228009808024516259 24943467342014712036774389)
    ·
      refine ⟨2338450063313879253447599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24943467342014712036774389 2338450063313879253447599)
      ·
        refine ⟨3507675094970818880171399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338450063313879253447599 3507675094970818880171399)
        ·
          refine ⟨5261512642456228320257099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507675094970818880171399 5261512642456228320257099)
          ·
            refine ⟨7892268963684342480385649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261512642456228320257099 7892268963684342480385649)
            ·
              refine ⟨5919201722763256860289237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7892268963684342480385649 5919201722763256860289237)
              ·
                refine ⟨138731290377263832663029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5919201722763256860289237 138731290377263832663029)
                ·
                  rfl

theorem cell22_3647406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_3647406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647406 prefixEnd_3647406 := by exact prefixLift 3647406
  have htrace : WordTrace (prefixWord ++ tailWord_3647406) baseStart_3647406 baseEnd_3647406 := by
    simpa [prefixWord, tailWord_3647406, baseEnd_3647406] using wordTrace_append hprefix tailTrace_3647406
  have hstable : (prefixWord ++ tailWord_3647406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647406).length < 2 ^ (prefixWord ++ tailWord_3647406).sum := by decide
  have hdescent : baseEnd_3647406 < baseStart_3647406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647460 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3647460 : Nat := 118140960795 + 3647460 * 2 ^ 59
def prefixEnd_3647460 : Nat := 4983230072969 + 3 ^ 40 * 3647460 * 2
def baseEnd_3647460 : Nat := 1248600098698936353117095

theorem tailTrace_3647460 : CollatzResearch.WordTrace tailWord_3647460 prefixEnd_3647460 1248600098698936353117095 := by
  unfold tailWord_3647460
  simp only [CollatzResearch.WordTrace]
  refine ⟨66516897682941415709297917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88689196910588554279063889 66516897682941415709297917)
  ·
    refine ⟨24943836631103030890986719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66516897682941415709297917 24943836631103030890986719)
    ·
      refine ⟨37415754946654546336480079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24943836631103030890986719 37415754946654546336480079)
      ·
        refine ⟨56123632419981819504720119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37415754946654546336480079 56123632419981819504720119)
        ·
          refine ⟨84185448629972729257080179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56123632419981819504720119 84185448629972729257080179)
          ·
            refine ⟨126278172944959093885620269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84185448629972729257080179 126278172944959093885620269)
            ·
              refine ⟨47354314854359660207107601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126278172944959093885620269 47354314854359660207107601)
              ·
                refine ⟨35515736140769745155330701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47354314854359660207107601 35515736140769745155330701)
                ·
                  refine ⟨13318401052788654433249013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35515736140769745155330701 13318401052788654433249013)
                  ·
                    refine ⟨1248600098698936353117095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13318401052788654433249013 1248600098698936353117095)
                    ·
                      rfl

theorem cell22_3647460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3647460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647460 prefixEnd_3647460 := by exact prefixLift 3647460
  have htrace : WordTrace (prefixWord ++ tailWord_3647460) baseStart_3647460 baseEnd_3647460 := by
    simpa [prefixWord, tailWord_3647460, baseEnd_3647460] using wordTrace_append hprefix tailTrace_3647460
  have hstable : (prefixWord ++ tailWord_3647460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647460).length < 2 ^ (prefixWord ++ tailWord_3647460).sum := by decide
  have hdescent : baseEnd_3647460 < baseStart_3647460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647475 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 4, 4]
def baseStart_3647475 : Nat := 118140960795 + 3647475 * 2 ^ 59
def prefixEnd_3647475 : Nat := 4983230072969 + 3 ^ 40 * 3647475 * 2
def baseEnd_3647475 : Nat := 1248605233505481313992049

theorem tailTrace_3647475 : CollatzResearch.WordTrace tailWord_3647475 prefixEnd_3647475 1248605233505481313992049 := by
  unfold tailWord_3647475
  simp only [CollatzResearch.WordTrace]
  refine ⟨133034342460828488980391879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88689561640552325986927919 133034342460828488980391879)
  ·
    refine ⟨199551513691242733470587819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133034342460828488980391879 199551513691242733470587819)
    ·
      refine ⟨299327270536864100205881729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199551513691242733470587819 299327270536864100205881729)
      ·
        refine ⟨224495452902648075154411297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299327270536864100205881729 224495452902648075154411297)
        ·
          refine ⟨168371589676986056365808473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224495452902648075154411297 168371589676986056365808473)
          ·
            refine ⟨126278692257739542274356355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168371589676986056365808473 126278692257739542274356355)
            ·
              refine ⟨189418038386609313411534533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126278692257739542274356355 189418038386609313411534533)
              ·
                refine ⟨35515882197489246264662725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189418038386609313411534533 35515882197489246264662725)
                ·
                  refine ⟨6659227912029233674624261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35515882197489246264662725 6659227912029233674624261)
                  ·
                    refine ⟨1248605233505481313992049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6659227912029233674624261 1248605233505481313992049)
                    ·
                      rfl

theorem cell22_3647475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_3647475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647475 prefixEnd_3647475 := by exact prefixLift 3647475
  have htrace : WordTrace (prefixWord ++ tailWord_3647475) baseStart_3647475 baseEnd_3647475 := by
    simpa [prefixWord, tailWord_3647475, baseEnd_3647475] using wordTrace_append hprefix tailTrace_3647475
  have hstable : (prefixWord ++ tailWord_3647475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647475).length < 2 ^ (prefixWord ++ tailWord_3647475).sum := by decide
  have hdescent : baseEnd_3647475 < baseStart_3647475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647498 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_3647498 : Nat := 118140960795 + 3647498 * 2 ^ 59
def prefixEnd_3647498 : Nat := 4983230072969 + 3 ^ 40 * 3647498 * 2
def baseEnd_3647498 : Nat := 1248613106875516920666979

theorem tailTrace_3647498 : CollatzResearch.WordTrace tailWord_3647498 prefixEnd_3647498 1248613106875516920666979 := by
  unfold tailWord_3647498
  simp only [CollatzResearch.WordTrace]
  refine ⟨33258795334936290977119787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88690120893163442605652765 33258795334936290977119787)
  ·
    refine ⟨49888193002404436465679681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33258795334936290977119787 49888193002404436465679681)
    ·
      refine ⟨37416144751803327349259761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49888193002404436465679681 37416144751803327349259761)
      ·
        refine ⟨28062108563852495511944821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37416144751803327349259761 28062108563852495511944821)
        ·
          refine ⟨2630822677861171454244827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28062108563852495511944821 2630822677861171454244827)
          ·
            refine ⟨3946234016791757181367241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630822677861171454244827 3946234016791757181367241)
            ·
              refine ⟨2959675512593817886025431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946234016791757181367241 2959675512593817886025431)
              ·
                refine ⟨4439513268890726829038147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959675512593817886025431 4439513268890726829038147)
                ·
                  refine ⟨6659269903336090243557221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439513268890726829038147 6659269903336090243557221)
                  ·
                    refine ⟨1248613106875516920666979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6659269903336090243557221 1248613106875516920666979)
                    ·
                      rfl

theorem cell22_3647498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_3647498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647498 prefixEnd_3647498 := by exact prefixLift 3647498
  have htrace : WordTrace (prefixWord ++ tailWord_3647498) baseStart_3647498 baseEnd_3647498 := by
    simpa [prefixWord, tailWord_3647498, baseEnd_3647498] using wordTrace_append hprefix tailTrace_3647498
  have hstable : (prefixWord ++ tailWord_3647498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647498).length < 2 ^ (prefixWord ++ tailWord_3647498).sum := by decide
  have hdescent : baseEnd_3647498 < baseStart_3647498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647528 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3647528 : Nat := 118140960795 + 3647528 * 2 ^ 59
def prefixEnd_3647528 : Nat := 4983230072969 + 3 ^ 40 * 3647528 * 2
def baseEnd_3647528 : Nat := 1248623376488606842416887

theorem tailTrace_3647528 : CollatzResearch.WordTrace tailWord_3647528 prefixEnd_3647528 1248623376488606842416887 := by
  unfold tailWord_3647528
  simp only [CollatzResearch.WordTrace]
  refine ⟨66518137764818239516035619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88690850353090986021380825 66518137764818239516035619)
  ·
    refine ⟨99777206647227359274053429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66518137764818239516035619 99777206647227359274053429)
    ·
      refine ⟨9354113123177564931942509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99777206647227359274053429 9354113123177564931942509)
      ·
        refine ⟨3507792421191586849478441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9354113123177564931942509 3507792421191586849478441)
        ·
          refine ⟨2630844315893690137108831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3507792421191586849478441 2630844315893690137108831)
          ·
            refine ⟨3946266473840535205663247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630844315893690137108831 3946266473840535205663247)
            ·
              refine ⟨5919399710760802808494871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946266473840535205663247 5919399710760802808494871)
              ·
                refine ⟨8879099566141204212742307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919399710760802808494871 8879099566141204212742307)
                ·
                  refine ⟨13318649349211806319113461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879099566141204212742307 13318649349211806319113461)
                  ·
                    refine ⟨1248623376488606842416887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13318649349211806319113461 1248623376488606842416887)
                    ·
                      rfl

theorem cell22_3647528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3647528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647528 prefixEnd_3647528 := by exact prefixLift 3647528
  have htrace : WordTrace (prefixWord ++ tailWord_3647528) baseStart_3647528 baseEnd_3647528 := by
    simpa [prefixWord, tailWord_3647528, baseEnd_3647528] using wordTrace_append hprefix tailTrace_3647528
  have hstable : (prefixWord ++ tailWord_3647528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647528).length < 2 ^ (prefixWord ++ tailWord_3647528).sum := by decide
  have hdescent : baseEnd_3647528 < baseStart_3647528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647573 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_3647573 : Nat := 118140960795 + 3647573 * 2 ^ 59
def prefixEnd_3647573 : Nat := 4983230072969 + 3 ^ 40 * 3647573 * 2
def baseEnd_3647573 : Nat := 1248638780908241725041749

theorem tailTrace_3647573 : CollatzResearch.WordTrace tailWord_3647573 prefixEnd_3647573 1248638780908241725041749 := by
  unfold tailWord_3647573
  simp only [CollatzResearch.WordTrace]
  refine ⟨133037916814473451717459373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88691944542982301144972915 133037916814473451717459373)
  ·
    refine ⟨49889218805427544394047265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133037916814473451717459373 49889218805427544394047265)
    ·
      refine ⟨37416914104070658295535449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49889218805427544394047265 37416914104070658295535449)
      ·
        refine ⟨28062685578052993721651587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37416914104070658295535449 28062685578052993721651587)
        ·
          refine ⟨42094028367079490582477381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28062685578052993721651587 42094028367079490582477381)
          ·
            refine ⟨7892630318827404484214509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42094028367079490582477381 7892630318827404484214509)
            ·
              refine ⟨2959736369560276681580441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7892630318827404484214509 2959736369560276681580441)
              ·
                refine ⟨2219802277170207511185331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959736369560276681580441 2219802277170207511185331)
                ·
                  refine ⟨3329703415755311266777997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219802277170207511185331 3329703415755311266777997)
                  ·
                    refine ⟨1248638780908241725041749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329703415755311266777997 1248638780908241725041749)
                    ·
                      rfl

theorem cell22_3647573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_3647573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647573 prefixEnd_3647573 := by exact prefixLift 3647573
  have htrace : WordTrace (prefixWord ++ tailWord_3647573) baseStart_3647573 baseEnd_3647573 := by
    simpa [prefixWord, tailWord_3647573, baseEnd_3647573] using wordTrace_append hprefix tailTrace_3647573
  have hstable : (prefixWord ++ tailWord_3647573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647573).length < 2 ^ (prefixWord ++ tailWord_3647573).sum := by decide
  have hdescent : baseEnd_3647573 < baseStart_3647573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647586 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3647586 : Nat := 118140960795 + 3647586 * 2 ^ 59
def prefixEnd_3647586 : Nat := 4983230072969 + 3 ^ 40 * 3647586 * 2
def baseEnd_3647586 : Nat := 416214410357971341488903

theorem tailTrace_3647586 : CollatzResearch.WordTrace tailWord_3647586 prefixEnd_3647586 416214410357971341488903 := by
  unfold tailWord_3647586
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259597740856588734420653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88692260642284236625121741 33259597740856588734420653)
  ·
    refine ⟨12472349152821220775407745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33259597740856588734420653 12472349152821220775407745)
    ·
      refine ⟨9354261864615915581555809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12472349152821220775407745 9354261864615915581555809)
      ·
        refine ⟨7015696398461936686166857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9354261864615915581555809 7015696398461936686166857)
        ·
          refine ⟨5261772298846452514625143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7015696398461936686166857 5261772298846452514625143)
          ·
            refine ⟨7892658448269678771937715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261772298846452514625143 7892658448269678771937715)
            ·
              refine ⟨11838987672404518157906573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7892658448269678771937715 11838987672404518157906573)
              ·
                refine ⟨4439620377151694309214965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11838987672404518157906573 4439620377151694309214965)
                ·
                  refine ⟨416214410357971341488903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4439620377151694309214965 416214410357971341488903)
                  ·
                    rfl

theorem cell22_3647586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3647586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647586 prefixEnd_3647586 := by exact prefixLift 3647586
  have htrace : WordTrace (prefixWord ++ tailWord_3647586) baseStart_3647586 baseEnd_3647586 := by
    simpa [prefixWord, tailWord_3647586, baseEnd_3647586] using wordTrace_append hprefix tailTrace_3647586
  have hstable : (prefixWord ++ tailWord_3647586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647586).length < 2 ^ (prefixWord ++ tailWord_3647586).sum := by decide
  have hdescent : baseEnd_3647586 < baseStart_3647586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647597 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3647597 : Nat := 118140960795 + 3647597 * 2 ^ 59
def prefixEnd_3647597 : Nat := 4983230072969 + 3 ^ 40 * 3647597 * 2
def baseEnd_3647597 : Nat := 416215665532904554147225

theorem tailTrace_3647597 : CollatzResearch.WordTrace tailWord_3647597 prefixEnd_3647597 416215665532904554147225 := by
  unfold tailWord_3647597
  simp only [CollatzResearch.WordTrace]
  refine ⟨133038792166386503816333045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88692528110924335877555363 133038792166386503816333045)
  ·
    refine ⟨12472386765598734732781223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133038792166386503816333045 12472386765598734732781223)
    ·
      refine ⟨18708580148398102099171835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12472386765598734732781223 18708580148398102099171835)
      ·
        refine ⟨28062870222597153148757753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18708580148398102099171835 28062870222597153148757753)
        ·
          refine ⟨21047152666947864861568315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28062870222597153148757753 21047152666947864861568315)
          ·
            refine ⟨31570729000421797292352473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21047152666947864861568315 31570729000421797292352473)
            ·
              refine ⟨23678046750316347969264355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31570729000421797292352473 23678046750316347969264355)
              ·
                refine ⟨35517070125474521953896533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23678046750316347969264355 35517070125474521953896533)
                ·
                  refine ⟨416215665532904554147225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35517070125474521953896533 416215665532904554147225)
                  ·
                    rfl

theorem cell22_3647597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3647597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647597 prefixEnd_3647597 := by exact prefixLift 3647597
  have htrace : WordTrace (prefixWord ++ tailWord_3647597) baseStart_3647597 baseEnd_3647597 := by
    simpa [prefixWord, tailWord_3647597, baseEnd_3647597] using wordTrace_append hprefix tailTrace_3647597
  have hstable : (prefixWord ++ tailWord_3647597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647597).length < 2 ^ (prefixWord ++ tailWord_3647597).sum := by decide
  have hdescent : baseEnd_3647597 < baseStart_3647597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647599 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 1, 4]
def baseStart_3647599 : Nat := 118140960795 + 3647599 * 2 ^ 59
def prefixEnd_3647599 : Nat := 4983230072969 + 3 ^ 40 * 3647599 * 2
def baseEnd_3647599 : Nat := 1248647681239586323891669

theorem tailTrace_3647599 : CollatzResearch.WordTrace tailWord_3647599 prefixEnd_3647599 1248647681239586323891669 := by
  unfold tailWord_3647599
  simp only [CollatzResearch.WordTrace]
  refine ⟨133038865112379258157905851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88692576741586172105270567 133038865112379258157905851)
  ·
    refine ⟨199558297668568887236858777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133038865112379258157905851 199558297668568887236858777)
    ·
      refine ⟨149668723251426665427644083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199558297668568887236858777 149668723251426665427644083)
      ·
        refine ⟨224503084877139998141466125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149668723251426665427644083 224503084877139998141466125)
        ·
          refine ⟨84188656828927499303049797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224503084877139998141466125 84188656828927499303049797)
          ·
            refine ⟨15785373155423906119321837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84188656828927499303049797 15785373155423906119321837)
            ·
              refine ⟨5919514933283964794745689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15785373155423906119321837 5919514933283964794745689)
              ·
                refine ⟨4439636199962973596059267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5919514933283964794745689 4439636199962973596059267)
                ·
                  refine ⟨6659454299944460394088901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439636199962973596059267 6659454299944460394088901)
                  ·
                    refine ⟨1248647681239586323891669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6659454299944460394088901 1248647681239586323891669)
                    ·
                      rfl

theorem cell22_3647599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_3647599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647599 prefixEnd_3647599 := by exact prefixLift 3647599
  have htrace : WordTrace (prefixWord ++ tailWord_3647599) baseStart_3647599 baseEnd_3647599 := by
    simpa [prefixWord, tailWord_3647599, baseEnd_3647599] using wordTrace_append hprefix tailTrace_3647599
  have hstable : (prefixWord ++ tailWord_3647599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647599).length < 2 ^ (prefixWord ++ tailWord_3647599).sum := by decide
  have hdescent : baseEnd_3647599 < baseStart_3647599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647612 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3647612 : Nat := 118140960795 + 3647612 * 2 ^ 59
def prefixEnd_3647612 : Nat := 4983230072969 + 3 ^ 40 * 3647612 * 2
def baseEnd_3647612 : Nat := 1248652131405258623316629

theorem tailTrace_3647612 : CollatzResearch.WordTrace tailWord_3647612 prefixEnd_3647612 1248652131405258623316629 := by
  unfold tailWord_3647612
  simp only [CollatzResearch.WordTrace]
  refine ⟨66519669630666080689064545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88692892840888107585419393 66519669630666080689064545)
  ·
    refine ⟨49889752222999560516798409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66519669630666080689064545 49889752222999560516798409)
    ·
      refine ⟨37417314167249670387598807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49889752222999560516798409 37417314167249670387598807)
      ·
        refine ⟨56125971250874505581398211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37417314167249670387598807 56125971250874505581398211)
        ·
          refine ⟨84188956876311758372097317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56125971250874505581398211 84188956876311758372097317)
          ·
            refine ⟨15785429414308454694768247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84188956876311758372097317 15785429414308454694768247)
            ·
              refine ⟨23678144121462682042152371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785429414308454694768247 23678144121462682042152371)
              ·
                refine ⟨35517216182194023063228557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23678144121462682042152371 35517216182194023063228557)
                ·
                  refine ⟨13318956068322758648710709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35517216182194023063228557 13318956068322758648710709)
                  ·
                    refine ⟨1248652131405258623316629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13318956068322758648710709 1248652131405258623316629)
                    ·
                      rfl

theorem cell22_3647612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3647612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647612 prefixEnd_3647612 := by exact prefixLift 3647612
  have htrace : WordTrace (prefixWord ++ tailWord_3647612) baseStart_3647612 baseEnd_3647612 := by
    simpa [prefixWord, tailWord_3647612, baseEnd_3647612] using wordTrace_append hprefix tailTrace_3647612
  have hstable : (prefixWord ++ tailWord_3647612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647612).length < 2 ^ (prefixWord ++ tailWord_3647612).sum := by decide
  have hdescent : baseEnd_3647612 < baseStart_3647612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647661 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3647661 : Nat := 118140960795 + 3647661 * 2 ^ 59
def prefixEnd_3647661 : Nat := 4983230072969 + 3 ^ 40 * 3647661 * 2
def baseEnd_3647661 : Nat := 1248668905106638828841479

theorem tailTrace_3647661 : CollatzResearch.WordTrace tailWord_3647661 prefixEnd_3647661 1248668905106638828841479 := by
  unfold tailWord_3647661
  simp only [CollatzResearch.WordTrace]
  refine ⟨133041126438154642746662837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88694084292103095164441891 133041126438154642746662837)
  ·
    refine ⟨12472605603576997757499641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133041126438154642746662837 12472605603576997757499641)
    ·
      refine ⟨9354454202682748318124731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12472605603576997757499641 9354454202682748318124731)
      ·
        refine ⟨14031681304024122477187097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9354454202682748318124731 14031681304024122477187097)
        ·
          refine ⟨10523760978018091857890323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14031681304024122477187097 10523760978018091857890323)
          ·
            refine ⟨15785641467027137786835485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523760978018091857890323 15785641467027137786835485)
            ·
              refine ⟨5919615550135176670063307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15785641467027137786835485 5919615550135176670063307)
              ·
                refine ⟨8879423325202765005094961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919615550135176670063307 8879423325202765005094961)
                ·
                  refine ⟨6659567493902073753821221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8879423325202765005094961 6659567493902073753821221)
                  ·
                    refine ⟨1248668905106638828841479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6659567493902073753821221 1248668905106638828841479)
                    ·
                      rfl

theorem cell22_3647661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3647661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647661 prefixEnd_3647661 := by exact prefixLift 3647661
  have htrace : WordTrace (prefixWord ++ tailWord_3647661) baseStart_3647661 baseEnd_3647661 := by
    simpa [prefixWord, tailWord_3647661, baseEnd_3647661] using wordTrace_append hprefix tailTrace_3647661
  have hstable : (prefixWord ++ tailWord_3647661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647661).length < 2 ^ (prefixWord ++ tailWord_3647661).sum := by decide
  have hdescent : baseEnd_3647661 < baseStart_3647661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647691 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 1, 3]
def baseStart_3647691 : Nat := 118140960795 + 3647691 * 2 ^ 59
def prefixEnd_3647691 : Nat := 4983230072969 + 3 ^ 40 * 3647691 * 2
def baseEnd_3647691 : Nat := 1248679174719728750591387

theorem tailTrace_3647691 : CollatzResearch.WordTrace tailWord_3647691 prefixEnd_3647691 1248679174719728750591387 := by
  unfold tailWord_3647691
  simp only [CollatzResearch.WordTrace]
  refine ⟨133042220628045957870254927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88694813752030638580169951 133042220628045957870254927)
  ·
    refine ⟨199563330942068936805382391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133042220628045957870254927 199563330942068936805382391)
    ·
      refine ⟨299344996413103405208073587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199563330942068936805382391 299344996413103405208073587)
      ·
        refine ⟨449017494619655107812110381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299344996413103405208073587 449017494619655107812110381)
        ·
          refine ⟨168381560482370665429541393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449017494619655107812110381 168381560482370665429541393)
          ·
            refine ⟨126286170361777999072156045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168381560482370665429541393 126286170361777999072156045)
            ·
              refine ⟨47357313885666749652058517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126286170361777999072156045 47357313885666749652058517)
              ·
                refine ⟨2219874088390628889940243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47357313885666749652058517 2219874088390628889940243)
                ·
                  refine ⟨3329811132585943334910365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219874088390628889940243 3329811132585943334910365)
                  ·
                    refine ⟨1248679174719728750591387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329811132585943334910365 1248679174719728750591387)
                    ·
                      rfl

theorem cell22_3647691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 1, 3].length) (baseStart_3647691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647691 prefixEnd_3647691 := by exact prefixLift 3647691
  have htrace : WordTrace (prefixWord ++ tailWord_3647691) baseStart_3647691 baseEnd_3647691 := by
    simpa [prefixWord, tailWord_3647691, baseEnd_3647691] using wordTrace_append hprefix tailTrace_3647691
  have hstable : (prefixWord ++ tailWord_3647691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647691).length < 2 ^ (prefixWord ++ tailWord_3647691).sum := by decide
  have hdescent : baseEnd_3647691 < baseStart_3647691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647781 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_3647781 : Nat := 118140960795 + 3647781 * 2 ^ 59
def prefixEnd_3647781 : Nat := 4983230072969 + 3 ^ 40 * 3647781 * 2
def baseEnd_3647781 : Nat := 1248709983558998515841111

theorem tailTrace_3647781 : CollatzResearch.WordTrace tailWord_3647781 prefixEnd_3647781 1248709983558998515841111 := by
  unfold tailWord_3647781
  simp only [CollatzResearch.WordTrace]
  refine ⟨133045503197719903241031197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88697002131813268827354131 133045503197719903241031197)
  ·
    refine ⟨49892063699144963715386699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133045503197719903241031197 49892063699144963715386699)
    ·
      refine ⟨74838095548717445573080049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49892063699144963715386699 74838095548717445573080049)
      ·
        refine ⟨56128571661538084179810037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74838095548717445573080049 56128571661538084179810037)
        ·
          refine ⟨5262053593269195391857191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56128571661538084179810037 5262053593269195391857191)
          ·
            refine ⟨7893080389903793087785787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262053593269195391857191 7893080389903793087785787)
            ·
              refine ⟨11839620584855689631678681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893080389903793087785787 11839620584855689631678681)
              ·
                refine ⟨8879715438641767223759011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11839620584855689631678681 8879715438641767223759011)
                ·
                  refine ⟨13319573157962650835638517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879715438641767223759011 13319573157962650835638517)
                  ·
                    refine ⟨1248709983558998515841111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13319573157962650835638517 1248709983558998515841111)
                    ·
                      rfl

theorem cell22_3647781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_3647781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647781 prefixEnd_3647781 := by exact prefixLift 3647781
  have htrace : WordTrace (prefixWord ++ tailWord_3647781) baseStart_3647781 baseEnd_3647781 := by
    simpa [prefixWord, tailWord_3647781, baseEnd_3647781] using wordTrace_append hprefix tailTrace_3647781
  have hstable : (prefixWord ++ tailWord_3647781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647781).length < 2 ^ (prefixWord ++ tailWord_3647781).sum := by decide
  have hdescent : baseEnd_3647781 < baseStart_3647781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647794 : List Nat := [3, 2, 1, 1, 5, 10]
def baseStart_3647794 : Nat := 118140960795 + 3647794 * 2 ^ 59
def prefixEnd_3647794 : Nat := 4983230072969 + 3 ^ 40 * 3647794 * 2
def baseEnd_3647794 : Nat := 15416227576847787842791

theorem tailTrace_3647794 : CollatzResearch.WordTrace tailWord_3647794 prefixEnd_3647794 15416227576847787842791 := by
  unfold tailWord_3647794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33261494336668201615313609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88697318231115204307502957 33261494336668201615313609)
  ·
    refine ⟨24946120752501151211485207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33261494336668201615313609 24946120752501151211485207)
    ·
      refine ⟨37419181128751726817227811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24946120752501151211485207 37419181128751726817227811)
      ·
        refine ⟨56128771693127590225841717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37419181128751726817227811 56128771693127590225841717)
        ·
          refine ⟨5262072346230711583672661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56128771693127590225841717 5262072346230711583672661)
          ·
            refine ⟨15416227576847787842791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5262072346230711583672661 15416227576847787842791)
            ·
              rfl

theorem cell22_3647794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 10].length) (baseStart_3647794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647794 prefixEnd_3647794 := by exact prefixLift 3647794
  have htrace : WordTrace (prefixWord ++ tailWord_3647794) baseStart_3647794 baseEnd_3647794 := by
    simpa [prefixWord, tailWord_3647794, baseEnd_3647794] using wordTrace_append hprefix tailTrace_3647794
  have hstable : (prefixWord ++ tailWord_3647794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647794).length < 2 ^ (prefixWord ++ tailWord_3647794).sum := by decide
  have hdescent : baseEnd_3647794 < baseStart_3647794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647826 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_3647826 : Nat := 118140960795 + 3647826 * 2 ^ 59
def prefixEnd_3647826 : Nat := 4983230072969 + 3 ^ 40 * 3647826 * 2
def baseEnd_3647826 : Nat := 1248725387978633398465973

theorem tailTrace_3647826 : CollatzResearch.WordTrace tailWord_3647826 prefixEnd_3647826 1248725387978633398465973 := by
  unfold tailWord_3647826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33261786120639218981604833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88698096321704583950946221 33261786120639218981604833)
  ·
    refine ⟨24946339590479414236203625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33261786120639218981604833 24946339590479414236203625)
    ·
      refine ⟨18709754692859560677152719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24946339590479414236203625 18709754692859560677152719)
      ·
        refine ⟨28064632039289341015729079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18709754692859560677152719 28064632039289341015729079)
        ·
          refine ⟨42096948058934011523593619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28064632039289341015729079 42096948058934011523593619)
          ·
            refine ⟨63145422088401017285390429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42096948058934011523593619 63145422088401017285390429)
            ·
              refine ⟨23679533283150381482021411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63145422088401017285390429 23679533283150381482021411)
              ·
                refine ⟨35519299924725572223032117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23679533283150381482021411 35519299924725572223032117)
                ·
                  refine ⟨3329934367943022395909261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35519299924725572223032117 3329934367943022395909261)
                  ·
                    refine ⟨1248725387978633398465973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329934367943022395909261 1248725387978633398465973)
                    ·
                      rfl

theorem cell22_3647826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_3647826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647826 prefixEnd_3647826 := by exact prefixLift 3647826
  have htrace : WordTrace (prefixWord ++ tailWord_3647826) baseStart_3647826 baseEnd_3647826 := by
    simpa [prefixWord, tailWord_3647826, baseEnd_3647826] using wordTrace_append hprefix tailTrace_3647826
  have hstable : (prefixWord ++ tailWord_3647826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647826).length < 2 ^ (prefixWord ++ tailWord_3647826).sum := by decide
  have hdescent : baseEnd_3647826 < baseStart_3647826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647856 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_3647856 : Nat := 118140960795 + 3647856 * 2 ^ 59
def prefixEnd_3647856 : Nat := 4983230072969 + 3 ^ 40 * 3647856 * 2
def baseEnd_3647856 : Nat := 416245219197241106738627

theorem tailTrace_3647856 : CollatzResearch.WordTrace tailWord_3647856 prefixEnd_3647856 416245219197241106738627 := by
  unfold tailWord_3647856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66524119336224095525005711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88698825781632127366674281 66524119336224095525005711)
  ·
    refine ⟨99786179004336143287508567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66524119336224095525005711 99786179004336143287508567)
    ·
      refine ⟨149679268506504214931262851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99786179004336143287508567 149679268506504214931262851)
      ·
        refine ⟨224518902759756322396894277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149679268506504214931262851 224518902759756322396894277)
        ·
          refine ⟨42097294267454310449417677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224518902759756322396894277 42097294267454310449417677)
          ·
            refine ⟨15786485350295366418531629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42097294267454310449417677 15786485350295366418531629)
            ·
              refine ⟨5919932006360762406949361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15786485350295366418531629 5919932006360762406949361)
              ·
                refine ⟨4439949004770571805212021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5919932006360762406949361 4439949004770571805212021)
                ·
                  refine ⟨416245219197241106738627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4439949004770571805212021 416245219197241106738627)
                  ·
                    rfl

theorem cell22_3647856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_3647856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647856 prefixEnd_3647856 := by exact prefixLift 3647856
  have htrace : WordTrace (prefixWord ++ tailWord_3647856) baseStart_3647856 baseEnd_3647856 := by
    simpa [prefixWord, tailWord_3647856, baseEnd_3647856] using wordTrace_append hprefix tailTrace_3647856
  have hstable : (prefixWord ++ tailWord_3647856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647856).length < 2 ^ (prefixWord ++ tailWord_3647856).sum := by decide
  have hdescent : baseEnd_3647856 < baseStart_3647856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647924 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3647924 : Nat := 118140960795 + 3647924 * 2 ^ 59
def prefixEnd_3647924 : Nat := 4983230072969 + 3 ^ 40 * 3647924 * 2
def baseEnd_3647924 : Nat := 416252978460464603171891

theorem tailTrace_3647924 : CollatzResearch.WordTrace tailWord_3647924 prefixEnd_3647924 416252978460464603171891 := by
  unfold tailWord_3647924
  simp only [CollatzResearch.WordTrace]
  refine ⟨66525359418100919331743413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88700479224134559108991217 66525359418100919331743413)
  ·
    refine ⟨6236752445446961187350945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66525359418100919331743413 6236752445446961187350945)
    ·
      refine ⟨4677564334085220890513209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6236752445446961187350945 4677564334085220890513209)
      ·
        refine ⟨3508173250563915667884907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4677564334085220890513209 3508173250563915667884907)
        ·
          refine ⟨5262259875845873501827361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508173250563915667884907 5262259875845873501827361)
          ·
            refine ⟨3946694906884405126370521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5262259875845873501827361 3946694906884405126370521)
            ·
              refine ⟨2960021180163303844777891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946694906884405126370521 2960021180163303844777891)
              ·
                refine ⟨4440031770244955767166837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960021180163303844777891 4440031770244955767166837)
                ·
                  refine ⟨416252978460464603171891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4440031770244955767166837 416252978460464603171891)
                  ·
                    rfl

theorem cell22_3647924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3647924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647924 prefixEnd_3647924 := by exact prefixLift 3647924
  have htrace : WordTrace (prefixWord ++ tailWord_3647924) baseStart_3647924 baseEnd_3647924 := by
    simpa [prefixWord, tailWord_3647924, baseEnd_3647924] using wordTrace_append hprefix tailTrace_3647924
  have hstable : (prefixWord ++ tailWord_3647924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647924).length < 2 ^ (prefixWord ++ tailWord_3647924).sum := by decide
  have hdescent : baseEnd_3647924 < baseStart_3647924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647937 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3647937 : Nat := 118140960795 + 3647937 * 2 ^ 59
def prefixEnd_3647937 : Nat := 4983230072969 + 3 ^ 40 * 3647937 * 2
def baseEnd_3647937 : Nat := 1248763385547066108940633

theorem tailTrace_3647937 : CollatzResearch.WordTrace tailWord_3647937 prefixEnd_3647937 1248763385547066108940633 := by
  unfold tailWord_3647937
  simp only [CollatzResearch.WordTrace]
  refine ⟨133051192985154741883710065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88700795323436494589140043 133051192985154741883710065)
  ·
    refine ⟨99788394738866056412782549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133051192985154741883710065 99788394738866056412782549)
    ·
      refine ⟨2338790501692173197174591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 99788394738866056412782549 2338790501692173197174591)
      ·
        refine ⟨3508185752538259795761887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338790501692173197174591 3508185752538259795761887)
        ·
          refine ⟨5262278628807389693642831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508185752538259795761887 5262278628807389693642831)
          ·
            refine ⟨7893417943211084540464247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262278628807389693642831 7893417943211084540464247)
            ·
              refine ⟨11840126914816626810696371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893417943211084540464247 11840126914816626810696371)
              ·
                refine ⟨17760190372224940216044557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11840126914816626810696371 17760190372224940216044557)
                ·
                  refine ⟨6660071389584352581016709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17760190372224940216044557 6660071389584352581016709)
                  ·
                    refine ⟨1248763385547066108940633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660071389584352581016709 1248763385547066108940633)
                    ·
                      rfl

theorem cell22_3647937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3647937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647937 prefixEnd_3647937 := by exact prefixLift 3647937
  have htrace : WordTrace (prefixWord ++ tailWord_3647937) baseStart_3647937 baseEnd_3647937 := by
    simpa [prefixWord, tailWord_3647937, baseEnd_3647937] using wordTrace_append hprefix tailTrace_3647937
  have hstable : (prefixWord ++ tailWord_3647937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647937).length < 2 ^ (prefixWord ++ tailWord_3647937).sum := by decide
  have hdescent : baseEnd_3647937 < baseStart_3647937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647976 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3647976 : Nat := 118140960795 + 3647976 * 2 ^ 59
def prefixEnd_3647976 : Nat := 4983230072969 + 3 ^ 40 * 3647976 * 2
def baseEnd_3647976 : Nat := 1248776736044083007215513

theorem tailTrace_3647976 : CollatzResearch.WordTrace tailWord_3647976 prefixEnd_3647976 1248776736044083007215513 := by
  unfold tailWord_3647976
  simp only [CollatzResearch.WordTrace]
  refine ⟨66526307716006725772189891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88701743621342301029586521 66526307716006725772189891)
  ·
    refine ⟨99789461574010088658284837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66526307716006725772189891 99789461574010088658284837)
    ·
      refine ⟨18710524045126891623428407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99789461574010088658284837 18710524045126891623428407)
      ·
        refine ⟨28065786067690337435142611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18710524045126891623428407 28065786067690337435142611)
        ·
          refine ⟨42098679101535506152713917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28065786067690337435142611 42098679101535506152713917)
          ·
            refine ⟨15787004663075814807267719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42098679101535506152713917 15787004663075814807267719)
            ·
              refine ⟨23680506994613722210901579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15787004663075814807267719 23680506994613722210901579)
              ·
                refine ⟨35520760491920583316352369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23680506994613722210901579 35520760491920583316352369)
                ·
                  refine ⟨26640570368940437487264277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35520760491920583316352369 26640570368940437487264277)
                  ·
                    refine ⟨1248776736044083007215513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26640570368940437487264277 1248776736044083007215513)
                    ·
                      rfl

theorem cell22_3647976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3647976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3647976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3647976 prefixEnd_3647976 := by exact prefixLift 3647976
  have htrace : WordTrace (prefixWord ++ tailWord_3647976) baseStart_3647976 baseEnd_3647976 := by
    simpa [prefixWord, tailWord_3647976, baseEnd_3647976] using wordTrace_append hprefix tailTrace_3647976
  have hstable : (prefixWord ++ tailWord_3647976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647976).length < 2 ^ (prefixWord ++ tailWord_3647976).sum := by decide
  have hdescent : baseEnd_3647976 < baseStart_3647976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648012 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_3648012 : Nat := 118140960795 + 3648012 * 2 ^ 59
def prefixEnd_3648012 : Nat := 4983230072969 + 3 ^ 40 * 3648012 * 2
def baseEnd_3648012 : Nat := 1248789059579790913315403

theorem tailTrace_3648012 : CollatzResearch.WordTrace tailWord_3648012 prefixEnd_3648012 1248789059579790913315403 := by
  unfold tailWord_3648012
  simp only [CollatzResearch.WordTrace]
  refine ⟨66526964229941514846345145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88702618973255353128460193 66526964229941514846345145)
  ·
    refine ⟨49895223172456136134758859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66526964229941514846345145 49895223172456136134758859)
    ·
      refine ⟨74842834758684204202138289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49895223172456136134758859 74842834758684204202138289)
      ·
        refine ⟨56132126069013153151603717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74842834758684204202138289 56132126069013153151603717)
        ·
          refine ⟨10524773637939966215925697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56132126069013153151603717 10524773637939966215925697)
          ·
            refine ⟨7893580228454974661944273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10524773637939966215925697 7893580228454974661944273)
            ·
              refine ⟨5920185171341230996458205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7893580228454974661944273 5920185171341230996458205)
              ·
                refine ⟨2220069439252961623671827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5920185171341230996458205 2220069439252961623671827)
                ·
                  refine ⟨3330104158879442435507741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220069439252961623671827 3330104158879442435507741)
                  ·
                    refine ⟨1248789059579790913315403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330104158879442435507741 1248789059579790913315403)
                    ·
                      rfl

theorem cell22_3648012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_3648012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648012 prefixEnd_3648012 := by exact prefixLift 3648012
  have htrace : WordTrace (prefixWord ++ tailWord_3648012) baseStart_3648012 baseEnd_3648012 := by
    simpa [prefixWord, tailWord_3648012, baseEnd_3648012] using wordTrace_append hprefix tailTrace_3648012
  have hstable : (prefixWord ++ tailWord_3648012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648012).length < 2 ^ (prefixWord ++ tailWord_3648012).sum := by decide
  have hdescent : baseEnd_3648012 < baseStart_3648012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648081 : List Nat := [1, 2, 2, 1, 3, 3, 10]
def baseStart_3648081 : Nat := 118140960795 + 3648081 * 2 ^ 59
def prefixEnd_3648081 : Nat := 4983230072969 + 3 ^ 40 * 3648081 * 2
def baseEnd_3648081 : Nat := 46252321469996212345933

theorem tailTrace_3648081 : CollatzResearch.WordTrace tailWord_3648081 prefixEnd_3648081 46252321469996212345933 := by
  unfold tailWord_3648081
  simp only [CollatzResearch.WordTrace]
  refine ⟨133056445096633054476952097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88704296731088702984634731 133056445096633054476952097)
  ·
    refine ⟨99792333822474790857714073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133056445096633054476952097 99792333822474790857714073)
    ·
      refine ⟨74844250366856093143285555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99792333822474790857714073 74844250366856093143285555)
      ·
        refine ⟨112266375550284139714928333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74844250366856093143285555 112266375550284139714928333)
        ·
          refine ⟨42099890831356552393098125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112266375550284139714928333 42099890831356552393098125)
          ·
            refine ⟨15787459061758707147411797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42099890831356552393098125 15787459061758707147411797)
            ·
              refine ⟨46252321469996212345933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15787459061758707147411797 46252321469996212345933)
              ·
                rfl

theorem cell22_3648081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 10].length) (baseStart_3648081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648081 prefixEnd_3648081 := by exact prefixLift 3648081
  have htrace : WordTrace (prefixWord ++ tailWord_3648081) baseStart_3648081 baseEnd_3648081 := by
    simpa [prefixWord, tailWord_3648081, baseEnd_3648081] using wordTrace_append hprefix tailTrace_3648081
  have hstable : (prefixWord ++ tailWord_3648081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648081).length < 2 ^ (prefixWord ++ tailWord_3648081).sum := by decide
  have hdescent : baseEnd_3648081 < baseStart_3648081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648117 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3648117 : Nat := 118140960795 + 3648117 * 2 ^ 59
def prefixEnd_3648117 : Nat := 4983230072969 + 3 ^ 40 * 3648117 * 2
def baseEnd_3648117 : Nat := 1248825003225605639440081

theorem tailTrace_3648117 : CollatzResearch.WordTrace tailWord_3648117 prefixEnd_3648117 1248825003225605639440081 := by
  unfold tailWord_3648117
  simp only [CollatzResearch.WordTrace]
  refine ⟨133057758124502632625262605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88705172083001755083508403 133057758124502632625262605)
  ·
    refine ⟨49896659296688487234473477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133057758124502632625262605 49896659296688487234473477)
    ·
      refine ⟨9355623618129091356463777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49896659296688487234473477 9355623618129091356463777)
      ·
        refine ⟨7016717713596818517347833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9355623618129091356463777 7016717713596818517347833)
        ·
          refine ⟨5262538285197613888010875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7016717713596818517347833 5262538285197613888010875)
          ·
            refine ⟨7893807427796420832016313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262538285197613888010875 7893807427796420832016313)
            ·
              refine ⟨5920355570847315624012235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7893807427796420832016313 5920355570847315624012235)
              ·
                refine ⟨8880533356270973436018353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920355570847315624012235 8880533356270973436018353)
                ·
                  refine ⟨6660400017203230077013765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880533356270973436018353 6660400017203230077013765)
                  ·
                    refine ⟨1248825003225605639440081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660400017203230077013765 1248825003225605639440081)
                    ·
                      rfl

theorem cell22_3648117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3648117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648117 prefixEnd_3648117 := by exact prefixLift 3648117
  have htrace : WordTrace (prefixWord ++ tailWord_3648117) baseStart_3648117 baseEnd_3648117 := by
    simpa [prefixWord, tailWord_3648117, baseEnd_3648117] using wordTrace_append hprefix tailTrace_3648117
  have hstable : (prefixWord ++ tailWord_3648117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648117).length < 2 ^ (prefixWord ++ tailWord_3648117).sum := by decide
  have hdescent : baseEnd_3648117 < baseStart_3648117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648188 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_3648188 : Nat := 118140960795 + 3648188 * 2 ^ 59
def prefixEnd_3648188 : Nat := 4983230072969 + 3 ^ 40 * 3648188 * 2
def baseEnd_3648188 : Nat := 416283102658861706971621

theorem tailTrace_3648188 : CollatzResearch.WordTrace tailWord_3648188 prefixEnd_3648188 416283102658861706971621 := by
  unfold tailWord_3648188
  simp only [CollatzResearch.WordTrace]
  refine ⟨66530173853622705875548609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88706898471496941167398145 66530173853622705875548609)
  ·
    refine ⟨49897630390217029406661457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66530173853622705875548609 49897630390217029406661457)
    ·
      refine ⟨37423222792662772054996093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49897630390217029406661457 37423222792662772054996093)
      ·
        refine ⟨14033708547248539520623535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37423222792662772054996093 14033708547248539520623535)
        ·
          refine ⟨21050562820872809280935303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14033708547248539520623535 21050562820872809280935303)
          ·
            refine ⟨31575844231309213921402955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21050562820872809280935303 31575844231309213921402955)
            ·
              refine ⟨47363766346963820882104433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31575844231309213921402955 47363766346963820882104433)
              ·
                refine ⟨35522824760222865661578325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47363766346963820882104433 35522824760222865661578325)
                ·
                  refine ⟨416283102658861706971621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35522824760222865661578325 416283102658861706971621)
                  ·
                    rfl

theorem cell22_3648188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_3648188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648188 prefixEnd_3648188 := by exact prefixLift 3648188
  have htrace : WordTrace (prefixWord ++ tailWord_3648188) baseStart_3648188 baseEnd_3648188 := by
    simpa [prefixWord, tailWord_3648188, baseEnd_3648188] using wordTrace_append hprefix tailTrace_3648188
  have hstable : (prefixWord ++ tailWord_3648188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648188).length < 2 ^ (prefixWord ++ tailWord_3648188).sum := by decide
  have hdescent : baseEnd_3648188 < baseStart_3648188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648218 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_3648218 : Nat := 118140960795 + 3648218 * 2 ^ 59
def prefixEnd_3648218 : Nat := 4983230072969 + 3 ^ 40 * 3648218 * 2
def baseEnd_3648218 : Nat := 1248859577589675042664771

theorem tailTrace_3648218 : CollatzResearch.WordTrace tailWord_3648218 prefixEnd_3648218 1248859577589675042664771 := by
  unfold tailWord_3648218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265360474284181718672327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88707627931424484583126205 33265360474284181718672327)
  ·
    refine ⟨49898040711426272578008491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33265360474284181718672327 49898040711426272578008491)
    ·
      refine ⟨74847061067139408867012737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49898040711426272578008491 74847061067139408867012737)
      ·
        refine ⟨56135295800354556650259553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74847061067139408867012737 56135295800354556650259553)
        ·
          refine ⟨42101471850265917487694665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56135295800354556650259553 42101471850265917487694665)
          ·
            refine ⟨31576103887699438115770999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42101471850265917487694665 31576103887699438115770999)
            ·
              refine ⟨47364155831549157173656499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31576103887699438115770999 47364155831549157173656499)
              ·
                refine ⟨71046233747323735760484749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47364155831549157173656499 71046233747323735760484749)
                ·
                  refine ⟨26642337655246400910181781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71046233747323735760484749 26642337655246400910181781)
                  ·
                    refine ⟨1248859577589675042664771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26642337655246400910181781 1248859577589675042664771)
                    ·
                      rfl

theorem cell22_3648218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_3648218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648218 prefixEnd_3648218 := by exact prefixLift 3648218
  have htrace : WordTrace (prefixWord ++ tailWord_3648218) baseStart_3648218 baseEnd_3648218 := by
    simpa [prefixWord, tailWord_3648218, baseEnd_3648218] using wordTrace_append hprefix tailTrace_3648218
  have hstable : (prefixWord ++ tailWord_3648218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648218).length < 2 ^ (prefixWord ++ tailWord_3648218).sum := by decide
  have hdescent : baseEnd_3648218 < baseStart_3648218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648357 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 4]
def baseStart_3648357 : Nat := 118140960795 + 3648357 * 2 ^ 59
def prefixEnd_3648357 : Nat := 4983230072969 + 3 ^ 40 * 3648357 * 2
def baseEnd_3648357 : Nat := 416302386710108337813115

theorem tailTrace_3648357 : CollatzResearch.WordTrace tailWord_3648357 prefixEnd_3648357 416302386710108337813115 := by
  unfold tailWord_3648357
  simp only [CollatzResearch.WordTrace]
  refine ⟨133066511643633153613999325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88711007762422102409332883 133066511643633153613999325)
  ·
    refine ⟨49899941866362432605249747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133066511643633153613999325 49899941866362432605249747)
    ·
      refine ⟨74849912799543648907874621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49899941866362432605249747 74849912799543648907874621)
      ·
        refine ⟨28068717299828868340452983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74849912799543648907874621 28068717299828868340452983)
        ·
          refine ⟨42103075949743302510679475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28068717299828868340452983 42103075949743302510679475)
          ·
            refine ⟨63154613924614953766019213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42103075949743302510679475 63154613924614953766019213)
            ·
              refine ⟨23682980221730607662257205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63154613924614953766019213 23682980221730607662257205)
              ·
                refine ⟨2220279395787244468336613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23682980221730607662257205 2220279395787244468336613)
                ·
                  refine ⟨416302386710108337813115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220279395787244468336613 416302386710108337813115)
                  ·
                    rfl

theorem cell22_3648357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_3648357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648357 prefixEnd_3648357 := by exact prefixLift 3648357
  have htrace : WordTrace (prefixWord ++ tailWord_3648357) baseStart_3648357 baseEnd_3648357 := by
    simpa [prefixWord, tailWord_3648357, baseEnd_3648357] using wordTrace_append hprefix tailTrace_3648357
  have hstable : (prefixWord ++ tailWord_3648357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648357).length < 2 ^ (prefixWord ++ tailWord_3648357).sum := by decide
  have hdescent : baseEnd_3648357 < baseStart_3648357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648359 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3648359 : Nat := 118140960795 + 3648359 * 2 ^ 59
def prefixEnd_3648359 : Nat := 4983230072969 + 3 ^ 40 * 3648359 * 2
def baseEnd_3648359 : Nat := 1248907844771197674889339

theorem tailTrace_3648359 : CollatzResearch.WordTrace tailWord_3648359 prefixEnd_3648359 1248907844771197674889339 := by
  unfold tailWord_3648359
  simp only [CollatzResearch.WordTrace]
  refine ⟨133066584589625907955572131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88711056393083938637048087 133066584589625907955572131)
  ·
    refine ⟨199599876884438861933358197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133066584589625907955572131 199599876884438861933358197)
    ·
      refine ⟨18712488457916143306252331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199599876884438861933358197 18712488457916143306252331)
      ·
        refine ⟨28068732686874214959378497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18712488457916143306252331 28068732686874214959378497)
        ·
          refine ⟨21051549515155661219533873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28068732686874214959378497 21051549515155661219533873)
          ·
            refine ⟨15788662136366745914650405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21051549515155661219533873 15788662136366745914650405)
            ·
              refine ⟨2960374150568764858996951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15788662136366745914650405 2960374150568764858996951)
              ·
                refine ⟨4440561225853147288495427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960374150568764858996951 4440561225853147288495427)
                ·
                  refine ⟨6660841838779720932743141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440561225853147288495427 6660841838779720932743141)
                  ·
                    refine ⟨1248907844771197674889339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660841838779720932743141 1248907844771197674889339)
                    ·
                      rfl

theorem cell22_3648359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3648359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648359 prefixEnd_3648359 := by exact prefixLift 3648359
  have htrace : WordTrace (prefixWord ++ tailWord_3648359) baseStart_3648359 baseEnd_3648359 := by
    simpa [prefixWord, tailWord_3648359, baseEnd_3648359] using wordTrace_append hprefix tailTrace_3648359
  have hstable : (prefixWord ++ tailWord_3648359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648359).length < 2 ^ (prefixWord ++ tailWord_3648359).sum := by decide
  have hdescent : baseEnd_3648359 < baseStart_3648359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648374 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3648374 : Nat := 118140960795 + 3648374 * 2 ^ 59
def prefixEnd_3648374 : Nat := 4983230072969 + 3 ^ 40 * 3648374 * 2
def baseEnd_3648374 : Nat := 416304326525914211921431

theorem tailTrace_3648374 : CollatzResearch.WordTrace tailWord_3648374 prefixEnd_3648374 416304326525914211921431 := by
  unfold tailWord_3648374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316695730285722844835511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88711421123047710344912117 8316695730285722844835511)
  ·
    refine ⟨12475043595428584267253267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316695730285722844835511 12475043595428584267253267)
    ·
      refine ⟨18712565393142876400879901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12475043595428584267253267 18712565393142876400879901)
      ·
        refine ⟨7017212022428578650329963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18712565393142876400879901 7017212022428578650329963)
        ·
          refine ⟨10525818033642867975494945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017212022428578650329963 10525818033642867975494945)
          ·
            refine ⟨7894363525232150981621209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10525818033642867975494945 7894363525232150981621209)
            ·
              refine ⟨5920772643924113236215907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7894363525232150981621209 5920772643924113236215907)
              ·
                refine ⟨8881158965886169854323861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920772643924113236215907 8881158965886169854323861)
                ·
                  refine ⟨416304326525914211921431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8881158965886169854323861 416304326525914211921431)
                  ·
                    rfl

theorem cell22_3648374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3648374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648374 prefixEnd_3648374 := by exact prefixLift 3648374
  have htrace : WordTrace (prefixWord ++ tailWord_3648374) baseStart_3648374 baseEnd_3648374 := by
    simpa [prefixWord, tailWord_3648374, baseEnd_3648374] using wordTrace_append hprefix tailTrace_3648374
  have hstable : (prefixWord ++ tailWord_3648374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648374).length < 2 ^ (prefixWord ++ tailWord_3648374).sum := by decide
  have hdescent : baseEnd_3648374 < baseStart_3648374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648507 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 6, 3]
def baseStart_3648507 : Nat := 118140960795 + 3648507 * 2 ^ 59
def prefixEnd_3648507 : Nat := 4983230072969 + 3 ^ 40 * 3648507 * 2
def baseEnd_3648507 : Nat := 1248958508195774622188885

theorem tailTrace_3648507 : CollatzResearch.WordTrace tailWord_3648507 prefixEnd_3648507 1248958508195774622188885 := by
  unfold tailWord_3648507
  simp only [CollatzResearch.WordTrace]
  refine ⟨133071982593089729231959775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88714655062059819487973183 133071982593089729231959775)
  ·
    refine ⟨199607973889634593847939663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133071982593089729231959775 199607973889634593847939663)
    ·
      refine ⟨299411960834451890771909495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199607973889634593847939663 299411960834451890771909495)
      ·
        refine ⟨449117941251677836157864243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299411960834451890771909495 449117941251677836157864243)
        ·
          refine ⟨673676911877516754236796365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449117941251677836157864243 673676911877516754236796365)
          ·
            refine ⟨252628841954068782838798637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673676911877516754236796365 252628841954068782838798637)
            ·
              refine ⟨94735815732775793564549489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252628841954068782838798637 94735815732775793564549489)
              ·
                refine ⟨71051861799581845173412117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94735815732775793564549489 71051861799581845173412117)
                ·
                  refine ⟨3330556021855398992503693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71051861799581845173412117 3330556021855398992503693)
                  ·
                    refine ⟨1248958508195774622188885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330556021855398992503693 1248958508195774622188885)
                    ·
                      rfl

theorem cell22_3648507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 3].length) (baseStart_3648507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648507 prefixEnd_3648507 := by exact prefixLift 3648507
  have htrace : WordTrace (prefixWord ++ tailWord_3648507) baseStart_3648507 baseEnd_3648507 := by
    simpa [prefixWord, tailWord_3648507, baseEnd_3648507] using wordTrace_append hprefix tailTrace_3648507
  have hstable : (prefixWord ++ tailWord_3648507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648507).length < 2 ^ (prefixWord ++ tailWord_3648507).sum := by decide
  have hdescent : baseEnd_3648507 < baseStart_3648507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648526 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_3648526 : Nat := 118140960795 + 3648526 * 2 ^ 59
def prefixEnd_3648526 : Nat := 4983230072969 + 3 ^ 40 * 3648526 * 2
def baseEnd_3648526 : Nat := 416321670761354968654609

theorem tailTrace_3648526 : CollatzResearch.WordTrace tailWord_3648526 prefixEnd_3648526 416321670761354968654609 := by
  unfold tailWord_3648526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634084447502611934612679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88715117053347263651267621 16634084447502611934612679)
  ·
    refine ⟨24951126671253917901919019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16634084447502611934612679 24951126671253917901919019)
    ·
      refine ⟨37426690006880876852878529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24951126671253917901919019 37426690006880876852878529)
      ·
        refine ⟨28070017505160657639658897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37426690006880876852878529 28070017505160657639658897)
        ·
          refine ⟨21052513128870493229744173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28070017505160657639658897 21052513128870493229744173)
          ·
            refine ⟨7894692423326434961154065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21052513128870493229744173 7894692423326434961154065)
            ·
              refine ⟨5921019317494826220865549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7894692423326434961154065 5921019317494826220865549)
              ·
                refine ⟨2220382244060559832824581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5921019317494826220865549 2220382244060559832824581)
                ·
                  refine ⟨416321670761354968654609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220382244060559832824581 416321670761354968654609)
                  ·
                    rfl

theorem cell22_3648526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_3648526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648526 prefixEnd_3648526 := by exact prefixLift 3648526
  have htrace : WordTrace (prefixWord ++ tailWord_3648526) baseStart_3648526 baseEnd_3648526 := by
    simpa [prefixWord, tailWord_3648526, baseEnd_3648526] using wordTrace_append hprefix tailTrace_3648526
  have hstable : (prefixWord ++ tailWord_3648526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648526).length < 2 ^ (prefixWord ++ tailWord_3648526).sum := by decide
  have hdescent : baseEnd_3648526 < baseStart_3648526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648541 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_3648541 : Nat := 118140960795 + 3648541 * 2 ^ 59
def prefixEnd_3648541 : Nat := 4983230072969 + 3 ^ 40 * 3648541 * 2
def baseEnd_3648541 : Nat := 1248970147090609866838781

theorem tailTrace_3648541 : CollatzResearch.WordTrace tailWord_3648541 prefixEnd_3648541 1248970147090609866838781 := by
  unfold tailWord_3648541
  simp only [CollatzResearch.WordTrace]
  refine ⟨133073222674966553038697477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88715481783311035359131651 133073222674966553038697477)
  ·
    refine ⟨24951229251556228694755777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133073222674966553038697477 24951229251556228694755777)
    ·
      refine ⟨18713421938667171521066833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24951229251556228694755777 18713421938667171521066833)
      ·
        refine ⟨14035066454000378640800125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18713421938667171521066833 14035066454000378640800125)
        ·
          refine ⟨5263149920250141990300047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14035066454000378640800125 5263149920250141990300047)
          ·
            refine ⟨7894724880375212985450071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263149920250141990300047 7894724880375212985450071)
            ·
              refine ⟨11842087320562819478175107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894724880375212985450071 11842087320562819478175107)
              ·
                refine ⟨17763130980844229217262661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11842087320562819478175107 17763130980844229217262661)
                ·
                  refine ⟨3330587058908292978236749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17763130980844229217262661 3330587058908292978236749)
                  ·
                    refine ⟨1248970147090609866838781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330587058908292978236749 1248970147090609866838781)
                    ·
                      rfl

theorem cell22_3648541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_3648541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648541 prefixEnd_3648541 := by exact prefixLift 3648541
  have htrace : WordTrace (prefixWord ++ tailWord_3648541) baseStart_3648541 baseEnd_3648541 := by
    simpa [prefixWord, tailWord_3648541, baseEnd_3648541] using wordTrace_append hprefix tailTrace_3648541
  have hstable : (prefixWord ++ tailWord_3648541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648541).length < 2 ^ (prefixWord ++ tailWord_3648541).sum := by decide
  have hdescent : baseEnd_3648541 < baseStart_3648541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648558 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3648558 : Nat := 118140960795 + 3648558 * 2 ^ 59
def prefixEnd_3648558 : Nat := 4983230072969 + 3 ^ 40 * 3648558 * 2
def baseEnd_3648558 : Nat := 1248975966538027489163729

theorem tailTrace_3648558 : CollatzResearch.WordTrace tailWord_3648558 prefixEnd_3648558 1248975966538027489163729 := by
  unfold tailWord_3648558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634230339488120617758291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88715895143936643294710885 16634230339488120617758291)
  ·
    refine ⟨24951345509232180926637437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16634230339488120617758291 24951345509232180926637437)
    ·
      refine ⟨9356754565962067847489039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24951345509232180926637437 9356754565962067847489039)
      ·
        refine ⟨14035131848943101771233559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9356754565962067847489039 14035131848943101771233559)
        ·
          refine ⟨21052697773414652656850339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14035131848943101771233559 21052697773414652656850339)
          ·
            refine ⟨31579046660121978985275509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21052697773414652656850339 31579046660121978985275509)
            ·
              refine ⟨2960535624386435529869579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31579046660121978985275509 2960535624386435529869579)
              ·
                refine ⟨4440803436579653294804369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960535624386435529869579 4440803436579653294804369)
                ·
                  refine ⟨3330602577434739971103277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4440803436579653294804369 3330602577434739971103277)
                  ·
                    refine ⟨1248975966538027489163729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330602577434739971103277 1248975966538027489163729)
                    ·
                      rfl

theorem cell22_3648558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3648558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648558 prefixEnd_3648558 := by exact prefixLift 3648558
  have htrace : WordTrace (prefixWord ++ tailWord_3648558) baseStart_3648558 baseEnd_3648558 := by
    simpa [prefixWord, tailWord_3648558, baseEnd_3648558] using wordTrace_append hprefix tailTrace_3648558
  have hstable : (prefixWord ++ tailWord_3648558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648558).length < 2 ^ (prefixWord ++ tailWord_3648558).sum := by decide
  have hdescent : baseEnd_3648558 < baseStart_3648558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648612 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3648612 : Nat := 118140960795 + 3648612 * 2 ^ 59
def prefixEnd_3648612 : Nat := 4983230072969 + 3 ^ 40 * 3648612 * 2
def baseEnd_3648612 : Nat := 1248994451841589348313563

theorem tailTrace_3648612 : CollatzResearch.WordTrace tailWord_3648612 prefixEnd_3648612 1248994451841589348313563 := by
  unfold tailWord_3648612
  simp only [CollatzResearch.WordTrace]
  refine ⟨66537906128854666082266045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88717208171806221443021393 66537906128854666082266045)
  ·
    refine ⟨24951714798320499780849767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66537906128854666082266045 24951714798320499780849767)
    ·
      refine ⟨37427572197480749671274651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24951714798320499780849767 37427572197480749671274651)
      ·
        refine ⟨56141358296221124506911977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37427572197480749671274651 56141358296221124506911977)
        ·
          refine ⟨42106018722165843380183983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56141358296221124506911977 42106018722165843380183983)
          ·
            refine ⟨63159028083248765070275975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42106018722165843380183983 63159028083248765070275975)
            ·
              refine ⟨94738542124873147605413963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63159028083248765070275975 94738542124873147605413963)
              ·
                refine ⟨142107813187309721408120945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94738542124873147605413963 142107813187309721408120945)
                ·
                  refine ⟨106580859890482291056090709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142107813187309721408120945 106580859890482291056090709)
                  ·
                    refine ⟨1248994451841589348313563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106580859890482291056090709 1248994451841589348313563)
                    ·
                      rfl

theorem cell22_3648612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3648612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648612 prefixEnd_3648612 := by exact prefixLift 3648612
  have htrace : WordTrace (prefixWord ++ tailWord_3648612) baseStart_3648612 baseEnd_3648612 := by
    simpa [prefixWord, tailWord_3648612, baseEnd_3648612] using wordTrace_append hprefix tailTrace_3648612
  have hstable : (prefixWord ++ tailWord_3648612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648612).length < 2 ^ (prefixWord ++ tailWord_3648612).sum := by decide
  have hdescent : baseEnd_3648612 < baseStart_3648612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648659 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 4, 3]
def baseStart_3648659 : Nat := 118140960795 + 3648659 * 2 ^ 59
def prefixEnd_3648659 : Nat := 4983230072969 + 3 ^ 40 * 3648659 * 2
def baseEnd_3648659 : Nat := 1249010540902096892388419

theorem tailTrace_3648659 : CollatzResearch.WordTrace tailWord_3648659 prefixEnd_3648659 1249010540902096892388419 := by
  unfold tailWord_3648659
  simp only [CollatzResearch.WordTrace]
  refine ⟨133077526488539059191493031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88718350992359372794328687 133077526488539059191493031)
  ·
    refine ⟨199616289732808588787239547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133077526488539059191493031 199616289732808588787239547)
    ·
      refine ⟨299424434599212883180859321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199616289732808588787239547 299424434599212883180859321)
      ·
        refine ⟨224568325949409662385644491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299424434599212883180859321 224568325949409662385644491)
        ·
          refine ⟨336852488924114493578466737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224568325949409662385644491 336852488924114493578466737)
          ·
            refine ⟨252639366693085870183850053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336852488924114493578466737 252639366693085870183850053)
            ·
              refine ⟨47369881254953600659471885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252639366693085870183850053 47369881254953600659471885)
              ·
                refine ⟨17763705470607600247301957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47369881254953600659471885 17763705470607600247301957)
                ·
                  refine ⟨3330694775738925046369117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17763705470607600247301957 3330694775738925046369117)
                  ·
                    refine ⟨1249010540902096892388419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330694775738925046369117 1249010540902096892388419)
                    ·
                      rfl

theorem cell22_3648659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 3].length) (baseStart_3648659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648659 prefixEnd_3648659 := by exact prefixLift 3648659
  have htrace : WordTrace (prefixWord ++ tailWord_3648659) baseStart_3648659 baseEnd_3648659 := by
    simpa [prefixWord, tailWord_3648659, baseEnd_3648659] using wordTrace_append hprefix tailTrace_3648659
  have hstable : (prefixWord ++ tailWord_3648659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648659).length < 2 ^ (prefixWord ++ tailWord_3648659).sum := by decide
  have hdescent : baseEnd_3648659 < baseStart_3648659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648676 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_3648676 : Nat := 118140960795 + 3648676 * 2 ^ 59
def prefixEnd_3648676 : Nat := 4983230072969 + 3 ^ 40 * 3648676 * 2
def baseEnd_3648676 : Nat := 1249016360349514514713367

theorem tailTrace_3648676 : CollatzResearch.WordTrace tailWord_3648676 prefixEnd_3648676 1249016360349514514713367 := by
  unfold tailWord_3648676
  simp only [CollatzResearch.WordTrace]
  refine ⟨66539073264738735547430941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88718764352984980729907921 66539073264738735547430941)
  ·
    refine ⟨24952152474277025830286603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66539073264738735547430941 24952152474277025830286603)
    ·
      refine ⟨37428228711415538745429905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24952152474277025830286603 37428228711415538745429905)
      ·
        refine ⟨28071171533561654059072429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37428228711415538745429905 28071171533561654059072429)
        ·
          refine ⟨10526689325085620272152161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28071171533561654059072429 10526689325085620272152161)
          ·
            refine ⟨7895016993814215204114121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10526689325085620272152161 7895016993814215204114121)
            ·
              refine ⟨5921262745360661403085591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895016993814215204114121 5921262745360661403085591)
              ·
                refine ⟨8881894118040992104628387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921262745360661403085591 8881894118040992104628387)
                ·
                  refine ⟨13322841177061488156942581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8881894118040992104628387 13322841177061488156942581)
                  ·
                    refine ⟨1249016360349514514713367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13322841177061488156942581 1249016360349514514713367)
                    ·
                      rfl

theorem cell22_3648676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_3648676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648676 prefixEnd_3648676 := by exact prefixLift 3648676
  have htrace : WordTrace (prefixWord ++ tailWord_3648676) baseStart_3648676 baseEnd_3648676 := by
    simpa [prefixWord, tailWord_3648676, baseEnd_3648676] using wordTrace_append hprefix tailTrace_3648676
  have hstable : (prefixWord ++ tailWord_3648676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648676).length < 2 ^ (prefixWord ++ tailWord_3648676).sum := by decide
  have hdescent : baseEnd_3648676 < baseStart_3648676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648755 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 1, 3]
def baseStart_3648755 : Nat := 118140960795 + 3648755 * 2 ^ 59
def prefixEnd_3648755 : Nat := 4983230072969 + 3 ^ 40 * 3648755 * 2
def baseEnd_3648755 : Nat := 1249043403663984641988125

theorem tailTrace_3648755 : CollatzResearch.WordTrace tailWord_3648755 prefixEnd_3648755 1249043403663984641988125 := by
  unfold tailWord_3648755
  simp only [CollatzResearch.WordTrace]
  refine ⟨133081027896191267586987719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88720685264127511724658479 133081027896191267586987719)
  ·
    refine ⟨199621541844286901380481579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133081027896191267586987719 199621541844286901380481579)
    ·
      refine ⟨299432312766430352070722369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199621541844286901380481579 299432312766430352070722369)
      ·
        refine ⟨224574234574822764053041777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299432312766430352070722369 224574234574822764053041777)
        ·
          refine ⟨168430675931117073039781333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224574234574822764053041777 168430675931117073039781333)
          ·
            refine ⟨3947593967135556399369875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168430675931117073039781333 3947593967135556399369875)
            ·
              refine ⟨5921390950703334599054813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947593967135556399369875 5921390950703334599054813)
              ·
                refine ⟨2220521606513750474645555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5921390950703334599054813 2220521606513750474645555)
                ·
                  refine ⟨3330782409770625711968333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220521606513750474645555 3330782409770625711968333)
                  ·
                    refine ⟨1249043403663984641988125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330782409770625711968333 1249043403663984641988125)
                    ·
                      rfl

theorem cell22_3648755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 3].length) (baseStart_3648755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648755 prefixEnd_3648755 := by exact prefixLift 3648755
  have htrace : WordTrace (prefixWord ++ tailWord_3648755) baseStart_3648755 baseEnd_3648755 := by
    simpa [prefixWord, tailWord_3648755, baseEnd_3648755] using wordTrace_append hprefix tailTrace_3648755
  have hstable : (prefixWord ++ tailWord_3648755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648755).length < 2 ^ (prefixWord ++ tailWord_3648755).sum := by decide
  have hdescent : baseEnd_3648755 < baseStart_3648755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648772 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3648772 : Nat := 118140960795 + 3648772 * 2 ^ 59
def prefixEnd_3648772 : Nat := 4983230072969 + 3 ^ 40 * 3648772 * 2
def baseEnd_3648772 : Nat := 1249049223111402264313073

theorem tailTrace_3648772 : CollatzResearch.WordTrace tailWord_3648772 prefixEnd_3648772 1249049223111402264313073 := by
  unfold tailWord_3648772
  simp only [CollatzResearch.WordTrace]
  refine ⟨66540823968564839745178285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88721098624753119660237713 66540823968564839745178285)
  ·
    refine ⟨24952808988211814904441857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66540823968564839745178285 24952808988211814904441857)
    ·
      refine ⟨18714606741158861178331393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24952808988211814904441857 18714606741158861178331393)
      ·
        refine ⟨14035955055869145883748545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18714606741158861178331393 14035955055869145883748545)
        ·
          refine ⟨10526966291901859412811409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14035955055869145883748545 10526966291901859412811409)
          ·
            refine ⟨7895224718926394559608557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10526966291901859412811409 7895224718926394559608557)
            ·
              refine ⟨2960709269597397959853209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7895224718926394559608557 2960709269597397959853209)
              ·
                refine ⟨2220531952198048469889907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960709269597397959853209 2220531952198048469889907)
                ·
                  refine ⟨3330797928297072704834861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220531952198048469889907 3330797928297072704834861)
                  ·
                    refine ⟨1249049223111402264313073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330797928297072704834861 1249049223111402264313073)
                    ·
                      rfl

theorem cell22_3648772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3648772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648772 prefixEnd_3648772 := by exact prefixLift 3648772
  have htrace : WordTrace (prefixWord ++ tailWord_3648772) baseStart_3648772 baseEnd_3648772 := by
    simpa [prefixWord, tailWord_3648772, baseEnd_3648772] using wordTrace_append hprefix tailTrace_3648772
  have hstable : (prefixWord ++ tailWord_3648772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648772).length < 2 ^ (prefixWord ++ tailWord_3648772).sum := by decide
  have hdescent : baseEnd_3648772 < baseStart_3648772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648826 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_3648826 : Nat := 118140960795 + 3648826 * 2 ^ 59
def prefixEnd_3648826 : Nat := 4983230072969 + 3 ^ 40 * 3648826 * 2
def baseEnd_3648826 : Nat := 1249067708414964123462907

theorem tailTrace_3648826 : CollatzResearch.WordTrace tailWord_3648826 prefixEnd_3648826 1249067708414964123462907 := by
  unfold tailWord_3648826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270904369733511678205583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88722411652622697808548221 33270904369733511678205583)
  ·
    refine ⟨49906356554600267517308375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33270904369733511678205583 49906356554600267517308375)
    ·
      refine ⟨74859534831900401275962563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49906356554600267517308375 74859534831900401275962563)
      ·
        refine ⟨112289302247850601913943845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74859534831900401275962563 112289302247850601913943845)
        ·
          refine ⟨21054244171471987858864471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112289302247850601913943845 21054244171471987858864471)
          ·
            refine ⟨31581366257207981788296707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21054244171471987858864471 31581366257207981788296707)
            ·
              refine ⟨47372049385811972682445061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31581366257207981788296707 47372049385811972682445061)
              ·
                refine ⟨8882259259839744877958449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47372049385811972682445061 8882259259839744877958449)
                ·
                  refine ⟨6661694444879808658468837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882259259839744877958449 6661694444879808658468837)
                  ·
                    refine ⟨1249067708414964123462907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661694444879808658468837 1249067708414964123462907)
                    ·
                      rfl

theorem cell22_3648826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_3648826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648826 prefixEnd_3648826 := by exact prefixLift 3648826
  have htrace : WordTrace (prefixWord ++ tailWord_3648826) baseStart_3648826 baseEnd_3648826 := by
    simpa [prefixWord, tailWord_3648826, baseEnd_3648826] using wordTrace_append hprefix tailTrace_3648826
  have hstable : (prefixWord ++ tailWord_3648826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648826).length < 2 ^ (prefixWord ++ tailWord_3648826).sum := by decide
  have hdescent : baseEnd_3648826 < baseStart_3648826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648828 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_3648828 : Nat := 118140960795 + 3648828 * 2 ^ 59
def prefixEnd_3648828 : Nat := 4983230072969 + 3 ^ 40 * 3648828 * 2
def baseEnd_3648828 : Nat := 1249068393055836784912901

theorem tailTrace_3648828 : CollatzResearch.WordTrace tailWord_3648828 prefixEnd_3648828 1249068393055836784912901 := by
  unfold tailWord_3648828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66541845212463400527197569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88722460283284534036263425 66541845212463400527197569)
  ·
    refine ⟨49906383909347550395398177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66541845212463400527197569 49906383909347550395398177)
    ·
      refine ⟨37429787932010662796548633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49906383909347550395398177 37429787932010662796548633)
      ·
        refine ⟨28072340949007997097411475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37429787932010662796548633 28072340949007997097411475)
        ·
          refine ⟨42108511423511995646117213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28072340949007997097411475 42108511423511995646117213)
          ·
            refine ⟨15790691783816998367293955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42108511423511995646117213 15790691783816998367293955)
            ·
              refine ⟨23686037675725497550940933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15790691783816998367293955 23686037675725497550940933)
              ·
                refine ⟨4441132064198530790801425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23686037675725497550940933 4441132064198530790801425)
                ·
                  refine ⟨3330849048148898093101069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441132064198530790801425 3330849048148898093101069)
                  ·
                    refine ⟨1249068393055836784912901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330849048148898093101069 1249068393055836784912901)
                    ·
                      rfl

theorem cell22_3648828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_3648828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648828 prefixEnd_3648828 := by exact prefixLift 3648828
  have htrace : WordTrace (prefixWord ++ tailWord_3648828) baseStart_3648828 baseEnd_3648828 := by
    simpa [prefixWord, tailWord_3648828, baseEnd_3648828] using wordTrace_append hprefix tailTrace_3648828
  have hstable : (prefixWord ++ tailWord_3648828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648828).length < 2 ^ (prefixWord ++ tailWord_3648828).sum := by decide
  have hdescent : baseEnd_3648828 < baseStart_3648828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648901 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3648901 : Nat := 118140960795 + 3648901 * 2 ^ 59
def prefixEnd_3648901 : Nat := 4983230072969 + 3 ^ 40 * 3648901 * 2
def baseEnd_3648901 : Nat := 1249093382447688927837677

theorem tailTrace_3648901 : CollatzResearch.WordTrace tailWord_3648901 prefixEnd_3648901 1249093382447688927837677 := by
  unfold tailWord_3648901
  simp only [CollatzResearch.WordTrace]
  refine ⟨133086352953662334521802557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88724235302441556347868371 133086352953662334521802557)
  ·
    refine ⟨49907382357623375445675959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133086352953662334521802557 49907382357623375445675959)
    ·
      refine ⟨74861073536435063168513939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49907382357623375445675959 74861073536435063168513939)
      ·
        refine ⟨112291610304652594752770909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74861073536435063168513939 112291610304652594752770909)
        ·
          refine ⟨42109353864244723032289091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112291610304652594752770909 42109353864244723032289091)
          ·
            refine ⟨63164030796367084548433637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42109353864244723032289091 63164030796367084548433637)
            ·
              refine ⟨11843255774318828352831307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63164030796367084548433637 11843255774318828352831307)
              ·
                refine ⟨17764883661478242529246961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11843255774318828352831307 17764883661478242529246961)
                ·
                  refine ⟨13323662746108681896935221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17764883661478242529246961 13323662746108681896935221)
                  ·
                    refine ⟨1249093382447688927837677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13323662746108681896935221 1249093382447688927837677)
                    ·
                      rfl

theorem cell22_3648901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3648901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648901 prefixEnd_3648901 := by exact prefixLift 3648901
  have htrace : WordTrace (prefixWord ++ tailWord_3648901) baseStart_3648901 baseEnd_3648901 := by
    simpa [prefixWord, tailWord_3648901, baseEnd_3648901] using wordTrace_append hprefix tailTrace_3648901
  have hstable : (prefixWord ++ tailWord_3648901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648901).length < 2 ^ (prefixWord ++ tailWord_3648901).sum := by decide
  have hdescent : baseEnd_3648901 < baseStart_3648901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648946 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3648946 : Nat := 118140960795 + 3648946 * 2 ^ 59
def prefixEnd_3648946 : Nat := 4983230072969 + 3 ^ 40 * 3648946 * 2
def baseEnd_3648946 : Nat := 1249108786867323810462539

theorem tailTrace_3648946 : CollatzResearch.WordTrace tailWord_3648946 prefixEnd_3648946 1249108786867323810462539 := by
  unfold tailWord_3648946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271998559624826801797673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88725329492332871471460461 33271998559624826801797673)
  ·
    refine ⟨24953998919718620101348255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33271998559624826801797673 24953998919718620101348255)
    ·
      refine ⟨37430998379577930152022383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24953998919718620101348255 37430998379577930152022383)
      ·
        refine ⟨56146497569366895228033575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37430998379577930152022383 56146497569366895228033575)
        ·
          refine ⟨84219746354050342842050363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56146497569366895228033575 84219746354050342842050363)
          ·
            refine ⟨126329619531075514263075545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84219746354050342842050363 126329619531075514263075545)
            ·
              refine ⟨94747214648306635697306659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126329619531075514263075545 94747214648306635697306659)
              ·
                refine ⟨142120821972459953545959989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94747214648306635697306659 142120821972459953545959989)
                ·
                  refine ⟨13323827059918120644933749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142120821972459953545959989 13323827059918120644933749)
                  ·
                    refine ⟨1249108786867323810462539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13323827059918120644933749 1249108786867323810462539)
                    ·
                      rfl

theorem cell22_3648946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3648946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648946 prefixEnd_3648946 := by exact prefixLift 3648946
  have htrace : WordTrace (prefixWord ++ tailWord_3648946) baseStart_3648946 baseEnd_3648946 := by
    simpa [prefixWord, tailWord_3648946, baseEnd_3648946] using wordTrace_append hprefix tailTrace_3648946
  have hstable : (prefixWord ++ tailWord_3648946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648946).length < 2 ^ (prefixWord ++ tailWord_3648946).sum := by decide
  have hdescent : baseEnd_3648946 < baseStart_3648946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648980 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3648980 : Nat := 118140960795 + 3648980 * 2 ^ 59
def prefixEnd_3648980 : Nat := 4983230072969 + 3 ^ 40 * 3648980 * 2
def baseEnd_3648980 : Nat := 1249120425762159055112435

theorem tailTrace_3648980 : CollatzResearch.WordTrace tailWord_3648980 prefixEnd_3648980 1249120425762159055112435 := by
  unfold tailWord_3648980
  simp only [CollatzResearch.WordTrace]
  refine ⟨66544617160188065506964197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88726156213584087342618929 66544617160188065506964197)
  ·
    refine ⟨12477115717535262282555787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66544617160188065506964197 12477115717535262282555787)
    ·
      refine ⟨18715673576302893423833681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12477115717535262282555787 18715673576302893423833681)
      ·
        refine ⟨14036755182227170067875261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18715673576302893423833681 14036755182227170067875261)
        ·
          refine ⟨5263783193335188775453223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14036755182227170067875261 5263783193335188775453223)
          ·
            refine ⟨7895674790002783163179835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263783193335188775453223 7895674790002783163179835)
            ·
              refine ⟨11843512185004174744769753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895674790002783163179835 11843512185004174744769753)
              ·
                refine ⟨8882634138753131058577315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11843512185004174744769753 8882634138753131058577315)
                ·
                  refine ⟨13323951208129696587865973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8882634138753131058577315 13323951208129696587865973)
                  ·
                    refine ⟨1249120425762159055112435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13323951208129696587865973 1249120425762159055112435)
                    ·
                      rfl

theorem cell22_3648980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3648980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648980 prefixEnd_3648980 := by exact prefixLift 3648980
  have htrace : WordTrace (prefixWord ++ tailWord_3648980) baseStart_3648980 baseEnd_3648980 := by
    simpa [prefixWord, tailWord_3648980, baseEnd_3648980] using wordTrace_append hprefix tailTrace_3648980
  have hstable : (prefixWord ++ tailWord_3648980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648980).length < 2 ^ (prefixWord ++ tailWord_3648980).sum := by decide
  have hdescent : baseEnd_3648980 < baseStart_3648980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648997 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_3648997 : Nat := 118140960795 + 3648997 * 2 ^ 59
def prefixEnd_3648997 : Nat := 4983230072969 + 3 ^ 40 * 3648997 * 2
def baseEnd_3648997 : Nat := 1249126245209576677437383

theorem tailTrace_3648997 : CollatzResearch.WordTrace tailWord_3648997 prefixEnd_3648997 1249126245209576677437383 := by
  unfold tailWord_3648997
  simp only [CollatzResearch.WordTrace]
  refine ⟨133089854361314542917297245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88726569574209695278198163 133089854361314542917297245)
  ·
    refine ⟨49908695385492953593986467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133089854361314542917297245 49908695385492953593986467)
    ·
      refine ⟨74863043078239430390979701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49908695385492953593986467 74863043078239430390979701)
      ·
        refine ⟨7018410288584946599154347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74863043078239430390979701 7018410288584946599154347)
        ·
          refine ⟨10527615432877419898731521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018410288584946599154347 10527615432877419898731521)
          ·
            refine ⟨7895711574658064924048641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10527615432877419898731521 7895711574658064924048641)
            ·
              refine ⟨5921783680993548693036481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895711574658064924048641 5921783680993548693036481)
              ·
                refine ⟨4441337760745161519777361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5921783680993548693036481 4441337760745161519777361)
                ·
                  refine ⟨3331003320558871139833021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441337760745161519777361 3331003320558871139833021)
                  ·
                    refine ⟨1249126245209576677437383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331003320558871139833021 1249126245209576677437383)
                    ·
                      rfl

theorem cell22_3648997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_3648997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3648997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3648997 prefixEnd_3648997 := by exact prefixLift 3648997
  have htrace : WordTrace (prefixWord ++ tailWord_3648997) baseStart_3648997 baseEnd_3648997 := by
    simpa [prefixWord, tailWord_3648997, baseEnd_3648997] using wordTrace_append hprefix tailTrace_3648997
  have hstable : (prefixWord ++ tailWord_3648997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648997).length < 2 ^ (prefixWord ++ tailWord_3648997).sum := by decide
  have hdescent : baseEnd_3648997 < baseStart_3648997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649010 : List Nat := [3, 2, 1, 4, 1, 3, 1, 7]
def baseStart_3649010 : Nat := 118140960795 + 3649010 * 2 ^ 59
def prefixEnd_3649010 : Nat := 4983230072969 + 3 ^ 40 * 3649010 * 2
def baseEnd_3649010 : Nat := 138792299486138775206927

theorem tailTrace_3649010 : CollatzResearch.WordTrace tailWord_3649010 prefixEnd_3649010 138792299486138775206927 := by
  unfold tailWord_3649010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33272582127566861534380121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88726885673511630758346989 33272582127566861534380121)
  ·
    refine ⟨24954436595675146150785091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33272582127566861534380121 24954436595675146150785091)
    ·
      refine ⟨37431654893512719226177637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24954436595675146150785091 37431654893512719226177637)
      ·
        refine ⟨7018435292533634854908307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37431654893512719226177637 7018435292533634854908307)
        ·
          refine ⟨10527652938800452282362461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018435292533634854908307 10527652938800452282362461)
          ·
            refine ⟨3947869852050169605885923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10527652938800452282362461 3947869852050169605885923)
            ·
              refine ⟨5921804778075254408828885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947869852050169605885923 5921804778075254408828885)
              ·
                refine ⟨138792299486138775206927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5921804778075254408828885 138792299486138775206927)
                ·
                  rfl

theorem cell22_3649010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_3649010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649010 prefixEnd_3649010 := by exact prefixLift 3649010
  have htrace : WordTrace (prefixWord ++ tailWord_3649010) baseStart_3649010 baseEnd_3649010 := by
    simpa [prefixWord, tailWord_3649010, baseEnd_3649010] using wordTrace_append hprefix tailTrace_3649010
  have hstable : (prefixWord ++ tailWord_3649010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649010).length < 2 ^ (prefixWord ++ tailWord_3649010).sum := by decide
  have hdescent : baseEnd_3649010 < baseStart_3649010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649053 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3649053 : Nat := 118140960795 + 3649053 * 2 ^ 59
def prefixEnd_3649053 : Nat := 4983230072969 + 3 ^ 40 * 3649053 * 2
def baseEnd_3649053 : Nat := 1249145415154011198037211

theorem tailTrace_3649053 : CollatzResearch.WordTrace tailWord_3649053 prefixEnd_3649053 1249145415154011198037211 := by
  unfold tailWord_3649053
  simp only [CollatzResearch.WordTrace]
  refine ⟨133091896849111664481335813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88727931232741109654223875 133091896849111664481335813)
  ·
    refine ⟨24954730659208437090250465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133091896849111664481335813 24954730659208437090250465)
    ·
      refine ⟨18716047994406327817687849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24954730659208437090250465 18716047994406327817687849)
      ·
        refine ⟨14037035995804745863265887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18716047994406327817687849 14037035995804745863265887)
        ·
          refine ⟨21055553993707118794898831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037035995804745863265887 21055553993707118794898831)
          ·
            refine ⟨31583330990560678192348247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21055553993707118794898831 31583330990560678192348247)
            ·
              refine ⟨47374996485841017288522371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31583330990560678192348247 47374996485841017288522371)
              ·
                refine ⟨71062494728761525932783557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47374996485841017288522371 71062494728761525932783557)
                ·
                  refine ⟨13324217761642786112396917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71062494728761525932783557 13324217761642786112396917)
                  ·
                    refine ⟨1249145415154011198037211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13324217761642786112396917 1249145415154011198037211)
                    ·
                      rfl

theorem cell22_3649053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3649053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649053 prefixEnd_3649053 := by exact prefixLift 3649053
  have htrace : WordTrace (prefixWord ++ tailWord_3649053) baseStart_3649053 baseEnd_3649053 := by
    simpa [prefixWord, tailWord_3649053, baseEnd_3649053] using wordTrace_append hprefix tailTrace_3649053
  have hstable : (prefixWord ++ tailWord_3649053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649053).length < 2 ^ (prefixWord ++ tailWord_3649053).sum := by decide
  have hdescent : baseEnd_3649053 < baseStart_3649053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649070 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3649070 : Nat := 118140960795 + 3649070 * 2 ^ 59
def prefixEnd_3649070 : Nat := 4983230072969 + 3 ^ 40 * 3649070 * 2
def baseEnd_3649070 : Nat := 1249151234601428820362159

theorem tailTrace_3649070 : CollatzResearch.WordTrace tailWord_3649070 prefixEnd_3649070 1249151234601428820362159 := by
  unfold tailWord_3649070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16636564611256259548088083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88728344593366717589803109 16636564611256259548088083)
  ·
    refine ⟨24954846916884389322132125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16636564611256259548088083 24954846916884389322132125)
    ·
      refine ⟨9358067593831645995799547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24954846916884389322132125 9358067593831645995799547)
      ·
        refine ⟨14037101390747468993699321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9358067593831645995799547 14037101390747468993699321)
        ·
          refine ⟨10527826043060601745274491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14037101390747468993699321 10527826043060601745274491)
          ·
            refine ⟨15791739064590902617911737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10527826043060601745274491 15791739064590902617911737)
            ·
              refine ⟨11843804298443176963433803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15791739064590902617911737 11843804298443176963433803)
              ·
                refine ⟨17765706447664765445150705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11843804298443176963433803 17765706447664765445150705)
                ·
                  refine ⟨13324279835748574083863029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17765706447664765445150705 13324279835748574083863029)
                  ·
                    refine ⟨1249151234601428820362159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13324279835748574083863029 1249151234601428820362159)
                    ·
                      rfl

theorem cell22_3649070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3649070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649070 prefixEnd_3649070 := by exact prefixLift 3649070
  have htrace : WordTrace (prefixWord ++ tailWord_3649070) baseStart_3649070 baseEnd_3649070 := by
    simpa [prefixWord, tailWord_3649070, baseEnd_3649070] using wordTrace_append hprefix tailTrace_3649070
  have hstable : (prefixWord ++ tailWord_3649070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649070).length < 2 ^ (prefixWord ++ tailWord_3649070).sum := by decide
  have hdescent : baseEnd_3649070 < baseStart_3649070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649098 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3649098 : Nat := 118140960795 + 3649098 * 2 ^ 59
def prefixEnd_3649098 : Nat := 4983230072969 + 3 ^ 40 * 3649098 * 2
def baseEnd_3649098 : Nat := 1249160819573646080662073

theorem tailTrace_3649098 : CollatzResearch.WordTrace tailWord_3649098 prefixEnd_3649098 1249160819573646080662073 := by
  unfold tailWord_3649098
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273384533487159291680987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88729025422632424777815965 33273384533487159291680987)
  ·
    refine ⟨49910076800230738937521481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33273384533487159291680987 49910076800230738937521481)
    ·
      refine ⟨37432557600173054203141111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49910076800230738937521481 37432557600173054203141111)
      ·
        refine ⟨56148836400259581304711667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37432557600173054203141111 56148836400259581304711667)
        ·
          refine ⟨84223254600389371957067501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56148836400259581304711667 84223254600389371957067501)
          ·
            refine ⟨31583720475146014483900313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84223254600389371957067501 31583720475146014483900313)
            ·
              refine ⟨23687790356359510862925235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31583720475146014483900313 23687790356359510862925235)
              ·
                refine ⟨35531685534539266294387853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23687790356359510862925235 35531685534539266294387853)
                ·
                  refine ⟨13324382075452224860395445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35531685534539266294387853 13324382075452224860395445)
                  ·
                    refine ⟨1249160819573646080662073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13324382075452224860395445 1249160819573646080662073)
                    ·
                      rfl

theorem cell22_3649098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3649098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649098 prefixEnd_3649098 := by exact prefixLift 3649098
  have htrace : WordTrace (prefixWord ++ tailWord_3649098) baseStart_3649098 baseEnd_3649098 := by
    simpa [prefixWord, tailWord_3649098, baseEnd_3649098] using wordTrace_append hprefix tailTrace_3649098
  have hstable : (prefixWord ++ tailWord_3649098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649098).length < 2 ^ (prefixWord ++ tailWord_3649098).sum := by decide
  have hdescent : baseEnd_3649098 < baseStart_3649098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649110 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3649110 : Nat := 118140960795 + 3649110 * 2 ^ 59
def prefixEnd_3649110 : Nat := 4983230072969 + 3 ^ 40 * 3649110 * 2
def baseEnd_3649110 : Nat := 1249164927418882049362037

theorem tailTrace_3649110 : CollatzResearch.WordTrace tailWord_3649110 prefixEnd_3649110 1249164927418882049362037 := by
  unfold tailWord_3649110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318373488119072701010049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88729317206603442144107189 8318373488119072701010049)
  ·
    refine ⟨6238780116089304525757537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8318373488119072701010049 6238780116089304525757537)
    ·
      refine ⟨4679085087066978394318153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6238780116089304525757537 4679085087066978394318153)
      ·
        refine ⟨3509313815300233795738615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4679085087066978394318153 3509313815300233795738615)
        ·
          refine ⟨5263970722950350693607923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509313815300233795738615 5263970722950350693607923)
          ·
            refine ⟨7895956084425526040411885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263970722950350693607923 7895956084425526040411885)
            ·
              refine ⟨2960983531659572265154457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7895956084425526040411885 2960983531659572265154457)
              ·
                refine ⟨2220737648744679198865843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960983531659572265154457 2220737648744679198865843)
                ·
                  refine ⟨3331106473117018798298765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220737648744679198865843 3331106473117018798298765)
                  ·
                    refine ⟨1249164927418882049362037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331106473117018798298765 1249164927418882049362037)
                    ·
                      rfl

theorem cell22_3649110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3649110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649110 prefixEnd_3649110 := by exact prefixLift 3649110
  have htrace : WordTrace (prefixWord ++ tailWord_3649110) baseStart_3649110 baseEnd_3649110 := by
    simpa [prefixWord, tailWord_3649110, baseEnd_3649110] using wordTrace_append hprefix tailTrace_3649110
  have hstable : (prefixWord ++ tailWord_3649110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649110).length < 2 ^ (prefixWord ++ tailWord_3649110).sum := by decide
  have hdescent : baseEnd_3649110 < baseStart_3649110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649173 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3649173 : Nat := 118140960795 + 3649173 * 2 ^ 59
def prefixEnd_3649173 : Nat := 4983230072969 + 3 ^ 40 * 3649173 * 2
def baseEnd_3649173 : Nat := 416395497868790295012281

theorem tailTrace_3649173 : CollatzResearch.WordTrace tailWord_3649173 prefixEnd_3649173 416395497868790295012281 := by
  unfold tailWord_3649173
  simp only [CollatzResearch.WordTrace]
  refine ⟨133096273608676924975704173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88730849072451283317136115 133096273608676924975704173)
  ·
    refine ⟨49911102603253846865889065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133096273608676924975704173 49911102603253846865889065)
    ·
      refine ⟨37433326952440385149416799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49911102603253846865889065 37433326952440385149416799)
      ·
        refine ⟨56149990428660577724125199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37433326952440385149416799 56149990428660577724125199)
        ·
          refine ⟨84224985642990866586187799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56149990428660577724125199 84224985642990866586187799)
          ·
            refine ⟨126337478464486299879281699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84224985642990866586187799 126337478464486299879281699)
            ·
              refine ⟨189506217696729449818922549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126337478464486299879281699 189506217696729449818922549)
              ·
                refine ⟨17766207909068385920523989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189506217696729449818922549 17766207909068385920523989)
                ·
                  refine ⟨416395497868790295012281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17766207909068385920523989 416395497868790295012281)
                  ·
                    rfl

theorem cell22_3649173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3649173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649173 prefixEnd_3649173 := by exact prefixLift 3649173
  have htrace : WordTrace (prefixWord ++ tailWord_3649173) baseStart_3649173 baseEnd_3649173 := by
    simpa [prefixWord, tailWord_3649173, baseEnd_3649173] using wordTrace_append hprefix tailTrace_3649173
  have hstable : (prefixWord ++ tailWord_3649173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649173).length < 2 ^ (prefixWord ++ tailWord_3649173).sum := by decide
  have hdescent : baseEnd_3649173 < baseStart_3649173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649265 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3649265 : Nat := 118140960795 + 3649265 * 2 ^ 59
def prefixEnd_3649265 : Nat := 4983230072969 + 3 ^ 40 * 3649265 * 2
def baseEnd_3649265 : Nat := 1249217987086513311736561

theorem tailTrace_3649265 : CollatzResearch.WordTrace tailWord_3649265 prefixEnd_3649265 1249217987086513311736561 := by
  unfold tailWord_3649265
  simp only [CollatzResearch.WordTrace]
  refine ⟨133099629124343624688053249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88733086082895749792035499 133099629124343624688053249)
  ·
    refine ⟨99824721843257718516039937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133099629124343624688053249 99824721843257718516039937)
    ·
      refine ⟨74868541382443288887029953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99824721843257718516039937 74868541382443288887029953)
      ·
        refine ⟨56151406036832466665272465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74868541382443288887029953 56151406036832466665272465)
        ·
          refine ⟨42113554527624349998954349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56151406036832466665272465 42113554527624349998954349)
          ·
            refine ⟨15792582947859131249607881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42113554527624349998954349 15792582947859131249607881)
            ·
              refine ⟨11844437210894348437205911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15792582947859131249607881 11844437210894348437205911)
              ·
                refine ⟨17766655816341522655808867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11844437210894348437205911 17766655816341522655808867)
                ·
                  refine ⟨26649983724512283983713301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17766655816341522655808867 26649983724512283983713301)
                  ·
                    refine ⟨1249217987086513311736561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26649983724512283983713301 1249217987086513311736561)
                    ·
                      rfl

theorem cell22_3649265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3649265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649265 prefixEnd_3649265 := by exact prefixLift 3649265
  have htrace : WordTrace (prefixWord ++ tailWord_3649265) baseStart_3649265 baseEnd_3649265 := by
    simpa [prefixWord, tailWord_3649265, baseEnd_3649265] using wordTrace_append hprefix tailTrace_3649265
  have hstable : (prefixWord ++ tailWord_3649265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649265).length < 2 ^ (prefixWord ++ tailWord_3649265).sum := by decide
  have hdescent : baseEnd_3649265 < baseStart_3649265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649301 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_3649301 : Nat := 118140960795 + 3649301 * 2 ^ 59
def prefixEnd_3649301 : Nat := 4983230072969 + 3 ^ 40 * 3649301 * 2
def baseEnd_3649301 : Nat := 1249230310622221217836451

theorem tailTrace_3649301 : CollatzResearch.WordTrace tailWord_3649301 prefixEnd_3649301 1249230310622221217836451 := by
  unfold tailWord_3649301
  simp only [CollatzResearch.WordTrace]
  refine ⟨133100942152213202836363757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88733961434808801890909171 133100942152213202836363757)
  ·
    refine ⟨49912853307079951063636409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133100942152213202836363757 49912853307079951063636409)
    ·
      refine ⟨37434639980309963297727307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49912853307079951063636409 37434639980309963297727307)
      ·
        refine ⟨56151959970464944946590961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37434639980309963297727307 56151959970464944946590961)
        ·
          refine ⟨42113969977848708709943221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56151959970464944946590961 42113969977848708709943221)
          ·
            refine ⟨3948184685423316441557177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42113969977848708709943221 3948184685423316441557177)
            ·
              refine ⟨2961138514067487331167883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948184685423316441557177 2961138514067487331167883)
              ·
                refine ⟨4441707771101230996751825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961138514067487331167883 4441707771101230996751825)
                ·
                  refine ⟨3331280828325923247563869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441707771101230996751825 3331280828325923247563869)
                  ·
                    refine ⟨1249230310622221217836451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331280828325923247563869 1249230310622221217836451)
                    ·
                      rfl

theorem cell22_3649301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_3649301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649301 prefixEnd_3649301 := by exact prefixLift 3649301
  have htrace : WordTrace (prefixWord ++ tailWord_3649301) baseStart_3649301 baseEnd_3649301 := by
    simpa [prefixWord, tailWord_3649301, baseEnd_3649301] using wordTrace_append hprefix tailTrace_3649301
  have hstable : (prefixWord ++ tailWord_3649301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649301).length < 2 ^ (prefixWord ++ tailWord_3649301).sum := by decide
  have hdescent : baseEnd_3649301 < baseStart_3649301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649312 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_3649312 : Nat := 118140960795 + 3649312 * 2 ^ 59
def prefixEnd_3649312 : Nat := 4983230072969 + 3 ^ 40 * 3649312 * 2
def baseEnd_3649312 : Nat := 1249234076147020855811417

theorem tailTrace_3649312 : CollatzResearch.WordTrace tailWord_3649312 prefixEnd_3649312 1249234076147020855811417 := by
  unfold tailWord_3649312
  simp only [CollatzResearch.WordTrace]
  refine ⟨66550671677586675857507095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88734228903448901143342793 66550671677586675857507095)
  ·
    refine ⟨99826007516380013786260643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66550671677586675857507095 99826007516380013786260643)
    ·
      refine ⟨149739011274570020679390965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99826007516380013786260643 149739011274570020679390965)
      ·
        refine ⟨14038032306990939438692903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149739011274570020679390965 14038032306990939438692903)
        ·
          refine ⟨21057048460486409158039355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14038032306990939438692903 21057048460486409158039355)
          ·
            refine ⟨31585572690729613737059033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21057048460486409158039355 31585572690729613737059033)
            ·
              refine ⟨23689179518047210302794275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31585572690729613737059033 23689179518047210302794275)
              ·
                refine ⟨35533769277070815454191413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23689179518047210302794275 35533769277070815454191413)
                ·
                  refine ⟨3331290869725388948830445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35533769277070815454191413 3331290869725388948830445)
                  ·
                    refine ⟨1249234076147020855811417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331290869725388948830445 1249234076147020855811417)
                    ·
                      rfl

theorem cell22_3649312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_3649312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649312 prefixEnd_3649312 := by exact prefixLift 3649312
  have htrace : WordTrace (prefixWord ++ tailWord_3649312) baseStart_3649312 baseEnd_3649312 := by
    simpa [prefixWord, tailWord_3649312, baseEnd_3649312] using wordTrace_append hprefix tailTrace_3649312
  have hstable : (prefixWord ++ tailWord_3649312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649312).length < 2 ^ (prefixWord ++ tailWord_3649312).sum := by decide
  have hdescent : baseEnd_3649312 < baseStart_3649312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649511 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 5]
def baseStart_3649511 : Nat := 118140960795 + 3649511 * 2 ^ 59
def prefixEnd_3649511 : Nat := 4983230072969 + 3 ^ 40 * 3649511 * 2
def baseEnd_3649511 : Nat := 416434065971283556695269

theorem tailTrace_3649511 : CollatzResearch.WordTrace tailWord_3649511 prefixEnd_3649511 416434065971283556695269 := by
  unfold tailWord_3649511
  simp only [CollatzResearch.WordTrace]
  refine ⟨133108601481452408701508387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88739067654301605801005591 133108601481452408701508387)
  ·
    refine ⟨199662902222178613052262581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133108601481452408701508387 199662902222178613052262581)
    ·
      refine ⟨18718397083329244973649617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199662902222178613052262581 18718397083329244973649617)
      ·
        refine ⟨14038797812496933730237213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18718397083329244973649617 14038797812496933730237213)
        ·
          refine ⟨5264549179686350148838955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14038797812496933730237213 5264549179686350148838955)
          ·
            refine ⟨7896823769529525223258433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264549179686350148838955 7896823769529525223258433)
            ·
              refine ⟨5922617827147143917443825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896823769529525223258433 5922617827147143917443825)
              ·
                refine ⟨4441963370360357938082869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5922617827147143917443825 4441963370360357938082869)
                ·
                  refine ⟨416434065971283556695269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4441963370360357938082869 416434065971283556695269)
                  ·
                    rfl

theorem cell22_3649511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 5].length) (baseStart_3649511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649511 prefixEnd_3649511 := by exact prefixLift 3649511
  have htrace : WordTrace (prefixWord ++ tailWord_3649511) baseStart_3649511 baseEnd_3649511 := by
    simpa [prefixWord, tailWord_3649511, baseEnd_3649511] using wordTrace_append hprefix tailTrace_3649511
  have hstable : (prefixWord ++ tailWord_3649511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649511).length < 2 ^ (prefixWord ++ tailWord_3649511).sum := by decide
  have hdescent : baseEnd_3649511 < baseStart_3649511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649526 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3649526 : Nat := 118140960795 + 3649526 * 2 ^ 59
def prefixEnd_3649526 : Nat := 4983230072969 + 3 ^ 40 * 3649526 * 2
def baseEnd_3649526 : Nat := 1249307332720395630960761

theorem tailTrace_3649526 : CollatzResearch.WordTrace tailWord_3649526 prefixEnd_3649526 1249307332720395630960761 := by
  unfold tailWord_3649526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319321786024879141456527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88739432384265377508869621 8319321786024879141456527)
  ·
    refine ⟨12478982679037318712184791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8319321786024879141456527 12478982679037318712184791)
    ·
      refine ⟨18718474018555978068277187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12478982679037318712184791 18718474018555978068277187)
      ·
        refine ⟨28077711027833967102415781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18718474018555978068277187 28077711027833967102415781)
        ·
          refine ⟨5264570817718868831702959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28077711027833967102415781 5264570817718868831702959)
          ·
            refine ⟨7896856226578303247554439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264570817718868831702959 7896856226578303247554439)
            ·
              refine ⟨11845284339867454871331659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7896856226578303247554439 11845284339867454871331659)
              ·
                refine ⟨17767926509801182306997489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11845284339867454871331659 17767926509801182306997489)
                ·
                  refine ⟨13325944882350886730248117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17767926509801182306997489 13325944882350886730248117)
                  ·
                    refine ⟨1249307332720395630960761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13325944882350886730248117 1249307332720395630960761)
                    ·
                      rfl

theorem cell22_3649526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3649526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649526 prefixEnd_3649526 := by exact prefixLift 3649526
  have htrace : WordTrace (prefixWord ++ tailWord_3649526) baseStart_3649526 baseEnd_3649526 := by
    simpa [prefixWord, tailWord_3649526, baseEnd_3649526] using wordTrace_append hprefix tailTrace_3649526
  have hstable : (prefixWord ++ tailWord_3649526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649526).length < 2 ^ (prefixWord ++ tailWord_3649526).sum := by decide
  have hdescent : baseEnd_3649526 < baseStart_3649526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649549 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3649549 : Nat := 118140960795 + 3649549 * 2 ^ 59
def prefixEnd_3649549 : Nat := 4983230072969 + 3 ^ 40 * 3649549 * 2
def baseEnd_3649549 : Nat := 1249315206090431237635691

theorem tailTrace_3649549 : CollatzResearch.WordTrace tailWord_3649549 prefixEnd_3649549 1249315206090431237635691 := by
  unfold tailWord_3649549
  simp only [CollatzResearch.WordTrace]
  refine ⟨133109987455314741191391701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88739991636876494127594467 133109987455314741191391701)
  ·
    refine ⟨3119765330983939246673243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 133109987455314741191391701 3119765330983939246673243)
    ·
      refine ⟨4679647996475908870009865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119765330983939246673243 4679647996475908870009865)
      ·
        refine ⟨3509735997356931652507399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4679647996475908870009865 3509735997356931652507399)
        ·
          refine ⟨5264603996035397478761099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509735997356931652507399 5264603996035397478761099)
          ·
            refine ⟨7896905994053096218141649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264603996035397478761099 7896905994053096218141649)
            ·
              refine ⟨5922679495539822163606237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896905994053096218141649 5922679495539822163606237)
              ·
                refine ⟨2221004810827433311352339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5922679495539822163606237 2221004810827433311352339)
                ·
                  refine ⟨3331507216241149967028509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221004810827433311352339 3331507216241149967028509)
                  ·
                    refine ⟨1249315206090431237635691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331507216241149967028509 1249315206090431237635691)
                    ·
                      rfl

theorem cell22_3649549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3649549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649549 prefixEnd_3649549 := by exact prefixLift 3649549
  have htrace : WordTrace (prefixWord ++ tailWord_3649549) baseStart_3649549 baseEnd_3649549 := by
    simpa [prefixWord, tailWord_3649549, baseEnd_3649549] using wordTrace_append hprefix tailTrace_3649549
  have hstable : (prefixWord ++ tailWord_3649549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649549).length < 2 ^ (prefixWord ++ tailWord_3649549).sum := by decide
  have hdescent : baseEnd_3649549 < baseStart_3649549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649552 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_3649552 : Nat := 118140960795 + 3649552 * 2 ^ 59
def prefixEnd_3649552 : Nat := 4983230072969 + 3 ^ 40 * 3649552 * 2
def baseEnd_3649552 : Nat := 1249316233051740229810681

theorem tailTrace_3649552 : CollatzResearch.WordTrace tailWord_3649552 prefixEnd_3649552 1249316233051740229810681 := by
  unfold tailWord_3649552
  simp only [CollatzResearch.WordTrace]
  refine ⟨66555048437151936351875455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88740064582869248469167273 66555048437151936351875455)
  ·
    refine ⟨99832572655727904527813183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66555048437151936351875455 99832572655727904527813183)
    ·
      refine ⟨149748858983591856791719775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99832572655727904527813183 149748858983591856791719775)
      ·
        refine ⟨224623288475387785187579663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149748858983591856791719775 224623288475387785187579663)
        ·
          refine ⟨336934932713081677781369495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224623288475387785187579663 336934932713081677781369495)
          ·
            refine ⟨505402399069622516672054243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336934932713081677781369495 505402399069622516672054243)
            ·
              refine ⟨758103598604433775008081365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505402399069622516672054243 758103598604433775008081365)
              ·
                refine ⟨17768053092291416601751907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 758103598604433775008081365 17768053092291416601751907)
                ·
                  refine ⟨26652079638437124902627861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17768053092291416601751907 26652079638437124902627861)
                  ·
                    refine ⟨1249316233051740229810681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26652079638437124902627861 1249316233051740229810681)
                    ·
                      rfl

theorem cell22_3649552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_3649552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649552 prefixEnd_3649552 := by exact prefixLift 3649552
  have htrace : WordTrace (prefixWord ++ tailWord_3649552) baseStart_3649552 baseEnd_3649552 := by
    simpa [prefixWord, tailWord_3649552, baseEnd_3649552] using wordTrace_append hprefix tailTrace_3649552
  have hstable : (prefixWord ++ tailWord_3649552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649552).length < 2 ^ (prefixWord ++ tailWord_3649552).sum := by decide
  have hdescent : baseEnd_3649552 < baseStart_3649552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649567 : List Nat := [1, 1, 2, 4, 1, 2, 11]
def baseStart_3649567 : Nat := 118140960795 + 3649567 * 2 ^ 59
def prefixEnd_3649567 : Nat := 4983230072969 + 3 ^ 40 * 3649567 * 2
def baseEnd_3649567 : Nat := 46271161772529081136505

theorem tailTrace_3649567 : CollatzResearch.WordTrace tailWord_3649567 prefixEnd_3649567 46271161772529081136505 := by
  unfold tailWord_3649567
  simp only [CollatzResearch.WordTrace]
  refine ⟨133110643969249530265546955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88740429312833020177031303 133110643969249530265546955)
  ·
    refine ⟨199665965953874295398320433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133110643969249530265546955 199665965953874295398320433)
    ·
      refine ⟨149749474465405721548740325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199665965953874295398320433 149749474465405721548740325)
      ·
        refine ⟨28078026462263572790388811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149749474465405721548740325 28078026462263572790388811)
        ·
          refine ⟨42117039693395359185583217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28078026462263572790388811 42117039693395359185583217)
          ·
            refine ⟨31587779770046519389187413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42117039693395359185583217 31587779770046519389187413)
            ·
              refine ⟨46271161772529081136505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31587779770046519389187413 46271161772529081136505)
              ·
                rfl

theorem cell22_3649567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 11].length) (baseStart_3649567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649567 prefixEnd_3649567 := by exact prefixLift 3649567
  have htrace : WordTrace (prefixWord ++ tailWord_3649567) baseStart_3649567 baseEnd_3649567 := by
    simpa [prefixWord, tailWord_3649567, baseEnd_3649567] using wordTrace_append hprefix tailTrace_3649567
  have hstable : (prefixWord ++ tailWord_3649567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649567).length < 2 ^ (prefixWord ++ tailWord_3649567).sum := by decide
  have hdescent : baseEnd_3649567 < baseStart_3649567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649601 : List Nat := [1, 2, 5, 1, 2, 1, 4, 6]
def baseStart_3649601 : Nat := 118140960795 + 3649601 * 2 ^ 59
def prefixEnd_3649601 : Nat := 4983230072969 + 3 ^ 40 * 3649601 * 2
def baseEnd_3649601 : Nat := 138814778528124492815059

theorem tailTrace_3649601 : CollatzResearch.WordTrace tailWord_3649601 prefixEnd_3649601 138814778528124492815059 := by
  unfold tailWord_3649601
  simp only [CollatzResearch.WordTrace]
  refine ⟨133111884051126354072284657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88741256034084236048189771 133111884051126354072284657)
  ·
    refine ⟨99833913038344765554213493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133111884051126354072284657 99833913038344765554213493)
    ·
      refine ⟨9359429347344821770707515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99833913038344765554213493 9359429347344821770707515)
      ·
        refine ⟨14039144021017232656061273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359429347344821770707515 14039144021017232656061273)
        ·
          refine ⟨10529358015762924492045955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14039144021017232656061273 10529358015762924492045955)
          ·
            refine ⟨15794037023644386738068933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529358015762924492045955 15794037023644386738068933)
            ·
              refine ⟨2961381941933322513387925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15794037023644386738068933 2961381941933322513387925)
              ·
                refine ⟨138814778528124492815059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2961381941933322513387925 138814778528124492815059)
                ·
                  rfl

theorem cell22_3649601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 6].length) (baseStart_3649601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649601 prefixEnd_3649601 := by exact prefixLift 3649601
  have htrace : WordTrace (prefixWord ++ tailWord_3649601) baseStart_3649601 baseEnd_3649601 := by
    simpa [prefixWord, tailWord_3649601, baseEnd_3649601] using wordTrace_append hprefix tailTrace_3649601
  have hstable : (prefixWord ++ tailWord_3649601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649601).length < 2 ^ (prefixWord ++ tailWord_3649601).sum := by decide
  have hdescent : baseEnd_3649601 < baseStart_3649601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649646 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_3649646 : Nat := 118140960795 + 3649646 * 2 ^ 59
def prefixEnd_3649646 : Nat := 4983230072969 + 3 ^ 40 * 3649646 * 2
def baseEnd_3649646 : Nat := 416449470390918439320131

theorem tailTrace_3649646 : CollatzResearch.WordTrace tailWord_3649646 prefixEnd_3649646 416449470390918439320131 := by
  unfold tailWord_3649646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639190666995415844709099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88742350223975551171781861 16639190666995415844709099)
  ·
    refine ⟨24958786000493123767063649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16639190666995415844709099 24958786000493123767063649)
    ·
      refine ⟨18719089500369842825297737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24958786000493123767063649 18719089500369842825297737)
      ·
        refine ⟨14039317125277382118973303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18719089500369842825297737 14039317125277382118973303)
        ·
          refine ⟨21058975687916073178459955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039317125277382118973303 21058975687916073178459955)
          ·
            refine ⟨31588463531874109767689933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21058975687916073178459955 31588463531874109767689933)
            ·
              refine ⟨11845673824452791162883725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31588463531874109767689933 11845673824452791162883725)
              ·
                refine ⟨4442127684169796686081397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11845673824452791162883725 4442127684169796686081397)
                ·
                  refine ⟨416449470390918439320131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442127684169796686081397 416449470390918439320131)
                  ·
                    rfl

theorem cell22_3649646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_3649646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649646 prefixEnd_3649646 := by exact prefixLift 3649646
  have htrace : WordTrace (prefixWord ++ tailWord_3649646) baseStart_3649646 baseEnd_3649646 := by
    simpa [prefixWord, tailWord_3649646, baseEnd_3649646] using wordTrace_append hprefix tailTrace_3649646
  have hstable : (prefixWord ++ tailWord_3649646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649646).length < 2 ^ (prefixWord ++ tailWord_3649646).sum := by decide
  have hdescent : baseEnd_3649646 < baseStart_3649646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649740 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_3649740 : Nat := 118140960795 + 3649740 * 2 ^ 59
def prefixEnd_3649740 : Nat := 4983230072969 + 3 ^ 40 * 3649740 * 2
def baseEnd_3649740 : Nat := 1249380589293770406110105

theorem tailTrace_3649740 : CollatzResearch.WordTrace tailWord_3649740 prefixEnd_3649740 1249380589293770406110105 := by
  unfold tailWord_3649740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66558476898811390405797337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88744635865081853874396449 66558476898811390405797337)
  ·
    refine ⟨49918857674108542804348003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66558476898811390405797337 49918857674108542804348003)
    ·
      refine ⟨74878286511162814206522005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49918857674108542804348003 74878286511162814206522005)
      ·
        refine ⟨3509919680210756915930719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74878286511162814206522005 3509919680210756915930719)
        ·
          refine ⟨5264879520316135373896079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509919680210756915930719 5264879520316135373896079)
          ·
            refine ⟨7897319280474203060844119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264879520316135373896079 7897319280474203060844119)
            ·
              refine ⟨11845978920711304591266179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897319280474203060844119 11845978920711304591266179)
              ·
                refine ⟨17768968381066956886899269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11845978920711304591266179 17768968381066956886899269)
                ·
                  refine ⟨3331681571450054416293613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17768968381066956886899269 3331681571450054416293613)
                  ·
                    refine ⟨1249380589293770406110105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331681571450054416293613 1249380589293770406110105)
                    ·
                      rfl

theorem cell22_3649740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_3649740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649740 prefixEnd_3649740 := by exact prefixLift 3649740
  have htrace : WordTrace (prefixWord ++ tailWord_3649740) baseStart_3649740 baseEnd_3649740 := by
    simpa [prefixWord, tailWord_3649740, baseEnd_3649740] using wordTrace_append hprefix tailTrace_3649740
  have hstable : (prefixWord ++ tailWord_3649740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649740).length < 2 ^ (prefixWord ++ tailWord_3649740).sum := by decide
  have hdescent : baseEnd_3649740 < baseStart_3649740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649757 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3649757 : Nat := 118140960795 + 3649757 * 2 ^ 59
def prefixEnd_3649757 : Nat := 4983230072969 + 3 ^ 40 * 3649757 * 2
def baseEnd_3649757 : Nat := 1249386408741188028435053

theorem tailTrace_3649757 : CollatzResearch.WordTrace tailWord_3649757 prefixEnd_3649757 1249386408741188028435053 := by
  unfold tailWord_3649757
  simp only [CollatzResearch.WordTrace]
  refine ⟨133117573838561192714963525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88745049225707461809975683 133117573838561192714963525)
  ·
    refine ⟨24959545094730223634055661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133117573838561192714963525 24959545094730223634055661)
    ·
      refine ⟨9359829410523833862770873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24959545094730223634055661 9359829410523833862770873)
      ·
        refine ⟨7019872057892875397078155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9359829410523833862770873 7019872057892875397078155)
        ·
          refine ⟨10529808086839313095617233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7019872057892875397078155 10529808086839313095617233)
          ·
            refine ⟨7897356065129484821712925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10529808086839313095617233 7897356065129484821712925)
            ·
              refine ⟨2961508524423556808142347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7897356065129484821712925 2961508524423556808142347)
              ·
                refine ⟨4442262786635335212213521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961508524423556808142347 4442262786635335212213521)
                ·
                  refine ⟨3331697089976501409160141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4442262786635335212213521 3331697089976501409160141)
                  ·
                    refine ⟨1249386408741188028435053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331697089976501409160141 1249386408741188028435053)
                    ·
                      rfl

theorem cell22_3649757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3649757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649757 prefixEnd_3649757 := by exact prefixLift 3649757
  have htrace : WordTrace (prefixWord ++ tailWord_3649757) baseStart_3649757 baseEnd_3649757 := by
    simpa [prefixWord, tailWord_3649757, baseEnd_3649757] using wordTrace_append hprefix tailTrace_3649757
  have hstable : (prefixWord ++ tailWord_3649757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649757).length < 2 ^ (prefixWord ++ tailWord_3649757).sum := by decide
  have hdescent : baseEnd_3649757 < baseStart_3649757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649768 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3649768 : Nat := 118140960795 + 3649768 * 2 ^ 59
def prefixEnd_3649768 : Nat := 4983230072969 + 3 ^ 40 * 3649768 * 2
def baseEnd_3649768 : Nat := 1249390174265987666410019

theorem tailTrace_3649768 : CollatzResearch.WordTrace tailWord_3649768 prefixEnd_3649768 1249390174265987666410019 := by
  unfold tailWord_3649768
  simp only [CollatzResearch.WordTrace]
  refine ⟨66558987520760670796806979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88745316694347561062409305 66558987520760670796806979)
  ·
    refine ⟨99838481281141006195210469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66558987520760670796806979 99838481281141006195210469)
    ·
      refine ⟨18719715240213938661601963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99838481281141006195210469 18719715240213938661601963)
      ·
        refine ⟨28079572860320907992402945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18719715240213938661601963 28079572860320907992402945)
        ·
          refine ⟨21059679645240680994302209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28079572860320907992402945 21059679645240680994302209)
          ·
            refine ⟨15794759733930510745726657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21059679645240680994302209 15794759733930510745726657)
            ·
              refine ⟨11846069800447883059294993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15794759733930510745726657 11846069800447883059294993)
              ·
                refine ⟨8884552350335912294471245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11846069800447883059294993 8884552350335912294471245)
                ·
                  refine ⟨3331707131375967110426717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8884552350335912294471245 3331707131375967110426717)
                  ·
                    refine ⟨1249390174265987666410019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331707131375967110426717 1249390174265987666410019)
                    ·
                      rfl

theorem cell22_3649768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3649768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649768 prefixEnd_3649768 := by exact prefixLift 3649768
  have htrace : WordTrace (prefixWord ++ tailWord_3649768) baseStart_3649768 baseEnd_3649768 := by
    simpa [prefixWord, tailWord_3649768, baseEnd_3649768] using wordTrace_append hprefix tailTrace_3649768
  have hstable : (prefixWord ++ tailWord_3649768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649768).length < 2 ^ (prefixWord ++ tailWord_3649768).sum := by decide
  have hdescent : baseEnd_3649768 < baseStart_3649768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649815 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 5]
def baseStart_3649815 : Nat := 118140960795 + 3649815 * 2 ^ 59
def prefixEnd_3649815 : Nat := 4983230072969 + 3 ^ 40 * 3649815 * 2
def baseEnd_3649815 : Nat := 416468754442165070161625

theorem tailTrace_3649815 : CollatzResearch.WordTrace tailWord_3649815 prefixEnd_3649815 416468754442165070161625 := by
  unfold tailWord_3649815
  simp only [CollatzResearch.WordTrace]
  refine ⟨133119689272351068620574899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88746459514900712413716599 133119689272351068620574899)
  ·
    refine ⟨199679533908526602930862349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133119689272351068620574899 199679533908526602930862349)
    ·
      refine ⟨74879825215697476099073381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199679533908526602930862349 74879825215697476099073381)
      ·
        refine ⟨14039967227943276768576259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74879825215697476099073381 14039967227943276768576259)
        ·
          refine ⟨21059950841914915152864389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039967227943276768576259 21059950841914915152864389)
          ·
            refine ⟨3948740782859046591162073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21059950841914915152864389 3948740782859046591162073)
            ·
              refine ⟨2961555587144284943371555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948740782859046591162073 2961555587144284943371555)
              ·
                refine ⟨4442333380716427415057333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961555587144284943371555 4442333380716427415057333)
                ·
                  refine ⟨416468754442165070161625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442333380716427415057333 416468754442165070161625)
                  ·
                    rfl

theorem cell22_3649815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 5].length) (baseStart_3649815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649815 prefixEnd_3649815 := by exact prefixLift 3649815
  have htrace : WordTrace (prefixWord ++ tailWord_3649815) baseStart_3649815 baseEnd_3649815 := by
    simpa [prefixWord, tailWord_3649815, baseEnd_3649815] using wordTrace_append hprefix tailTrace_3649815
  have hstable : (prefixWord ++ tailWord_3649815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649815).length < 2 ^ (prefixWord ++ tailWord_3649815).sum := by decide
  have hdescent : baseEnd_3649815 < baseStart_3649815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649828 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3649828 : Nat := 118140960795 + 3649828 * 2 ^ 59
def prefixEnd_3649828 : Nat := 4983230072969 + 3 ^ 40 * 3649828 * 2
def baseEnd_3649828 : Nat := 1249410713492167509909835

theorem tailTrace_3649828 : CollatzResearch.WordTrace tailWord_3649828 prefixEnd_3649828 1249410713492167509909835 := by
  unfold tailWord_3649828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66560081710651985920399069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88746775614202647893865425 66560081710651985920399069)
  ·
    refine ⟨24960030641494494720149651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66560081710651985920399069 24960030641494494720149651)
    ·
      refine ⟨37440045962241742080224477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24960030641494494720149651 37440045962241742080224477)
      ·
        refine ⟨14040017235840653280084179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37440045962241742080224477 14040017235840653280084179)
        ·
          refine ⟨21060025853760979920126269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14040017235840653280084179 21060025853760979920126269)
          ·
            refine ⟨7897509695160367470047351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21060025853760979920126269 7897509695160367470047351)
            ·
              refine ⟨11846264542740551205071027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897509695160367470047351 11846264542740551205071027)
              ·
                refine ⟨17769396814110826807606541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11846264542740551205071027 17769396814110826807606541)
                ·
                  refine ⟨6663523805291560052852453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17769396814110826807606541 6663523805291560052852453)
                  ·
                    refine ⟨1249410713492167509909835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663523805291560052852453 1249410713492167509909835)
                    ·
                      rfl

theorem cell22_3649828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3649828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649828 prefixEnd_3649828 := by exact prefixLift 3649828
  have htrace : WordTrace (prefixWord ++ tailWord_3649828) baseStart_3649828 baseEnd_3649828 := by
    simpa [prefixWord, tailWord_3649828, baseEnd_3649828] using wordTrace_append hprefix tailTrace_3649828
  have hstable : (prefixWord ++ tailWord_3649828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649828).length < 2 ^ (prefixWord ++ tailWord_3649828).sum := by decide
  have hdescent : baseEnd_3649828 < baseStart_3649828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649843 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 4]
def baseStart_3649843 : Nat := 118140960795 + 3649843 * 2 ^ 59
def prefixEnd_3649843 : Nat := 4983230072969 + 3 ^ 40 * 3649843 * 2
def baseEnd_3649843 : Nat := 416471949432904156928263

theorem tailTrace_3649843 : CollatzResearch.WordTrace tailWord_3649843 prefixEnd_3649843 416471949432904156928263 := by
  unfold tailWord_3649843
  simp only [CollatzResearch.WordTrace]
  refine ⟨133120710516249629402594183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88747140344166419601729455 133120710516249629402594183)
  ·
    refine ⟨199681065774374444103891275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133120710516249629402594183 199681065774374444103891275)
    ·
      refine ⟨299521598661561666155836913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199681065774374444103891275 299521598661561666155836913)
      ·
        refine ⟨224641198996171249616877685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299521598661561666155836913 224641198996171249616877685)
        ·
          refine ⟨21060112405891054651582283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224641198996171249616877685 21060112405891054651582283)
          ·
            refine ⟨31590168608836581977373425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21060112405891054651582283 31590168608836581977373425)
            ·
              refine ⟨23692626456627436483030069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31590168608836581977373425 23692626456627436483030069)
              ·
                refine ⟨2221183730308822170284069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23692626456627436483030069 2221183730308822170284069)
                ·
                  refine ⟨416471949432904156928263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221183730308822170284069 416471949432904156928263)
                  ·
                    rfl

theorem cell22_3649843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 4].length) (baseStart_3649843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649843 prefixEnd_3649843 := by exact prefixLift 3649843
  have htrace : WordTrace (prefixWord ++ tailWord_3649843) baseStart_3649843 baseEnd_3649843 := by
    simpa [prefixWord, tailWord_3649843, baseEnd_3649843] using wordTrace_append hprefix tailTrace_3649843
  have hstable : (prefixWord ++ tailWord_3649843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649843).length < 2 ^ (prefixWord ++ tailWord_3649843).sum := by decide
  have hdescent : baseEnd_3649843 < baseStart_3649843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649845 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3649845 : Nat := 118140960795 + 3649845 * 2 ^ 59
def prefixEnd_3649845 : Nat := 4983230072969 + 3 ^ 40 * 3649845 * 2
def baseEnd_3649845 : Nat := 1249416532939585132234783

theorem tailTrace_3649845 : CollatzResearch.WordTrace tailWord_3649845 prefixEnd_3649845 1249416532939585132234783 := by
  unfold tailWord_3649845
  simp only [CollatzResearch.WordTrace]
  refine ⟨133120783462242383744166989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88747188974828255829444659 133120783462242383744166989)
  ·
    refine ⟨49920293798340893904062621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133120783462242383744166989 49920293798340893904062621)
    ·
      refine ⟨18720110174377835214023483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49920293798340893904062621 18720110174377835214023483)
      ·
        refine ⟨28080165261566752821035225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18720110174377835214023483 28080165261566752821035225)
        ·
          refine ⟨21060123946175064615776419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28080165261566752821035225 21060123946175064615776419)
          ·
            refine ⟨31590185919262596923664629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21060123946175064615776419 31590185919262596923664629)
            ·
              refine ⟨2961579929930868461593559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31590185919262596923664629 2961579929930868461593559)
              ·
                refine ⟨4442369894896302692390339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961579929930868461593559 4442369894896302692390339)
                ·
                  refine ⟨6663554842344454038585509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442369894896302692390339 6663554842344454038585509)
                  ·
                    refine ⟨1249416532939585132234783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663554842344454038585509 1249416532939585132234783)
                    ·
                      rfl

theorem cell22_3649845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3649845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649845 prefixEnd_3649845 := by exact prefixLift 3649845
  have htrace : WordTrace (prefixWord ++ tailWord_3649845) baseStart_3649845 baseEnd_3649845 := by
    simpa [prefixWord, tailWord_3649845, baseEnd_3649845] using wordTrace_append hprefix tailTrace_3649845
  have hstable : (prefixWord ++ tailWord_3649845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649845).length < 2 ^ (prefixWord ++ tailWord_3649845).sum := by decide
  have hdescent : baseEnd_3649845 < baseStart_3649845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649856 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_3649856 : Nat := 118140960795 + 3649856 * 2 ^ 59
def prefixEnd_3649856 : Nat := 4983230072969 + 3 ^ 40 * 3649856 * 2
def baseEnd_3649856 : Nat := 1249420298464384770209749

theorem tailTrace_3649856 : CollatzResearch.WordTrace tailWord_3649856 prefixEnd_3649856 1249420298464384770209749 := by
  unfold tailWord_3649856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66560592332601266311408711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88747456443468355081878281 66560592332601266311408711)
  ·
    refine ⟨99840888498901899467113067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66560592332601266311408711 99840888498901899467113067)
    ·
      refine ⟨149761332748352849200669601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99840888498901899467113067 149761332748352849200669601)
      ·
        refine ⟨112320999561264636900502201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149761332748352849200669601 112320999561264636900502201)
        ·
          refine ⟨84240749670948477675376651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112320999561264636900502201 84240749670948477675376651)
          ·
            refine ⟨126361124506422716513064977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84240749670948477675376651 126361124506422716513064977)
            ·
              refine ⟨94770843379817037384798733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126361124506422716513064977 94770843379817037384798733)
              ·
                refine ⟨35539066267431389019299525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94770843379817037384798733 35539066267431389019299525)
                ·
                  refine ⟨6663574925143385441118661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35539066267431389019299525 6663574925143385441118661)
                  ·
                    refine ⟨1249420298464384770209749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663574925143385441118661 1249420298464384770209749)
                    ·
                      rfl

theorem cell22_3649856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_3649856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649856 prefixEnd_3649856 := by exact prefixLift 3649856
  have htrace : WordTrace (prefixWord ++ tailWord_3649856) baseStart_3649856 baseEnd_3649856 := by
    simpa [prefixWord, tailWord_3649856, baseEnd_3649856] using wordTrace_append hprefix tailTrace_3649856
  have hstable : (prefixWord ++ tailWord_3649856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649856).length < 2 ^ (prefixWord ++ tailWord_3649856).sum := by decide
  have hdescent : baseEnd_3649856 < baseStart_3649856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649890 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3649890 : Nat := 118140960795 + 3649890 * 2 ^ 59
def prefixEnd_3649890 : Nat := 4983230072969 + 3 ^ 40 * 3649890 * 2
def baseEnd_3649890 : Nat := 1249431937359220014859645

theorem tailTrace_3649890 : CollatzResearch.WordTrace tailWord_3649890 prefixEnd_3649890 1249431937359220014859645 := by
  unfold tailWord_3649890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33280606186769839107388781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88748283164719570953036749 33280606186769839107388781)
  ·
    refine ⟨12480227320038689665270793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33280606186769839107388781 12480227320038689665270793)
    ·
      refine ⟨9360170490029017248953095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12480227320038689665270793 9360170490029017248953095)
      ·
        refine ⟨14040255735043525873429643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9360170490029017248953095 14040255735043525873429643)
        ·
          refine ⟨21060383602565288810144465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14040255735043525873429643 21060383602565288810144465)
          ·
            refine ⟨15795287701923966607608349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21060383602565288810144465 15795287701923966607608349)
            ·
              refine ⟨5923232888221487477853131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15795287701923966607608349 5923232888221487477853131)
              ·
                refine ⟨8884849332332231216779697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923232888221487477853131 8884849332332231216779697)
                ·
                  refine ⟨6663636999249173412584773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8884849332332231216779697 6663636999249173412584773)
                  ·
                    refine ⟨1249431937359220014859645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663636999249173412584773 1249431937359220014859645)
                    ·
                      rfl

theorem cell22_3649890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3649890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649890 prefixEnd_3649890 := by exact prefixLift 3649890
  have htrace : WordTrace (prefixWord ++ tailWord_3649890) baseStart_3649890 baseEnd_3649890 := by
    simpa [prefixWord, tailWord_3649890, baseEnd_3649890] using wordTrace_append hprefix tailTrace_3649890
  have hstable : (prefixWord ++ tailWord_3649890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649890).length < 2 ^ (prefixWord ++ tailWord_3649890).sum := by decide
  have hdescent : baseEnd_3649890 < baseStart_3649890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649950 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3649950 : Nat := 118140960795 + 3649950 * 2 ^ 59
def prefixEnd_3649950 : Nat := 4983230072969 + 3 ^ 40 * 3649950 * 2
def baseEnd_3649950 : Nat := 416484158861799952786487

theorem tailTrace_3649950 : CollatzResearch.WordTrace tailWord_3649950 prefixEnd_3649950 416484158861799952786487 := by
  unfold tailWord_3649950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640576640857748334592413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88749742084574657784492869 16640576640857748334592413)
  ·
    refine ⟨6240216240321655625472155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16640576640857748334592413 6240216240321655625472155)
    ·
      refine ⟨9360324360482483438208233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240216240321655625472155 9360324360482483438208233)
      ·
        refine ⟨7020243270361862578656175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9360324360482483438208233 7020243270361862578656175)
        ·
          refine ⟨10530364905542793867984263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020243270361862578656175 10530364905542793867984263)
          ·
            refine ⟨15795547358314190801976395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10530364905542793867984263 15795547358314190801976395)
            ·
              refine ⟨23693321037471286202964593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15795547358314190801976395 23693321037471286202964593)
              ·
                refine ⟨17769990778103464652223445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23693321037471286202964593 17769990778103464652223445)
                ·
                  refine ⟨416484158861799952786487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17769990778103464652223445 416484158861799952786487)
                  ·
                    rfl

theorem cell22_3649950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3649950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649950 prefixEnd_3649950 := by exact prefixLift 3649950
  have htrace : WordTrace (prefixWord ++ tailWord_3649950) baseStart_3649950 baseEnd_3649950 := by
    simpa [prefixWord, tailWord_3649950, baseEnd_3649950] using wordTrace_append hprefix tailTrace_3649950
  have hstable : (prefixWord ++ tailWord_3649950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649950).length < 2 ^ (prefixWord ++ tailWord_3649950).sum := by decide
  have hdescent : baseEnd_3649950 < baseStart_3649950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649961 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 8]
def baseStart_3649961 : Nat := 118140960795 + 3649961 * 2 ^ 59
def prefixEnd_3649961 : Nat := 4983230072969 + 3 ^ 40 * 3649961 * 2
def baseEnd_3649961 : Nat := 416485414036733165444809

theorem tailTrace_3649961 : CollatzResearch.WordTrace tailWord_3649961 prefixEnd_3649961 416485414036733165444809 := by
  unfold tailWord_3649961
  simp only [CollatzResearch.WordTrace]
  refine ⟨133125014329822135555389737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88750009553214757036926491 133125014329822135555389737)
  ·
    refine ⟨99843760747366601666542303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133125014329822135555389737 99843760747366601666542303)
    ·
      refine ⟨149765641121049902499813455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99843760747366601666542303 149765641121049902499813455)
      ·
        refine ⟨224648461681574853749720183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149765641121049902499813455 224648461681574853749720183)
        ·
          refine ⟨336972692522362280624580275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224648461681574853749720183 336972692522362280624580275)
          ·
            refine ⟨505459038783543420936870413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336972692522362280624580275 505459038783543420936870413)
            ·
              refine ⟨189547139543828782851326405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505459038783543420936870413 189547139543828782851326405)
              ·
                refine ⟨35540088664467896784623701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189547139543828782851326405 35540088664467896784623701)
                ·
                  refine ⟨416485414036733165444809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35540088664467896784623701 416485414036733165444809)
                  ·
                    rfl

theorem cell22_3649961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_3649961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3649961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3649961 prefixEnd_3649961 := by exact prefixLift 3649961
  have htrace : WordTrace (prefixWord ++ tailWord_3649961) baseStart_3649961 baseEnd_3649961 := by
    simpa [prefixWord, tailWord_3649961, baseEnd_3649961] using wordTrace_append hprefix tailTrace_3649961
  have hstable : (prefixWord ++ tailWord_3649961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649961).length < 2 ^ (prefixWord ++ tailWord_3649961).sum := by decide
  have hdescent : baseEnd_3649961 < baseStart_3649961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650029 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 4]
def baseStart_3650029 : Nat := 118140960795 + 3650029 * 2 ^ 59
def prefixEnd_3650029 : Nat := 4983230072969 + 3 ^ 40 * 3650029 * 2
def baseEnd_3650029 : Nat := 416493173299956661878073

theorem tailTrace_3650029 : CollatzResearch.WordTrace tailWord_3650029 prefixEnd_3650029 416493173299956661878073 := by
  unfold tailWord_3650029
  simp only [CollatzResearch.WordTrace]
  refine ⟨133127494493575783168865141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88751662995717188779243427 133127494493575783168865141)
  ·
    refine ⟨12480702608772729672081107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133127494493575783168865141 12480702608772729672081107)
    ·
      refine ⟨18721053913159094508121661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12480702608772729672081107 18721053913159094508121661)
      ·
        refine ⟨7020395217434660440545623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18721053913159094508121661 7020395217434660440545623)
        ·
          refine ⟨10530592826151990660818435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020395217434660440545623 10530592826151990660818435)
          ·
            refine ⟨15795889239227985991227653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10530592826151990660818435 15795889239227985991227653)
            ·
              refine ⟨2961729232355247373355185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15795889239227985991227653 2961729232355247373355185)
              ·
                refine ⟨2221296924266435530016389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961729232355247373355185 2221296924266435530016389)
                ·
                  refine ⟨416493173299956661878073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221296924266435530016389 416493173299956661878073)
                  ·
                    rfl

theorem cell22_3650029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_3650029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650029 prefixEnd_3650029 := by exact prefixLift 3650029
  have htrace : WordTrace (prefixWord ++ tailWord_3650029) baseStart_3650029 baseEnd_3650029 := by
    simpa [prefixWord, tailWord_3650029, baseEnd_3650029] using wordTrace_append hprefix tailTrace_3650029
  have hstable : (prefixWord ++ tailWord_3650029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650029).length < 2 ^ (prefixWord ++ tailWord_3650029).sum := by decide
  have hdescent : baseEnd_3650029 < baseStart_3650029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650085 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3650085 : Nat := 118140960795 + 3650085 * 2 ^ 59
def prefixEnd_3650085 : Nat := 4983230072969 + 3 ^ 40 * 3650085 * 2
def baseEnd_3650085 : Nat := 416499563281434835411349

theorem tailTrace_3650085 : CollatzResearch.WordTrace tailWord_3650085 prefixEnd_3650085 416499563281434835411349 := by
  unfold tailWord_3650085
  simp only [CollatzResearch.WordTrace]
  refine ⟨133129536981372904732903709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88753024654248603155269139 133129536981372904732903709)
  ·
    refine ⟨49923576368014839274838891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133129536981372904732903709 49923576368014839274838891)
    ·
      refine ⟨74885364552022258912258337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49923576368014839274838891 74885364552022258912258337)
      ·
        refine ⟨56164023414016694184193753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74885364552022258912258337 56164023414016694184193753)
        ·
          refine ⟨42123017560512520638145315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56164023414016694184193753 42123017560512520638145315)
          ·
            refine ⟨63184526340768780957217973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42123017560512520638145315 63184526340768780957217973)
            ·
              refine ⟨5923549344447073214739185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63184526340768780957217973 5923549344447073214739185)
              ·
                refine ⟨4442662008335304911054389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923549344447073214739185 4442662008335304911054389)
                ·
                  refine ⟨416499563281434835411349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442662008335304911054389 416499563281434835411349)
                  ·
                    rfl

theorem cell22_3650085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3650085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650085 prefixEnd_3650085 := by exact prefixLift 3650085
  have htrace : WordTrace (prefixWord ++ tailWord_3650085) baseStart_3650085 baseEnd_3650085 := by
    simpa [prefixWord, tailWord_3650085, baseEnd_3650085] using wordTrace_append hprefix tailTrace_3650085
  have hstable : (prefixWord ++ tailWord_3650085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650085).length < 2 ^ (prefixWord ++ tailWord_3650085).sum := by decide
  have hdescent : baseEnd_3650085 < baseStart_3650085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650132 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3650132 : Nat := 118140960795 + 3650132 * 2 ^ 59
def prefixEnd_3650132 : Nat := 4983230072969 + 3 ^ 40 * 3650132 * 2
def baseEnd_3650132 : Nat := 1249514778904812050308903

theorem tailTrace_3650132 : CollatzResearch.WordTrace tailWord_3650132 prefixEnd_3650132 1249514778904812050308903 := by
  unfold tailWord_3650132
  simp only [CollatzResearch.WordTrace]
  refine ⟨66565625606101315879932325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88754167474801754506576433 66565625606101315879932325)
  ·
    refine ⟨12481054801143996727487311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66565625606101315879932325 12481054801143996727487311)
    ·
      refine ⟨18721582201715995091230967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481054801143996727487311 18721582201715995091230967)
      ·
        refine ⟨28082373302573992636846451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721582201715995091230967 28082373302573992636846451)
        ·
          refine ⟨42123559953860988955269677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28082373302573992636846451 42123559953860988955269677)
          ·
            refine ⟨15796334982697870858226129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42123559953860988955269677 15796334982697870858226129)
            ·
              refine ⟨11847251237023403143669597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15796334982697870858226129 11847251237023403143669597)
              ·
                refine ⟨4442719213883776178876099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11847251237023403143669597 4442719213883776178876099)
                ·
                  refine ⟨6664078820825664268314149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442719213883776178876099 6664078820825664268314149)
                  ·
                    refine ⟨1249514778904812050308903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664078820825664268314149 1249514778904812050308903)
                    ·
                      rfl

theorem cell22_3650132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3650132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650132 prefixEnd_3650132 := by exact prefixLift 3650132
  have htrace : WordTrace (prefixWord ++ tailWord_3650132) baseStart_3650132 baseEnd_3650132 := by
    simpa [prefixWord, tailWord_3650132, baseEnd_3650132] using wordTrace_append hprefix tailTrace_3650132
  have hstable : (prefixWord ++ tailWord_3650132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650132).length < 2 ^ (prefixWord ++ tailWord_3650132).sum := by decide
  have hdescent : baseEnd_3650132 < baseStart_3650132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650166 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_3650166 : Nat := 118140960795 + 3650166 * 2 ^ 59
def prefixEnd_3650166 : Nat := 4983230072969 + 3 ^ 40 * 3650166 * 2
def baseEnd_3650166 : Nat := 1249526417799647294958799

theorem tailTrace_3650166 : CollatzResearch.WordTrace tailWord_3650166 prefixEnd_3650166 1249526417799647294958799 := by
  unfold tailWord_3650166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320780705879965972912647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88754994196052970377734901 8320780705879965972912647)
  ·
    refine ⟨12481171058819948959368971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8320780705879965972912647 12481171058819948959368971)
    ·
      refine ⟨18721756588229923439053457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481171058819948959368971 18721756588229923439053457)
      ·
        refine ⟨14041317441172442579290093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18721756588229923439053457 14041317441172442579290093)
        ·
          refine ⟨5265494040439665967233785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14041317441172442579290093 5265494040439665967233785)
          ·
            refine ⟨3949120530329749475425339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5265494040439665967233785 3949120530329749475425339)
            ·
              refine ⟨5923680795494624213138009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949120530329749475425339 5923680795494624213138009)
              ·
                refine ⟨4442760596620968159853507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923680795494624213138009 4442760596620968159853507)
                ·
                  refine ⟨6664140894931452239780261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442760596620968159853507 6664140894931452239780261)
                  ·
                    refine ⟨1249526417799647294958799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664140894931452239780261 1249526417799647294958799)
                    ·
                      rfl

theorem cell22_3650166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_3650166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650166 prefixEnd_3650166 := by exact prefixLift 3650166
  have htrace : WordTrace (prefixWord ++ tailWord_3650166) baseStart_3650166 baseEnd_3650166 := by
    simpa [prefixWord, tailWord_3650166, baseEnd_3650166] using wordTrace_append hprefix tailTrace_3650166
  have hstable : (prefixWord ++ tailWord_3650166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650166).length < 2 ^ (prefixWord ++ tailWord_3650166).sum := by decide
  have hdescent : baseEnd_3650166 < baseStart_3650166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650177 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3650177 : Nat := 118140960795 + 3650177 * 2 ^ 59
def prefixEnd_3650177 : Nat := 4983230072969 + 3 ^ 40 * 3650177 * 2
def baseEnd_3650177 : Nat := 1249530183324446932933765

theorem tailTrace_3650177 : CollatzResearch.WordTrace tailWord_3650177 prefixEnd_3650177 1249530183324446932933765 := by
  unfold tailWord_3650177
  simp only [CollatzResearch.WordTrace]
  refine ⟨133132892497039604445252785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88755261664693069630168523 133132892497039604445252785)
  ·
    refine ⟨99849669372779703333939589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133132892497039604445252785 99849669372779703333939589)
    ·
      refine ⟨18721813007396194375113673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99849669372779703333939589 18721813007396194375113673)
      ·
        refine ⟨14041359755547145781335255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18721813007396194375113673 14041359755547145781335255)
        ·
          refine ⟨21062039633320718672002883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14041359755547145781335255 21062039633320718672002883)
          ·
            refine ⟨31593059449981078008004325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21062039633320718672002883 31593059449981078008004325)
            ·
              refine ⟨5923698646871452126500811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31593059449981078008004325 5923698646871452126500811)
              ·
                refine ⟨8885547970307178189751217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923698646871452126500811 8885547970307178189751217)
                ·
                  refine ⟨6664160977730383642313413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8885547970307178189751217 6664160977730383642313413)
                  ·
                    refine ⟨1249530183324446932933765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664160977730383642313413 1249530183324446932933765)
                    ·
                      rfl

theorem cell22_3650177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3650177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650177 prefixEnd_3650177 := by exact prefixLift 3650177
  have htrace : WordTrace (prefixWord ++ tailWord_3650177) baseStart_3650177 baseEnd_3650177 := by
    simpa [prefixWord, tailWord_3650177, baseEnd_3650177] using wordTrace_append hprefix tailTrace_3650177
  have hstable : (prefixWord ++ tailWord_3650177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650177).length < 2 ^ (prefixWord ++ tailWord_3650177).sum := by decide
  have hdescent : baseEnd_3650177 < baseStart_3650177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650196 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3650196 : Nat := 118140960795 + 3650196 * 2 ^ 59
def prefixEnd_3650196 : Nat := 4983230072969 + 3 ^ 40 * 3650196 * 2
def baseEnd_3650196 : Nat := 1249536687412737216708707

theorem tailTrace_3650196 : CollatzResearch.WordTrace tailWord_3650196 prefixEnd_3650196 1249536687412737216708707 := by
  unfold tailWord_3650196
  simp only [CollatzResearch.WordTrace]
  refine ⟨66566792741985385345097221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88755723655980513793462961 66566792741985385345097221)
  ·
    refine ⟨12481273639122259752205729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66566792741985385345097221 12481273639122259752205729)
    ·
      refine ⟨9360955229341694814154297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12481273639122259752205729 9360955229341694814154297)
      ·
        refine ⟨7020716422006271110615723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9360955229341694814154297 7020716422006271110615723)
        ·
          refine ⟨10531074633009406665923585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020716422006271110615723 10531074633009406665923585)
          ·
            refine ⟨7898305974757054999442689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10531074633009406665923585 7898305974757054999442689)
            ·
              refine ⟨5923729481067791249582017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7898305974757054999442689 5923729481067791249582017)
              ·
                refine ⟨4442797110800843437186513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923729481067791249582017 4442797110800843437186513)
                ·
                  refine ⟨3332097833100632577889885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4442797110800843437186513 3332097833100632577889885)
                  ·
                    refine ⟨1249536687412737216708707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332097833100632577889885 1249536687412737216708707)
                    ·
                      rfl

theorem cell22_3650196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3650196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650196 prefixEnd_3650196 := by exact prefixLift 3650196
  have htrace : WordTrace (prefixWord ++ tailWord_3650196) baseStart_3650196 baseEnd_3650196 := by
    simpa [prefixWord, tailWord_3650196, baseEnd_3650196] using wordTrace_append hprefix tailTrace_3650196
  have hstable : (prefixWord ++ tailWord_3650196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650196).length < 2 ^ (prefixWord ++ tailWord_3650196).sum := by decide
  have hdescent : baseEnd_3650196 < baseStart_3650196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650205 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3650205 : Nat := 118140960795 + 3650205 * 2 ^ 59
def prefixEnd_3650205 : Nat := 4983230072969 + 3 ^ 40 * 3650205 * 2
def baseEnd_3650205 : Nat := 1249539768296664193233679

theorem tailTrace_3650205 : CollatzResearch.WordTrace tailWord_3650205 prefixEnd_3650205 1249539768296664193233679 := by
  unfold tailWord_3650205
  simp only [CollatzResearch.WordTrace]
  refine ⟨133133913740938165227272069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88755942493958776818181379 133133913740938165227272069)
  ·
    refine ⟨24962608826425905980113513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133133913740938165227272069 24962608826425905980113513)
    ·
      refine ⟨18721956619819429485085135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24962608826425905980113513 18721956619819429485085135)
      ·
        refine ⟨28082934929729144227627703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721956619819429485085135 28082934929729144227627703)
        ·
          refine ⟨42124402394593716341441555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28082934929729144227627703 42124402394593716341441555)
          ·
            refine ⟨63186603591890574512162333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42124402394593716341441555 63186603591890574512162333)
            ·
              refine ⟨23694976346958965442060875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63186603591890574512162333 23694976346958965442060875)
              ·
                refine ⟨35542464520438448163091313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23694976346958965442060875 35542464520438448163091313)
                ·
                  refine ⟨26656848390328836122318485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35542464520438448163091313 26656848390328836122318485)
                  ·
                    refine ⟨1249539768296664193233679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26656848390328836122318485 1249539768296664193233679)
                    ·
                      rfl

theorem cell22_3650205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3650205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650205 prefixEnd_3650205 := by exact prefixLift 3650205
  have htrace : WordTrace (prefixWord ++ tailWord_3650205) baseStart_3650205 baseEnd_3650205 := by
    simpa [prefixWord, tailWord_3650205, baseEnd_3650205] using wordTrace_append hprefix tailTrace_3650205
  have hstable : (prefixWord ++ tailWord_3650205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650205).length < 2 ^ (prefixWord ++ tailWord_3650205).sum := by decide
  have hdescent : baseEnd_3650205 < baseStart_3650205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650209 : List Nat := [1, 2, 3, 3, 4, 1, 1, 7]
def baseStart_3650209 : Nat := 118140960795 + 3650209 * 2 ^ 59
def prefixEnd_3650209 : Nat := 4983230072969 + 3 ^ 40 * 3650209 * 2
def baseEnd_3650209 : Nat := 138837904175378835125963

theorem tailTrace_3650209 : CollatzResearch.WordTrace tailWord_3650209 prefixEnd_3650209 138837904175378835125963 := by
  unfold tailWord_3650209
  simp only [CollatzResearch.WordTrace]
  refine ⟨133134059632923673910417681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88756039755282449273611787 133134059632923673910417681)
  ·
    refine ⟨99850544724692755432813261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133134059632923673910417681 99850544724692755432813261)
    ·
      refine ⟨37443954271759783287304973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99850544724692755432813261 37443954271759783287304973)
      ·
        refine ⟨14041482851909918732739365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37443954271759783287304973 14041482851909918732739365)
        ·
          refine ⟨2632778034733109762388631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14041482851909918732739365 2632778034733109762388631)
          ·
            refine ⟨3949167052099664643582947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632778034733109762388631 3949167052099664643582947)
            ·
              refine ⟨5923750578149496965374421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949167052099664643582947 5923750578149496965374421)
              ·
                refine ⟨138837904175378835125963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5923750578149496965374421 138837904175378835125963)
                ·
                  rfl

theorem cell22_3650209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 7].length) (baseStart_3650209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650209 prefixEnd_3650209 := by exact prefixLift 3650209
  have htrace : WordTrace (prefixWord ++ tailWord_3650209) baseStart_3650209 baseEnd_3650209 := by
    simpa [prefixWord, tailWord_3650209, baseEnd_3650209] using wordTrace_append hprefix tailTrace_3650209
  have hstable : (prefixWord ++ tailWord_3650209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650209).length < 2 ^ (prefixWord ++ tailWord_3650209).sum := by decide
  have hdescent : baseEnd_3650209 < baseStart_3650209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650252 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_3650252 : Nat := 118140960795 + 3650252 * 2 ^ 59
def prefixEnd_3650252 : Nat := 4983230072969 + 3 ^ 40 * 3650252 * 2
def baseEnd_3650252 : Nat := 1249555857357171737308535

theorem tailTrace_3650252 : CollatzResearch.WordTrace tailWord_3650252 prefixEnd_3650252 1249555857357171737308535 := by
  unfold tailWord_3650252
  simp only [CollatzResearch.WordTrace]
  refine ⟨66567813985883946127116505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88757085314511928169488673 66567813985883946127116505)
  ·
    refine ⟨49925860489412959595337379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66567813985883946127116505 49925860489412959595337379)
    ·
      refine ⟨74888790734119439393006069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49925860489412959595337379 74888790734119439393006069)
      ·
        refine ⟨7020824131323697443094319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74888790734119439393006069 7020824131323697443094319)
        ·
          refine ⟨10531236196985546164641479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020824131323697443094319 10531236196985546164641479)
          ·
            refine ⟨15796854295478319246962219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531236196985546164641479 15796854295478319246962219)
            ·
              refine ⟨23695281443217478870443329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796854295478319246962219 23695281443217478870443329)
              ·
                refine ⟨17771461082413109152832497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23695281443217478870443329 17771461082413109152832497)
                ·
                  refine ⟨13328595811809831864624373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17771461082413109152832497 13328595811809831864624373)
                  ·
                    refine ⟨1249555857357171737308535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13328595811809831864624373 1249555857357171737308535)
                    ·
                      rfl

theorem cell22_3650252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_3650252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650252 prefixEnd_3650252 := by exact prefixLift 3650252
  have htrace : WordTrace (prefixWord ++ tailWord_3650252) baseStart_3650252 baseEnd_3650252 := by
    simpa [prefixWord, tailWord_3650252, baseEnd_3650252] using wordTrace_append hprefix tailTrace_3650252
  have hstable : (prefixWord ++ tailWord_3650252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650252).length < 2 ^ (prefixWord ++ tailWord_3650252).sum := by decide
  have hdescent : baseEnd_3650252 < baseStart_3650252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650254 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_3650254 : Nat := 118140960795 + 3650254 * 2 ^ 59
def prefixEnd_3650254 : Nat := 4983230072969 + 3 ^ 40 * 3650254 * 2
def baseEnd_3650254 : Nat := 416518847332681466252843

theorem tailTrace_3650254 : CollatzResearch.WordTrace tailWord_3650254 prefixEnd_3650254 416518847332681466252843 := by
  unfold tailWord_3650254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641962614720080824475727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88757133945173764397203877 16641962614720080824475727)
  ·
    refine ⟨24962943922080121236713591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16641962614720080824475727 24962943922080121236713591)
    ·
      refine ⟨37444415883120181855070387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24962943922080121236713591 37444415883120181855070387)
      ·
        refine ⟨56166623824680272782605581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37444415883120181855070387 56166623824680272782605581)
        ·
          refine ⟨21062483934255102293477093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56166623824680272782605581 21062483934255102293477093)
          ·
            refine ⟨3949215737672831680026955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21062483934255102293477093 3949215737672831680026955)
            ·
              refine ⟨5923823606509247520040433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949215737672831680026955 5923823606509247520040433)
              ·
                refine ⟨4442867704881935640030325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923823606509247520040433 4442867704881935640030325)
                ·
                  refine ⟨416518847332681466252843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442867704881935640030325 416518847332681466252843)
                  ·
                    rfl

theorem cell22_3650254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_3650254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650254 prefixEnd_3650254 := by exact prefixLift 3650254
  have htrace : WordTrace (prefixWord ++ tailWord_3650254) baseStart_3650254 baseEnd_3650254 := by
    simpa [prefixWord, tailWord_3650254, baseEnd_3650254] using wordTrace_append hprefix tailTrace_3650254
  have hstable : (prefixWord ++ tailWord_3650254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650254).length < 2 ^ (prefixWord ++ tailWord_3650254).sum := by decide
  have hdescent : baseEnd_3650254 < baseStart_3650254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650292 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3650292 : Nat := 118140960795 + 3650292 * 2 ^ 59
def prefixEnd_3650292 : Nat := 4983230072969 + 3 ^ 40 * 3650292 * 2
def baseEnd_3650292 : Nat := 1249569550174624966308413

theorem tailTrace_3650292 : CollatzResearch.WordTrace tailWord_3650292 prefixEnd_3650292 1249569550174624966308413 := by
  unfold tailWord_3650292
  simp only [CollatzResearch.WordTrace]
  refine ⟨66568543445811489542844565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88758057927748652723792753 66568543445811489542844565)
  ·
    refine ⟨3120400474022413572320839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66568543445811489542844565 3120400474022413572320839)
    ·
      refine ⟨4680600711033620358481259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120400474022413572320839 4680600711033620358481259)
      ·
        refine ⟨7020901066550430537721889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680600711033620358481259 7020901066550430537721889)
        ·
          refine ⟨5265675799912822903291417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7020901066550430537721889 5265675799912822903291417)
          ·
            refine ⟨3949256849934617177468563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5265675799912822903291417 3949256849934617177468563)
            ·
              refine ⟨5923885274901925766202845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949256849934617177468563 5923885274901925766202845)
              ·
                refine ⟨2221456978088222162326067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5923885274901925766202845 2221456978088222162326067)
                ·
                  refine ⟨3332185467132333243489101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221456978088222162326067 3332185467132333243489101)
                  ·
                    refine ⟨1249569550174624966308413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332185467132333243489101 1249569550174624966308413)
                    ·
                      rfl

theorem cell22_3650292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3650292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650292 prefixEnd_3650292 := by exact prefixLift 3650292
  have htrace : WordTrace (prefixWord ++ tailWord_3650292) baseStart_3650292 baseEnd_3650292 := by
    simpa [prefixWord, tailWord_3650292, baseEnd_3650292] using wordTrace_append hprefix tailTrace_3650292
  have hstable : (prefixWord ++ tailWord_3650292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650292).length < 2 ^ (prefixWord ++ tailWord_3650292).sum := by decide
  have hdescent : baseEnd_3650292 < baseStart_3650292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650312 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_3650312 : Nat := 118140960795 + 3650312 * 2 ^ 59
def prefixEnd_3650312 : Nat := 4983230072969 + 3 ^ 40 * 3650312 * 2
def baseEnd_3650312 : Nat := 1249576396583351580808351

theorem tailTrace_3650312 : CollatzResearch.WordTrace tailWord_3650312 prefixEnd_3650312 1249576396583351580808351 := by
  unfold tailWord_3650312
  simp only [CollatzResearch.WordTrace]
  refine ⟨66568908175775261250708595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88758544234367015000944793 66568908175775261250708595)
  ·
    refine ⟨99853362263662891876062893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66568908175775261250708595 99853362263662891876062893)
    ·
      refine ⟨37445010848873584453523585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99853362263662891876062893 37445010848873584453523585)
      ·
        refine ⟨28083758136655188340142689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37445010848873584453523585 28083758136655188340142689)
        ·
          refine ⟨21062818602491391255107017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28083758136655188340142689 21062818602491391255107017)
          ·
            refine ⟨15797113951868543441330263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21062818602491391255107017 15797113951868543441330263)
            ·
              refine ⟨23695670927802815161995395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15797113951868543441330263 23695670927802815161995395)
              ·
                refine ⟨35543506391704222742993093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23695670927802815161995395 35543506391704222742993093)
                ·
                  refine ⟨6664407448444541764311205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35543506391704222742993093 6664407448444541764311205)
                  ·
                    refine ⟨1249576396583351580808351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664407448444541764311205 1249576396583351580808351)
                    ·
                      rfl

theorem cell22_3650312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_3650312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650312 prefixEnd_3650312 := by exact prefixLift 3650312
  have htrace : WordTrace (prefixWord ++ tailWord_3650312) baseStart_3650312 baseEnd_3650312 := by
    simpa [prefixWord, tailWord_3650312, baseEnd_3650312] using wordTrace_append hprefix tailTrace_3650312
  have hstable : (prefixWord ++ tailWord_3650312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650312).length < 2 ^ (prefixWord ++ tailWord_3650312).sum := by decide
  have hdescent : baseEnd_3650312 < baseStart_3650312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650314 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_3650314 : Nat := 118140960795 + 3650314 * 2 ^ 59
def prefixEnd_3650314 : Nat := 4983230072969 + 3 ^ 40 * 3650314 * 2
def baseEnd_3650314 : Nat := 1249577081224224242258345

theorem tailTrace_3650314 : CollatzResearch.WordTrace tailWord_3650314 prefixEnd_3650314 1249577081224224242258345 := by
  unfold tailWord_3650314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33284472324385819210747499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88758592865028851228659997 33284472324385819210747499)
  ·
    refine ⟨49926708486578728816121249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33284472324385819210747499 49926708486578728816121249)
    ·
      refine ⟨37445031364934046612090937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49926708486578728816121249 37445031364934046612090937)
      ·
        refine ⟨28083773523700534959068203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37445031364934046612090937 28083773523700534959068203)
        ·
          refine ⟨42125660285550802438602305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28083773523700534959068203 42125660285550802438602305)
          ·
            refine ⟨31594245214163101828951729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42125660285550802438602305 31594245214163101828951729)
            ·
              refine ⟨23695683910622326371713797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31594245214163101828951729 23695683910622326371713797)
              ·
                refine ⟨4442940733241686194696337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23695683910622326371713797 4442940733241686194696337)
                ·
                  refine ⟨3332205549931264646022253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4442940733241686194696337 3332205549931264646022253)
                  ·
                    refine ⟨1249577081224224242258345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332205549931264646022253 1249577081224224242258345)
                    ·
                      rfl

theorem cell22_3650314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_3650314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650314 prefixEnd_3650314 := by exact prefixLift 3650314
  have htrace : WordTrace (prefixWord ++ tailWord_3650314) baseStart_3650314 baseEnd_3650314 := by
    simpa [prefixWord, tailWord_3650314, baseEnd_3650314] using wordTrace_append hprefix tailTrace_3650314
  have hstable : (prefixWord ++ tailWord_3650314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650314).length < 2 ^ (prefixWord ++ tailWord_3650314).sum := by decide
  have hdescent : baseEnd_3650314 < baseStart_3650314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650376 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 1, 3]
def baseStart_3650376 : Nat := 118140960795 + 3650376 * 2 ^ 59
def prefixEnd_3650376 : Nat := 4983230072969 + 3 ^ 40 * 3650376 * 2
def baseEnd_3650376 : Nat := 1249598305091276747208155

theorem tailTrace_3650376 : CollatzResearch.WordTrace tailWord_3650376 prefixEnd_3650376 1249598305091276747208155 := by
  unfold tailWord_3650376
  simp only [CollatzResearch.WordTrace]
  refine ⟨66570075311659330715873491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88760100415545774287831321 66570075311659330715873491)
  ·
    refine ⟨99855112967488996073810237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66570075311659330715873491 99855112967488996073810237)
    ·
      refine ⟨37445667362808373527678839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99855112967488996073810237 37445667362808373527678839)
      ·
        refine ⟨56168501044212560291518259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37445667362808373527678839 56168501044212560291518259)
        ·
          refine ⟨84252751566318840437277389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56168501044212560291518259 84252751566318840437277389)
          ·
            refine ⟨31594781837369565163979021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84252751566318840437277389 31594781837369565163979021)
            ·
              refine ⟨11848043189013586936492133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31594781837369565163979021 11848043189013586936492133)
              ·
                refine ⟨2221508097940047550592275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11848043189013586936492133 2221508097940047550592275)
                ·
                  refine ⟨3332262146910071325888413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221508097940047550592275 3332262146910071325888413)
                  ·
                    refine ⟨1249598305091276747208155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332262146910071325888413 1249598305091276747208155)
                    ·
                      rfl

theorem cell22_3650376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_3650376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650376 prefixEnd_3650376 := by exact prefixLift 3650376
  have htrace : WordTrace (prefixWord ++ tailWord_3650376) baseStart_3650376 baseEnd_3650376 := by
    simpa [prefixWord, tailWord_3650376, baseEnd_3650376] using wordTrace_append hprefix tailTrace_3650376
  have hstable : (prefixWord ++ tailWord_3650376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650376).length < 2 ^ (prefixWord ++ tailWord_3650376).sum := by decide
  have hdescent : baseEnd_3650376 < baseStart_3650376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650466 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3650466 : Nat := 118140960795 + 3650466 * 2 ^ 59
def prefixEnd_3650466 : Nat := 4983230072969 + 3 ^ 40 * 3650466 * 2
def baseEnd_3650466 : Nat := 1249629113930546512457879

theorem tailTrace_3650466 : CollatzResearch.WordTrace tailWord_3650466 prefixEnd_3650466 1249629113930546512457879 := by
  unfold tailWord_3650466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33285858298248151700630813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88762288795328404535015501 33285858298248151700630813)
  ·
    refine ⟨12482196861843056887736555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33285858298248151700630813 12482196861843056887736555)
    ·
      refine ⟨18723295292764585331604833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12482196861843056887736555 18723295292764585331604833)
      ·
        refine ⟨14042471469573438998703625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18723295292764585331604833 14042471469573438998703625)
        ·
          refine ⟨10531853602180079249027719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14042471469573438998703625 10531853602180079249027719)
          ·
            refine ⟨15797780403270118873541579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531853602180079249027719 15797780403270118873541579)
            ·
              refine ⟨23696670604905178310312369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15797780403270118873541579 23696670604905178310312369)
              ·
                refine ⟨17772502953678883732734277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23696670604905178310312369 17772502953678883732734277)
                ·
                  refine ⟨3332344303814790699887677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17772502953678883732734277 3332344303814790699887677)
                  ·
                    refine ⟨1249629113930546512457879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332344303814790699887677 1249629113930546512457879)
                    ·
                      rfl

theorem cell22_3650466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3650466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650466 prefixEnd_3650466 := by exact prefixLift 3650466
  have htrace : WordTrace (prefixWord ++ tailWord_3650466) baseStart_3650466 baseEnd_3650466 := by
    simpa [prefixWord, tailWord_3650466, baseEnd_3650466] using wordTrace_append hprefix tailTrace_3650466
  have hstable : (prefixWord ++ tailWord_3650466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650466).length < 2 ^ (prefixWord ++ tailWord_3650466).sum := by decide
  have hdescent : baseEnd_3650466 < baseStart_3650466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650481 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3650481 : Nat := 118140960795 + 3650481 * 2 ^ 59
def prefixEnd_3650481 : Nat := 4983230072969 + 3 ^ 40 * 3650481 * 2
def baseEnd_3650481 : Nat := 1249634248737091473332833

theorem tailTrace_3650481 : CollatzResearch.WordTrace tailWord_3650481 prefixEnd_3650481 1249634248737091473332833 := by
  unfold tailWord_3650481
  simp only [CollatzResearch.WordTrace]
  refine ⟨133143980287938264364319297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88762653525292176242879531 133143980287938264364319297)
  ·
    refine ⟨99857985215953698273239473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133143980287938264364319297 99857985215953698273239473)
    ·
      refine ⟨74893488911965273704929605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99857985215953698273239473 74893488911965273704929605)
      ·
        refine ⟨14042529170993488819674301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74893488911965273704929605 14042529170993488819674301)
        ·
          refine ⟨5265948439122558307377863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14042529170993488819674301 5265948439122558307377863)
          ·
            refine ⟨7898922658683837461066795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265948439122558307377863 7898922658683837461066795)
            ·
              refine ⟨11848383988025756191600193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898922658683837461066795 11848383988025756191600193)
              ·
                refine ⟨8886287991019317143700145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11848383988025756191600193 8886287991019317143700145)
                ·
                  refine ⟨6664715993264487857775109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8886287991019317143700145 6664715993264487857775109)
                  ·
                    refine ⟨1249634248737091473332833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664715993264487857775109 1249634248737091473332833)
                    ·
                      rfl

theorem cell22_3650481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3650481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650481 prefixEnd_3650481 := by exact prefixLift 3650481
  have htrace : WordTrace (prefixWord ++ tailWord_3650481) baseStart_3650481 baseEnd_3650481 := by
    simpa [prefixWord, tailWord_3650481, baseEnd_3650481] using wordTrace_append hprefix tailTrace_3650481
  have hstable : (prefixWord ++ tailWord_3650481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650481).length < 2 ^ (prefixWord ++ tailWord_3650481).sum := by decide
  have hdescent : baseEnd_3650481 < baseStart_3650481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650500 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3650500 : Nat := 118140960795 + 3650500 * 2 ^ 59
def prefixEnd_3650500 : Nat := 4983230072969 + 3 ^ 40 * 3650500 * 2
def baseEnd_3650500 : Nat := 1249640752825381757107775

theorem tailTrace_3650500 : CollatzResearch.WordTrace tailWord_3650500 prefixEnd_3650500 1249640752825381757107775 := by
  unfold tailWord_3650500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66572336637434715304630477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88763115516579620406173969 66572336637434715304630477)
  ·
    refine ⟨24964626239038018239236429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66572336637434715304630477 24964626239038018239236429)
    ·
      refine ⟨9361734839639256839713661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24964626239038018239236429 9361734839639256839713661)
      ·
        refine ⟨3510650564864721314892623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9361734839639256839713661 3510650564864721314892623)
        ·
          refine ⟨5265975847297081972338935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510650564864721314892623 5265975847297081972338935)
          ·
            refine ⟨7898963770945622958508403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265975847297081972338935 7898963770945622958508403)
            ·
              refine ⟨11848445656418434437762605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898963770945622958508403 11848445656418434437762605)
              ·
                refine ⟨4443167121156912914160977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11848445656418434437762605 4443167121156912914160977)
                ·
                  refine ⟨3332375340867684685620733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4443167121156912914160977 3332375340867684685620733)
                  ·
                    refine ⟨1249640752825381757107775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332375340867684685620733 1249640752825381757107775)
                    ·
                      rfl

theorem cell22_3650500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3650500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650500 prefixEnd_3650500 := by exact prefixLift 3650500
  have htrace : WordTrace (prefixWord ++ tailWord_3650500) baseStart_3650500 baseEnd_3650500 := by
    simpa [prefixWord, tailWord_3650500, baseEnd_3650500] using wordTrace_append hprefix tailTrace_3650500
  have hstable : (prefixWord ++ tailWord_3650500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650500).length < 2 ^ (prefixWord ++ tailWord_3650500).sum := by decide
  have hdescent : baseEnd_3650500 < baseStart_3650500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650545 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 1, 3]
def baseStart_3650545 : Nat := 118140960795 + 3650545 * 2 ^ 59
def prefixEnd_3650545 : Nat := 4983230072969 + 3 ^ 40 * 3650545 * 2
def baseEnd_3650545 : Nat := 1249656157245016639732637

theorem tailTrace_3650545 : CollatzResearch.WordTrace tailWord_3650545 prefixEnd_3650545 1249656157245016639732637 := by
  unfold tailWord_3650545
  simp only [CollatzResearch.WordTrace]
  refine ⟨133146314559706403294649089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88764209706470935529766059 133146314559706403294649089)
  ·
    refine ⟨99859735919779802470986817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133146314559706403294649089 99859735919779802470986817)
    ·
      refine ⟨74894801939834851853240113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99859735919779802470986817 74894801939834851853240113)
      ·
        refine ⟨56171101454876138889930085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74894801939834851853240113 56171101454876138889930085)
        ·
          refine ⟨10532081522789276041861891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56171101454876138889930085 10532081522789276041861891)
          ·
            refine ⟨15798122284183914062792837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532081522789276041861891 15798122284183914062792837)
            ·
              refine ⟨2962147928284483886773657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15798122284183914062792837 2962147928284483886773657)
              ·
                refine ⟨2221610946213362915080243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962147928284483886773657 2221610946213362915080243)
                ·
                  refine ⟨3332416419320044372620365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221610946213362915080243 3332416419320044372620365)
                  ·
                    refine ⟨1249656157245016639732637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332416419320044372620365 1249656157245016639732637)
                    ·
                      rfl

theorem cell22_3650545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_3650545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650545 prefixEnd_3650545 := by exact prefixLift 3650545
  have htrace : WordTrace (prefixWord ++ tailWord_3650545) baseStart_3650545 baseEnd_3650545 := by
    simpa [prefixWord, tailWord_3650545, baseEnd_3650545] using wordTrace_append hprefix tailTrace_3650545
  have hstable : (prefixWord ++ tailWord_3650545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650545).length < 2 ^ (prefixWord ++ tailWord_3650545).sum := by decide
  have hdescent : baseEnd_3650545 < baseStart_3650545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650588 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3650588 : Nat := 118140960795 + 3650588 * 2 ^ 59
def prefixEnd_3650588 : Nat := 4983230072969 + 3 ^ 40 * 3650588 * 2
def baseEnd_3650588 : Nat := 1249670877023778860907505

theorem tailTrace_3650588 : CollatzResearch.WordTrace tailWord_3650588 prefixEnd_3650588 1249670877023778860907505 := by
  unfold tailWord_3650588
  simp only [CollatzResearch.WordTrace]
  refine ⟨66573941449275310819232209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88765255265700414425642945 66573941449275310819232209)
  ·
    refine ⟨49930456086956483114424157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66573941449275310819232209 49930456086956483114424157)
    ·
      refine ⟨18723921032608681167909059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49930456086956483114424157 18723921032608681167909059)
      ·
        refine ⟨28085881548913021751863589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18723921032608681167909059 28085881548913021751863589)
        ·
          refine ⟨5266102790421191578474423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28085881548913021751863589 5266102790421191578474423)
          ·
            refine ⟨7899154185631787367711635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266102790421191578474423 7899154185631787367711635)
            ·
              refine ⟨11848731278447681051567453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899154185631787367711635 11848731278447681051567453)
              ·
                refine ⟨4443274229417880394337795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11848731278447681051567453 4443274229417880394337795)
                ·
                  refine ⟨6664911344126820591506693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443274229417880394337795 6664911344126820591506693)
                  ·
                    refine ⟨1249670877023778860907505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664911344126820591506693 1249670877023778860907505)
                    ·
                      rfl

theorem cell22_3650588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3650588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650588 prefixEnd_3650588 := by exact prefixLift 3650588
  have htrace : WordTrace (prefixWord ++ tailWord_3650588) baseStart_3650588 baseEnd_3650588 := by
    simpa [prefixWord, tailWord_3650588, baseEnd_3650588] using wordTrace_append hprefix tailTrace_3650588
  have hstable : (prefixWord ++ tailWord_3650588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650588).length < 2 ^ (prefixWord ++ tailWord_3650588).sum := by decide
  have hdescent : baseEnd_3650588 < baseStart_3650588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650631 : List Nat := [1, 1, 4, 1, 3, 2, 4, 6]
def baseStart_3650631 : Nat := 118140960795 + 3650631 * 2 ^ 59
def prefixEnd_3650631 : Nat := 4983230072969 + 3 ^ 40 * 3650631 * 2
def baseEnd_3650631 : Nat := 138853955200282342453597

theorem tailTrace_3650631 : CollatzResearch.WordTrace tailWord_3650631 prefixEnd_3650631 138853955200282342453597 := by
  unfold tailWord_3650631
  simp only [CollatzResearch.WordTrace]
  refine ⟨133149451237394839982279747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88766300824929893321519831 133149451237394839982279747)
  ·
    refine ⟨199724176856092259973419621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133149451237394839982279747 199724176856092259973419621)
    ·
      refine ⟨37448283160517298745016179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199724176856092259973419621 37448283160517298745016179)
      ·
        refine ⟨56172424740775948117524269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37448283160517298745016179 56172424740775948117524269)
        ·
          refine ⟨21064659277790980544071601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56172424740775948117524269 21064659277790980544071601)
          ·
            refine ⟨15798494458343235408053701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21064659277790980544071601 15798494458343235408053701)
            ·
              refine ⟨2962217710939356639010069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15798494458343235408053701 2962217710939356639010069)
              ·
                refine ⟨138853955200282342453597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2962217710939356639010069 138853955200282342453597)
                ·
                  rfl

theorem cell22_3650631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 6].length) (baseStart_3650631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650631 prefixEnd_3650631 := by exact prefixLift 3650631
  have htrace : WordTrace (prefixWord ++ tailWord_3650631) baseStart_3650631 baseEnd_3650631 := by
    simpa [prefixWord, tailWord_3650631, baseEnd_3650631] using wordTrace_append hprefix tailTrace_3650631
  have hstable : (prefixWord ++ tailWord_3650631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650631).length < 2 ^ (prefixWord ++ tailWord_3650631).sum := by decide
  have hdescent : baseEnd_3650631 < baseStart_3650631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650654 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3650654 : Nat := 118140960795 + 3650654 * 2 ^ 59
def prefixEnd_3650654 : Nat := 4983230072969 + 3 ^ 40 * 3650654 * 2
def baseEnd_3650654 : Nat := 416564490057525562919101

theorem tailTrace_3650654 : CollatzResearch.WordTrace tailWord_3650654 prefixEnd_3650654 416564490057525562919101 := by
  unfold tailWord_3650654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643786264538939363795877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88766860077541009940244677 16643786264538939363795877)
  ·
    refine ⟨3120709924601051130711727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16643786264538939363795877 3120709924601051130711727)
    ·
      refine ⟨4681064886901576696067591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120709924601051130711727 4681064886901576696067591)
      ·
        refine ⟨7021597330352365044101387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681064886901576696067591 7021597330352365044101387)
        ·
          refine ⟨10532395995528547566152081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021597330352365044101387 10532395995528547566152081)
          ·
            refine ⟨7899296996646410674614061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532395995528547566152081 7899296996646410674614061)
            ·
              refine ⟨2962236373742404002980273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7899296996646410674614061 2962236373742404002980273)
              ·
                refine ⟨2221677280306803002235205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962236373742404002980273 2221677280306803002235205)
                ·
                  refine ⟨416564490057525562919101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221677280306803002235205 416564490057525562919101)
                  ·
                    rfl

theorem cell22_3650654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3650654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650654 prefixEnd_3650654 := by exact prefixLift 3650654
  have htrace : WordTrace (prefixWord ++ tailWord_3650654) baseStart_3650654 baseEnd_3650654 := by
    simpa [prefixWord, tailWord_3650654, baseEnd_3650654] using wordTrace_append hprefix tailTrace_3650654
  have hstable : (prefixWord ++ tailWord_3650654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650654).length < 2 ^ (prefixWord ++ tailWord_3650654).sum := by decide
  have hdescent : baseEnd_3650654 < baseStart_3650654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650663 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3650663 : Nat := 118140960795 + 3650663 * 2 ^ 59
def prefixEnd_3650663 : Nat := 4983230072969 + 3 ^ 40 * 3650663 * 2
def baseEnd_3650663 : Nat := 1249696551056503665282275

theorem tailTrace_3650663 : CollatzResearch.WordTrace tailWord_3650663 prefixEnd_3650663 1249696551056503665282275 := by
  unfold tailWord_3650663
  simp only [CollatzResearch.WordTrace]
  refine ⟨133150618373278909447444643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88767078915519272964963095 133150618373278909447444643)
  ·
    refine ⟨199725927559918364171166965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133150618373278909447444643 199725927559918364171166965)
    ·
      refine ⟨18724305708742346641046903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199725927559918364171166965 18724305708742346641046903)
      ·
        refine ⟨28086458563113519961570355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18724305708742346641046903 28086458563113519961570355)
        ·
          refine ⟨42129687844670279942355533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28086458563113519961570355 42129687844670279942355533)
          ·
            refine ⟨15798632941751354978383325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42129687844670279942355533 15798632941751354978383325)
            ·
              refine ⟨5924487353156758116893747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15798632941751354978383325 5924487353156758116893747)
              ·
                refine ⟨8886731029735137175340621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5924487353156758116893747 8886731029735137175340621)
                ·
                  refine ⟨3332524136150676440752733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8886731029735137175340621 3332524136150676440752733)
                  ·
                    refine ⟨1249696551056503665282275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332524136150676440752733 1249696551056503665282275)
                    ·
                      rfl

theorem cell22_3650663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3650663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650663 prefixEnd_3650663 := by exact prefixLift 3650663
  have htrace : WordTrace (prefixWord ++ tailWord_3650663) baseStart_3650663 baseEnd_3650663 := by
    simpa [prefixWord, tailWord_3650663, baseEnd_3650663] using wordTrace_append hprefix tailTrace_3650663
  have hstable : (prefixWord ++ tailWord_3650663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650663).length < 2 ^ (prefixWord ++ tailWord_3650663).sum := by decide
  have hdescent : baseEnd_3650663 < baseStart_3650663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650704 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_3650704 : Nat := 118140960795 + 3650704 * 2 ^ 59
def prefixEnd_3650704 : Nat := 4983230072969 + 3 ^ 40 * 3650704 * 2
def baseEnd_3650704 : Nat := 416570195398131075002383

theorem tailTrace_3650704 : CollatzResearch.WordTrace tailWord_3650704 prefixEnd_3650704 416570195398131075002383 := by
  unfold tailWord_3650704
  simp only [CollatzResearch.WordTrace]
  refine ⟨66576056883065186724843583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88768075844086915633124777 66576056883065186724843583)
  ·
    refine ⟨99864085324597780087265375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66576056883065186724843583 99864085324597780087265375)
    ·
      refine ⟨149796127986896670130898063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99864085324597780087265375 149796127986896670130898063)
      ·
        refine ⟨224694191980345005196347095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149796127986896670130898063 224694191980345005196347095)
        ·
          refine ⟨337041287970517507794520643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224694191980345005196347095 337041287970517507794520643)
          ·
            refine ⟨505561931955776261691780965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337041287970517507794520643 505561931955776261691780965)
            ·
              refine ⟨94792862241708049067208931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 505561931955776261691780965 94792862241708049067208931)
              ·
                refine ⟨142189293362562073600813397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94792862241708049067208931 142189293362562073600813397)
                ·
                  refine ⟨416570195398131075002383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 142189293362562073600813397 416570195398131075002383)
                  ·
                    rfl

theorem cell22_3650704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_3650704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650704 prefixEnd_3650704 := by exact prefixLift 3650704
  have htrace : WordTrace (prefixWord ++ tailWord_3650704) baseStart_3650704 baseEnd_3650704 := by
    simpa [prefixWord, tailWord_3650704, baseEnd_3650704] using wordTrace_append hprefix tailTrace_3650704
  have hstable : (prefixWord ++ tailWord_3650704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650704).length < 2 ^ (prefixWord ++ tailWord_3650704).sum := by decide
  have hdescent : baseEnd_3650704 < baseStart_3650704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650714 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_3650714 : Nat := 118140960795 + 3650714 * 2 ^ 59
def prefixEnd_3650714 : Nat := 4983230072969 + 3 ^ 40 * 3650714 * 2
def baseEnd_3650714 : Nat := 1249714009398756532257119

theorem tailTrace_3650714 : CollatzResearch.WordTrace tailWord_3650714 prefixEnd_3650714 1249714009398756532257119 := by
  unfold tailWord_3650714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33288119624023536289387799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88768318997396096771700797 33288119624023536289387799)
  ·
    refine ⟨49932179436035304434081699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33288119624023536289387799 49932179436035304434081699)
    ·
      refine ⟨74898269154052956651122549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49932179436035304434081699 74898269154052956651122549)
      ·
        refine ⟨7021712733192464686042739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74898269154052956651122549 7021712733192464686042739)
        ·
          refine ⟨10532569099788697029064109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021712733192464686042739 10532569099788697029064109)
          ·
            refine ⟨3949713412420761385899041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10532569099788697029064109 3949713412420761385899041)
            ·
              refine ⟨2962285059315571039424281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949713412420761385899041 2962285059315571039424281)
              ·
                refine ⟨2221713794486678279568211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962285059315571039424281 2221713794486678279568211)
                ·
                  refine ⟨3332570691730017419352317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221713794486678279568211 3332570691730017419352317)
                  ·
                    refine ⟨1249714009398756532257119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332570691730017419352317 1249714009398756532257119)
                    ·
                      rfl

theorem cell22_3650714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_3650714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650714 prefixEnd_3650714 := by exact prefixLift 3650714
  have htrace : WordTrace (prefixWord ++ tailWord_3650714) baseStart_3650714 baseEnd_3650714 := by
    simpa [prefixWord, tailWord_3650714, baseEnd_3650714] using wordTrace_append hprefix tailTrace_3650714
  have hstable : (prefixWord ++ tailWord_3650714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650714).length < 2 ^ (prefixWord ++ tailWord_3650714).sum := by decide
  have hdescent : baseEnd_3650714 < baseStart_3650714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650721 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 6]
def baseStart_3650721 : Nat := 118140960795 + 3650721 * 2 ^ 59
def prefixEnd_3650721 : Nat := 4983230072969 + 3 ^ 40 * 3650721 * 2
def baseEnd_3650721 : Nat := 416572135213936949110699

theorem tailTrace_3650721 : CollatzResearch.WordTrace tailWord_3650721 prefixEnd_3650721 416572135213936949110699 := by
  unfold tailWord_3650721
  simp only [CollatzResearch.WordTrace]
  refine ⟨133152733807068785353056017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88768489204712523568704011 133152733807068785353056017)
  ·
    refine ⟨99864550355301589014792013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133152733807068785353056017 99864550355301589014792013)
    ·
      refine ⟨37449206383238095880547005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99864550355301589014792013 37449206383238095880547005)
      ·
        refine ⟨14043452393714285955205127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37449206383238095880547005 14043452393714285955205127)
        ·
          refine ⟨21065178590571428932807691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14043452393714285955205127 21065178590571428932807691)
          ·
            refine ⟨31597767885857143399211537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21065178590571428932807691 31597767885857143399211537)
            ·
              refine ⟨23698325914392857549408653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31597767885857143399211537 23698325914392857549408653)
              ·
                refine ⟨8886872217897321581028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23698325914392857549408653 8886872217897321581028245)
                ·
                  refine ⟨416572135213936949110699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8886872217897321581028245 416572135213936949110699)
                  ·
                    rfl

theorem cell22_3650721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_3650721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650721 prefixEnd_3650721 := by exact prefixLift 3650721
  have htrace : WordTrace (prefixWord ++ tailWord_3650721) baseStart_3650721 baseEnd_3650721 := by
    simpa [prefixWord, tailWord_3650721, baseEnd_3650721] using wordTrace_append hprefix tailTrace_3650721
  have hstable : (prefixWord ++ tailWord_3650721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650721).length < 2 ^ (prefixWord ++ tailWord_3650721).sum := by decide
  have hdescent : baseEnd_3650721 < baseStart_3650721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650845 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 5]
def baseStart_3650845 : Nat := 118140960795 + 3650845 * 2 ^ 59
def prefixEnd_3650845 : Nat := 4983230072969 + 3 ^ 40 * 3650845 * 2
def baseEnd_3650845 : Nat := 416586284458638619077239

theorem tailTrace_3650845 : CollatzResearch.WordTrace tailWord_3650845 prefixEnd_3650845 416586284458638619077239 := by
  unfold tailWord_3650845
  simp only [CollatzResearch.WordTrace]
  refine ⟨133157256458619554530569989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88771504305746369687046659 133157256458619554530569989)
  ·
    refine ⟨24966985585991166474481873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133157256458619554530569989 24966985585991166474481873)
    ·
      refine ⟨18725239189493374855861405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24966985585991166474481873 18725239189493374855861405)
      ·
        refine ⟨7021964696060015570948027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18725239189493374855861405 7021964696060015570948027)
        ·
          refine ⟨10532947044090023356422041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021964696060015570948027 10532947044090023356422041)
          ·
            refine ⟨7899710283067517517316531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532947044090023356422041 7899710283067517517316531)
            ·
              refine ⟨11849565424601276275974797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899710283067517517316531 11849565424601276275974797)
              ·
                refine ⟨4443587034225478603490549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11849565424601276275974797 4443587034225478603490549)
                ·
                  refine ⟨416586284458638619077239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4443587034225478603490549 416586284458638619077239)
                  ·
                    rfl

theorem cell22_3650845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_3650845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650845 prefixEnd_3650845 := by exact prefixLift 3650845
  have htrace : WordTrace (prefixWord ++ tailWord_3650845) baseStart_3650845 baseEnd_3650845 := by
    simpa [prefixWord, tailWord_3650845, baseEnd_3650845] using wordTrace_append hprefix tailTrace_3650845
  have hstable : (prefixWord ++ tailWord_3650845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650845).length < 2 ^ (prefixWord ++ tailWord_3650845).sum := by decide
  have hdescent : baseEnd_3650845 < baseStart_3650845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650905 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_3650905 : Nat := 118140960795 + 3650905 * 2 ^ 59
def prefixEnd_3650905 : Nat := 4983230072969 + 3 ^ 40 * 3650905 * 2
def baseEnd_3650905 : Nat := 1249779392602095700731533

theorem tailTrace_3650905 : CollatzResearch.WordTrace tailWord_3650905 prefixEnd_3650905 1249779392602095700731533 := by
  unfold tailWord_3650905
  simp only [CollatzResearch.WordTrace]
  refine ⟨133159444838402184777754169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88772963225601456518502779 133159444838402184777754169)
  ·
    refine ⟨99869583628801638583315627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133159444838402184777754169 99869583628801638583315627)
    ·
      refine ⟨149804375443202457874973441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99869583628801638583315627 149804375443202457874973441)
      ·
        refine ⟨112353281582401843406230081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149804375443202457874973441 112353281582401843406230081)
        ·
          refine ⟨84264961186801382554672561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112353281582401843406230081 84264961186801382554672561)
          ·
            refine ⟨63198720890101036916004421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84264961186801382554672561 63198720890101036916004421)
            ·
              refine ⟨11849760166893944421750829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63198720890101036916004421 11849760166893944421750829)
              ·
                refine ⟨4443660062585229158156561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11849760166893944421750829 4443660062585229158156561)
                ·
                  refine ⟨3332745046938921868617421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4443660062585229158156561 3332745046938921868617421)
                  ·
                    refine ⟨1249779392602095700731533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332745046938921868617421 1249779392602095700731533)
                    ·
                      rfl

theorem cell22_3650905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_3650905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650905 prefixEnd_3650905 := by exact prefixLift 3650905
  have htrace : WordTrace (prefixWord ++ tailWord_3650905) baseStart_3650905 baseEnd_3650905 := by
    simpa [prefixWord, tailWord_3650905, baseEnd_3650905] using wordTrace_append hprefix tailTrace_3650905
  have hstable : (prefixWord ++ tailWord_3650905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650905).length < 2 ^ (prefixWord ++ tailWord_3650905).sum := by decide
  have hdescent : baseEnd_3650905 < baseStart_3650905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650920 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3650920 : Nat := 118140960795 + 3650920 * 2 ^ 59
def prefixEnd_3650920 : Nat := 4983230072969 + 3 ^ 40 * 3650920 * 2
def baseEnd_3650920 : Nat := 1249784527408640661606487

theorem tailTrace_3650920 : CollatzResearch.WordTrace tailWord_3650920 prefixEnd_3650920 1249784527408640661606487 := by
  unfold tailWord_3650920
  simp only [CollatzResearch.WordTrace]
  refine ⟨66579995966673921169775107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88773327955565228226366809 66579995966673921169775107)
  ·
    refine ⟨99869993950010881754662661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66579995966673921169775107 99869993950010881754662661)
    ·
      refine ⟨18725623865627040328999249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99869993950010881754662661 18725623865627040328999249)
      ·
        refine ⟨14044217899220280246749437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18725623865627040328999249 14044217899220280246749437)
        ·
          refine ⟨5266581712207605092531039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14044217899220280246749437 5266581712207605092531039)
          ·
            refine ⟨7899872568311407638796559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266581712207605092531039 7899872568311407638796559)
            ·
              refine ⟨11849808852467111458194839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899872568311407638796559 11849808852467111458194839)
              ·
                refine ⟨17774713278700667187292259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11849808852467111458194839 17774713278700667187292259)
                ·
                  refine ⟨26662069918051000780938389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17774713278700667187292259 26662069918051000780938389)
                  ·
                    refine ⟨1249784527408640661606487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26662069918051000780938389 1249784527408640661606487)
                    ·
                      rfl

theorem cell22_3650920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3650920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650920 prefixEnd_3650920 := by exact prefixLift 3650920
  have htrace : WordTrace (prefixWord ++ tailWord_3650920) baseStart_3650920 baseEnd_3650920 := by
    simpa [prefixWord, tailWord_3650920, baseEnd_3650920] using wordTrace_append hprefix tailTrace_3650920
  have hstable : (prefixWord ++ tailWord_3650920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650920).length < 2 ^ (prefixWord ++ tailWord_3650920).sum := by decide
  have hdescent : baseEnd_3650920 < baseStart_3650920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650926 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3650926 : Nat := 118140960795 + 3650926 * 2 ^ 59
def prefixEnd_3650926 : Nat := 4983230072969 + 3 ^ 40 * 3650926 * 2
def baseEnd_3650926 : Nat := 1249786581331258645956469

theorem tailTrace_3650926 : CollatzResearch.WordTrace tailWord_3650926 prefixEnd_3650926 1249786581331258645956469 := by
  unfold tailWord_3650926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645026346415763170533579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88773473847550736909512421 16645026346415763170533579)
  ·
    refine ⟨24967539519623644755800369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16645026346415763170533579 24967539519623644755800369)
    ·
      refine ⟨18725654639717733566850277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24967539519623644755800369 18725654639717733566850277)
      ·
        refine ⟨3511060244947075043784427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18725654639717733566850277 3511060244947075043784427)
        ·
          refine ⟨5266590367420612565676641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511060244947075043784427 5266590367420612565676641)
          ·
            refine ⟨3949942775565459424257481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5266590367420612565676641 3949942775565459424257481)
            ·
              refine ⟨2962457081674094568193111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949942775565459424257481 2962457081674094568193111)
              ·
                refine ⟨4443685622511141852289667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962457081674094568193111 4443685622511141852289667)
                ·
                  refine ⟨6665528433766712778434501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443685622511141852289667 6665528433766712778434501)
                  ·
                    refine ⟨1249786581331258645956469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665528433766712778434501 1249786581331258645956469)
                    ·
                      rfl

theorem cell22_3650926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3650926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3650926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3650926 prefixEnd_3650926 := by exact prefixLift 3650926
  have htrace : WordTrace (prefixWord ++ tailWord_3650926) baseStart_3650926 baseEnd_3650926 := by
    simpa [prefixWord, tailWord_3650926, baseEnd_3650926] using wordTrace_append hprefix tailTrace_3650926
  have hstable : (prefixWord ++ tailWord_3650926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650926).length < 2 ^ (prefixWord ++ tailWord_3650926).sum := by decide
  have hdescent : baseEnd_3650926 < baseStart_3650926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651001 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 1, 3]
def baseStart_3651001 : Nat := 118140960795 + 3651001 * 2 ^ 59
def prefixEnd_3651001 : Nat := 4983230072969 + 3 ^ 40 * 3651001 * 2
def baseEnd_3651001 : Nat := 1249812255363983450331239

theorem tailTrace_3651001 : CollatzResearch.WordTrace tailWord_3651001 prefixEnd_3651001 1249812255363983450331239 := by
  unfold tailWord_3651001
  simp only [CollatzResearch.WordTrace]
  refine ⟨133162946246054393173248857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88775297497369595448832571 133162946246054393173248857)
  ·
    refine ⟨99872209684540794879936643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133162946246054393173248857 99872209684540794879936643)
    ·
      refine ⟨149808314526811192319904965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99872209684540794879936643 149808314526811192319904965)
      ·
        refine ⟨28089058973777098559982181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149808314526811192319904965 28089058973777098559982181)
        ·
          refine ⟨5266698557583205979996659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28089058973777098559982181 5266698557583205979996659)
          ·
            refine ⟨7900047836374808969994989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266698557583205979996659 7900047836374808969994989)
            ·
              refine ⟨2962517938640553363748121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7900047836374808969994989 2962517938640553363748121)
              ·
                refine ⟨2221888453980415022811091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962517938640553363748121 2221888453980415022811091)
                ·
                  refine ⟨3332832680970622534216637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221888453980415022811091 3332832680970622534216637)
                  ·
                    refine ⟨1249812255363983450331239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332832680970622534216637 1249812255363983450331239)
                    ·
                      rfl

theorem cell22_3651001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_3651001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651001 prefixEnd_3651001 := by exact prefixLift 3651001
  have htrace : WordTrace (prefixWord ++ tailWord_3651001) baseStart_3651001 baseEnd_3651001 := by
    simpa [prefixWord, tailWord_3651001, baseEnd_3651001] using wordTrace_append hprefix tailTrace_3651001
  have hstable : (prefixWord ++ tailWord_3651001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651001).length < 2 ^ (prefixWord ++ tailWord_3651001).sum := by decide
  have hdescent : baseEnd_3651001 < baseStart_3651001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651040 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_3651040 : Nat := 118140960795 + 3651040 * 2 ^ 59
def prefixEnd_3651040 : Nat := 4983230072969 + 3 ^ 40 * 3651040 * 2
def baseEnd_3651040 : Nat := 1249825605861000348606119

theorem tailTrace_3651040 : CollatzResearch.WordTrace tailWord_3651040 prefixEnd_3651040 1249825605861000348606119 := by
  unfold tailWord_3651040
  simp only [CollatzResearch.WordTrace]
  refine ⟨66582184346456551416959287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88776245795275401889279049 66582184346456551416959287)
  ·
    refine ⟨99873276519684827125438931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66582184346456551416959287 99873276519684827125438931)
    ·
      refine ⟨149809914779527240688158397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99873276519684827125438931 149809914779527240688158397)
      ·
        refine ⟨56178718042322715258059399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149809914779527240688158397 56178718042322715258059399)
        ·
          refine ⟨84268077063484072887089099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56178718042322715258059399 84268077063484072887089099)
          ·
            refine ⟨126402115595226109330633649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84268077063484072887089099 126402115595226109330633649)
            ·
              refine ⟨94801586696419581997975237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126402115595226109330633649 94801586696419581997975237)
              ·
                refine ⟨17775297505578671624620357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94801586696419581997975237 17775297505578671624620357)
                ·
                  refine ⟨3332868282296000929616317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17775297505578671624620357 3332868282296000929616317)
                  ·
                    refine ⟨1249825605861000348606119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332868282296000929616317 1249825605861000348606119)
                    ·
                      rfl

theorem cell22_3651040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_3651040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651040 prefixEnd_3651040 := by exact prefixLift 3651040
  have htrace : WordTrace (prefixWord ++ tailWord_3651040) baseStart_3651040 baseEnd_3651040 := by
    simpa [prefixWord, tailWord_3651040, baseEnd_3651040] using wordTrace_append hprefix tailTrace_3651040
  have hstable : (prefixWord ++ tailWord_3651040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651040).length < 2 ^ (prefixWord ++ tailWord_3651040).sum := by decide
  have hdescent : baseEnd_3651040 < baseStart_3651040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651055 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 2, 4]
def baseStart_3651055 : Nat := 118140960795 + 3651055 * 2 ^ 59
def prefixEnd_3651055 : Nat := 4983230072969 + 3 ^ 40 * 3651055 * 2
def baseEnd_3651055 : Nat := 1249830740667545309481073

theorem tailTrace_3651055 : CollatzResearch.WordTrace tailWord_3651055 prefixEnd_3651055 1249830740667545309481073 := by
  unfold tailWord_3651055
  simp only [CollatzResearch.WordTrace]
  refine ⟨133164915787858760395714619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88776610525239173597143079 133164915787858760395714619)
  ·
    refine ⟨199747373681788140593571929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133164915787858760395714619 199747373681788140593571929)
    ·
      refine ⟨149810530261341105445178947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199747373681788140593571929 149810530261341105445178947)
      ·
        refine ⟨224715795392011658167768421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149810530261341105445178947 224715795392011658167768421)
        ·
          refine ⟨42134211636002185906456579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224715795392011658167768421 42134211636002185906456579)
          ·
            refine ⟨63201317454003278859684869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42134211636002185906456579 63201317454003278859684869)
            ·
              refine ⟨11850247022625614786190913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63201317454003278859684869 11850247022625614786190913)
              ·
                refine ⟨8887685266969211089643185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11850247022625614786190913 8887685266969211089643185)
                ·
                  refine ⟨6665763950226908317232389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887685266969211089643185 6665763950226908317232389)
                  ·
                    refine ⟨1249830740667545309481073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665763950226908317232389 1249830740667545309481073)
                    ·
                      rfl

theorem cell22_3651055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_3651055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651055 prefixEnd_3651055 := by exact prefixLift 3651055
  have htrace : WordTrace (prefixWord ++ tailWord_3651055) baseStart_3651055 baseEnd_3651055 := by
    simpa [prefixWord, tailWord_3651055, baseEnd_3651055] using wordTrace_append hprefix tailTrace_3651055
  have hstable : (prefixWord ++ tailWord_3651055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651055).length < 2 ^ (prefixWord ++ tailWord_3651055).sum := by decide
  have hdescent : baseEnd_3651055 < baseStart_3651055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651057 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_3651057 : Nat := 118140960795 + 3651057 * 2 ^ 59
def prefixEnd_3651057 : Nat := 4983230072969 + 3 ^ 40 * 3651057 * 2
def baseEnd_3651057 : Nat := 1249831425308417970931067

theorem tailTrace_3651057 : CollatzResearch.WordTrace tailWord_3651057 prefixEnd_3651057 1249831425308417970931067 := by
  unfold tailWord_3651057
  simp only [CollatzResearch.WordTrace]
  refine ⟨133164988733851514737287425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88776659155901009824858283 133164988733851514737287425)
  ·
    refine ⟨99873741550388636052965569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133164988733851514737287425 99873741550388636052965569)
    ·
      refine ⟨74905306162791477039724177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99873741550388636052965569 74905306162791477039724177)
      ·
        refine ⟨56178979622093607779793133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74905306162791477039724177 56178979622093607779793133)
        ·
          refine ⟨21067117358285102917422425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56178979622093607779793133 21067117358285102917422425)
          ·
            refine ⟨15800338018713827188066819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21067117358285102917422425 15800338018713827188066819)
            ·
              refine ⟨23700507028070740782100229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15800338018713827188066819 23700507028070740782100229)
              ·
                refine ⟨4443845067763263896643793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23700507028070740782100229 4443845067763263896643793)
                ·
                  refine ⟨3332883800822447922482845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4443845067763263896643793 3332883800822447922482845)
                  ·
                    refine ⟨1249831425308417970931067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3332883800822447922482845 1249831425308417970931067)
                    ·
                      rfl

theorem cell22_3651057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_3651057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651057 prefixEnd_3651057 := by exact prefixLift 3651057
  have htrace : WordTrace (prefixWord ++ tailWord_3651057) baseStart_3651057 baseEnd_3651057 := by
    simpa [prefixWord, tailWord_3651057, baseEnd_3651057] using wordTrace_append hprefix tailTrace_3651057
  have hstable : (prefixWord ++ tailWord_3651057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651057).length < 2 ^ (prefixWord ++ tailWord_3651057).sum := by decide
  have hdescent : baseEnd_3651057 < baseStart_3651057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651074 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3651074 : Nat := 118140960795 + 3651074 * 2 ^ 59
def prefixEnd_3651074 : Nat := 4983230072969 + 3 ^ 40 * 3651074 * 2
def baseEnd_3651074 : Nat := 1249837244755835593256015

theorem tailTrace_3651074 : CollatzResearch.WordTrace tailWord_3651074 prefixEnd_3651074 1249837244755835593256015 := by
  unfold tailWord_3651074
  simp only [CollatzResearch.WordTrace]
  refine ⟨33291402193697481660164069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88777072516526617760437517 33291402193697481660164069)
  ·
    refine ⟨6242137911318277811280763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33291402193697481660164069 6242137911318277811280763)
    ·
      refine ⟨9363206866977416716921145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242137911318277811280763 9363206866977416716921145)
      ·
        refine ⟨7022405150233062537690859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9363206866977416716921145 7022405150233062537690859)
        ·
          refine ⟨10533607725349593806536289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022405150233062537690859 10533607725349593806536289)
          ·
            refine ⟨7900205794012195354902217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533607725349593806536289 7900205794012195354902217)
            ·
              refine ⟨5925154345509146516176663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900205794012195354902217 5925154345509146516176663)
              ·
                refine ⟨8887731518263719774264995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925154345509146516176663 8887731518263719774264995)
                ·
                  refine ⟨13331597277395579661397493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8887731518263719774264995 13331597277395579661397493)
                  ·
                    refine ⟨1249837244755835593256015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13331597277395579661397493 1249837244755835593256015)
                    ·
                      rfl

theorem cell22_3651074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3651074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651074 prefixEnd_3651074 := by exact prefixLift 3651074
  have htrace : WordTrace (prefixWord ++ tailWord_3651074) baseStart_3651074 baseEnd_3651074 := by
    simpa [prefixWord, tailWord_3651074, baseEnd_3651074] using wordTrace_append hprefix tailTrace_3651074
  have hstable : (prefixWord ++ tailWord_3651074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651074).length < 2 ^ (prefixWord ++ tailWord_3651074).sum := by decide
  have hdescent : baseEnd_3651074 < baseStart_3651074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651130 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_3651130 : Nat := 118140960795 + 3651130 * 2 ^ 59
def prefixEnd_3651130 : Nat := 4983230072969 + 3 ^ 40 * 3651130 * 2
def baseEnd_3651130 : Nat := 1249856414700270113855843

theorem tailTrace_3651130 : CollatzResearch.WordTrace tailWord_3651130 prefixEnd_3651130 1249856414700270113855843 := by
  unfold tailWord_3651130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33291912815646762051173711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88778434175058032136463229 33291912815646762051173711)
  ·
    refine ⟨49937869223470143076760567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33291912815646762051173711 49937869223470143076760567)
    ·
      refine ⟨74906803835205214615140851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49937869223470143076760567 74906803835205214615140851)
      ·
        refine ⟨112360205752807821922711277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74906803835205214615140851 112360205752807821922711277)
        ·
          refine ⟨42135077157302933221016729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112360205752807821922711277 42135077157302933221016729)
          ·
            refine ⟨31601307867977199915762547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42135077157302933221016729 31601307867977199915762547)
            ·
              refine ⟨47401961801965799873643821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31601307867977199915762547 47401961801965799873643821)
              ·
                refine ⟨17775735675737174952616433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47401961801965799873643821 17775735675737174952616433)
                ·
                  refine ⟨13331801756802881214462325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17775735675737174952616433 13331801756802881214462325)
                  ·
                    refine ⟨1249856414700270113855843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13331801756802881214462325 1249856414700270113855843)
                    ·
                      rfl

theorem cell22_3651130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_3651130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651130 prefixEnd_3651130 := by exact prefixLift 3651130
  have htrace : WordTrace (prefixWord ++ tailWord_3651130) baseStart_3651130 baseEnd_3651130 := by
    simpa [prefixWord, tailWord_3651130, baseEnd_3651130] using wordTrace_append hprefix tailTrace_3651130
  have hstable : (prefixWord ++ tailWord_3651130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651130).length < 2 ^ (prefixWord ++ tailWord_3651130).sum := by decide
  have hdescent : baseEnd_3651130 < baseStart_3651130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651145 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_3651145 : Nat := 118140960795 + 3651145 * 2 ^ 59
def prefixEnd_3651145 : Nat := 4983230072969 + 3 ^ 40 * 3651145 * 2
def baseEnd_3651145 : Nat := 1249861549506815074730797

theorem tailTrace_3651145 : CollatzResearch.WordTrace tailWord_3651145 prefixEnd_3651145 1249861549506815074730797 := by
  unfold tailWord_3651145
  simp only [CollatzResearch.WordTrace]
  refine ⟨133168198357532705766490889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88778798905021803844327259 133168198357532705766490889)
  ·
    refine ⟨99876148768149529324868167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133168198357532705766490889 99876148768149529324868167)
    ·
      refine ⟨149814223152224293987302251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99876148768149529324868167 149814223152224293987302251)
      ·
        refine ⟨224721334728336440980953377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149814223152224293987302251 224721334728336440980953377)
        ·
          refine ⟨168541001046252330735715033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224721334728336440980953377 168541001046252330735715033)
          ·
            refine ⟨126405750784689248051786275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168541001046252330735715033 126405750784689248051786275)
            ·
              refine ⟨189608626177033872077679413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126405750784689248051786275 189608626177033872077679413)
              ·
                refine ⟨17775808704096925507282445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189608626177033872077679413 17775808704096925507282445)
                ·
                  refine ⟨6665928264036347065230917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17775808704096925507282445 6665928264036347065230917)
                  ·
                    refine ⟨1249861549506815074730797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665928264036347065230917 1249861549506815074730797)
                    ·
                      rfl

theorem cell22_3651145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_3651145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651145 prefixEnd_3651145 := by exact prefixLift 3651145
  have htrace : WordTrace (prefixWord ++ tailWord_3651145) baseStart_3651145 baseEnd_3651145 := by
    simpa [prefixWord, tailWord_3651145, baseEnd_3651145] using wordTrace_append hprefix tailTrace_3651145
  have hstable : (prefixWord ++ tailWord_3651145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651145).length < 2 ^ (prefixWord ++ tailWord_3651145).sum := by decide
  have hdescent : baseEnd_3651145 < baseStart_3651145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651177 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 4]
def baseStart_3651177 : Nat := 118140960795 + 3651177 * 2 ^ 59
def prefixEnd_3651177 : Nat := 4983230072969 + 3 ^ 40 * 3651177 * 2
def baseEnd_3651177 : Nat := 416624167920259219310233

theorem tailTrace_3651177 : CollatzResearch.WordTrace tailWord_3651177 prefixEnd_3651177 416624167920259219310233 := by
  unfold tailWord_3651177
  simp only [CollatzResearch.WordTrace]
  refine ⟨133169365493416775231655785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88779576995611183487770523 133169365493416775231655785)
  ·
    refine ⟨99877024120062581423741839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133169365493416775231655785 99877024120062581423741839)
    ·
      refine ⟨149815536180093872135612759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99877024120062581423741839 149815536180093872135612759)
      ·
        refine ⟨224723304270140808203419139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149815536180093872135612759 224723304270140808203419139)
        ·
          refine ⟨337084956405211212305128709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224723304270140808203419139 337084956405211212305128709)
          ·
            refine ⟨63203429325977102307211633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337084956405211212305128709 63203429325977102307211633)
            ·
              refine ⟨47402571994482826730408725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63203429325977102307211633 47402571994482826730408725)
              ·
                refine ⟨2221995562241382502987909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47402571994482826730408725 2221995562241382502987909)
                ·
                  refine ⟨416624167920259219310233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221995562241382502987909 416624167920259219310233)
                  ·
                    rfl

theorem cell22_3651177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_3651177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651177 prefixEnd_3651177 := by exact prefixLift 3651177
  have htrace : WordTrace (prefixWord ++ tailWord_3651177) baseStart_3651177 baseEnd_3651177 := by
    simpa [prefixWord, tailWord_3651177, baseEnd_3651177] using wordTrace_append hprefix tailTrace_3651177
  have hstable : (prefixWord ++ tailWord_3651177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651177).length < 2 ^ (prefixWord ++ tailWord_3651177).sum := by decide
  have hdescent : baseEnd_3651177 < baseStart_3651177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651205 : List Nat := [1, 3, 1, 1, 4, 1, 1, 10]
def baseStart_3651205 : Nat := 118140960795 + 3651205 * 2 ^ 59
def prefixEnd_3651205 : Nat := 4983230072969 + 3 ^ 40 * 3651205 * 2
def baseEnd_3651205 : Nat := 138875787636999435358957

theorem tailTrace_3651205 : CollatzResearch.WordTrace tailWord_3651205 prefixEnd_3651205 138875787636999435358957 := by
  unfold tailWord_3651205
  simp only [CollatzResearch.WordTrace]
  refine ⟨133170386737315336013675069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88780257824876890675783379 133170386737315336013675069)
  ·
    refine ⟨49938895026493251005128151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133170386737315336013675069 49938895026493251005128151)
    ·
      refine ⟨74908342539739876507692227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49938895026493251005128151 74908342539739876507692227)
      ·
        refine ⟨112362513809609814761538341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74908342539739876507692227 112362513809609814761538341)
        ·
          refine ⟨21067971339301840267788439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112362513809609814761538341 21067971339301840267788439)
          ·
            refine ⟨31601957008952760401682659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21067971339301840267788439 31601957008952760401682659)
            ·
              refine ⟨47402935513429140602523989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31601957008952760401682659 47402935513429140602523989)
              ·
                refine ⟨138875787636999435358957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47402935513429140602523989 138875787636999435358957)
                ·
                  rfl

theorem cell22_3651205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 10].length) (baseStart_3651205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651205 prefixEnd_3651205 := by exact prefixLift 3651205
  have htrace : WordTrace (prefixWord ++ tailWord_3651205) baseStart_3651205 baseEnd_3651205 := by
    simpa [prefixWord, tailWord_3651205, baseEnd_3651205] using wordTrace_append hprefix tailTrace_3651205
  have hstable : (prefixWord ++ tailWord_3651205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651205).length < 2 ^ (prefixWord ++ tailWord_3651205).sum := by decide
  have hdescent : baseEnd_3651205 < baseStart_3651205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651207 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3651207 : Nat := 118140960795 + 3651207 * 2 ^ 59
def prefixEnd_3651207 : Nat := 4983230072969 + 3 ^ 40 * 3651207 * 2
def baseEnd_3651207 : Nat := 1249882773373867579680607

theorem tailTrace_3651207 : CollatzResearch.WordTrace tailWord_3651207 prefixEnd_3651207 1249882773373867579680607 := by
  unfold tailWord_3651207
  simp only [CollatzResearch.WordTrace]
  refine ⟨133170459683308090355247875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88780306455538726903498583 133170459683308090355247875)
  ·
    refine ⟨199755689524962135532871813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133170459683308090355247875 199755689524962135532871813)
    ·
      refine ⟨37454191785930400412413465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199755689524962135532871813 37454191785930400412413465)
      ·
        refine ⟨28090643839447800309310099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37454191785930400412413465 28090643839447800309310099)
        ·
          refine ⟨42135965759171700463965149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28090643839447800309310099 42135965759171700463965149)
          ·
            refine ⟨15800987159689387673986931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42135965759171700463965149 15800987159689387673986931)
            ·
              refine ⟨23701480739534081510980397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15800987159689387673986931 23701480739534081510980397)
              ·
                refine ⟨8888055277325280566617649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23701480739534081510980397 8888055277325280566617649)
                ·
                  refine ⟨6666041457993960424963237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8888055277325280566617649 6666041457993960424963237)
                  ·
                    refine ⟨1249882773373867579680607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6666041457993960424963237 1249882773373867579680607)
                    ·
                      rfl

theorem cell22_3651207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3651207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651207 prefixEnd_3651207 := by exact prefixLift 3651207
  have htrace : WordTrace (prefixWord ++ tailWord_3651207) baseStart_3651207 baseEnd_3651207 := by
    simpa [prefixWord, tailWord_3651207, baseEnd_3651207] using wordTrace_append hprefix tailTrace_3651207
  have hstable : (prefixWord ++ tailWord_3651207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651207).length < 2 ^ (prefixWord ++ tailWord_3651207).sum := by decide
  have hdescent : baseEnd_3651207 < baseStart_3651207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651222 : List Nat := [5, 3, 14]
def baseStart_3651222 : Nat := 118140960795 + 3651222 * 2 ^ 59
def prefixEnd_3651222 : Nat := 4983230072969 + 3 ^ 40 * 3651222 * 2
def baseEnd_3651222 : Nat := 571507959844724527003

theorem tailTrace_3651222 : CollatzResearch.WordTrace tailWord_3651222 prefixEnd_3651222 571507959844724527003 := by
  unfold tailWord_3651222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8323187923640859244815245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88780671185502498611362613 8323187923640859244815245)
  ·
    refine ⟨3121195471365322216805717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8323187923640859244815245 3121195471365322216805717)
    ·
      refine ⟨571507959844724527003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 3121195471365322216805717 571507959844724527003)
      ·
        rfl

theorem cell22_3651222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 14].length) (baseStart_3651222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651222 prefixEnd_3651222 := by exact prefixLift 3651222
  have htrace : WordTrace (prefixWord ++ tailWord_3651222) baseStart_3651222 baseEnd_3651222 := by
    simpa [prefixWord, tailWord_3651222, baseEnd_3651222] using wordTrace_append hprefix tailTrace_3651222
  have hstable : (prefixWord ++ tailWord_3651222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651222).length < 2 ^ (prefixWord ++ tailWord_3651222).sum := by decide
  have hdescent : baseEnd_3651222 < baseStart_3651222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651228 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 4]
def baseStart_3651228 : Nat := 118140960795 + 3651228 * 2 ^ 59
def prefixEnd_3651228 : Nat := 4983230072969 + 3 ^ 40 * 3651228 * 2
def baseEnd_3651228 : Nat := 416629987367676841635181

theorem tailTrace_3651228 : CollatzResearch.WordTrace tailWord_3651228 prefixEnd_3651228 416629987367676841635181 := by
  unfold tailWord_3651228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66585612808116005470881169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88780817077488007294508225 66585612808116005470881169)
  ·
    refine ⟨49939209606087004103160877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66585612808116005470881169 49939209606087004103160877)
    ·
      refine ⟨18727203602282626538685329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49939209606087004103160877 18727203602282626538685329)
      ·
        refine ⟨14045402701711969904013997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18727203602282626538685329 14045402701711969904013997)
        ·
          refine ⟨5267026013141988714005249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14045402701711969904013997 5267026013141988714005249)
          ·
            refine ⟨3950269509856491535503937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5267026013141988714005249 3950269509856491535503937)
            ·
              refine ⟨2962702132392368651627953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950269509856491535503937 2962702132392368651627953)
              ·
                refine ⟨2222026599294276488720965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962702132392368651627953 2222026599294276488720965)
                ·
                  refine ⟨416629987367676841635181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222026599294276488720965 416629987367676841635181)
                  ·
                    rfl

theorem cell22_3651228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_3651228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651228 prefixEnd_3651228 := by exact prefixLift 3651228
  have htrace : WordTrace (prefixWord ++ tailWord_3651228) baseStart_3651228 baseEnd_3651228 := by
    simpa [prefixWord, tailWord_3651228, baseEnd_3651228] using wordTrace_append hprefix tailTrace_3651228
  have hstable : (prefixWord ++ tailWord_3651228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651228).length < 2 ^ (prefixWord ++ tailWord_3651228).sum := by decide
  have hdescent : baseEnd_3651228 < baseStart_3651228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651235 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_3651235 : Nat := 118140960795 + 3651235 * 2 ^ 59
def prefixEnd_3651235 : Nat := 4983230072969 + 3 ^ 40 * 3651235 * 2
def baseEnd_3651235 : Nat := 1249892358346084839980521

theorem tailTrace_3651235 : CollatzResearch.WordTrace tailWord_3651235 prefixEnd_3651235 1249892358346084839980521 := by
  unfold tailWord_3651235
  simp only [CollatzResearch.WordTrace]
  refine ⟨133171480927206651137267159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88780987284804434091511439 133171480927206651137267159)
  ·
    refine ⟨199757221390809976705900739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133171480927206651137267159 199757221390809976705900739)
    ·
      refine ⟨299635832086214965058851109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199757221390809976705900739 299635832086214965058851109)
      ·
        refine ⟨56181718516165305948534583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299635832086214965058851109 56181718516165305948534583)
        ·
          refine ⟨84272577774247958922801875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56181718516165305948534583 84272577774247958922801875)
          ·
            refine ⟨126408866661371938384202813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84272577774247958922801875 126408866661371938384202813)
            ·
              refine ⟨47403324998014476894076055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126408866661371938384202813 47403324998014476894076055)
              ·
                refine ⟨71104987497021715341114083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47403324998014476894076055 71104987497021715341114083)
                ·
                  refine ⟨106657481245532573011671125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71104987497021715341114083 106657481245532573011671125)
                  ·
                    refine ⟨1249892358346084839980521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106657481245532573011671125 1249892358346084839980521)
                    ·
                      rfl

theorem cell22_3651235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_3651235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651235 prefixEnd_3651235 := by exact prefixLift 3651235
  have htrace : WordTrace (prefixWord ++ tailWord_3651235) baseStart_3651235 baseEnd_3651235 := by
    simpa [prefixWord, tailWord_3651235, baseEnd_3651235] using wordTrace_append hprefix tailTrace_3651235
  have hstable : (prefixWord ++ tailWord_3651235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651235).length < 2 ^ (prefixWord ++ tailWord_3651235).sum := by decide
  have hdescent : baseEnd_3651235 < baseStart_3651235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651271 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3651271 : Nat := 118140960795 + 3651271 * 2 ^ 59
def prefixEnd_3651271 : Nat := 4983230072969 + 3 ^ 40 * 3651271 * 2
def baseEnd_3651271 : Nat := 1249904681881792746080411

theorem tailTrace_3651271 : CollatzResearch.WordTrace tailWord_3651271 prefixEnd_3651271 1249904681881792746080411 := by
  unfold tailWord_3651271
  simp only [CollatzResearch.WordTrace]
  refine ⟨133172793955076229285577667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88781862636717486190385111 133172793955076229285577667)
  ·
    refine ⟨199759190932614343928366501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133172793955076229285577667 199759190932614343928366501)
    ·
      refine ⟨37454848299865189486568719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199759190932614343928366501 37454848299865189486568719)
      ·
        refine ⟨56182272449797784229853079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37454848299865189486568719 56182272449797784229853079)
        ·
          refine ⟨84273408674696676344779619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56182272449797784229853079 84273408674696676344779619)
          ·
            refine ⟨126410113012045014517169429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84273408674696676344779619 126410113012045014517169429)
            ·
              refine ⟨5925474047439610055492317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126410113012045014517169429 5925474047439610055492317)
              ·
                refine ⟨2222052767789853770809619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5925474047439610055492317 2222052767789853770809619)
                ·
                  refine ⟨3333079151684780656214429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222052767789853770809619 3333079151684780656214429)
                  ·
                    refine ⟨1249904681881792746080411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333079151684780656214429 1249904681881792746080411)
                    ·
                      rfl

theorem cell22_3651271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3651271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651271 prefixEnd_3651271 := by exact prefixLift 3651271
  have htrace : WordTrace (prefixWord ++ tailWord_3651271) baseStart_3651271 baseEnd_3651271 := by
    simpa [prefixWord, tailWord_3651271, baseEnd_3651271] using wordTrace_append hprefix tailTrace_3651271
  have hstable : (prefixWord ++ tailWord_3651271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651271).length < 2 ^ (prefixWord ++ tailWord_3651271).sum := by decide
  have hdescent : baseEnd_3651271 < baseStart_3651271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651284 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3651284 : Nat := 118140960795 + 3651284 * 2 ^ 59
def prefixEnd_3651284 : Nat := 4983230072969 + 3 ^ 40 * 3651284 * 2
def baseEnd_3651284 : Nat := 416636377349155015168457

theorem tailTrace_3651284 : CollatzResearch.WordTrace tailWord_3651284 prefixEnd_3651284 416636377349155015168457 := by
  unfold tailWord_3651284
  simp only [CollatzResearch.WordTrace]
  refine ⟨66586634052014566252900453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88782178736019421670533937 66586634052014566252900453)
  ·
    refine ⟨12484993884752731172418835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66586634052014566252900453 12484993884752731172418835)
    ·
      refine ⟨18727490827129096758628253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12484993884752731172418835 18727490827129096758628253)
      ·
        refine ⟨7022809060173411284485595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18727490827129096758628253 7022809060173411284485595)
        ·
          refine ⟨10534213590260116926728393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022809060173411284485595 10534213590260116926728393)
          ·
            refine ⟨7900660192695087695046295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10534213590260116926728393 7900660192695087695046295)
            ·
              refine ⟨11850990289042631542569443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900660192695087695046295 11850990289042631542569443)
              ·
                refine ⟨17776485433563947313854165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11850990289042631542569443 17776485433563947313854165)
                ·
                  refine ⟨416636377349155015168457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17776485433563947313854165 416636377349155015168457)
                  ·
                    rfl

theorem cell22_3651284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3651284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651284 prefixEnd_3651284 := by exact prefixLift 3651284
  have htrace : WordTrace (prefixWord ++ tailWord_3651284) baseStart_3651284 baseEnd_3651284 := by
    simpa [prefixWord, tailWord_3651284, baseEnd_3651284] using wordTrace_append hprefix tailTrace_3651284
  have hstable : (prefixWord ++ tailWord_3651284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651284).length < 2 ^ (prefixWord ++ tailWord_3651284).sum := by decide
  have hdescent : baseEnd_3651284 < baseStart_3651284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651327 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 1, 5]
def baseStart_3651327 : Nat := 118140960795 + 3651327 * 2 ^ 59
def prefixEnd_3651327 : Nat := 4983230072969 + 3 ^ 40 * 3651327 * 2
def baseEnd_3651327 : Nat := 1249923851826227266680239

theorem tailTrace_3651327 : CollatzResearch.WordTrace tailWord_3651327 prefixEnd_3651327 1249923851826227266680239 := by
  unfold tailWord_3651327
  simp only [CollatzResearch.WordTrace]
  refine ⟨133174836442873350849616235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88783224295248900566410823 133174836442873350849616235)
  ·
    refine ⟨199762254664310026274424353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133174836442873350849616235 199762254664310026274424353)
    ·
      refine ⟨149821690998232519705818265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199762254664310026274424353 149821690998232519705818265)
      ·
        refine ⟨112366268248674389779363699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149821690998232519705818265 112366268248674389779363699)
        ·
          refine ⟨168549402373011584669045549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112366268248674389779363699 168549402373011584669045549)
          ·
            refine ⟨63206025889879344250892081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168549402373011584669045549 63206025889879344250892081)
            ·
              refine ⟨47404519417409508188169061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63206025889879344250892081 47404519417409508188169061)
              ·
                refine ⟨8888347390764282785281699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47404519417409508188169061 8888347390764282785281699)
                ·
                  refine ⟨13332521086146424177922549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8888347390764282785281699 13332521086146424177922549)
                  ·
                    refine ⟨1249923851826227266680239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13332521086146424177922549 1249923851826227266680239)
                    ·
                      rfl

theorem cell22_3651327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_3651327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651327 prefixEnd_3651327 := by exact prefixLift 3651327
  have htrace : WordTrace (prefixWord ++ tailWord_3651327) baseStart_3651327 baseEnd_3651327 := by
    simpa [prefixWord, tailWord_3651327, baseEnd_3651327] using wordTrace_append hprefix tailTrace_3651327
  have hstable : (prefixWord ++ tailWord_3651327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651327).length < 2 ^ (prefixWord ++ tailWord_3651327).sum := by decide
  have hdescent : baseEnd_3651327 < baseStart_3651327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651346 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3651346 : Nat := 118140960795 + 3651346 * 2 ^ 59
def prefixEnd_3651346 : Nat := 4983230072969 + 3 ^ 40 * 3651346 * 2
def baseEnd_3651346 : Nat := 416643451971505850151727

theorem tailTrace_3651346 : CollatzResearch.WordTrace tailWord_3651346 prefixEnd_3651346 416643451971505850151727 := by
  unfold tailWord_3651346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33293882357451129273639473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88783686286536344729705261 33293882357451129273639473)
  ·
    refine ⟨24970411768088346955229605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33293882357451129273639473 24970411768088346955229605)
    ·
      refine ⟨4681952206516565054105551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24970411768088346955229605 4681952206516565054105551)
      ·
        refine ⟨7022928309774847581158327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681952206516565054105551 7022928309774847581158327)
        ·
          refine ⟨10534392464662271371737491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022928309774847581158327 10534392464662271371737491)
          ·
            refine ⟨15801588696993407057606237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534392464662271371737491 15801588696993407057606237)
            ·
              refine ⟨5925595761372527646602339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15801588696993407057606237 5925595761372527646602339)
              ·
                refine ⟨8888393642058791469903509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925595761372527646602339 8888393642058791469903509)
                ·
                  refine ⟨416643451971505850151727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8888393642058791469903509 416643451971505850151727)
                  ·
                    rfl

theorem cell22_3651346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3651346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651346 prefixEnd_3651346 := by exact prefixLift 3651346
  have htrace : WordTrace (prefixWord ++ tailWord_3651346) baseStart_3651346 baseEnd_3651346 := by
    simpa [prefixWord, tailWord_3651346, baseEnd_3651346] using wordTrace_append hprefix tailTrace_3651346
  have hstable : (prefixWord ++ tailWord_3651346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651346).length < 2 ^ (prefixWord ++ tailWord_3651346).sum := by decide
  have hdescent : baseEnd_3651346 < baseStart_3651346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651361 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_3651361 : Nat := 118140960795 + 3651361 * 2 ^ 59
def prefixEnd_3651361 : Nat := 4983230072969 + 3 ^ 40 * 3651361 * 2
def baseEnd_3651361 : Nat := 1249935490721062511330135

theorem tailTrace_3651361 : CollatzResearch.WordTrace tailWord_3651361 prefixEnd_3651361 1249935490721062511330135 := by
  unfold tailWord_3651361
  simp only [CollatzResearch.WordTrace]
  refine ⟨133176076524750174656353937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88784051016500116437569291 133176076524750174656353937)
  ·
    refine ⟨99882057393562630992265453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133176076524750174656353937 99882057393562630992265453)
    ·
      refine ⟨37455771522585986622099545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99882057393562630992265453 37455771522585986622099545)
      ·
        refine ⟨28091828641939489966574659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37455771522585986622099545 28091828641939489966574659)
        ·
          refine ⟨42137742962909234949861989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28091828641939489966574659 42137742962909234949861989)
          ·
            refine ⟨7900826805545481553099123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42137742962909234949861989 7900826805545481553099123)
            ·
              refine ⟨11851240208318222329648685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900826805545481553099123 11851240208318222329648685)
              ·
                refine ⟨4444215078119333373618257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11851240208318222329648685 4444215078119333373618257)
                ·
                  refine ⟨3333161308589500030213693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444215078119333373618257 3333161308589500030213693)
                  ·
                    refine ⟨1249935490721062511330135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333161308589500030213693 1249935490721062511330135)
                    ·
                      rfl

theorem cell22_3651361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_3651361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651361 prefixEnd_3651361 := by exact prefixLift 3651361
  have htrace : WordTrace (prefixWord ++ tailWord_3651361) baseStart_3651361 baseEnd_3651361 := by
    simpa [prefixWord, tailWord_3651361, baseEnd_3651361] using wordTrace_append hprefix tailTrace_3651361
  have hstable : (prefixWord ++ tailWord_3651361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651361).length < 2 ^ (prefixWord ++ tailWord_3651361).sum := by decide
  have hdescent : baseEnd_3651361 < baseStart_3651361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651470 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_3651470 : Nat := 118140960795 + 3651470 * 2 ^ 59
def prefixEnd_3651470 : Nat := 4983230072969 + 3 ^ 40 * 3651470 * 2
def baseEnd_3651470 : Nat := 416657601216207520118267

theorem tailTrace_3651470 : CollatzResearch.WordTrace tailWord_3651470 prefixEnd_3651470 416657601216207520118267 := by
  unfold tailWord_3651470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647506510169410784008983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88786701387570190848047909 16647506510169410784008983)
  ·
    refine ⟨24971259765254116176013475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647506510169410784008983 24971259765254116176013475)
    ·
      refine ⟨37456889647881174264020213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24971259765254116176013475 37456889647881174264020213)
      ·
        refine ⟨3511583404488860087251895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37456889647881174264020213 3511583404488860087251895)
        ·
          refine ⟨5267375106733290130877843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511583404488860087251895 5267375106733290130877843)
          ·
            refine ⟨7901062660099935196316765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267375106733290130877843 7901062660099935196316765)
            ·
              refine ⟨2962898497537475698618787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7901062660099935196316765 2962898497537475698618787)
              ·
                refine ⟨4444347746306213547928181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962898497537475698618787 4444347746306213547928181)
                ·
                  refine ⟨416657601216207520118267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4444347746306213547928181 416657601216207520118267)
                  ·
                    rfl

theorem cell22_3651470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_3651470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651470 prefixEnd_3651470 := by exact prefixLift 3651470
  have htrace : WordTrace (prefixWord ++ tailWord_3651470) baseStart_3651470 baseEnd_3651470 := by
    simpa [prefixWord, tailWord_3651470, baseEnd_3651470] using wordTrace_append hprefix tailTrace_3651470
  have hstable : (prefixWord ++ tailWord_3651470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651470).length < 2 ^ (prefixWord ++ tailWord_3651470).sum := by decide
  have hdescent : baseEnd_3651470 < baseStart_3651470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651509 : List Nat := [1, 3, 3, 2, 1, 2, 10]
def baseStart_3651509 : Nat := 118140960795 + 3651509 * 2 ^ 59
def prefixEnd_3651509 : Nat := 4983230072969 + 3 ^ 40 * 3651509 * 2
def baseEnd_3651509 : Nat := 46295783486875535504803

theorem tailTrace_3651509 : CollatzResearch.WordTrace tailWord_3651509 prefixEnd_3651509 46295783486875535504803 := by
  unfold tailWord_3651509
  simp only [CollatzResearch.WordTrace]
  refine ⟨133181474528213995932741581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88787649685475997288494387 133181474528213995932741581)
  ·
    refine ⟨49943052948080248474778093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133181474528213995932741581 49943052948080248474778093)
    ·
      refine ⟨18728644855530093178041785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49943052948080248474778093 18728644855530093178041785)
      ·
        refine ⟨14046483641647569883531339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18728644855530093178041785 14046483641647569883531339)
        ·
          refine ⟨21069725462471354825297009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14046483641647569883531339 21069725462471354825297009)
          ·
            refine ⟨15802294096853516118972757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21069725462471354825297009 15802294096853516118972757)
            ·
              refine ⟨46295783486875535504803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15802294096853516118972757 46295783486875535504803)
              ·
                rfl

theorem cell22_3651509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 10].length) (baseStart_3651509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651509 prefixEnd_3651509 := by exact prefixLift 3651509
  have htrace : WordTrace (prefixWord ++ tailWord_3651509) baseStart_3651509 baseEnd_3651509 := by
    simpa [prefixWord, tailWord_3651509, baseEnd_3651509] using wordTrace_append hprefix tailTrace_3651509
  have hstable : (prefixWord ++ tailWord_3651509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651509).length < 2 ^ (prefixWord ++ tailWord_3651509).sum := by decide
  have hdescent : baseEnd_3651509 < baseStart_3651509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651618 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3651618 : Nat := 118140960795 + 3651618 * 2 ^ 59
def prefixEnd_3651618 : Nat := 4983230072969 + 3 ^ 40 * 3651618 * 2
def baseEnd_3651618 : Nat := 1250023467073199507654347

theorem tailTrace_3651618 : CollatzResearch.WordTrace tailWord_3651618 prefixEnd_3651618 1250023467073199507654347 := by
  unfold tailWord_3651618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33296362521204776887114877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88790300056546071698973005 33296362521204776887114877)
  ·
    refine ⟨12486135945451791332668079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33296362521204776887114877 12486135945451791332668079)
    ·
      refine ⟨18729203918177686999002119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12486135945451791332668079 18729203918177686999002119)
      ·
        refine ⟨28093805877266530498503179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18729203918177686999002119 28093805877266530498503179)
        ·
          refine ⟨42140708815899795747754769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28093805877266530498503179 42140708815899795747754769)
          ·
            refine ⟨31605531611924846810816077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42140708815899795747754769 31605531611924846810816077)
            ·
              refine ⟨11852074354471817554056029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31605531611924846810816077 11852074354471817554056029)
              ·
                refine ⟨4444527882926931582771011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11852074354471817554056029 4444527882926931582771011)
                ·
                  refine ⟨6666791824390397374156517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444527882926931582771011 6666791824390397374156517)
                  ·
                    refine ⟨1250023467073199507654347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6666791824390397374156517 1250023467073199507654347)
                    ·
                      rfl

theorem cell22_3651618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3651618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651618 prefixEnd_3651618 := by exact prefixLift 3651618
  have htrace : WordTrace (prefixWord ++ tailWord_3651618) baseStart_3651618 baseEnd_3651618 := by
    simpa [prefixWord, tailWord_3651618, baseEnd_3651618] using wordTrace_append hprefix tailTrace_3651618
  have hstable : (prefixWord ++ tailWord_3651618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651618).length < 2 ^ (prefixWord ++ tailWord_3651618).sum := by decide
  have hdescent : baseEnd_3651618 < baseStart_3651618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651633 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 4]
def baseStart_3651633 : Nat := 118140960795 + 3651633 * 2 ^ 59
def prefixEnd_3651633 : Nat := 4983230072969 + 3 ^ 40 * 3651633 * 2
def baseEnd_3651633 : Nat := 416676200626581489509767

theorem tailTrace_3651633 : CollatzResearch.WordTrace tailWord_3651633 prefixEnd_3651633 416676200626581489509767 := by
  unfold tailWord_3651633
  simp only [CollatzResearch.WordTrace]
  refine ⟨133185997179764765110255553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88790664786509843406837035 133185997179764765110255553)
  ·
    refine ⟨99889497884823573832691665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133185997179764765110255553 99889497884823573832691665)
    ·
      refine ⟨74917123413617680374518749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99889497884823573832691665 74917123413617680374518749)
      ·
        refine ⟨28093921280106630140444531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74917123413617680374518749 28093921280106630140444531)
        ·
          refine ⟨42140881920159945210666797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28093921280106630140444531 42140881920159945210666797)
          ·
            refine ⟨15802830720059979454000049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42140881920159945210666797 15802830720059979454000049)
            ·
              refine ⟨11852123040044984590500037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15802830720059979454000049 11852123040044984590500037)
              ·
                refine ⟨2222273070008434610718757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11852123040044984590500037 2222273070008434610718757)
                ·
                  refine ⟨416676200626581489509767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222273070008434610718757 416676200626581489509767)
                  ·
                    rfl

theorem cell22_3651633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_3651633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651633 prefixEnd_3651633 := by exact prefixLift 3651633
  have htrace : WordTrace (prefixWord ++ tailWord_3651633) baseStart_3651633 baseEnd_3651633 := by
    simpa [prefixWord, tailWord_3651633, baseEnd_3651633] using wordTrace_append hprefix tailTrace_3651633
  have hstable : (prefixWord ++ tailWord_3651633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651633).length < 2 ^ (prefixWord ++ tailWord_3651633).sum := by decide
  have hdescent : baseEnd_3651633 < baseStart_3651633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651648 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_3651648 : Nat := 118140960795 + 3651648 * 2 ^ 59
def prefixEnd_3651648 : Nat := 4983230072969 + 3 ^ 40 * 3651648 * 2
def baseEnd_3651648 : Nat := 1250033736686289429404255

theorem tailTrace_3651648 : CollatzResearch.WordTrace tailWord_3651648 prefixEnd_3651648 1250033736686289429404255 := by
  unfold tailWord_3651648
  simp only [CollatzResearch.WordTrace]
  refine ⟨66593272137355211336025799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88791029516473615114701065 66593272137355211336025799)
  ·
    refine ⟨99889908206032817004038699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66593272137355211336025799 99889908206032817004038699)
    ·
      refine ⟨149834862309049225506058049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99889908206032817004038699 149834862309049225506058049)
      ·
        refine ⟨112376146731786919129543537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149834862309049225506058049 112376146731786919129543537)
        ·
          refine ⟨84282110048840189347157653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112376146731786919129543537 84282110048840189347157653)
          ·
            refine ⟨3950723908539383875648015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84282110048840189347157653 3950723908539383875648015)
            ·
              refine ⟨5926085862809075813472023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950723908539383875648015 5926085862809075813472023)
              ·
                refine ⟨8889128794213613720208035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926085862809075813472023 8889128794213613720208035)
                ·
                  refine ⟨13333693191320420580312053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889128794213613720208035 13333693191320420580312053)
                  ·
                    refine ⟨1250033736686289429404255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13333693191320420580312053 1250033736686289429404255)
                    ·
                      rfl

theorem cell22_3651648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_3651648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651648 prefixEnd_3651648 := by exact prefixLift 3651648
  have htrace : WordTrace (prefixWord ++ tailWord_3651648) baseStart_3651648 baseEnd_3651648 := by
    simpa [prefixWord, tailWord_3651648, baseEnd_3651648] using wordTrace_append hprefix tailTrace_3651648
  have hstable : (prefixWord ++ tailWord_3651648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651648).length < 2 ^ (prefixWord ++ tailWord_3651648).sum := by decide
  have hdescent : baseEnd_3651648 < baseStart_3651648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651744 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 1, 3]
def baseStart_3651744 : Nat := 118140960795 + 3651744 * 2 ^ 59
def prefixEnd_3651744 : Nat := 4983230072969 + 3 ^ 40 * 3651744 * 2
def baseEnd_3651744 : Nat := 1250066599448177179003961

theorem tailTrace_3651744 : CollatzResearch.WordTrace tailWord_3651744 prefixEnd_3651744 1250066599448177179003961 := by
  unfold tailWord_3651744
  simp only [CollatzResearch.WordTrace]
  refine ⟨66595022841181315533773143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88793363788241754045030857 66595022841181315533773143)
  ·
    refine ⟨99892534261771973300659715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66595022841181315533773143 99892534261771973300659715)
    ·
      refine ⟨149838801392657959950989573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99892534261771973300659715 149838801392657959950989573)
      ·
        refine ⟨28094775261123367490810545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149838801392657959950989573 28094775261123367490810545)
        ·
          refine ⟨21071081445842525618107909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28094775261123367490810545 21071081445842525618107909)
          ·
            refine ⟨3950827771095473553395233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21071081445842525618107909 3950827771095473553395233)
            ·
              refine ⟨2963120828321605165046425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950827771095473553395233 2963120828321605165046425)
              ·
                refine ⟨2222340621241203873784819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963120828321605165046425 2222340621241203873784819)
                ·
                  refine ⟨3333510931861805810677229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222340621241203873784819 3333510931861805810677229)
                  ·
                    refine ⟨1250066599448177179003961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333510931861805810677229 1250066599448177179003961)
                    ·
                      rfl

theorem cell22_3651744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_3651744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651744 prefixEnd_3651744 := by exact prefixLift 3651744
  have htrace : WordTrace (prefixWord ++ tailWord_3651744) baseStart_3651744 baseEnd_3651744 := by
    simpa [prefixWord, tailWord_3651744, baseEnd_3651744] using wordTrace_append hprefix tailTrace_3651744
  have hstable : (prefixWord ++ tailWord_3651744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651744).length < 2 ^ (prefixWord ++ tailWord_3651744).sum := by decide
  have hdescent : baseEnd_3651744 < baseStart_3651744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651800 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_3651800 : Nat := 118140960795 + 3651800 * 2 ^ 59
def prefixEnd_3651800 : Nat := 4983230072969 + 3 ^ 40 * 3651800 * 2
def baseEnd_3651800 : Nat := 1250085769392611699603789

theorem tailTrace_3651800 : CollatzResearch.WordTrace tailWord_3651800 prefixEnd_3651800 1250085769392611699603789 := by
  unfold tailWord_3651800
  simp only [CollatzResearch.WordTrace]
  refine ⟨66596044085079876315792427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88794725446773168421056569 66596044085079876315792427)
  ·
    refine ⟨99894066127619814473688641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66596044085079876315792427 99894066127619814473688641)
    ·
      refine ⟨74920549595714860855266481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99894066127619814473688641 74920549595714860855266481)
      ·
        refine ⟨56190412196786145641449861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74920549595714860855266481 56190412196786145641449861)
        ·
          refine ⟨10535702286897402307771849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56190412196786145641449861 10535702286897402307771849)
          ·
            refine ⟨7901776715173051730828887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10535702286897402307771849 7901776715173051730828887)
            ·
              refine ⟨11852665072759577596243331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901776715173051730828887 11852665072759577596243331)
              ·
                refine ⟨17778997609139366394364997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11852665072759577596243331 17778997609139366394364997)
                ·
                  refine ⟨3333562051713631198943437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17778997609139366394364997 3333562051713631198943437)
                  ·
                    refine ⟨1250085769392611699603789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333562051713631198943437 1250085769392611699603789)
                    ·
                      rfl

theorem cell22_3651800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_3651800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651800 prefixEnd_3651800 := by exact prefixLift 3651800
  have htrace : WordTrace (prefixWord ++ tailWord_3651800) baseStart_3651800 baseEnd_3651800 := by
    simpa [prefixWord, tailWord_3651800, baseEnd_3651800] using wordTrace_append hprefix tailTrace_3651800
  have hstable : (prefixWord ++ tailWord_3651800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651800).length < 2 ^ (prefixWord ++ tailWord_3651800).sum := by decide
  have hdescent : baseEnd_3651800 < baseStart_3651800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651830 : List Nat := [5, 1, 1, 1, 1, 1, 6, 6]
def baseStart_3651830 : Nat := 118140960795 + 3651830 * 2 ^ 59
def prefixEnd_3651830 : Nat := 4983230072969 + 3 ^ 40 * 3651830 * 2
def baseEnd_3651830 : Nat := 138899559889522402372633

theorem tailTrace_3651830 : CollatzResearch.WordTrace tailWord_3651830 prefixEnd_3651830 138899559889522402372633 := by
  unfold tailWord_3651830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8324573897503191734698559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88795454906700711836784629 8324573897503191734698559)
  ·
    refine ⟨12486860846254787602047839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8324573897503191734698559 12486860846254787602047839)
    ·
      refine ⟨18730291269382181403071759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12486860846254787602047839 18730291269382181403071759)
      ·
        refine ⟨28095436904073272104607639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18730291269382181403071759 28095436904073272104607639)
        ·
          refine ⟨42143155356109908156911459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28095436904073272104607639 42143155356109908156911459)
          ·
            refine ⟨63214733034164862235367189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42143155356109908156911459 63214733034164862235367189)
            ·
              refine ⟨2963190610976477917282837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63214733034164862235367189 2963190610976477917282837)
              ·
                refine ⟨138899559889522402372633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2963190610976477917282837 138899559889522402372633)
                ·
                  rfl

theorem cell22_3651830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_3651830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651830 prefixEnd_3651830 := by exact prefixLift 3651830
  have htrace : WordTrace (prefixWord ++ tailWord_3651830) baseStart_3651830 baseEnd_3651830 := by
    simpa [prefixWord, tailWord_3651830, baseEnd_3651830] using wordTrace_append hprefix tailTrace_3651830
  have hstable : (prefixWord ++ tailWord_3651830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651830).length < 2 ^ (prefixWord ++ tailWord_3651830).sum := by decide
  have hdescent : baseEnd_3651830 < baseStart_3651830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651847 : List Nat := [1, 1, 4, 5, 2, 1, 8]
def baseStart_3651847 : Nat := 118140960795 + 3651847 * 2 ^ 59
def prefixEnd_3651847 : Nat := 4983230072969 + 3 ^ 40 * 3651847 * 2
def baseEnd_3651847 : Nat := 46300068831597009025135

theorem tailTrace_3651847 : CollatzResearch.WordTrace tailWord_3651847 prefixEnd_3651847 46300068831597009025135 := by
  unfold tailWord_3651847
  simp only [CollatzResearch.WordTrace]
  refine ⟨133193802400989479658545795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88795868267326319772363863 133193802400989479658545795)
  ·
    refine ⟨199790703601484219487818693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133193802400989479658545795 199790703601484219487818693)
    ·
      refine ⟨37460756925278291153966005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199790703601484219487818693 37460756925278291153966005)
      ·
        refine ⟨3511945961744839795684313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37460756925278291153966005 3511945961744839795684313)
        ·
          refine ⟨2633959471308629846763235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3511945961744839795684313 2633959471308629846763235)
          ·
            refine ⟨3950939206962944770144853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633959471308629846763235 3950939206962944770144853)
            ·
              refine ⟨46300068831597009025135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3950939206962944770144853 46300068831597009025135)
              ·
                rfl

theorem cell22_3651847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 8].length) (baseStart_3651847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651847 prefixEnd_3651847 := by exact prefixLift 3651847
  have htrace : WordTrace (prefixWord ++ tailWord_3651847) baseStart_3651847 baseEnd_3651847 := by
    simpa [prefixWord, tailWord_3651847, baseEnd_3651847] using wordTrace_append hprefix tailTrace_3651847
  have hstable : (prefixWord ++ tailWord_3651847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651847).length < 2 ^ (prefixWord ++ tailWord_3651847).sum := by decide
  have hdescent : baseEnd_3651847 < baseStart_3651847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651873 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3651873 : Nat := 118140960795 + 3651873 * 2 ^ 59
def prefixEnd_3651873 : Nat := 4983230072969 + 3 ^ 40 * 3651873 * 2
def baseEnd_3651873 : Nat := 1250110758784463842528565

theorem tailTrace_3651873 : CollatzResearch.WordTrace tailWord_3651873 prefixEnd_3651873 1250110758784463842528565 := by
  unfold tailWord_3651873
  simp only [CollatzResearch.WordTrace]
  refine ⟨133194750698895286098992273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88796500465930190732661515 133194750698895286098992273)
  ·
    refine ⟨99896063024171464574244205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133194750698895286098992273 99896063024171464574244205)
    ·
      refine ⟨37461023634064299215341577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99896063024171464574244205 37461023634064299215341577)
      ·
        refine ⟨28095767725548224411506183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37461023634064299215341577 28095767725548224411506183)
        ·
          refine ⟨42143651588322336617259275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28095767725548224411506183 42143651588322336617259275)
          ·
            refine ⟨63215477382483504925888913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42143651588322336617259275 63215477382483504925888913)
            ·
              refine ⟨47411608036862628694416685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63215477382483504925888913 47411608036862628694416685)
              ·
                refine ⟨17779353013823485760406257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47411608036862628694416685 17779353013823485760406257)
                ·
                  refine ⟨13334514760367614320304693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17779353013823485760406257 13334514760367614320304693)
                  ·
                    refine ⟨1250110758784463842528565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13334514760367614320304693 1250110758784463842528565)
                    ·
                      rfl

theorem cell22_3651873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3651873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651873 prefixEnd_3651873 := by exact prefixLift 3651873
  have htrace : WordTrace (prefixWord ++ tailWord_3651873) baseStart_3651873 baseEnd_3651873 := by
    simpa [prefixWord, tailWord_3651873, baseEnd_3651873] using wordTrace_append hprefix tailTrace_3651873
  have hstable : (prefixWord ++ tailWord_3651873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651873).length < 2 ^ (prefixWord ++ tailWord_3651873).sum := by decide
  have hdescent : baseEnd_3651873 < baseStart_3651873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651969 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3651969 : Nat := 118140960795 + 3651969 * 2 ^ 59
def prefixEnd_3651969 : Nat := 4983230072969 + 3 ^ 40 * 3651969 * 2
def baseEnd_3651969 : Nat := 1250143621546351592128271

theorem tailTrace_3651969 : CollatzResearch.WordTrace tailWord_3651969 prefixEnd_3651969 1250143621546351592128271 := by
  unfold tailWord_3651969
  simp only [CollatzResearch.WordTrace]
  refine ⟨133198252106547494494486961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88798834737698329662991307 133198252106547494494486961)
  ·
    refine ⟨99898689079910620870865221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133198252106547494494486961 99898689079910620870865221)
    ·
      refine ⟨18731004202483241413287229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99898689079910620870865221 18731004202483241413287229)
      ·
        refine ⟨7024126575931215529982711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18731004202483241413287229 7024126575931215529982711)
        ·
          refine ⟨10536189863896823294974067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024126575931215529982711 10536189863896823294974067)
          ·
            refine ⟨15804284795845234942461101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10536189863896823294974067 15804284795845234942461101)
            ·
              refine ⟨5926606798441963103422913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15804284795845234942461101 5926606798441963103422913)
              ·
                refine ⟨4444955098831472327567185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5926606798441963103422913 4444955098831472327567185)
                ·
                  refine ⟨3333716324123604245675389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444955098831472327567185 3333716324123604245675389)
                  ·
                    refine ⟨1250143621546351592128271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333716324123604245675389 1250143621546351592128271)
                    ·
                      rfl

theorem cell22_3651969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3651969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3651969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3651969 prefixEnd_3651969 := by exact prefixLift 3651969
  have htrace : WordTrace (prefixWord ++ tailWord_3651969) baseStart_3651969 baseEnd_3651969 := by
    simpa [prefixWord, tailWord_3651969, baseEnd_3651969] using wordTrace_append hprefix tailTrace_3651969
  have hstable : (prefixWord ++ tailWord_3651969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651969).length < 2 ^ (prefixWord ++ tailWord_3651969).sum := by decide
  have hdescent : baseEnd_3651969 < baseStart_3651969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652089 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 4]
def baseStart_3652089 : Nat := 118140960795 + 3652089 * 2 ^ 59
def prefixEnd_3652089 : Nat := 4983230072969 + 3 ^ 40 * 3652089 * 2
def baseEnd_3652089 : Nat := 416728233332903759709301

theorem tailTrace_3652089 : CollatzResearch.WordTrace tailWord_3652089 prefixEnd_3652089 416728233332903759709301 := by
  unfold tailWord_3652089
  simp only [CollatzResearch.WordTrace]
  refine ⟨133202628866112754988855321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88801752577408503325903547 133202628866112754988855321)
  ·
    refine ⟨99901971649584566241641491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133202628866112754988855321 99901971649584566241641491)
    ·
      refine ⟨149852957474376849362462237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99901971649584566241641491 149852957474376849362462237)
      ·
        refine ⟨56194859052891318510923339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149852957474376849362462237 56194859052891318510923339)
        ·
          refine ⟨84292288579336977766385009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56194859052891318510923339 84292288579336977766385009)
          ·
            refine ⟨63219216434502733324788757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84292288579336977766385009 63219216434502733324788757)
            ·
              refine ⟨2963400770367315624599473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63219216434502733324788757 2963400770367315624599473)
              ·
                refine ⟨2222550577775486718449605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963400770367315624599473 2222550577775486718449605)
                ·
                  refine ⟨416728233332903759709301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222550577775486718449605 416728233332903759709301)
                  ·
                    rfl

theorem cell22_3652089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_3652089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652089 prefixEnd_3652089 := by exact prefixLift 3652089
  have htrace : WordTrace (prefixWord ++ tailWord_3652089) baseStart_3652089 baseEnd_3652089 := by
    simpa [prefixWord, tailWord_3652089, baseEnd_3652089] using wordTrace_append hprefix tailTrace_3652089
  have hstable : (prefixWord ++ tailWord_3652089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652089).length < 2 ^ (prefixWord ++ tailWord_3652089).sum := by decide
  have hdescent : baseEnd_3652089 < baseStart_3652089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652117 : List Nat := [1, 3, 2, 1, 3, 1, 5, 6]
def baseStart_3652117 : Nat := 118140960795 + 3652117 * 2 ^ 59
def prefixEnd_3652117 : Nat := 4983230072969 + 3 ^ 40 * 3652117 * 2
def baseEnd_3652117 : Nat := 138910476107880948825313

theorem tailTrace_3652117 : CollatzResearch.WordTrace tailWord_3652117 prefixEnd_3652117 138910476107880948825313 := by
  unfold tailWord_3652117
  simp only [CollatzResearch.WordTrace]
  refine ⟨133203650110011315770874605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88802433406674210513916403 133203650110011315770874605)
  ·
    refine ⟨49951368791254243414077977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133203650110011315770874605 49951368791254243414077977)
    ·
      refine ⟨37463526593440682560558483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49951368791254243414077977 37463526593440682560558483)
      ·
        refine ⟨56195289890161023840837725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37463526593440682560558483 56195289890161023840837725)
        ·
          refine ⟨21073233708810383940314147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56195289890161023840837725 21073233708810383940314147)
          ·
            refine ⟨31609850563215575910471221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21073233708810383940314147 31609850563215575910471221)
            ·
              refine ⟨2963423490301460241606677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31609850563215575910471221 2963423490301460241606677)
              ·
                refine ⟨138910476107880948825313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2963423490301460241606677 138910476107880948825313)
                ·
                  rfl

theorem cell22_3652117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 6].length) (baseStart_3652117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652117 prefixEnd_3652117 := by exact prefixLift 3652117
  have htrace : WordTrace (prefixWord ++ tailWord_3652117) baseStart_3652117 baseEnd_3652117 := by
    simpa [prefixWord, tailWord_3652117, baseEnd_3652117] using wordTrace_append hprefix tailTrace_3652117
  have hstable : (prefixWord ++ tailWord_3652117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652117).length < 2 ^ (prefixWord ++ tailWord_3652117).sum := by decide
  have hdescent : baseEnd_3652117 < baseStart_3652117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652119 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 1, 6]
def baseStart_3652119 : Nat := 118140960795 + 3652119 * 2 ^ 59
def prefixEnd_3652119 : Nat := 4983230072969 + 3 ^ 40 * 3652119 * 2
def baseEnd_3652119 : Nat := 1250194969611801200877811

theorem tailTrace_3652119 : CollatzResearch.WordTrace tailWord_3652119 prefixEnd_3652119 1250194969611801200877811 := by
  unfold tailWord_3652119
  simp only [CollatzResearch.WordTrace]
  refine ⟨133203723056004070112447411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88802482037336046741631607 133203723056004070112447411)
  ·
    refine ⟨199805584584006105168671117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133203723056004070112447411 199805584584006105168671117)
    ·
      refine ⟨74927094219002289438251669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199805584584006105168671117 74927094219002289438251669)
      ·
        refine ⟨3512207541515732317418047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74927094219002289438251669 3512207541515732317418047)
        ·
          refine ⟨5268311312273598476127071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512207541515732317418047 5268311312273598476127071)
          ·
            refine ⟨7902466968410397714190607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268311312273598476127071 7902466968410397714190607)
            ·
              refine ⟨11853700452615596571285911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7902466968410397714190607 11853700452615596571285911)
              ·
                refine ⟨17780550678923394856928867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11853700452615596571285911 17780550678923394856928867)
                ·
                  refine ⟨26670826018385092285393301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17780550678923394856928867 26670826018385092285393301)
                  ·
                    refine ⟨1250194969611801200877811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26670826018385092285393301 1250194969611801200877811)
                    ·
                      rfl

theorem cell22_3652119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_3652119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652119 prefixEnd_3652119 := by exact prefixLift 3652119
  have htrace : WordTrace (prefixWord ++ tailWord_3652119) baseStart_3652119 baseEnd_3652119 := by
    simpa [prefixWord, tailWord_3652119, baseEnd_3652119] using wordTrace_append hprefix tailTrace_3652119
  have hstable : (prefixWord ++ tailWord_3652119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652119).length < 2 ^ (prefixWord ++ tailWord_3652119).sum := by decide
  have hdescent : baseEnd_3652119 < baseStart_3652119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652149 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3652149 : Nat := 118140960795 + 3652149 * 2 ^ 59
def prefixEnd_3652149 : Nat := 4983230072969 + 3 ^ 40 * 3652149 * 2
def baseEnd_3652149 : Nat := 1250205239224891122627719

theorem tailTrace_3652149 : CollatzResearch.WordTrace tailWord_3652149 prefixEnd_3652149 1250205239224891122627719 := by
  unfold tailWord_3652149
  simp only [CollatzResearch.WordTrace]
  refine ⟨133204817245895385236039501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88803211497263590157359667 133204817245895385236039501)
  ·
    refine ⟨49951806467210769463514813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133204817245895385236039501 49951806467210769463514813)
    ·
      refine ⟨18731927425204038548818055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49951806467210769463514813 18731927425204038548818055)
      ·
        refine ⟨28097891137806057823227083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18731927425204038548818055 28097891137806057823227083)
        ·
          refine ⟨42146836706709086734840625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28097891137806057823227083 42146836706709086734840625)
          ·
            refine ⟨31610127530031815051130469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42146836706709086734840625 31610127530031815051130469)
            ·
              refine ⟨5926898911880965322086963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31610127530031815051130469 5926898911880965322086963)
              ·
                refine ⟨8890348367821447983130445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926898911880965322086963 8890348367821447983130445)
                ·
                  refine ⟨3333880637933042993673917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8890348367821447983130445 3333880637933042993673917)
                  ·
                    refine ⟨1250205239224891122627719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333880637933042993673917 1250205239224891122627719)
                    ·
                      rfl

theorem cell22_3652149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3652149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652149 prefixEnd_3652149 := by exact prefixLift 3652149
  have htrace : WordTrace (prefixWord ++ tailWord_3652149) baseStart_3652149 baseEnd_3652149 := by
    simpa [prefixWord, tailWord_3652149, baseEnd_3652149] using wordTrace_append hprefix tailTrace_3652149
  have hstable : (prefixWord ++ tailWord_3652149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652149).length < 2 ^ (prefixWord ++ tailWord_3652149).sum := by decide
  have hdescent : baseEnd_3652149 < baseStart_3652149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652200 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 1, 3]
def baseStart_3652200 : Nat := 118140960795 + 3652200 * 2 ^ 59
def prefixEnd_3652200 : Nat := 4983230072969 + 3 ^ 40 * 3652200 * 2
def baseEnd_3652200 : Nat := 1250222697567143989602563

theorem tailTrace_3652200 : CollatzResearch.WordTrace tailWord_3652200 prefixEnd_3652200 1250222697567143989602563 := by
  unfold tailWord_3652200
  simp only [CollatzResearch.WordTrace]
  refine ⟨66603338684355310473073027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88804451579140413964097369 66603338684355310473073027)
  ·
    refine ⟨99905008026532965709609541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66603338684355310473073027 99905008026532965709609541)
    ·
      refine ⟨18732189004974931070551789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99905008026532965709609541 18732189004974931070551789)
      ·
        refine ⟨7024570876865599151456921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18732189004974931070551789 7024570876865599151456921)
        ·
          refine ⟨5268428157649199363592691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7024570876865599151456921 5268428157649199363592691)
          ·
            refine ⟨7902642236473799045389037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268428157649199363592691 7902642236473799045389037)
            ·
              refine ⟨2963490838677674642020889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7902642236473799045389037 2963490838677674642020889)
              ·
                refine ⟨2222618129008255981515667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963490838677674642020889 2222618129008255981515667)
                ·
                  refine ⟨3333927193512383972273501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222618129008255981515667 3333927193512383972273501)
                  ·
                    refine ⟨1250222697567143989602563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333927193512383972273501 1250222697567143989602563)
                    ·
                      rfl

theorem cell22_3652200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_3652200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652200 prefixEnd_3652200 := by exact prefixLift 3652200
  have htrace : WordTrace (prefixWord ++ tailWord_3652200) baseStart_3652200 baseEnd_3652200 := by
    simpa [prefixWord, tailWord_3652200, baseEnd_3652200] using wordTrace_append hprefix tailTrace_3652200
  have hstable : (prefixWord ++ tailWord_3652200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652200).length < 2 ^ (prefixWord ++ tailWord_3652200).sum := by decide
  have hdescent : baseEnd_3652200 < baseStart_3652200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652207 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 6]
def baseStart_3652207 : Nat := 118140960795 + 3652207 * 2 ^ 59
def prefixEnd_3652207 : Nat := 4983230072969 + 3 ^ 40 * 3652207 * 2
def baseEnd_3652207 : Nat := 416741697936732768225847

theorem tailTrace_3652207 : CollatzResearch.WordTrace tailWord_3652207 prefixEnd_3652207 416741697936732768225847 := by
  unfold tailWord_3652207
  simp only [CollatzResearch.WordTrace]
  refine ⟨133206932679685261141650875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88804621786456840761100583 133206932679685261141650875)
  ·
    refine ⟨199810399019527891712476313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133206932679685261141650875 199810399019527891712476313)
    ·
      refine ⟨149857799264645918784357235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199810399019527891712476313 149857799264645918784357235)
      ·
        refine ⟨224786698896968878176535853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149857799264645918784357235 224786698896968878176535853)
        ·
          refine ⟨84295012086363329316200945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224786698896968878176535853 84295012086363329316200945)
          ·
            refine ⟨63221259064772496987150709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84295012086363329316200945 63221259064772496987150709)
            ·
              refine ⟨5926993037322421592545379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63221259064772496987150709 5926993037322421592545379)
              ·
                refine ⟨8890489555983632388818069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926993037322421592545379 8890489555983632388818069)
                ·
                  refine ⟨416741697936732768225847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8890489555983632388818069 416741697936732768225847)
                  ·
                    rfl

theorem cell22_3652207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 6].length) (baseStart_3652207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652207 prefixEnd_3652207 := by exact prefixLift 3652207
  have htrace : WordTrace (prefixWord ++ tailWord_3652207) baseStart_3652207 baseEnd_3652207 := by
    simpa [prefixWord, tailWord_3652207, baseEnd_3652207] using wordTrace_append hprefix tailTrace_3652207
  have hstable : (prefixWord ++ tailWord_3652207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652207).length < 2 ^ (prefixWord ++ tailWord_3652207).sum := by decide
  have hdescent : baseEnd_3652207 < baseStart_3652207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652213 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 5]
def baseStart_3652213 : Nat := 118140960795 + 3652213 * 2 ^ 59
def prefixEnd_3652213 : Nat := 4983230072969 + 3 ^ 40 * 3652213 * 2
def baseEnd_3652213 : Nat := 416742382577605429675841

theorem tailTrace_3652213 : CollatzResearch.WordTrace tailWord_3652213 prefixEnd_3652213 416742382577605429675841 := by
  unfold tailWord_3652213
  simp only [CollatzResearch.WordTrace]
  refine ⟨133207151517663524166369293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88804767678442349444246195 133207151517663524166369293)
  ·
    refine ⟨49952681819123821562388485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133207151517663524166369293 49952681819123821562388485)
    ·
      refine ⟨9366127841085716542947841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49952681819123821562388485 9366127841085716542947841)
      ·
        refine ⟨7024595880814287407210881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9366127841085716542947841 7024595880814287407210881)
        ·
          refine ⟨5268446910610715555408161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7024595880814287407210881 5268446910610715555408161)
          ·
            refine ⟨3951335182958036666556121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5268446910610715555408161 3951335182958036666556121)
            ·
              refine ⟨2963501387218527499917091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951335182958036666556121 2963501387218527499917091)
              ·
                refine ⟨4445252080827791249875637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963501387218527499917091 4445252080827791249875637)
                ·
                  refine ⟨416742382577605429675841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4445252080827791249875637 416742382577605429675841)
                  ·
                    rfl

theorem cell22_3652213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_3652213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652213 prefixEnd_3652213 := by exact prefixLift 3652213
  have htrace : WordTrace (prefixWord ++ tailWord_3652213) baseStart_3652213 baseEnd_3652213 := by
    simpa [prefixWord, tailWord_3652213, baseEnd_3652213] using wordTrace_append hprefix tailTrace_3652213
  have hstable : (prefixWord ++ tailWord_3652213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652213).length < 2 ^ (prefixWord ++ tailWord_3652213).sum := by decide
  have hdescent : baseEnd_3652213 < baseStart_3652213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652252 : List Nat := [2, 2, 3, 2, 2, 11]
def baseStart_3652252 : Nat := 118140960795 + 3652252 * 2 ^ 59
def prefixEnd_3652252 : Nat := 4983230072969 + 3 ^ 40 * 3652252 * 2
def baseEnd_3652252 : Nat := 15435067879380656633363

theorem tailTrace_3652252 : CollatzResearch.WordTrace tailWord_3652252 prefixEnd_3652252 15435067879380656633363 := by
  unfold tailWord_3652252
  simp only [CollatzResearch.WordTrace]
  refine ⟨66604286982261116913519505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88805715976348155884692673 66604286982261116913519505)
  ·
    refine ⟨49953215236695837685139629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66604286982261116913519505 49953215236695837685139629)
    ·
      refine ⟨18732455713760939131927361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49953215236695837685139629 18732455713760939131927361)
      ·
        refine ⟨14049341785320704348945521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18732455713760939131927361 14049341785320704348945521)
        ·
          refine ⟨10537006338990528261709141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14049341785320704348945521 10537006338990528261709141)
          ·
            refine ⟨15435067879380656633363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10537006338990528261709141 15435067879380656633363)
            ·
              rfl

theorem cell22_3652252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 11].length) (baseStart_3652252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652252 prefixEnd_3652252 := by exact prefixLift 3652252
  have htrace : WordTrace (prefixWord ++ tailWord_3652252) baseStart_3652252 baseEnd_3652252 := by
    simpa [prefixWord, tailWord_3652252, baseEnd_3652252] using wordTrace_append hprefix tailTrace_3652252
  have hstable : (prefixWord ++ tailWord_3652252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652252).length < 2 ^ (prefixWord ++ tailWord_3652252).sum := by decide
  have hdescent : baseEnd_3652252 < baseStart_3652252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652269 : List Nat := [1, 5, 2, 1, 1, 2, 3, 7]
def baseStart_3652269 : Nat := 118140960795 + 3652269 * 2 ^ 59
def prefixEnd_3652269 : Nat := 4983230072969 + 3 ^ 40 * 3652269 * 2
def baseEnd_3652269 : Nat := 138916257519694534403039

theorem tailTrace_3652269 : CollatzResearch.WordTrace tailWord_3652269 prefixEnd_3652269 138916257519694534403039 := by
  unfold tailWord_3652269
  simp only [CollatzResearch.WordTrace]
  refine ⟨133209194005460645730407861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88806129336973763820271907 133209194005460645730407861)
  ·
    refine ⟨12488361938011935537225737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133209194005460645730407861 12488361938011935537225737)
    ·
      refine ⟨9366271453508951652919303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12488361938011935537225737 9366271453508951652919303)
      ·
        refine ⟨14049407180263427479378955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9366271453508951652919303 14049407180263427479378955)
        ·
          refine ⟨21074110770395141219068433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14049407180263427479378955 21074110770395141219068433)
          ·
            refine ⟨15805583077796355914301325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21074110770395141219068433 15805583077796355914301325)
            ·
              refine ⟨5927093654173633467862997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15805583077796355914301325 5927093654173633467862997)
              ·
                refine ⟨138916257519694534403039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5927093654173633467862997 138916257519694534403039)
                ·
                  rfl

theorem cell22_3652269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 7].length) (baseStart_3652269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652269 prefixEnd_3652269 := by exact prefixLift 3652269
  have htrace : WordTrace (prefixWord ++ tailWord_3652269) baseStart_3652269 baseEnd_3652269 := by
    simpa [prefixWord, tailWord_3652269, baseEnd_3652269] using wordTrace_append hprefix tailTrace_3652269
  have hstable : (prefixWord ++ tailWord_3652269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652269).length < 2 ^ (prefixWord ++ tailWord_3652269).sum := by decide
  have hdescent : baseEnd_3652269 < baseStart_3652269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652282 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_3652282 : Nat := 118140960795 + 3652282 * 2 ^ 59
def prefixEnd_3652282 : Nat := 4983230072969 + 3 ^ 40 * 3652282 * 2
def baseEnd_3652282 : Nat := 1250250767842923109052311

theorem tailTrace_3652282 : CollatzResearch.WordTrace tailWord_3652282 prefixEnd_3652282 1250250767842923109052311 := by
  unfold tailWord_3652282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33302417038603387237657775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88806445436275699300420733 33302417038603387237657775)
  ·
    refine ⟨49953625557905080856486663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33302417038603387237657775 49953625557905080856486663)
    ·
      refine ⟨74930438336857621284729995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49953625557905080856486663 74930438336857621284729995)
      ·
        refine ⟨112395657505286431927094993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74930438336857621284729995 112395657505286431927094993)
        ·
          refine ⟨84296743128964823945321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112395657505286431927094993 84296743128964823945321245)
          ·
            refine ⟨31611278673361808979495467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84296743128964823945321245 31611278673361808979495467)
            ·
              refine ⟨47416918010042713469243201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31611278673361808979495467 47416918010042713469243201)
              ·
                refine ⟨35562688507532035101932401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47416918010042713469243201 35562688507532035101932401)
                ·
                  refine ⟨26672016380649026326449301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35562688507532035101932401 26672016380649026326449301)
                  ·
                    refine ⟨1250250767842923109052311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26672016380649026326449301 1250250767842923109052311)
                    ·
                      rfl

theorem cell22_3652282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_3652282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652282 prefixEnd_3652282 := by exact prefixLift 3652282
  have htrace : WordTrace (prefixWord ++ tailWord_3652282) baseStart_3652282 baseEnd_3652282 := by
    simpa [prefixWord, tailWord_3652282, baseEnd_3652282] using wordTrace_append hprefix tailTrace_3652282
  have hstable : (prefixWord ++ tailWord_3652282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652282).length < 2 ^ (prefixWord ++ tailWord_3652282).sum := by decide
  have hdescent : baseEnd_3652282 < baseStart_3652282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652294 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3652294 : Nat := 118140960795 + 3652294 * 2 ^ 59
def prefixEnd_3652294 : Nat := 4983230072969 + 3 ^ 40 * 3652294 * 2
def baseEnd_3652294 : Nat := 1250254875688159077752275

theorem tailTrace_3652294 : CollatzResearch.WordTrace tailWord_3652294 prefixEnd_3652294 1250254875688159077752275 := by
  unfold tailWord_3652294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162815807199064843752123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88806737220246716666711957 4162815807199064843752123)
  ·
    refine ⟨6244223710798597265628185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4162815807199064843752123 6244223710798597265628185)
    ·
      refine ⟨4683167783098947949221139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6244223710798597265628185 4683167783098947949221139)
      ·
        refine ⟨7024751674648421923831709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683167783098947949221139 7024751674648421923831709)
        ·
          refine ⟨2634281877993158221436891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7024751674648421923831709 2634281877993158221436891)
          ·
            refine ⟨3951422816989737332155337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634281877993158221436891 3951422816989737332155337)
            ·
              refine ⟨2963567112742302999116503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951422816989737332155337 2963567112742302999116503)
              ·
                refine ⟨4445350669113454498674755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963567112742302999116503 4445350669113454498674755)
                ·
                  refine ⟨6668026003670181748012133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445350669113454498674755 6668026003670181748012133)
                  ·
                    refine ⟨1250254875688159077752275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668026003670181748012133 1250254875688159077752275)
                    ·
                      rfl

theorem cell22_3652294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3652294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652294 prefixEnd_3652294 := by exact prefixLift 3652294
  have htrace : WordTrace (prefixWord ++ tailWord_3652294) baseStart_3652294 baseEnd_3652294 := by
    simpa [prefixWord, tailWord_3652294, baseEnd_3652294] using wordTrace_append hprefix tailTrace_3652294
  have hstable : (prefixWord ++ tailWord_3652294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652294).length < 2 ^ (prefixWord ++ tailWord_3652294).sum := by decide
  have hdescent : baseEnd_3652294 < baseStart_3652294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652389 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3652389 : Nat := 118140960795 + 3652389 * 2 ^ 59
def prefixEnd_3652389 : Nat := 4983230072969 + 3 ^ 40 * 3652389 * 2
def baseEnd_3652389 : Nat := 1250287396129610496626983

theorem tailTrace_3652389 : CollatzResearch.WordTrace tailWord_3652389 prefixEnd_3652389 1250287396129610496626983 := by
  unfold tailWord_3652389
  simp only [CollatzResearch.WordTrace]
  refine ⟨133213570765025906224776221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88809047176683937483184147 133213570765025906224776221)
  ·
    refine ⟨49955089036884714834291083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133213570765025906224776221 49955089036884714834291083)
    ·
      refine ⟨74932633555327072251436625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49955089036884714834291083 74932633555327072251436625)
      ·
        refine ⟨56199475166495304188577469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74932633555327072251436625 56199475166495304188577469)
        ·
          refine ⟨21074803187435739070716551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56199475166495304188577469 21074803187435739070716551)
          ·
            refine ⟨31612204781153608606074827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21074803187435739070716551 31612204781153608606074827)
            ·
              refine ⟨47418307171730412909112241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31612204781153608606074827 47418307171730412909112241)
              ·
                refine ⟨35563730378797809681834181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47418307171730412909112241 35563730378797809681834181)
                ·
                  refine ⟨6668199446024589315343909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35563730378797809681834181 6668199446024589315343909)
                  ·
                    refine ⟨1250287396129610496626983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668199446024589315343909 1250287396129610496626983)
                    ·
                      rfl

theorem cell22_3652389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3652389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652389 prefixEnd_3652389 := by exact prefixLift 3652389
  have htrace : WordTrace (prefixWord ++ tailWord_3652389) baseStart_3652389 baseEnd_3652389 := by
    simpa [prefixWord, tailWord_3652389, baseEnd_3652389] using wordTrace_append hprefix tailTrace_3652389
  have hstable : (prefixWord ++ tailWord_3652389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652389).length < 2 ^ (prefixWord ++ tailWord_3652389).sum := by decide
  have hdescent : baseEnd_3652389 < baseStart_3652389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652434 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3652434 : Nat := 118140960795 + 3652434 * 2 ^ 59
def prefixEnd_3652434 : Nat := 4983230072969 + 3 ^ 40 * 3652434 * 2
def baseEnd_3652434 : Nat := 1250302800549245379251845

theorem tailTrace_3652434 : CollatzResearch.WordTrace tailWord_3652434 prefixEnd_3652434 1250302800549245379251845 := by
  unfold tailWord_3652434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33303803012465719727541089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88810141366575252606776237 33303803012465719727541089)
  ·
    refine ⟨24977852259349289795655817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33303803012465719727541089 24977852259349289795655817)
    ·
      refine ⟨18733389194511967346741863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24977852259349289795655817 18733389194511967346741863)
      ·
        refine ⟨28100083791767951020112795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18733389194511967346741863 28100083791767951020112795)
        ·
          refine ⟨42150125687651926530169193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28100083791767951020112795 42150125687651926530169193)
          ·
            refine ⟨31612594265738944897626895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42150125687651926530169193 31612594265738944897626895)
            ·
              refine ⟨47418891398608417346440343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31612594265738944897626895 47418891398608417346440343)
              ·
                refine ⟨71128337097912626019660515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47418891398608417346440343 71128337097912626019660515)
                ·
                  refine ⟨106692505646868939029490773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71128337097912626019660515 106692505646868939029490773)
                  ·
                    refine ⟨1250302800549245379251845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106692505646868939029490773 1250302800549245379251845)
                    ·
                      rfl

theorem cell22_3652434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3652434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652434 prefixEnd_3652434 := by exact prefixLift 3652434
  have htrace : WordTrace (prefixWord ++ tailWord_3652434) baseStart_3652434 baseEnd_3652434 := by
    simpa [prefixWord, tailWord_3652434, baseEnd_3652434] using wordTrace_append hprefix tailTrace_3652434
  have hstable : (prefixWord ++ tailWord_3652434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652434).length < 2 ^ (prefixWord ++ tailWord_3652434).sum := by decide
  have hdescent : baseEnd_3652434 < baseStart_3652434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652511 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 6]
def baseStart_3652511 : Nat := 118140960795 + 3652511 * 2 ^ 59
def prefixEnd_3652511 : Nat := 4983230072969 + 3 ^ 40 * 3652511 * 2
def baseEnd_3652511 : Nat := 416776386407614281692203

theorem tailTrace_3652511 : CollatzResearch.WordTrace tailWord_3652511 prefixEnd_3652511 416776386407614281692203 := by
  unfold tailWord_3652511
  simp only [CollatzResearch.WordTrace]
  refine ⟨133218020470583921060717387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88812013647055947373811591 133218020470583921060717387)
  ·
    refine ⟨199827030705875881591076081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133218020470583921060717387 199827030705875881591076081)
    ·
      refine ⟨149870273029406911193307061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199827030705875881591076081 149870273029406911193307061)
      ·
        refine ⟨14050338096506897924372537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149870273029406911193307061 14050338096506897924372537)
        ·
          refine ⟨10537753572380173443279403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14050338096506897924372537 10537753572380173443279403)
          ·
            refine ⟨15806630358570260164919105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537753572380173443279403 15806630358570260164919105)
            ·
              refine ⟨11854972768927695123689329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15806630358570260164919105 11854972768927695123689329)
              ·
                refine ⟨8891229576695771342766997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11854972768927695123689329 8891229576695771342766997)
                ·
                  refine ⟨416776386407614281692203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8891229576695771342766997 416776386407614281692203)
                  ·
                    rfl

theorem cell22_3652511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 6].length) (baseStart_3652511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652511 prefixEnd_3652511 := by exact prefixLift 3652511
  have htrace : WordTrace (prefixWord ++ tailWord_3652511) baseStart_3652511 baseEnd_3652511 := by
    simpa [prefixWord, tailWord_3652511, baseEnd_3652511] using wordTrace_append hprefix tailTrace_3652511
  have hstable : (prefixWord ++ tailWord_3652511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652511).length < 2 ^ (prefixWord ++ tailWord_3652511).sum := by decide
  have hdescent : baseEnd_3652511 < baseStart_3652511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652513 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3652513 : Nat := 118140960795 + 3652513 * 2 ^ 59
def prefixEnd_3652513 : Nat := 4983230072969 + 3 ^ 40 * 3652513 * 2
def baseEnd_3652513 : Nat := 1250329843863715506526603

theorem tailTrace_3652513 : CollatzResearch.WordTrace tailWord_3652513 prefixEnd_3652513 1250329843863715506526603 := by
  unfold tailWord_3652513
  simp only [CollatzResearch.WordTrace]
  refine ⟨133218093416576675402290193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88812062277717783601526795 133218093416576675402290193)
  ·
    refine ⟨99913570062432506551717645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133218093416576675402290193 99913570062432506551717645)
    ·
      refine ⟨37467588773412189956894117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99913570062432506551717645 37467588773412189956894117)
      ·
        refine ⟨7025172895014785616917647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37467588773412189956894117 7025172895014785616917647)
        ·
          refine ⟨10537759342522178425376471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025172895014785616917647 10537759342522178425376471)
          ·
            refine ⟨15806639013783267638064707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537759342522178425376471 15806639013783267638064707)
            ·
              refine ⟨23709958520674901457097061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15806639013783267638064707 23709958520674901457097061)
              ·
                refine ⟨4445617222626544023205699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23709958520674901457097061 4445617222626544023205699)
                ·
                  refine ⟨6668425833939816034808549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445617222626544023205699 6668425833939816034808549)
                  ·
                    refine ⟨1250329843863715506526603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668425833939816034808549 1250329843863715506526603)
                    ·
                      rfl

theorem cell22_3652513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3652513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652513 prefixEnd_3652513 := by exact prefixLift 3652513
  have htrace : WordTrace (prefixWord ++ tailWord_3652513) baseStart_3652513 baseEnd_3652513 := by
    simpa [prefixWord, tailWord_3652513, baseEnd_3652513] using wordTrace_append hprefix tailTrace_3652513
  have hstable : (prefixWord ++ tailWord_3652513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652513).length < 2 ^ (prefixWord ++ tailWord_3652513).sum := by decide
  have hdescent : baseEnd_3652513 < baseStart_3652513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652556 : List Nat := [2, 2, 1, 4, 1, 1, 4, 7]
def baseStart_3652556 : Nat := 118140960795 + 3652556 * 2 ^ 59
def prefixEnd_3652556 : Nat := 4983230072969 + 3 ^ 40 * 3652556 * 2
def baseEnd_3652556 : Nat := 138927173738053080855719

theorem tailTrace_3652556 : CollatzResearch.WordTrace tailWord_3652556 prefixEnd_3652556 138927173738053080855719 := by
  unfold tailWord_3652556
  simp only [CollatzResearch.WordTrace]
  refine ⟨66609830877710446873052761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88813107836947262497403681 66609830877710446873052761)
  ·
    refine ⟨49957373158282835154789571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66609830877710446873052761 49957373158282835154789571)
    ·
      refine ⟨74936059737424252732184357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49957373158282835154789571 74936059737424252732184357)
      ·
        refine ⟨14050511200767047387284567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74936059737424252732184357 14050511200767047387284567)
        ·
          refine ⟨21075766801150571080926851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14050511200767047387284567 21075766801150571080926851)
          ·
            refine ⟨31613650201725856621390277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21075766801150571080926851 31613650201725856621390277)
            ·
              refine ⟨5927559412823598116510677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31613650201725856621390277 5927559412823598116510677)
              ·
                refine ⟨138927173738053080855719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5927559412823598116510677 138927173738053080855719)
                ·
                  rfl

theorem cell22_3652556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_3652556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652556 prefixEnd_3652556 := by exact prefixLift 3652556
  have htrace : WordTrace (prefixWord ++ tailWord_3652556) baseStart_3652556 baseEnd_3652556 := by
    simpa [prefixWord, tailWord_3652556, baseEnd_3652556] using wordTrace_append hprefix tailTrace_3652556
  have hstable : (prefixWord ++ tailWord_3652556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652556).length < 2 ^ (prefixWord ++ tailWord_3652556).sum := by decide
  have hdescent : baseEnd_3652556 < baseStart_3652556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652596 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3652596 : Nat := 118140960795 + 3652596 * 2 ^ 59
def prefixEnd_3652596 : Nat := 4983230072969 + 3 ^ 40 * 3652596 * 2
def baseEnd_3652596 : Nat := 416786085486643652233783

theorem tailTrace_3652596 : CollatzResearch.WordTrace tailWord_3652596 prefixEnd_3652596 416786085486643652233783 := by
  unfold tailWord_3652596
  simp only [CollatzResearch.WordTrace]
  refine ⟨66610560337637990288780821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88814080450183987051707761 66610560337637990288780821)
  ·
    refine ⟨3122370015826780794786601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66610560337637990288780821 3122370015826780794786601)
    ·
      refine ⟨2341777511870085596089951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3122370015826780794786601 2341777511870085596089951)
      ·
        refine ⟨3512666267805128394134927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341777511870085596089951 3512666267805128394134927)
        ·
          refine ⟨5268999401707692591202391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512666267805128394134927 5268999401707692591202391)
          ·
            refine ⟨7903499102561538886803587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268999401707692591202391 7903499102561538886803587)
            ·
              refine ⟨11855248653842308330205381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903499102561538886803587 11855248653842308330205381)
              ·
                refine ⟨2222859122595432811913509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11855248653842308330205381 2222859122595432811913509)
                ·
                  refine ⟨416786085486643652233783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222859122595432811913509 416786085486643652233783)
                  ·
                    rfl

theorem cell22_3652596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3652596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652596 prefixEnd_3652596 := by exact prefixLift 3652596
  have htrace : WordTrace (prefixWord ++ tailWord_3652596) baseStart_3652596 baseEnd_3652596 := by
    simpa [prefixWord, tailWord_3652596, baseEnd_3652596] using wordTrace_append hprefix tailTrace_3652596
  have hstable : (prefixWord ++ tailWord_3652596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652596).length < 2 ^ (prefixWord ++ tailWord_3652596).sum := by decide
  have hdescent : baseEnd_3652596 < baseStart_3652596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652616 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_3652616 : Nat := 118140960795 + 3652616 * 2 ^ 59
def prefixEnd_3652616 : Nat := 4983230072969 + 3 ^ 40 * 3652616 * 2
def baseEnd_3652616 : Nat := 1250365102868657571201287

theorem tailTrace_3652616 : CollatzResearch.WordTrace tailWord_3652616 prefixEnd_3652616 1250365102868657571201287 := by
  unfold tailWord_3652616
  simp only [CollatzResearch.WordTrace]
  refine ⟨66610925067601761996644851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88814566756802349328859801 66610925067601761996644851)
  ·
    refine ⟨99916387601402642994967277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66610925067601761996644851 99916387601402642994967277)
    ·
      refine ⟨37468645350525991123112729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99916387601402642994967277 37468645350525991123112729)
      ·
        refine ⟨28101484012894493342334547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37468645350525991123112729 28101484012894493342334547)
        ·
          refine ⟨42152226019341740013501821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28101484012894493342334547 42152226019341740013501821)
          ·
            refine ⟨15807084757253152505063183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42152226019341740013501821 15807084757253152505063183)
            ·
              refine ⟨23710627135879728757594775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15807084757253152505063183 23710627135879728757594775)
              ·
                refine ⟨35565940703819593136392163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23710627135879728757594775 35565940703819593136392163)
                ·
                  refine ⟨53348911055729389704588245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35565940703819593136392163 53348911055729389704588245)
                  ·
                    refine ⟨1250365102868657571201287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53348911055729389704588245 1250365102868657571201287)
                    ·
                      rfl

theorem cell22_3652616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_3652616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652616 prefixEnd_3652616 := by exact prefixLift 3652616
  have htrace : WordTrace (prefixWord ++ tailWord_3652616) baseStart_3652616 baseEnd_3652616 := by
    simpa [prefixWord, tailWord_3652616, baseEnd_3652616] using wordTrace_append hprefix tailTrace_3652616
  have hstable : (prefixWord ++ tailWord_3652616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652616).length < 2 ^ (prefixWord ++ tailWord_3652616).sum := by decide
  have hdescent : baseEnd_3652616 < baseStart_3652616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652618 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_3652618 : Nat := 118140960795 + 3652618 * 2 ^ 59
def prefixEnd_3652618 : Nat := 4983230072969 + 3 ^ 40 * 3652618 * 2
def baseEnd_3652618 : Nat := 416788595836510077550427

theorem tailTrace_3652618 : CollatzResearch.WordTrace tailWord_3652618 prefixEnd_3652618 416788595836510077550427 := by
  unfold tailWord_3652618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305480770299069583715627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88814615387464185556575005 33305480770299069583715627)
  ·
    refine ⟨49958221155448604375573441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33305480770299069583715627 49958221155448604375573441)
    ·
      refine ⟨37468665866586453281680081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49958221155448604375573441 37468665866586453281680081)
      ·
        refine ⟨28101499399939839961260061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37468665866586453281680081 28101499399939839961260061)
        ·
          refine ⟨10538062274977439985472523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28101499399939839961260061 10538062274977439985472523)
          ·
            refine ⟨15807093412466159978208785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538062274977439985472523 15807093412466159978208785)
            ·
              refine ⟨11855320059349619983656589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15807093412466159978208785 11855320059349619983656589)
              ·
                refine ⟨4445745022256107493871221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855320059349619983656589 4445745022256107493871221)
                ·
                  refine ⟨416788595836510077550427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4445745022256107493871221 416788595836510077550427)
                  ·
                    rfl

theorem cell22_3652618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_3652618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652618 prefixEnd_3652618 := by exact prefixLift 3652618
  have htrace : WordTrace (prefixWord ++ tailWord_3652618) baseStart_3652618 baseEnd_3652618 := by
    simpa [prefixWord, tailWord_3652618, baseEnd_3652618] using wordTrace_append hprefix tailTrace_3652618
  have hstable : (prefixWord ++ tailWord_3652618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652618).length < 2 ^ (prefixWord ++ tailWord_3652618).sum := by decide
  have hdescent : baseEnd_3652618 < baseStart_3652618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652626 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3652626 : Nat := 118140960795 + 3652626 * 2 ^ 59
def prefixEnd_3652626 : Nat := 4983230072969 + 3 ^ 40 * 3652626 * 2
def baseEnd_3652626 : Nat := 1250368526073020878451257

theorem tailTrace_3652626 : CollatzResearch.WordTrace tailWord_3652626 prefixEnd_3652626 1250368526073020878451257 := by
  unfold tailWord_3652626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305553716291823925288433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88814809910111530467435821 33305553716291823925288433)
  ·
    refine ⟨24979165287218867943966325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33305553716291823925288433 24979165287218867943966325)
    ·
      refine ⟨2341796745676768869746843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24979165287218867943966325 2341796745676768869746843)
      ·
        refine ⟨3512695118515153304620265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341796745676768869746843 3512695118515153304620265)
        ·
          refine ⟨2634521338886364978465199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512695118515153304620265 2634521338886364978465199)
          ·
            refine ⟨3951782008329547467697799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634521338886364978465199 3951782008329547467697799)
            ·
              refine ⟨5927673012494321201546699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951782008329547467697799 5927673012494321201546699)
              ·
                refine ⟨8891509518741481802320049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927673012494321201546699 8891509518741481802320049)
                ·
                  refine ⟨6668632139056111351740037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8891509518741481802320049 6668632139056111351740037)
                  ·
                    refine ⟨1250368526073020878451257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668632139056111351740037 1250368526073020878451257)
                    ·
                      rfl

theorem cell22_3652626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3652626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652626 prefixEnd_3652626 := by exact prefixLift 3652626
  have htrace : WordTrace (prefixWord ++ tailWord_3652626) baseStart_3652626 baseEnd_3652626 := by
    simpa [prefixWord, tailWord_3652626, baseEnd_3652626] using wordTrace_append hprefix tailTrace_3652626
  have hstable : (prefixWord ++ tailWord_3652626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652626).length < 2 ^ (prefixWord ++ tailWord_3652626).sum := by decide
  have hdescent : baseEnd_3652626 < baseStart_3652626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652693 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3652693 : Nat := 118140960795 + 3652693 * 2 ^ 59
def prefixEnd_3652693 : Nat := 4983230072969 + 3 ^ 40 * 3652693 * 2
def baseEnd_3652693 : Nat := 1250391461542255037026051

theorem tailTrace_3652693 : CollatzResearch.WordTrace tailWord_3652693 prefixEnd_3652693 1250391461542255037026051 := by
  unfold tailWord_3652693
  simp only [CollatzResearch.WordTrace]
  refine ⟨133224658555924566143842733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88816439037283044095895155 133224658555924566143842733)
  ·
    refine ⟨49959246958471712303941025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133224658555924566143842733 49959246958471712303941025)
    ·
      refine ⟨37469435218853784227955769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49959246958471712303941025 37469435218853784227955769)
      ·
        refine ⟨28102076414140338170966827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37469435218853784227955769 28102076414140338170966827)
        ·
          refine ⟨42153114621210507256450241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28102076414140338170966827 42153114621210507256450241)
          ·
            refine ⟨31614835965907880442337681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42153114621210507256450241 31614835965907880442337681)
            ·
              refine ⟨23711126974430910331753261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31614835965907880442337681 23711126974430910331753261)
              ·
                refine ⟨8891672615411591374407473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23711126974430910331753261 8891672615411591374407473)
                ·
                  refine ⟨6668754461558693530805605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8891672615411591374407473 6668754461558693530805605)
                  ·
                    refine ⟨1250391461542255037026051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668754461558693530805605 1250391461542255037026051)
                    ·
                      rfl

theorem cell22_3652693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3652693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652693 prefixEnd_3652693 := by exact prefixLift 3652693
  have htrace : WordTrace (prefixWord ++ tailWord_3652693) baseStart_3652693 baseEnd_3652693 := by
    simpa [prefixWord, tailWord_3652693, baseEnd_3652693] using wordTrace_append hprefix tailTrace_3652693
  have hstable : (prefixWord ++ tailWord_3652693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652693).length < 2 ^ (prefixWord ++ tailWord_3652693).sum := by decide
  have hdescent : baseEnd_3652693 < baseStart_3652693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652729 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 2, 3]
def baseStart_3652729 : Nat := 118140960795 + 3652729 * 2 ^ 59
def prefixEnd_3652729 : Nat := 4983230072969 + 3 ^ 40 * 3652729 * 2
def baseEnd_3652729 : Nat := 1250403785077962943125941

theorem tailTrace_3652729 : CollatzResearch.WordTrace tailWord_3652729 prefixEnd_3652729 1250403785077962943125941 := by
  unfold tailWord_3652729
  simp only [CollatzResearch.WordTrace]
  refine ⟨133225971583794144292153241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88817314389196096194768827 133225971583794144292153241)
  ·
    refine ⟨99919478687845608219114931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133225971583794144292153241 99919478687845608219114931)
    ·
      refine ⟨149879218031768412328672397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99919478687845608219114931 149879218031768412328672397)
      ·
        refine ⟨56204706761913154623252149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149879218031768412328672397 56204706761913154623252149)
        ·
          refine ⟨5269191258929358245929889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56204706761913154623252149 5269191258929358245929889)
          ·
            refine ⟨3951893444197018684447417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269191258929358245929889 3951893444197018684447417)
            ·
              refine ⟨2963920083147764013335563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951893444197018684447417 2963920083147764013335563)
              ·
                refine ⟨4445880124721646020003345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963920083147764013335563 4445880124721646020003345)
                ·
                  refine ⟨3334410093541234515002509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4445880124721646020003345 3334410093541234515002509)
                  ·
                    refine ⟨1250403785077962943125941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334410093541234515002509 1250403785077962943125941)
                    ·
                      rfl

theorem cell22_3652729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_3652729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652729 prefixEnd_3652729 := by exact prefixLift 3652729
  have htrace : WordTrace (prefixWord ++ tailWord_3652729) baseStart_3652729 baseEnd_3652729 := by
    simpa [prefixWord, tailWord_3652729, baseEnd_3652729] using wordTrace_append hprefix tailTrace_3652729
  have hstable : (prefixWord ++ tailWord_3652729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652729).length < 2 ^ (prefixWord ++ tailWord_3652729).sum := by decide
  have hdescent : baseEnd_3652729 < baseStart_3652729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652768 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_3652768 : Nat := 118140960795 + 3652768 * 2 ^ 59
def prefixEnd_3652768 : Nat := 4983230072969 + 3 ^ 40 * 3652768 * 2
def baseEnd_3652768 : Nat := 1250417135574979841400821

theorem tailTrace_3652768 : CollatzResearch.WordTrace tailWord_3652768 prefixEnd_3652768 1250417135574979841400821 := by
  unfold tailWord_3652768
  simp only [CollatzResearch.WordTrace]
  refine ⟨66613697015326426976411479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88818262687101902635215305 66613697015326426976411479)
  ·
    refine ⟨99920545522989640464617219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66613697015326426976411479 99920545522989640464617219)
    ·
      refine ⟨149880818284484460696925829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99920545522989640464617219 149880818284484460696925829)
      ·
        refine ⟨28102653428340836380673593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149880818284484460696925829 28102653428340836380673593)
        ·
          refine ⟨21076990071255627285505195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28102653428340836380673593 21076990071255627285505195)
          ·
            refine ⟨31615485106883440928257793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21076990071255627285505195 31615485106883440928257793)
            ·
              refine ⟨23711613830162580696193345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31615485106883440928257793 23711613830162580696193345)
              ·
                refine ⟨17783710372621935522145009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23711613830162580696193345 17783710372621935522145009)
                ·
                  refine ⟨13337782779466451641608757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17783710372621935522145009 13337782779466451641608757)
                  ·
                    refine ⟨1250417135574979841400821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13337782779466451641608757 1250417135574979841400821)
                    ·
                      rfl

theorem cell22_3652768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_3652768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652768 prefixEnd_3652768 := by exact prefixLift 3652768
  have htrace : WordTrace (prefixWord ++ tailWord_3652768) baseStart_3652768 baseEnd_3652768 := by
    simpa [prefixWord, tailWord_3652768, baseEnd_3652768] using wordTrace_append hprefix tailTrace_3652768
  have hstable : (prefixWord ++ tailWord_3652768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652768).length < 2 ^ (prefixWord ++ tailWord_3652768).sum := by decide
  have hdescent : baseEnd_3652768 < baseStart_3652768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652783 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 3, 4]
def baseStart_3652783 : Nat := 118140960795 + 3652783 * 2 ^ 59
def prefixEnd_3652783 : Nat := 4983230072969 + 3 ^ 40 * 3652783 * 2
def baseEnd_3652783 : Nat := 1250422270381524802275775

theorem tailTrace_3652783 : CollatzResearch.WordTrace tailWord_3652783 prefixEnd_3652783 1250422270381524802275775 := by
  unfold tailWord_3652783
  simp only [CollatzResearch.WordTrace]
  refine ⟨133227941125598511514619003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88818627417065674343079335 133227941125598511514619003)
  ·
    refine ⟨199841911688397767271928505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133227941125598511514619003 199841911688397767271928505)
    ·
      refine ⟨149881433766298325453946379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199841911688397767271928505 149881433766298325453946379)
      ·
        refine ⟨224822150649447488180919569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149881433766298325453946379 224822150649447488180919569)
        ·
          refine ⟨168616612987085616135689677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224822150649447488180919569 168616612987085616135689677)
          ·
            refine ⟨63231229870157106050883629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168616612987085616135689677 63231229870157106050883629)
            ·
              refine ⟨23711711201308914769081361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63231229870157106050883629 23711711201308914769081361)
              ·
                refine ⟨17783783400981686076811021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23711711201308914769081361 17783783400981686076811021)
                ·
                  refine ⟨6668918775368132278804133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17783783400981686076811021 6668918775368132278804133)
                  ·
                    refine ⟨1250422270381524802275775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6668918775368132278804133 1250422270381524802275775)
                    ·
                      rfl

theorem cell22_3652783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_3652783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652783 prefixEnd_3652783 := by exact prefixLift 3652783
  have htrace : WordTrace (prefixWord ++ tailWord_3652783) baseStart_3652783 baseEnd_3652783 := by
    simpa [prefixWord, tailWord_3652783, baseEnd_3652783] using wordTrace_append hprefix tailTrace_3652783
  have hstable : (prefixWord ++ tailWord_3652783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652783).length < 2 ^ (prefixWord ++ tailWord_3652783).sum := by decide
  have hdescent : baseEnd_3652783 < baseStart_3652783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652785 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3652785 : Nat := 118140960795 + 3652785 * 2 ^ 59
def prefixEnd_3652785 : Nat := 4983230072969 + 3 ^ 40 * 3652785 * 2
def baseEnd_3652785 : Nat := 1250422955022397463725769

theorem tailTrace_3652785 : CollatzResearch.WordTrace tailWord_3652785 prefixEnd_3652785 1250422955022397463725769 := by
  unfold tailWord_3652785
  simp only [CollatzResearch.WordTrace]
  refine ⟨133228014071591265856191809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88818676047727510570794539 133228014071591265856191809)
  ·
    refine ⟨99921010553693449392143857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133228014071591265856191809 99921010553693449392143857)
    ·
      refine ⟨74940757915270087044107893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99921010553693449392143857 74940757915270087044107893)
      ·
        refine ⟨7025696054556570660385115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74940757915270087044107893 7025696054556570660385115)
        ·
          refine ⟨10538544081834855990577673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025696054556570660385115 10538544081834855990577673)
          ·
            refine ⟨7903908061376141992933255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10538544081834855990577673 7903908061376141992933255)
            ·
              refine ⟨11855862092064212989399883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903908061376141992933255 11855862092064212989399883)
              ·
                refine ⟨17783793138096319484099825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11855862092064212989399883 17783793138096319484099825)
                ·
                  refine ⟨13337844853572239613074869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17783793138096319484099825 13337844853572239613074869)
                  ·
                    refine ⟨1250422955022397463725769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13337844853572239613074869 1250422955022397463725769)
                    ·
                      rfl

theorem cell22_3652785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3652785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652785 prefixEnd_3652785 := by exact prefixLift 3652785
  have htrace : WordTrace (prefixWord ++ tailWord_3652785) baseStart_3652785 baseEnd_3652785 := by
    simpa [prefixWord, tailWord_3652785, baseEnd_3652785] using wordTrace_append hprefix tailTrace_3652785
  have hstable : (prefixWord ++ tailWord_3652785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652785).length < 2 ^ (prefixWord ++ tailWord_3652785).sum := by decide
  have hdescent : baseEnd_3652785 < baseStart_3652785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652845 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3652845 : Nat := 118140960795 + 3652845 * 2 ^ 59
def prefixEnd_3652845 : Nat := 4983230072969 + 3 ^ 40 * 3652845 * 2
def baseEnd_3652845 : Nat := 1250443494248577307225585

theorem tailTrace_3652845 : CollatzResearch.WordTrace tailWord_3652845 prefixEnd_3652845 1250443494248577307225585 := by
  unfold tailWord_3652845
  simp only [CollatzResearch.WordTrace]
  refine ⟨133230202451373896103375989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88820134967582597402250659 133230202451373896103375989)
  ·
    refine ⟨12490331479816302759691499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133230202451373896103375989 12490331479816302759691499)
    ·
      refine ⟨18735497219724454139537249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12490331479816302759691499 18735497219724454139537249)
      ·
        refine ⟨14051622914793340604652937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18735497219724454139537249 14051622914793340604652937)
        ·
          refine ⟨10538717186095005453489703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14051622914793340604652937 10538717186095005453489703)
          ·
            refine ⟨15808075779142508180234555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538717186095005453489703 15808075779142508180234555)
            ·
              refine ⟨23712113668713762270351833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808075779142508180234555 23712113668713762270351833)
              ·
                refine ⟨17784085251535321702763875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23712113668713762270351833 17784085251535321702763875)
                ·
                  refine ⟨26676127877302982554145813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17784085251535321702763875 26676127877302982554145813)
                  ·
                    refine ⟨1250443494248577307225585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26676127877302982554145813 1250443494248577307225585)
                    ·
                      rfl

theorem cell22_3652845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3652845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652845 prefixEnd_3652845 := by exact prefixLift 3652845
  have htrace : WordTrace (prefixWord ++ tailWord_3652845) baseStart_3652845 baseEnd_3652845 := by
    simpa [prefixWord, tailWord_3652845, baseEnd_3652845] using wordTrace_append hprefix tailTrace_3652845
  have hstable : (prefixWord ++ tailWord_3652845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652845).length < 2 ^ (prefixWord ++ tailWord_3652845).sum := by decide
  have hdescent : baseEnd_3652845 < baseStart_3652845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652847 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 1, 5]
def baseStart_3652847 : Nat := 118140960795 + 3652847 * 2 ^ 59
def prefixEnd_3652847 : Nat := 4983230072969 + 3 ^ 40 * 3652847 * 2
def baseEnd_3652847 : Nat := 1250444178889449968675579

theorem tailTrace_3652847 : CollatzResearch.WordTrace tailWord_3652847 prefixEnd_3652847 1250444178889449968675579 := by
  unfold tailWord_3652847
  simp only [CollatzResearch.WordTrace]
  refine ⟨133230275397366650444948795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88820183598244433629965863 133230275397366650444948795)
  ·
    refine ⟨199845413096049975667423193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133230275397366650444948795 199845413096049975667423193)
    ·
      refine ⟨149884059822037481750567395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199845413096049975667423193 149884059822037481750567395)
      ·
        refine ⟨224826089733056222625851093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149884059822037481750567395 224826089733056222625851093)
        ·
          refine ⟨5269361478118505217793385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 224826089733056222625851093 5269361478118505217793385)
          ·
            refine ⟨3952021108588878913345039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269361478118505217793385 3952021108588878913345039)
            ·
              refine ⟨5928031662883318370017559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952021108588878913345039 5928031662883318370017559)
              ·
                refine ⟨8892047494324977555026339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928031662883318370017559 8892047494324977555026339)
                ·
                  refine ⟨13338071241487466332539509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892047494324977555026339 13338071241487466332539509)
                  ·
                    refine ⟨1250444178889449968675579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13338071241487466332539509 1250444178889449968675579)
                    ·
                      rfl

theorem cell22_3652847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_3652847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652847 prefixEnd_3652847 := by exact prefixLift 3652847
  have htrace : WordTrace (prefixWord ++ tailWord_3652847) baseStart_3652847 baseEnd_3652847 := by
    simpa [prefixWord, tailWord_3652847, baseEnd_3652847] using wordTrace_append hprefix tailTrace_3652847
  have hstable : (prefixWord ++ tailWord_3652847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652847).length < 2 ^ (prefixWord ++ tailWord_3652847).sum := by decide
  have hdescent : baseEnd_3652847 < baseStart_3652847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652858 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_3652858 : Nat := 118140960795 + 3652858 * 2 ^ 59
def prefixEnd_3652858 : Nat := 4983230072969 + 3 ^ 40 * 3652858 * 2
def baseEnd_3652858 : Nat := 1250447944414249606650545

theorem tailTrace_3652858 : CollatzResearch.WordTrace tailWord_3652858 prefixEnd_3652858 1250447944414249606650545 := by
  unfold tailWord_3652858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307669150081699830899807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88820451066884532882399485 33307669150081699830899807)
  ·
    refine ⟨49961503725122549746349711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33307669150081699830899807 49961503725122549746349711)
    ·
      refine ⟨74942255587683824619524567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49961503725122549746349711 74942255587683824619524567)
      ·
        refine ⟨112413383381525736929286851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74942255587683824619524567 112413383381525736929286851)
        ·
          refine ⟨168620075072288605393930277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112413383381525736929286851 168620075072288605393930277)
          ·
            refine ⟨31616264076054113511361927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168620075072288605393930277 31616264076054113511361927)
            ·
              refine ⟨47424396114081170267042891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31616264076054113511361927 47424396114081170267042891)
              ·
                refine ⟨71136594171121755400564337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47424396114081170267042891 71136594171121755400564337)
                ·
                  refine ⟨53352445628341316550423253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71136594171121755400564337 53352445628341316550423253)
                  ·
                    refine ⟨1250447944414249606650545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53352445628341316550423253 1250447944414249606650545)
                    ·
                      rfl

theorem cell22_3652858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_3652858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652858 prefixEnd_3652858 := by exact prefixLift 3652858
  have htrace : WordTrace (prefixWord ++ tailWord_3652858) baseStart_3652858 baseEnd_3652858 := by
    simpa [prefixWord, tailWord_3652858, baseEnd_3652858] using wordTrace_append hprefix tailTrace_3652858
  have hstable : (prefixWord ++ tailWord_3652858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652858).length < 2 ^ (prefixWord ++ tailWord_3652858).sum := by decide
  have hdescent : baseEnd_3652858 < baseStart_3652858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652860 : List Nat := [2, 2, 2, 1, 5, 1, 1, 8]
def baseStart_3652860 : Nat := 118140960795 + 3652860 * 2 ^ 59
def prefixEnd_3652860 : Nat := 4983230072969 + 3 ^ 40 * 3652860 * 2
def baseEnd_3652860 : Nat := 138938736561680252011171

theorem tailTrace_3652860 : CollatzResearch.WordTrace tailWord_3652860 prefixEnd_3652860 138938736561680252011171 := by
  unfold tailWord_3652860
  simp only [CollatzResearch.WordTrace]
  refine ⟨66615374773159776832586017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88820499697546369110114689 66615374773159776832586017)
  ·
    refine ⟨49961531079869832624439513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66615374773159776832586017 49961531079869832624439513)
    ·
      refine ⟨37471148309902374468329635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49961531079869832624439513 37471148309902374468329635)
      ·
        refine ⟨56206722464853561702494453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37471148309902374468329635 56206722464853561702494453)
        ·
          refine ⟨5269380231080021409608855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56206722464853561702494453 5269380231080021409608855)
          ·
            refine ⟨7904070346620032114413283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269380231080021409608855 7904070346620032114413283)
            ·
              refine ⟨11856105519930048171619925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904070346620032114413283 11856105519930048171619925)
              ·
                refine ⟨138938736561680252011171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11856105519930048171619925 138938736561680252011171)
                ·
                  rfl

theorem cell22_3652860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_3652860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652860 prefixEnd_3652860 := by exact prefixLift 3652860
  have htrace : WordTrace (prefixWord ++ tailWord_3652860) baseStart_3652860 baseEnd_3652860 := by
    simpa [prefixWord, tailWord_3652860, baseEnd_3652860] using wordTrace_append hprefix tailTrace_3652860
  have hstable : (prefixWord ++ tailWord_3652860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652860).length < 2 ^ (prefixWord ++ tailWord_3652860).sum := by decide
  have hdescent : baseEnd_3652860 < baseStart_3652860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652866 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3652866 : Nat := 118140960795 + 3652866 * 2 ^ 59
def prefixEnd_3652866 : Nat := 4983230072969 + 3 ^ 40 * 3652866 * 2
def baseEnd_3652866 : Nat := 416816894325913417483507

theorem tailTrace_3652866 : CollatzResearch.WordTrace tailWord_3652866 prefixEnd_3652866 416816894325913417483507 := by
  unfold tailWord_3652866
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307742096074454172472613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88820645589531877793260301 33307742096074454172472613)
  ·
    refine ⟨6245201643013960157338615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33307742096074454172472613 6245201643013960157338615)
    ·
      refine ⟨9367802464520940236007923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6245201643013960157338615 9367802464520940236007923)
      ·
        refine ⟨14051703696781410354011885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9367802464520940236007923 14051703696781410354011885)
        ·
          refine ⟨5269388886293028882754457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14051703696781410354011885 5269388886293028882754457)
          ·
            refine ⟨3952041664719771662065843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269388886293028882754457 3952041664719771662065843)
            ·
              refine ⟨5928062497079657493098765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952041664719771662065843 5928062497079657493098765)
              ·
                refine ⟨2223023436404871559912037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5928062497079657493098765 2223023436404871559912037)
                ·
                  refine ⟨416816894325913417483507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2223023436404871559912037 416816894325913417483507)
                  ·
                    rfl

theorem cell22_3652866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3652866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652866 prefixEnd_3652866 := by exact prefixLift 3652866
  have htrace : WordTrace (prefixWord ++ tailWord_3652866) baseStart_3652866 baseEnd_3652866 := by
    simpa [prefixWord, tailWord_3652866, baseEnd_3652866] using wordTrace_append hprefix tailTrace_3652866
  have hstable : (prefixWord ++ tailWord_3652866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652866).length < 2 ^ (prefixWord ++ tailWord_3652866).sum := by decide
  have hdescent : baseEnd_3652866 < baseStart_3652866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652892 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3652892 : Nat := 118140960795 + 3652892 * 2 ^ 59
def prefixEnd_3652892 : Nat := 4983230072969 + 3 ^ 40 * 3652892 * 2
def baseEnd_3652892 : Nat := 1250459583309084851300441

theorem tailTrace_3652892 : CollatzResearch.WordTrace tailWord_3652892 prefixEnd_3652892 1250459583309084851300441 := by
  unfold tailWord_3652892
  simp only [CollatzResearch.WordTrace]
  refine ⟨66615958341101811565168465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88821277788135748753557953 66615958341101811565168465)
  ·
    refine ⟨49961968755826358673876349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66615958341101811565168465 49961968755826358673876349)
    ·
      refine ⟨18735738283434884502703631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49961968755826358673876349 18735738283434884502703631)
      ·
        refine ⟨28103607425152326754055447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18735738283434884502703631 28103607425152326754055447)
        ·
          refine ⟨42155411137728490131083171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28103607425152326754055447 42155411137728490131083171)
          ·
            refine ⟨63233116706592735196624757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42155411137728490131083171 63233116706592735196624757)
            ·
              refine ⟨5928104691243068924683571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63233116706592735196624757 5928104691243068924683571)
              ·
                refine ⟨8892157036864603387025357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928104691243068924683571 8892157036864603387025357)
                ·
                  refine ⟨3334558888824226270134509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8892157036864603387025357 3334558888824226270134509)
                  ·
                    refine ⟨1250459583309084851300441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334558888824226270134509 1250459583309084851300441)
                    ·
                      rfl

theorem cell22_3652892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3652892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652892 prefixEnd_3652892 := by exact prefixLift 3652892
  have htrace : WordTrace (prefixWord ++ tailWord_3652892) baseStart_3652892 baseEnd_3652892 := by
    simpa [prefixWord, tailWord_3652892, baseEnd_3652892] using wordTrace_append hprefix tailTrace_3652892
  have hstable : (prefixWord ++ tailWord_3652892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652892).length < 2 ^ (prefixWord ++ tailWord_3652892).sum := by decide
  have hdescent : baseEnd_3652892 < baseStart_3652892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652894 : List Nat := [4, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3652894 : Nat := 118140960795 + 3652894 * 2 ^ 59
def prefixEnd_3652894 : Nat := 4983230072969 + 3 ^ 40 * 3652894 * 2
def baseEnd_3652894 : Nat := 138940029772217501416715

theorem tailTrace_3652894 : CollatzResearch.WordTrace tailWord_3652894 prefixEnd_3652894 138940029772217501416715 := by
  unfold tailWord_3652894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16653998703524547183988717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88821326418797584981273157 16653998703524547183988717)
  ·
    refine ⟨6245249513821705193995769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16653998703524547183988717 6245249513821705193995769)
    ·
      refine ⟨4683937135366278895496827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6245249513821705193995769 4683937135366278895496827)
      ·
        refine ⟨7025905703049418343245241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683937135366278895496827 7025905703049418343245241)
        ·
          refine ⟨5269429277287063757433931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7025905703049418343245241 5269429277287063757433931)
          ·
            refine ⟨7904143915930595636150897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269429277287063757433931 7904143915930595636150897)
            ·
              refine ⟨5928107936947946727113173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904143915930595636150897 5928107936947946727113173)
              ·
                refine ⟨138940029772217501416715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5928107936947946727113173 138940029772217501416715)
                ·
                  rfl

theorem cell22_3652894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3652894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652894 prefixEnd_3652894 := by exact prefixLift 3652894
  have htrace : WordTrace (prefixWord ++ tailWord_3652894) baseStart_3652894 baseEnd_3652894 := by
    simpa [prefixWord, tailWord_3652894, baseEnd_3652894] using wordTrace_append hprefix tailTrace_3652894
  have hstable : (prefixWord ++ tailWord_3652894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652894).length < 2 ^ (prefixWord ++ tailWord_3652894).sum := by decide
  have hdescent : baseEnd_3652894 < baseStart_3652894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652898 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3652898 : Nat := 118140960795 + 3652898 * 2 ^ 59
def prefixEnd_3652898 : Nat := 4983230072969 + 3 ^ 40 * 3652898 * 2
def baseEnd_3652898 : Nat := 1250461637231702835650423

theorem tailTrace_3652898 : CollatzResearch.WordTrace tailWord_3652898 prefixEnd_3652898 1250461637231702835650423 := by
  unfold tailWord_3652898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33308033880045471538763837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88821423680121257436703565 33308033880045471538763837)
  ·
    refine ⟨12490512705017051827036439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33308033880045471538763837 12490512705017051827036439)
    ·
      refine ⟨18735769057525577740554659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12490512705017051827036439 18735769057525577740554659)
      ·
        refine ⟨28103653586288366610831989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18735769057525577740554659 28103653586288366610831989)
        ·
          refine ⟨2634717523714534369765499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28103653586288366610831989 2634717523714534369765499)
          ·
            refine ⟨3952076285571801554648249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634717523714534369765499 3952076285571801554648249)
            ·
              refine ⟨2964057214178851165986187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3952076285571801554648249 2964057214178851165986187)
              ·
                refine ⟨4446085821268276748979281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964057214178851165986187 4446085821268276748979281)
                ·
                  refine ⟨3334564365951207561734461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4446085821268276748979281 3334564365951207561734461)
                  ·
                    refine ⟨1250461637231702835650423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334564365951207561734461 1250461637231702835650423)
                    ·
                      rfl

theorem cell22_3652898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3652898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652898 prefixEnd_3652898 := by exact prefixLift 3652898
  have htrace : WordTrace (prefixWord ++ tailWord_3652898) baseStart_3652898 baseEnd_3652898 := by
    simpa [prefixWord, tailWord_3652898, baseEnd_3652898] using wordTrace_append hprefix tailTrace_3652898
  have hstable : (prefixWord ++ tailWord_3652898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652898).length < 2 ^ (prefixWord ++ tailWord_3652898).sum := by decide
  have hdescent : baseEnd_3652898 < baseStart_3652898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652967 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 6]
def baseStart_3652967 : Nat := 118140960795 + 3652967 * 2 ^ 59
def prefixEnd_3652967 : Nat := 4983230072969 + 3 ^ 40 * 3652967 * 2
def baseEnd_3652967 : Nat := 416828419113936551891737

theorem tailTrace_3652967 : CollatzResearch.WordTrace tailWord_3652967 prefixEnd_3652967 416828419113936551891737 := by
  unfold tailWord_3652967
  simp only [CollatzResearch.WordTrace]
  refine ⟨133234652156931910939317155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88823101437954607292878103 133234652156931910939317155)
  ·
    refine ⟨199851978235397866408975733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133234652156931910939317155 199851978235397866408975733)
    ·
      refine ⟨18736122959568549975841475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199851978235397866408975733 18736122959568549975841475)
      ·
        refine ⟨28104184439352824963762213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736122959568549975841475 28104184439352824963762213)
        ·
          refine ⟨5269534582378654680705415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28104184439352824963762213 5269534582378654680705415)
          ·
            refine ⟨7904301873567982021058123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269534582378654680705415 7904301873567982021058123)
            ·
              refine ⟨11856452810351973031587185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904301873567982021058123 11856452810351973031587185)
              ·
                refine ⟨8892339607763979773690389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11856452810351973031587185 8892339607763979773690389)
                ·
                  refine ⟨416828419113936551891737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8892339607763979773690389 416828419113936551891737)
                  ·
                    rfl

theorem cell22_3652967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 6].length) (baseStart_3652967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652967 prefixEnd_3652967 := by exact prefixLift 3652967
  have htrace : WordTrace (prefixWord ++ tailWord_3652967) baseStart_3652967 baseEnd_3652967 := by
    simpa [prefixWord, tailWord_3652967, baseEnd_3652967] using wordTrace_append hprefix tailTrace_3652967
  have hstable : (prefixWord ++ tailWord_3652967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652967).length < 2 ^ (prefixWord ++ tailWord_3652967).sum := by decide
  have hdescent : baseEnd_3652967 < baseStart_3652967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652995 : List Nat := [1, 1, 1, 3, 5, 2, 9]
def baseStart_3652995 : Nat := 118140960795 + 3652995 * 2 ^ 59
def prefixEnd_3652995 : Nat := 4983230072969 + 3 ^ 40 * 3652995 * 2
def baseEnd_3652995 : Nat := 46314623789408404295375

theorem tailTrace_3652995 : CollatzResearch.WordTrace tailWord_3652995 prefixEnd_3652995 46314623789408404295375 := by
  unfold tailWord_3652995
  simp only [CollatzResearch.WordTrace]
  refine ⟨133235673400830471721336439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88823782267220314480890959 133235673400830471721336439)
  ·
    refine ⟨199853510101245707582004659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133235673400830471721336439 199853510101245707582004659)
    ·
      refine ⟨299780265151868561373006989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199853510101245707582004659 299780265151868561373006989)
      ·
        refine ⟨112417599431950710514877621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299780265151868561373006989 112417599431950710514877621)
        ·
          refine ⟨10539149946745379110769777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112417599431950710514877621 10539149946745379110769777)
          ·
            refine ⟨7904362460059034333077333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10539149946745379110769777 7904362460059034333077333)
            ·
              refine ⟨46314623789408404295375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7904362460059034333077333 46314623789408404295375)
              ·
                rfl

theorem cell22_3652995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 9].length) (baseStart_3652995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652995 prefixEnd_3652995 := by exact prefixLift 3652995
  have htrace : WordTrace (prefixWord ++ tailWord_3652995) baseStart_3652995 baseEnd_3652995 := by
    simpa [prefixWord, tailWord_3652995, baseEnd_3652995] using wordTrace_append hprefix tailTrace_3652995
  have hstable : (prefixWord ++ tailWord_3652995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652995).length < 2 ^ (prefixWord ++ tailWord_3652995).sum := by decide
  have hdescent : baseEnd_3652995 < baseStart_3652995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652999 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3652999 : Nat := 118140960795 + 3652999 * 2 ^ 59
def prefixEnd_3652999 : Nat := 4983230072969 + 3 ^ 40 * 3652999 * 2
def baseEnd_3652999 : Nat := 1250496211595772238875113

theorem tailTrace_3652999 : CollatzResearch.WordTrace tailWord_3652999 prefixEnd_3652999 1250496211595772238875113 := by
  unfold tailWord_3652999
  simp only [CollatzResearch.WordTrace]
  refine ⟨133235819292815980404482051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88823879528543986936321367 133235819292815980404482051)
  ·
    refine ⟨199853728939223970606723077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133235819292815980404482051 199853728939223970606723077)
    ·
      refine ⟨37472574176104494488760577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199853728939223970606723077 37472574176104494488760577)
      ·
        refine ⟨28104430632078370866570433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37472574176104494488760577 28104430632078370866570433)
        ·
          refine ⟨21078322974058778149927825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28104430632078370866570433 21078322974058778149927825)
          ·
            refine ⟨15808742230544083612445869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21078322974058778149927825 15808742230544083612445869)
            ·
              refine ⟨5928278336454031354667201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15808742230544083612445869 5928278336454031354667201)
              ·
                refine ⟨4446208752340523516000401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928278336454031354667201 4446208752340523516000401)
                ·
                  refine ⟨3334656564255392637000301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4446208752340523516000401 3334656564255392637000301)
                  ·
                    refine ⟨1250496211595772238875113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334656564255392637000301 1250496211595772238875113)
                    ·
                      rfl

theorem cell22_3652999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3652999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3652999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3652999 prefixEnd_3652999 := by exact prefixLift 3652999
  have htrace : WordTrace (prefixWord ++ tailWord_3652999) baseStart_3652999 baseEnd_3652999 := by
    simpa [prefixWord, tailWord_3652999, baseEnd_3652999] using wordTrace_append hprefix tailTrace_3652999
  have hstable : (prefixWord ++ tailWord_3652999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652999).length < 2 ^ (prefixWord ++ tailWord_3652999).sum := by decide
  have hdescent : baseEnd_3652999 < baseStart_3652999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653016 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 1, 5]
def baseStart_3653016 : Nat := 118140960795 + 3653016 * 2 ^ 59
def prefixEnd_3653016 : Nat := 4983230072969 + 3 ^ 40 * 3653016 * 2
def baseEnd_3653016 : Nat := 1250502031043189861200061

theorem tailTrace_3653016 : CollatzResearch.WordTrace tailWord_3653016 prefixEnd_3653016 1250502031043189861200061 := by
  unfold tailWord_3653016
  simp only [CollatzResearch.WordTrace]
  refine ⟨66618219666877196153925451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88824292889169594871900601 66618219666877196153925451)
  ·
    refine ⟨99927329500315794230888177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66618219666877196153925451 99927329500315794230888177)
    ·
      refine ⟨74945497125236845673166133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99927329500315794230888177 74945497125236845673166133)
      ·
        refine ⟨7026140355490954281859325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74945497125236845673166133 7026140355490954281859325)
        ·
          refine ⟨2634802633309107855697247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7026140355490954281859325 2634802633309107855697247)
          ·
            refine ⟨3952203949963661783545871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634802633309107855697247 3952203949963661783545871)
            ·
              refine ⟨5928305924945492675318807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952203949963661783545871 5928305924945492675318807)
              ·
                refine ⟨8892458887418239012978211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928305924945492675318807 8892458887418239012978211)
                ·
                  refine ⟨13338688331127358519467317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892458887418239012978211 13338688331127358519467317)
                  ·
                    refine ⟨1250502031043189861200061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13338688331127358519467317 1250502031043189861200061)
                    ·
                      rfl

theorem cell22_3653016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_3653016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653016 prefixEnd_3653016 := by exact prefixLift 3653016
  have htrace : WordTrace (prefixWord ++ tailWord_3653016) baseStart_3653016 baseEnd_3653016 := by
    simpa [prefixWord, tailWord_3653016, baseEnd_3653016] using wordTrace_append hprefix tailTrace_3653016
  have hstable : (prefixWord ++ tailWord_3653016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653016).length < 2 ^ (prefixWord ++ tailWord_3653016).sum := by decide
  have hdescent : baseEnd_3653016 < baseStart_3653016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653027 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 3, 3]
def baseStart_3653027 : Nat := 118140960795 + 3653027 * 2 ^ 59
def prefixEnd_3653027 : Nat := 4983230072969 + 3 ^ 40 * 3653027 * 2
def baseEnd_3653027 : Nat := 1250505796567989499175027

theorem tailTrace_3653027 : CollatzResearch.WordTrace tailWord_3653027 prefixEnd_3653027 1250505796567989499175027 := by
  unfold tailWord_3653027
  simp only [CollatzResearch.WordTrace]
  refine ⟨133236840536714541186501335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88824560357809694124334223 133236840536714541186501335)
  ·
    refine ⟨199855260805071811779752003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133236840536714541186501335 199855260805071811779752003)
    ·
      refine ⟨299782891207607717669628005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199855260805071811779752003 299782891207607717669628005)
      ·
        refine ⟨56209292101426447063055251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299782891207607717669628005 56209292101426447063055251)
        ·
          refine ⟨84313938152139670594582877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56209292101426447063055251 84313938152139670594582877)
          ·
            refine ⟨31617726807052376472968579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84313938152139670594582877 31617726807052376472968579)
            ·
              refine ⟨47426590210578564709452869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31617726807052376472968579 47426590210578564709452869)
              ·
                refine ⟨8892485664483480883022413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47426590210578564709452869 8892485664483480883022413)
                ·
                  refine ⟨3334682124181305331133405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8892485664483480883022413 3334682124181305331133405)
                  ·
                    refine ⟨1250505796567989499175027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334682124181305331133405 1250505796567989499175027)
                    ·
                      rfl

theorem cell22_3653027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 3].length) (baseStart_3653027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653027 prefixEnd_3653027 := by exact prefixLift 3653027
  have htrace : WordTrace (prefixWord ++ tailWord_3653027) baseStart_3653027 baseEnd_3653027 := by
    simpa [prefixWord, tailWord_3653027, baseEnd_3653027] using wordTrace_append hprefix tailTrace_3653027
  have hstable : (prefixWord ++ tailWord_3653027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653027).length < 2 ^ (prefixWord ++ tailWord_3653027).sum := by decide
  have hdescent : baseEnd_3653027 < baseStart_3653027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653055 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_3653055 : Nat := 118140960795 + 3653055 * 2 ^ 59
def prefixEnd_3653055 : Nat := 4983230072969 + 3 ^ 40 * 3653055 * 2
def baseEnd_3653055 : Nat := 1250515381540206759474941

theorem tailTrace_3653055 : CollatzResearch.WordTrace tailWord_3653055 prefixEnd_3653055 1250515381540206759474941 := by
  unfold tailWord_3653055
  simp only [CollatzResearch.WordTrace]
  refine ⟨133237861780613101968520619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88825241187075401312347079 133237861780613101968520619)
  ·
    refine ⟨199856792670919652952780929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133237861780613101968520619 199856792670919652952780929)
    ·
      refine ⟨149892594503189739714585697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199856792670919652952780929 149892594503189739714585697)
      ·
        refine ⟨112419445877392304785939273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149892594503189739714585697 112419445877392304785939273)
        ·
          refine ⟨84314584408044228589454455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112419445877392304785939273 84314584408044228589454455)
          ·
            refine ⟨126471876612066342884181683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84314584408044228589454455 126471876612066342884181683)
            ·
              refine ⟨189707814918099514326272525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126471876612066342884181683 189707814918099514326272525)
              ·
                refine ⟨71140430594287317872352197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189707814918099514326272525 71140430594287317872352197)
                ·
                  refine ⟨13338830736428872101066037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71140430594287317872352197 13338830736428872101066037)
                  ·
                    refine ⟨1250515381540206759474941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13338830736428872101066037 1250515381540206759474941)
                    ·
                      rfl

theorem cell22_3653055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_3653055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653055 prefixEnd_3653055 := by exact prefixLift 3653055
  have htrace : WordTrace (prefixWord ++ tailWord_3653055) baseStart_3653055 baseEnd_3653055 := by
    simpa [prefixWord, tailWord_3653055, baseEnd_3653055] using wordTrace_append hprefix tailTrace_3653055
  have hstable : (prefixWord ++ tailWord_3653055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653055).length < 2 ^ (prefixWord ++ tailWord_3653055).sum := by decide
  have hdescent : baseEnd_3653055 < baseStart_3653055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653087 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 3, 4]
def baseStart_3653087 : Nat := 118140960795 + 3653087 * 2 ^ 59
def prefixEnd_3653087 : Nat := 4983230072969 + 3 ^ 40 * 3653087 * 2
def baseEnd_3653087 : Nat := 1250526335794169342674843

theorem tailTrace_3653087 : CollatzResearch.WordTrace tailWord_3653087 prefixEnd_3653087 1250526335794169342674843 := by
  unfold tailWord_3653087
  simp only [CollatzResearch.WordTrace]
  refine ⟨133239028916497171433685515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88826019277664780955790343 133239028916497171433685515)
  ·
    refine ⟨199858543374745757150528273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133239028916497171433685515 199858543374745757150528273)
    ·
      refine ⟨149893907531059317862896205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199858543374745757150528273 149893907531059317862896205)
      ·
        refine ⟨56210215324147244198586077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149893907531059317862896205 56210215324147244198586077)
        ·
          refine ⟨21078830746555216574469779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56210215324147244198586077 21078830746555216574469779)
          ·
            refine ⟨31618246119832824861704669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21078830746555216574469779 31618246119832824861704669)
            ·
              refine ⟨11856842294937309323139251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31618246119832824861704669 11856842294937309323139251)
              ·
                refine ⟨17785263442405963984708877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11856842294937309323139251 17785263442405963984708877)
                ·
                  refine ⟨6669473790902236494265829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17785263442405963984708877 6669473790902236494265829)
                  ·
                    refine ⟨1250526335794169342674843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6669473790902236494265829 1250526335794169342674843)
                    ·
                      rfl

theorem cell22_3653087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_3653087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653087 prefixEnd_3653087 := by exact prefixLift 3653087
  have htrace : WordTrace (prefixWord ++ tailWord_3653087) baseStart_3653087 baseEnd_3653087 := by
    simpa [prefixWord, tailWord_3653087, baseEnd_3653087] using wordTrace_append hprefix tailTrace_3653087
  have hstable : (prefixWord ++ tailWord_3653087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653087).length < 2 ^ (prefixWord ++ tailWord_3653087).sum := by decide
  have hdescent : baseEnd_3653087 < baseStart_3653087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653230 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3653230 : Nat := 118140960795 + 3653230 * 2 ^ 59
def prefixEnd_3653230 : Nat := 4983230072969 + 3 ^ 40 * 3653230 * 2
def baseEnd_3653230 : Nat := 1250575287616564636349405

theorem tailTrace_3653230 : CollatzResearch.WordTrace tailWord_3653230 prefixEnd_3653230 1250575287616564636349405 := by
  unfold tailWord_3653230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16655530569372388357017643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88829496369986071237427429 16655530569372388357017643)
  ·
    refine ⟨24983295854058582535526465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16655530569372388357017643 24983295854058582535526465)
    ·
      refine ⟨18737471890543936901644849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24983295854058582535526465 18737471890543936901644849)
      ·
        refine ⟨14053103917907952676233637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18737471890543936901644849 14053103917907952676233637)
        ·
          refine ⟨2634956984607741126793807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14053103917907952676233637 2634956984607741126793807)
          ·
            refine ⟨3952435476911611690190711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634956984607741126793807 3952435476911611690190711)
            ·
              refine ⟨5928653215367417535286067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952435476911611690190711 5928653215367417535286067)
              ·
                refine ⟨8892979823051126302929101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928653215367417535286067 8892979823051126302929101)
                ·
                  refine ⟨3334867433644172363598413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8892979823051126302929101 3334867433644172363598413)
                  ·
                    refine ⟨1250575287616564636349405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334867433644172363598413 1250575287616564636349405)
                    ·
                      rfl

theorem cell22_3653230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3653230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653230 prefixEnd_3653230 := by exact prefixLift 3653230
  have htrace : WordTrace (prefixWord ++ tailWord_3653230) baseStart_3653230 baseEnd_3653230 := by
    simpa [prefixWord, tailWord_3653230, baseEnd_3653230] using wordTrace_append hprefix tailTrace_3653230
  have hstable : (prefixWord ++ tailWord_3653230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653230).length < 2 ^ (prefixWord ++ tailWord_3653230).sum := by decide
  have hdescent : baseEnd_3653230 < baseStart_3653230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653269 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3653269 : Nat := 118140960795 + 3653269 * 2 ^ 59
def prefixEnd_3653269 : Nat := 4983230072969 + 3 ^ 40 * 3653269 * 2
def baseEnd_3653269 : Nat := 1250588638113581534624285

theorem tailTrace_3653269 : CollatzResearch.WordTrace tailWord_3653269 prefixEnd_3653269 1250588638113581534624285 := by
  unfold tailWord_3653269
  simp only [CollatzResearch.WordTrace]
  refine ⟨133245667001837816516810861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88830444667891877677873907 133245667001837816516810861)
  ·
    refine ⟨49967125125689181193804073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133245667001837816516810861 49967125125689181193804073)
    ·
      refine ⟨37475343844266885895353055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49967125125689181193804073 37475343844266885895353055)
      ·
        refine ⟨56213015766400328843029583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37475343844266885895353055 56213015766400328843029583)
        ·
          refine ⟨84319523649600493264544375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56213015766400328843029583 84319523649600493264544375)
          ·
            refine ⟨126479285474400739896816563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84319523649600493264544375 126479285474400739896816563)
            ·
              refine ⟨189718928211601109845224845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126479285474400739896816563 189718928211601109845224845)
              ·
                refine ⟨71144598079350416191959317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189718928211601109845224845 71144598079350416191959317)
                ·
                  refine ⟨3334903034969550758998093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71144598079350416191959317 3334903034969550758998093)
                  ·
                    refine ⟨1250588638113581534624285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334903034969550758998093 1250588638113581534624285)
                    ·
                      rfl

theorem cell22_3653269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3653269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653269 prefixEnd_3653269 := by exact prefixLift 3653269
  have htrace : WordTrace (prefixWord ++ tailWord_3653269) baseStart_3653269 baseEnd_3653269 := by
    simpa [prefixWord, tailWord_3653269, baseEnd_3653269] using wordTrace_append hprefix tailTrace_3653269
  have hstable : (prefixWord ++ tailWord_3653269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653269).length < 2 ^ (prefixWord ++ tailWord_3653269).sum := by decide
  have hdescent : baseEnd_3653269 < baseStart_3653269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653316 : List Nat := [2, 3, 3, 1, 1, 1, 5, 6]
def baseStart_3653316 : Nat := 118140960795 + 3653316 * 2 ^ 59
def prefixEnd_3653316 : Nat := 4983230072969 + 3 ^ 40 * 3653316 * 2
def baseEnd_3653316 : Nat := 138956080797121008744349

theorem tailTrace_3653316 : CollatzResearch.WordTrace tailWord_3653316 prefixEnd_3653316 138956080797121008744349 := by
  unfold tailWord_3653316
  simp only [CollatzResearch.WordTrace]
  refine ⟨66623690616333771771885901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88831587488445029029181201 66623690616333771771885901)
  ·
    refine ⟨24983883981125164414457213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66623690616333771771885901 24983883981125164414457213)
    ·
      refine ⟨9368956492921936655421455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24983883981125164414457213 9368956492921936655421455)
      ·
        refine ⟨14053434739382904983132183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9368956492921936655421455 14053434739382904983132183)
        ·
          refine ⟨21080152109074357474698275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14053434739382904983132183 21080152109074357474698275)
          ·
            refine ⟨31620228163611536212047413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21080152109074357474698275 31620228163611536212047413)
            ·
              refine ⟨2964396390338581519879445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31620228163611536212047413 2964396390338581519879445)
              ·
                refine ⟨138956080797121008744349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2964396390338581519879445 138956080797121008744349)
                ·
                  rfl

theorem cell22_3653316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 6].length) (baseStart_3653316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653316 prefixEnd_3653316 := by exact prefixLift 3653316
  have htrace : WordTrace (prefixWord ++ tailWord_3653316) baseStart_3653316 baseEnd_3653316 := by
    simpa [prefixWord, tailWord_3653316, baseEnd_3653316] using wordTrace_append hprefix tailTrace_3653316
  have hstable : (prefixWord ++ tailWord_3653316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653316).length < 2 ^ (prefixWord ++ tailWord_3653316).sum := by decide
  have hdescent : baseEnd_3653316 < baseStart_3653316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653348 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3653348 : Nat := 118140960795 + 3653348 * 2 ^ 59
def prefixEnd_3653348 : Nat := 4983230072969 + 3 ^ 40 * 3653348 * 2
def baseEnd_3653348 : Nat := 1250615681428051661899043

theorem tailTrace_3653348 : CollatzResearch.WordTrace tailWord_3653348 prefixEnd_3653348 1250615681428051661899043 := by
  unfold tailWord_3653348
  simp only [CollatzResearch.WordTrace]
  refine ⟨66624274184275806504468349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88832365579034408672624465 66624274184275806504468349)
  ·
    refine ⟨24984102819103427439175631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66624274184275806504468349 24984102819103427439175631)
    ·
      refine ⟨37476154228655141158763447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24984102819103427439175631 37476154228655141158763447)
      ·
        refine ⟨56214231342982711738145171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37476154228655141158763447 56214231342982711738145171)
        ·
          refine ⟨84321347014474067607217757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56214231342982711738145171 84321347014474067607217757)
          ·
            refine ⟨31620505130427775352706659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84321347014474067607217757 31620505130427775352706659)
            ·
              refine ⟨47430757695641663029059989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31620505130427775352706659 47430757695641663029059989)
              ·
                refine ⟨2223316766983202954487187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47430757695641663029059989 2223316766983202954487187)
                ·
                  refine ⟨3334975150474804431730781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223316766983202954487187 3334975150474804431730781)
                  ·
                    refine ⟨1250615681428051661899043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334975150474804431730781 1250615681428051661899043)
                    ·
                      rfl

theorem cell22_3653348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3653348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653348 prefixEnd_3653348 := by exact prefixLift 3653348
  have htrace : WordTrace (prefixWord ++ tailWord_3653348) baseStart_3653348 baseEnd_3653348 := by
    simpa [prefixWord, tailWord_3653348, baseEnd_3653348] using wordTrace_append hprefix tailTrace_3653348
  have hstable : (prefixWord ++ tailWord_3653348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653348).length < 2 ^ (prefixWord ++ tailWord_3653348).sum := by decide
  have hdescent : baseEnd_3653348 < baseStart_3653348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653359 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_3653359 : Nat := 118140960795 + 3653359 * 2 ^ 59
def prefixEnd_3653359 : Nat := 4983230072969 + 3 ^ 40 * 3653359 * 2
def baseEnd_3653359 : Nat := 1250619446952851299874009

theorem tailTrace_3653359 : CollatzResearch.WordTrace tailWord_3653359 prefixEnd_3653359 1250619446952851299874009 := by
  unfold tailWord_3653359
  simp only [CollatzResearch.WordTrace]
  refine ⟨133248949571511761887587131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88832633047674507925058087 133248949571511761887587131)
  ·
    refine ⟨199873424357267642831380697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133248949571511761887587131 199873424357267642831380697)
    ·
      refine ⟨149905068267950732123535523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199873424357267642831380697 149905068267950732123535523)
      ·
        refine ⟨224857602401926098185303285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149905068267950732123535523 224857602401926098185303285)
        ·
          refine ⟨21080400225180571704872183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224857602401926098185303285 21080400225180571704872183)
          ·
            refine ⟨31620600337770857557308275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21080400225180571704872183 31620600337770857557308275)
            ·
              refine ⟨47430900506656286335962413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31620600337770857557308275 47430900506656286335962413)
              ·
                refine ⟨17786587689996107375985905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47430900506656286335962413 17786587689996107375985905)
                ·
                  refine ⟨13339940767497080531989429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17786587689996107375985905 13339940767497080531989429)
                  ·
                    refine ⟨1250619446952851299874009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13339940767497080531989429 1250619446952851299874009)
                    ·
                      rfl

theorem cell22_3653359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_3653359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653359 prefixEnd_3653359 := by exact prefixLift 3653359
  have htrace : WordTrace (prefixWord ++ tailWord_3653359) baseStart_3653359 baseEnd_3653359 := by
    simpa [prefixWord, tailWord_3653359, baseEnd_3653359] using wordTrace_append hprefix tailTrace_3653359
  have hstable : (prefixWord ++ tailWord_3653359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653359).length < 2 ^ (prefixWord ++ tailWord_3653359).sum := by decide
  have hdescent : baseEnd_3653359 < baseStart_3653359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653436 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_3653436 : Nat := 118140960795 + 3653436 * 2 ^ 59
def prefixEnd_3653436 : Nat := 4983230072969 + 3 ^ 40 * 3653436 * 2
def baseEnd_3653436 : Nat := 1250645805626448765698773

theorem tailTrace_3653436 : CollatzResearch.WordTrace tailWord_3653436 prefixEnd_3653436 1250645805626448765698773 := by
  unfold tailWord_3653436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66625878996116402019070081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88834505328155202692093441 66625878996116402019070081)
  ·
    refine ⟨49969409247087301514302561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66625878996116402019070081 49969409247087301514302561)
    ·
      refine ⟨37477056935315476135726921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49969409247087301514302561 37477056935315476135726921)
      ·
        refine ⟨28107792701486607101795191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37477056935315476135726921 28107792701486607101795191)
        ·
          refine ⟨42161689052229910652692787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28107792701486607101795191 42161689052229910652692787)
          ·
            refine ⟨63242533578344865979039181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42161689052229910652692787 63242533578344865979039181)
            ·
              refine ⟨23715950091879324742139693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63242533578344865979039181 23715950091879324742139693)
              ·
                refine ⟨8893481284454746778302385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23715950091879324742139693 8893481284454746778302385)
                ·
                  refine ⟨6670110963341060083726789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8893481284454746778302385 6670110963341060083726789)
                  ·
                    refine ⟨1250645805626448765698773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670110963341060083726789 1250645805626448765698773)
                    ·
                      rfl

theorem cell22_3653436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3653436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653436 prefixEnd_3653436 := by exact prefixLift 3653436
  have htrace : WordTrace (prefixWord ++ tailWord_3653436) baseStart_3653436 baseEnd_3653436 := by
    simpa [prefixWord, tailWord_3653436, baseEnd_3653436] using wordTrace_append hprefix tailTrace_3653436
  have hstable : (prefixWord ++ tailWord_3653436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653436).length < 2 ^ (prefixWord ++ tailWord_3653436).sum := by decide
  have hdescent : baseEnd_3653436 < baseStart_3653436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653438 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3653438 : Nat := 118140960795 + 3653438 * 2 ^ 59
def prefixEnd_3653438 : Nat := 4983230072969 + 3 ^ 40 * 3653438 * 2
def baseEnd_3653438 : Nat := 1250646490267321427148767

theorem tailTrace_3653438 : CollatzResearch.WordTrace tailWord_3653438 prefixEnd_3653438 1250646490267321427148767 := by
  unfold tailWord_3653438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16656478867278194797464121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88834553958817038919808645 16656478867278194797464121)
  ·
    refine ⟨12492359150458646098098091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16656478867278194797464121 12492359150458646098098091)
    ·
      refine ⟨18738538725687969147147137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12492359150458646098098091 18738538725687969147147137)
      ·
        refine ⟨14053904044265976860360353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18738538725687969147147137 14053904044265976860360353)
        ·
          refine ⟨10540428033199482645270265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14053904044265976860360353 10540428033199482645270265)
          ·
            refine ⟨7905321024899611983952699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540428033199482645270265 7905321024899611983952699)
            ·
              refine ⟨11857981537349417975929049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905321024899611983952699 11857981537349417975929049)
              ·
                refine ⟨8893486153012063481946787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857981537349417975929049 8893486153012063481946787)
                ·
                  refine ⟨13340229229518095222920181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8893486153012063481946787 13340229229518095222920181)
                  ·
                    refine ⟨1250646490267321427148767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13340229229518095222920181 1250646490267321427148767)
                    ·
                      rfl

theorem cell22_3653438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3653438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653438 prefixEnd_3653438 := by exact prefixLift 3653438
  have htrace : WordTrace (prefixWord ++ tailWord_3653438) baseStart_3653438 baseEnd_3653438 := by
    simpa [prefixWord, tailWord_3653438, baseEnd_3653438] using wordTrace_append hprefix tailTrace_3653438
  have hstable : (prefixWord ++ tailWord_3653438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653438).length < 2 ^ (prefixWord ++ tailWord_3653438).sum := by decide
  have hdescent : baseEnd_3653438 < baseStart_3653438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653530 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_3653530 : Nat := 118140960795 + 3653530 * 2 ^ 59
def prefixEnd_3653530 : Nat := 4983230072969 + 3 ^ 40 * 3653530 * 2
def baseEnd_3653530 : Nat := 416892661249154617949495

theorem tailTrace_3653530 : CollatzResearch.WordTrace tailWord_3653530 prefixEnd_3653530 416892661249154617949495 := by
  unfold tailWord_3653530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313796613473064523015511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88836790969261505394708029 33313796613473064523015511)
  ·
    refine ⟨49970694920209596784523267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33313796613473064523015511 49970694920209596784523267)
    ·
      refine ⟨74956042380314395176784901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49970694920209596784523267 74956042380314395176784901)
      ·
        refine ⟨14054257946308949095647169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74956042380314395176784901 14054257946308949095647169)
        ·
          refine ⟨10540693459731711821735377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14054257946308949095647169 10540693459731711821735377)
          ·
            refine ⟨7905520094798783866301533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540693459731711821735377 7905520094798783866301533)
            ·
              refine ⟨2964570035549543949863075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7905520094798783866301533 2964570035549543949863075)
              ·
                refine ⟨4446855053324315924794613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964570035549543949863075 4446855053324315924794613)
                ·
                  refine ⟨416892661249154617949495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4446855053324315924794613 416892661249154617949495)
                  ·
                    rfl

theorem cell22_3653530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_3653530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653530 prefixEnd_3653530 := by exact prefixLift 3653530
  have htrace : WordTrace (prefixWord ++ tailWord_3653530) baseStart_3653530 baseEnd_3653530 := by
    simpa [prefixWord, tailWord_3653530, baseEnd_3653530] using wordTrace_append hprefix tailTrace_3653530
  have hstable : (prefixWord ++ tailWord_3653530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653530).length < 2 ^ (prefixWord ++ tailWord_3653530).sum := by decide
  have hdescent : baseEnd_3653530 < baseStart_3653530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653588 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3653588 : Nat := 118140960795 + 3653588 * 2 ^ 59
def prefixEnd_3653588 : Nat := 4983230072969 + 3 ^ 40 * 3653588 * 2
def baseEnd_3653588 : Nat := 1250697838332771035898307

theorem tailTrace_3653588 : CollatzResearch.WordTrace tailWord_3653588 prefixEnd_3653588 1250697838332771035898307 := by
  unfold tailWord_3653588
  simp only [CollatzResearch.WordTrace]
  refine ⟨66628650943841066998836709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88838201258454755998448945 66628650943841066998836709)
  ·
    refine ⟨12492872051970200062281883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66628650943841066998836709 12492872051970200062281883)
    ·
      refine ⟨18739308077955300093422825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12492872051970200062281883 18739308077955300093422825)
      ·
        refine ⟨14054481058466475070067119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18739308077955300093422825 14054481058466475070067119)
        ·
          refine ⟨21081721587699712605100679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14054481058466475070067119 21081721587699712605100679)
          ·
            refine ⟨31622582381549568907651019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21081721587699712605100679 31622582381549568907651019)
            ·
              refine ⟨47433873572324353361476529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31622582381549568907651019 47433873572324353361476529)
              ·
                refine ⟨35575405179243265021107397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47433873572324353361476529 35575405179243265021107397)
                ·
                  refine ⟨6670388471108112191457637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35575405179243265021107397 6670388471108112191457637)
                  ·
                    refine ⟨1250697838332771035898307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670388471108112191457637 1250697838332771035898307)
                    ·
                      rfl

theorem cell22_3653588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3653588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653588 prefixEnd_3653588 := by exact prefixLift 3653588
  have htrace : WordTrace (prefixWord ++ tailWord_3653588) baseStart_3653588 baseEnd_3653588 := by
    simpa [prefixWord, tailWord_3653588, baseEnd_3653588] using wordTrace_append hprefix tailTrace_3653588
  have hstable : (prefixWord ++ tailWord_3653588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653588).length < 2 ^ (prefixWord ++ tailWord_3653588).sum := by decide
  have hdescent : baseEnd_3653588 < baseStart_3653588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653601 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3653601 : Nat := 118140960795 + 3653601 * 2 ^ 59
def prefixEnd_3653601 : Nat := 4983230072969 + 3 ^ 40 * 3653601 * 2
def baseEnd_3653601 : Nat := 1250702288498443335323267

theorem tailTrace_3653601 : CollatzResearch.WordTrace tailWord_3653601 prefixEnd_3653601 1250702288498443335323267 := by
  unfold tailWord_3653601
  simp only [CollatzResearch.WordTrace]
  refine ⟨133257776036635037217896657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88838517357756691478597771 133257776036635037217896657)
  ·
    refine ⟨99943332027476277913422493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133257776036635037217896657 99943332027476277913422493)
    ·
      refine ⟨37478749510303604217533435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99943332027476277913422493 37478749510303604217533435)
      ·
        refine ⟨56218124265455406326300153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37478749510303604217533435 56218124265455406326300153)
        ·
          refine ⟨42163593199091554744725115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56218124265455406326300153 42163593199091554744725115)
          ·
            refine ⟨63245389798637332117087673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42163593199091554744725115 63245389798637332117087673)
            ·
              refine ⟨47434042348977999087815755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63245389798637332117087673 47434042348977999087815755)
              ·
                refine ⟨71151063523466998631723633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47434042348977999087815755 71151063523466998631723633)
                ·
                  refine ⟨53363297642600248973792725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71151063523466998631723633 53363297642600248973792725)
                  ·
                    refine ⟨1250702288498443335323267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53363297642600248973792725 1250702288498443335323267)
                    ·
                      rfl

theorem cell22_3653601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3653601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653601 prefixEnd_3653601 := by exact prefixLift 3653601
  have htrace : WordTrace (prefixWord ++ tailWord_3653601) baseStart_3653601 baseEnd_3653601 := by
    simpa [prefixWord, tailWord_3653601, baseEnd_3653601] using wordTrace_append hprefix tailTrace_3653601
  have hstable : (prefixWord ++ tailWord_3653601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653601).length < 2 ^ (prefixWord ++ tailWord_3653601).sum := by decide
  have hdescent : baseEnd_3653601 < baseStart_3653601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653620 : List Nat := [2, 6, 2, 12]
def baseStart_3653620 : Nat := 118140960795 + 3653620 * 2 ^ 59
def prefixEnd_3653620 : Nat := 4983230072969 + 3 ^ 40 * 3653620 * 2
def baseEnd_3653620 : Nat := 1715649921243804690121

theorem tailTrace_3653620 : CollatzResearch.WordTrace tailWord_3653620 prefixEnd_3653620 1715649921243804690121 := by
  unfold tailWord_3653620
  simp only [CollatzResearch.WordTrace]
  refine ⟨66629234511783101731419157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88838979349044135641892209 66629234511783101731419157)
  ·
    refine ⟨3123245367739832893660273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66629234511783101731419157 3123245367739832893660273)
    ·
      refine ⟨2342434025804874670245205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3123245367739832893660273 2342434025804874670245205)
      ·
        refine ⟨1715649921243804690121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2342434025804874670245205 1715649921243804690121)
        ·
          rfl

theorem cell22_3653620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 12].length) (baseStart_3653620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653620 prefixEnd_3653620 := by exact prefixLift 3653620
  have htrace : WordTrace (prefixWord ++ tailWord_3653620) baseStart_3653620 baseEnd_3653620 := by
    simpa [prefixWord, tailWord_3653620, baseEnd_3653620] using wordTrace_append hprefix tailTrace_3653620
  have hstable : (prefixWord ++ tailWord_3653620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653620).length < 2 ^ (prefixWord ++ tailWord_3653620).sum := by decide
  have hdescent : baseEnd_3653620 < baseStart_3653620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653631 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 7]
def baseStart_3653631 : Nat := 118140960795 + 3653631 * 2 ^ 59
def prefixEnd_3653631 : Nat := 4983230072969 + 3 ^ 40 * 3653631 * 2
def baseEnd_3653631 : Nat := 416904186037177752357725

theorem tailTrace_3653631 : CollatzResearch.WordTrace tailWord_3653631 prefixEnd_3653631 416904186037177752357725 := by
  unfold tailWord_3653631
  simp only [CollatzResearch.WordTrace]
  refine ⟨133258870226526352341488747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88839246817684234894325831 133258870226526352341488747)
  ·
    refine ⟨199888305339789528512233121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133258870226526352341488747 199888305339789528512233121)
    ·
      refine ⟨149916229004842146384174841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199888305339789528512233121 149916229004842146384174841)
      ·
        refine ⟨112437171753631609788131131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149916229004842146384174841 112437171753631609788131131)
        ·
          refine ⟨168655757630447414682196697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112437171753631609788131131 168655757630447414682196697)
          ·
            refine ⟨126491818222835561011647523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168655757630447414682196697 126491818222835561011647523)
            ·
              refine ⟨189737727334253341517471285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126491818222835561011647523 189737727334253341517471285)
              ·
                refine ⟨17787911937586250767262933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189737727334253341517471285 17787911937586250767262933)
                ·
                  refine ⟨416904186037177752357725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17787911937586250767262933 416904186037177752357725)
                  ·
                    rfl

theorem cell22_3653631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_3653631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653631 prefixEnd_3653631 := by exact prefixLift 3653631
  have htrace : WordTrace (prefixWord ++ tailWord_3653631) baseStart_3653631 baseEnd_3653631 := by
    simpa [prefixWord, tailWord_3653631, baseEnd_3653631] using wordTrace_append hprefix tailTrace_3653631
  have hstable : (prefixWord ++ tailWord_3653631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653631).length < 2 ^ (prefixWord ++ tailWord_3653631).sum := by decide
  have hdescent : baseEnd_3653631 < baseStart_3653631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653740 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_3653740 : Nat := 118140960795 + 3653740 * 2 ^ 59
def prefixEnd_3653740 : Nat := 4983230072969 + 3 ^ 40 * 3653740 * 2
def baseEnd_3653740 : Nat := 1250749871039093306097841

theorem tailTrace_3653740 : CollatzResearch.WordTrace tailWord_3653740 prefixEnd_3653740 1250749871039093306097841 := by
  unfold tailWord_3653740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66631422891565731978603337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88841897188754309304804449 66631422891565731978603337)
  ·
    refine ⟨49973567168674298983952503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66631422891565731978603337 49973567168674298983952503)
    ·
      refine ⟨74960350753011448475928755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49973567168674298983952503 74960350753011448475928755)
      ·
        refine ⟨112440526129517172713893133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74960350753011448475928755 112440526129517172713893133)
        ·
          refine ⟨42165197298568939767709925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112440526129517172713893133 42165197298568939767709925)
          ·
            refine ⟨7905974493481676206445611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42165197298568939767709925 7905974493481676206445611)
            ·
              refine ⟨11858961740222514309668417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905974493481676206445611 11858961740222514309668417)
              ·
                refine ⟨8894221305166885732251313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11858961740222514309668417 8894221305166885732251313)
                ·
                  refine ⟨6670665978875164299188485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8894221305166885732251313 6670665978875164299188485)
                  ·
                    refine ⟨1250749871039093306097841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6670665978875164299188485 1250749871039093306097841)
                    ·
                      rfl

theorem cell22_3653740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_3653740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653740 prefixEnd_3653740 := by exact prefixLift 3653740
  have htrace : WordTrace (prefixWord ++ tailWord_3653740) baseStart_3653740 baseEnd_3653740 := by
    simpa [prefixWord, tailWord_3653740, baseEnd_3653740] using wordTrace_append hprefix tailTrace_3653740
  have hstable : (prefixWord ++ tailWord_3653740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653740).length < 2 ^ (prefixWord ++ tailWord_3653740).sum := by decide
  have hdescent : baseEnd_3653740 < baseStart_3653740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653742 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3653742 : Nat := 118140960795 + 3653742 * 2 ^ 59
def prefixEnd_3653742 : Nat := 4983230072969 + 3 ^ 40 * 3653742 * 2
def baseEnd_3653742 : Nat := 1250750555679965967547835

theorem tailTrace_3653742 : CollatzResearch.WordTrace tailWord_3653742 prefixEnd_3653742 1250750555679965967547835 := by
  unfold tailWord_3653742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16657864841140527287347435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88841945819416145532519653 16657864841140527287347435)
  ·
    refine ⟨24986797261710790931021153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16657864841140527287347435 24986797261710790931021153)
    ·
      refine ⟨18740097946283093198265865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24986797261710790931021153 18740097946283093198265865)
      ·
        refine ⟨14055073459712319898699399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18740097946283093198265865 14055073459712319898699399)
        ·
          refine ⟨21082610189568479848049099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055073459712319898699399 21082610189568479848049099)
          ·
            refine ⟨31623915284352719772073649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21082610189568479848049099 31623915284352719772073649)
            ·
              refine ⟨23717936463264539829055237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31623915284352719772073649 23717936463264539829055237)
              ·
                refine ⟨4447113086862101217947857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23717936463264539829055237 4447113086862101217947857)
                ·
                  refine ⟨3335334815146575913460893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447113086862101217947857 3335334815146575913460893)
                  ·
                    refine ⟨1250750555679965967547835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335334815146575913460893 1250750555679965967547835)
                    ·
                      rfl

theorem cell22_3653742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3653742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653742 prefixEnd_3653742 := by exact prefixLift 3653742
  have htrace : WordTrace (prefixWord ++ tailWord_3653742) baseStart_3653742 baseEnd_3653742 := by
    simpa [prefixWord, tailWord_3653742, baseEnd_3653742] using wordTrace_append hprefix tailTrace_3653742
  have hstable : (prefixWord ++ tailWord_3653742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653742).length < 2 ^ (prefixWord ++ tailWord_3653742).sum := by decide
  have hdescent : baseEnd_3653742 < baseStart_3653742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653806 : List Nat := [4, 1, 4, 2, 2, 1, 1, 7]
def baseStart_3653806 : Nat := 118140960795 + 3653806 * 2 ^ 59
def prefixEnd_3653806 : Nat := 4983230072969 + 3 ^ 40 * 3653806 * 2
def baseEnd_3653806 : Nat := 138974718243099014883071

theorem tailTrace_3653806 : CollatzResearch.WordTrace tailWord_3653806 prefixEnd_3653806 138974718243099014883071 := by
  unfold tailWord_3653806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658156625111544653638659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88843502000594904819406181 16658156625111544653638659)
  ·
    refine ⟨24987234937667316980457989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16658156625111544653638659 24987234937667316980457989)
    ·
      refine ⟨4685106550812621933835873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24987234937667316980457989 4685106550812621933835873)
      ·
        refine ⟨3513829913109466450376905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4685106550812621933835873 3513829913109466450376905)
        ·
          refine ⟨2635372434832099837782679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3513829913109466450376905 2635372434832099837782679)
          ·
            refine ⟨3953058652248149756674019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635372434832099837782679 3953058652248149756674019)
            ·
              refine ⟨5929587978372224635011029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953058652248149756674019 5929587978372224635011029)
              ·
                refine ⟨138974718243099014883071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5929587978372224635011029 138974718243099014883071)
                ·
                  rfl

theorem cell22_3653806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_3653806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653806 prefixEnd_3653806 := by exact prefixLift 3653806
  have htrace : WordTrace (prefixWord ++ tailWord_3653806) baseStart_3653806 baseEnd_3653806 := by
    simpa [prefixWord, tailWord_3653806, baseEnd_3653806] using wordTrace_append hprefix tailTrace_3653806
  have hstable : (prefixWord ++ tailWord_3653806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653806).length < 2 ^ (prefixWord ++ tailWord_3653806).sum := by decide
  have hdescent : baseEnd_3653806 < baseStart_3653806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653815 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3653815 : Nat := 118140960795 + 3653815 * 2 ^ 59
def prefixEnd_3653815 : Nat := 4983230072969 + 3 ^ 40 * 3653815 * 2
def baseEnd_3653815 : Nat := 1250775545071818110472611

theorem tailTrace_3653815 : CollatzResearch.WordTrace tailWord_3653815 prefixEnd_3653815 1250775545071818110472611 := by
  unfold tailWord_3653815
  simp only [CollatzResearch.WordTrace]
  refine ⟨133265581257859751766186899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88843720838573167844124599 133265581257859751766186899)
  ·
    refine ⟨199898371886789627649280349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133265581257859751766186899 199898371886789627649280349)
    ·
      refine ⟨74961889457546110368480131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199898371886789627649280349 74961889457546110368480131)
      ·
        refine ⟨112442834186319165552720197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74961889457546110368480131 112442834186319165552720197)
        ·
          refine ⟨21083031409934843541135037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112442834186319165552720197 21083031409934843541135037)
          ·
            refine ⟨7906136778725566327925639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21083031409934843541135037 7906136778725566327925639)
            ·
              refine ⟨11859205168088349491888459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906136778725566327925639 11859205168088349491888459)
              ·
                refine ⟨17788807752132524237832689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859205168088349491888459 17788807752132524237832689)
                ·
                  refine ⟨13341605814099393178374517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17788807752132524237832689 13341605814099393178374517)
                  ·
                    refine ⟨1250775545071818110472611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13341605814099393178374517 1250775545071818110472611)
                    ·
                      rfl

theorem cell22_3653815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3653815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653815 prefixEnd_3653815 := by exact prefixLift 3653815
  have htrace : WordTrace (prefixWord ++ tailWord_3653815) baseStart_3653815 baseEnd_3653815 := by
    simpa [prefixWord, tailWord_3653815, baseEnd_3653815] using wordTrace_append hprefix tailTrace_3653815
  have hstable : (prefixWord ++ tailWord_3653815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653815).length < 2 ^ (prefixWord ++ tailWord_3653815).sum := by decide
  have hdescent : baseEnd_3653815 < baseStart_3653815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653928 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3653928 : Nat := 118140960795 + 3653928 * 2 ^ 59
def prefixEnd_3653928 : Nat := 4983230072969 + 3 ^ 40 * 3653928 * 2
def baseEnd_3653928 : Nat := 1250814227281123482397265

theorem tailTrace_3653928 : CollatzResearch.WordTrace tailWord_3653928 prefixEnd_3653928 1250814227281123482397265 := by
  unfold tailWord_3653928
  simp only [CollatzResearch.WordTrace]
  refine ⟨66634851353225186032525219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88846468470966914710033625 66634851353225186032525219)
  ·
    refine ⟨99952277029837779048787829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66634851353225186032525219 99952277029837779048787829)
    ·
      refine ⟨9370525971547291785823859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99952277029837779048787829 9370525971547291785823859)
      ·
        refine ⟨14055788957320937678735789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370525971547291785823859 14055788957320937678735789)
        ·
          refine ⟨5270920858995351629525921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14055788957320937678735789 5270920858995351629525921)
          ·
            refine ⟨3953190644246513722144441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5270920858995351629525921 3953190644246513722144441)
            ·
              refine ⟨2964892983184885291608331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953190644246513722144441 2964892983184885291608331)
              ·
                refine ⟨4447339474777327937412497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964892983184885291608331 4447339474777327937412497)
                ·
                  refine ⟨3335504606082995953059373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447339474777327937412497 3335504606082995953059373)
                  ·
                    refine ⟨1250814227281123482397265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335504606082995953059373 1250814227281123482397265)
                    ·
                      rfl

theorem cell22_3653928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3653928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653928 prefixEnd_3653928 := by exact prefixLift 3653928
  have htrace : WordTrace (prefixWord ++ tailWord_3653928) baseStart_3653928 baseEnd_3653928 := by
    simpa [prefixWord, tailWord_3653928, baseEnd_3653928] using wordTrace_append hprefix tailTrace_3653928
  have hstable : (prefixWord ++ tailWord_3653928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653928).length < 2 ^ (prefixWord ++ tailWord_3653928).sum := by decide
  have hdescent : baseEnd_3653928 < baseStart_3653928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653995 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_3653995 : Nat := 118140960795 + 3653995 * 2 ^ 59
def prefixEnd_3653995 : Nat := 4983230072969 + 3 ^ 40 * 3653995 * 2
def baseEnd_3653995 : Nat := 1250837162750357640972059

theorem tailTrace_3653995 : CollatzResearch.WordTrace tailWord_3653995 prefixEnd_3653995 1250837162750357640972059 := by
  unfold tailWord_3653995
  simp only [CollatzResearch.WordTrace]
  refine ⟨133272146397207642507739439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88848097598138428338492959 133272146397207642507739439)
  ·
    refine ⟨199908219595811463761609159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133272146397207642507739439 199908219595811463761609159)
    ·
      refine ⟨299862329393717195642413739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199908219595811463761609159 299862329393717195642413739)
      ·
        refine ⟨449793494090575793463620609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299862329393717195642413739 449793494090575793463620609)
        ·
          refine ⟨337345120567931845097715457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449793494090575793463620609 337345120567931845097715457)
          ·
            refine ⟨253008840425948883823286593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337345120567931845097715457 253008840425948883823286593)
            ·
              refine ⟨189756630319461662867464945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253008840425948883823286593 189756630319461662867464945)
              ·
                refine ⟨142317472739596247150598709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189756630319461662867464945 142317472739596247150598709)
                ·
                  refine ⟨13342263069337148170368629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142317472739596247150598709 13342263069337148170368629)
                  ·
                    refine ⟨1250837162750357640972059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13342263069337148170368629 1250837162750357640972059)
                    ·
                      rfl

theorem cell22_3653995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_3653995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653995 prefixEnd_3653995 := by exact prefixLift 3653995
  have htrace : WordTrace (prefixWord ++ tailWord_3653995) baseStart_3653995 baseEnd_3653995 := by
    simpa [prefixWord, tailWord_3653995, baseEnd_3653995] using wordTrace_append hprefix tailTrace_3653995
  have hstable : (prefixWord ++ tailWord_3653995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653995).length < 2 ^ (prefixWord ++ tailWord_3653995).sum := by decide
  have hdescent : baseEnd_3653995 < baseStart_3653995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653997 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3653997 : Nat := 118140960795 + 3653997 * 2 ^ 59
def prefixEnd_3653997 : Nat := 4983230072969 + 3 ^ 40 * 3653997 * 2
def baseEnd_3653997 : Nat := 416945949130410100807351

theorem tailTrace_3653997 : CollatzResearch.WordTrace tailWord_3653997 prefixEnd_3653997 416945949130410100807351 := by
  unfold tailWord_3653997
  simp only [CollatzResearch.WordTrace]
  refine ⟨133272219343200396849312245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88848146228800264566208163 133272219343200396849312245)
  ·
    refine ⟨12494270563425037204623023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133272219343200396849312245 12494270563425037204623023)
    ·
      refine ⟨18741405845137555806934535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12494270563425037204623023 18741405845137555806934535)
      ·
        refine ⟨28112108767706333710401803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18741405845137555806934535 28112108767706333710401803)
        ·
          refine ⟨42168163151559500565602705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28112108767706333710401803 42168163151559500565602705)
          ·
            refine ⟨31626122363669625424202029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42168163151559500565602705 31626122363669625424202029)
            ·
              refine ⟨11859795886376109534075761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31626122363669625424202029 11859795886376109534075761)
              ·
                refine ⟨8894846914782082150556821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11859795886376109534075761 8894846914782082150556821)
                ·
                  refine ⟨416945949130410100807351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8894846914782082150556821 416945949130410100807351)
                  ·
                    rfl

theorem cell22_3653997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3653997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3653997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3653997 prefixEnd_3653997 := by exact prefixLift 3653997
  have htrace : WordTrace (prefixWord ++ tailWord_3653997) baseStart_3653997 baseEnd_3653997 := by
    simpa [prefixWord, tailWord_3653997, baseEnd_3653997] using wordTrace_append hprefix tailTrace_3653997
  have hstable : (prefixWord ++ tailWord_3653997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653997).length < 2 ^ (prefixWord ++ tailWord_3653997).sum := by decide
  have hdescent : baseEnd_3653997 < baseStart_3653997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654046 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3654046 : Nat := 118140960795 + 3654046 * 2 ^ 59
def prefixEnd_3654046 : Nat := 4983230072969 + 3 ^ 40 * 3654046 * 2
def baseEnd_3654046 : Nat := 1250854621092610507946903

theorem tailTrace_3654046 : CollatzResearch.WordTrace tailWord_3654046 prefixEnd_3654046 1250854621092610507946903 := by
  unfold tailWord_3654046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659250815002859777230749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88849337680015252145230661 16659250815002859777230749)
  ·
    refine ⟨6247219055626072416461531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16659250815002859777230749 6247219055626072416461531)
    ·
      refine ⟨9370828583439108624692297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247219055626072416461531 9370828583439108624692297)
      ·
        refine ⟨7028121437579331468519223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9370828583439108624692297 7028121437579331468519223)
        ·
          refine ⟨10542182156368997202778835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028121437579331468519223 10542182156368997202778835)
          ·
            refine ⟨15813273234553495804168253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542182156368997202778835 15813273234553495804168253)
            ·
              refine ⟨5929977462957560926563095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15813273234553495804168253 5929977462957560926563095)
              ·
                refine ⟨8894966194436341389844643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929977462957560926563095 8894966194436341389844643)
                ·
                  refine ⟨13342449291654512084766965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8894966194436341389844643 13342449291654512084766965)
                  ·
                    refine ⟨1250854621092610507946903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13342449291654512084766965 1250854621092610507946903)
                    ·
                      rfl

theorem cell22_3654046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3654046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654046 prefixEnd_3654046 := by exact prefixLift 3654046
  have htrace : WordTrace (prefixWord ++ tailWord_3654046) baseStart_3654046 baseEnd_3654046 := by
    simpa [prefixWord, tailWord_3654046, baseEnd_3654046] using wordTrace_append hprefix tailTrace_3654046
  have hstable : (prefixWord ++ tailWord_3654046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654046).length < 2 ^ (prefixWord ++ tailWord_3654046).sum := by decide
  have hdescent : baseEnd_3654046 < baseStart_3654046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654087 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 7]
def baseStart_3654087 : Nat := 118140960795 + 3654087 * 2 ^ 59
def prefixEnd_3654087 : Nat := 4983230072969 + 3 ^ 40 * 3654087 * 2
def baseEnd_3654087 : Nat := 416956218743500022557259

theorem tailTrace_3654087 : CollatzResearch.WordTrace tailWord_3654087 prefixEnd_3654087 416956218743500022557259 := by
  unfold tailWord_3654087
  simp only [CollatzResearch.WordTrace]
  refine ⟨133275501912874342220088515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88850334608582894813392343 133275501912874342220088515)
  ·
    refine ⟨199913252869311513330132773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133275501912874342220088515 199913252869311513330132773)
    ·
      refine ⟨37483734912995908749399895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199913252869311513330132773 37483734912995908749399895)
      ·
        refine ⟨56225602369493863124099843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37483734912995908749399895 56225602369493863124099843)
        ·
          refine ⟨84338403554240794686149765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56225602369493863124099843 84338403554240794686149765)
          ·
            refine ⟨15813450666420149003653081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84338403554240794686149765 15813450666420149003653081)
            ·
              refine ⟨11860087999815111752739811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15813450666420149003653081 11860087999815111752739811)
              ·
                refine ⟨17790131999722667629109717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860087999815111752739811 17790131999722667629109717)
                ·
                  refine ⟨416956218743500022557259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17790131999722667629109717 416956218743500022557259)
                  ·
                    rfl

theorem cell22_3654087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 7].length) (baseStart_3654087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654087 prefixEnd_3654087 := by exact prefixLift 3654087
  have htrace : WordTrace (prefixWord ++ tailWord_3654087) baseStart_3654087 baseEnd_3654087 := by
    simpa [prefixWord, tailWord_3654087, baseEnd_3654087] using wordTrace_append hprefix tailTrace_3654087
  have hstable : (prefixWord ++ tailWord_3654087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654087).length < 2 ^ (prefixWord ++ tailWord_3654087).sum := by decide
  have hdescent : baseEnd_3654087 < baseStart_3654087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654147 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_3654147 : Nat := 118140960795 + 3654147 * 2 ^ 59
def prefixEnd_3654147 : Nat := 4983230072969 + 3 ^ 40 * 3654147 * 2
def baseEnd_3654147 : Nat := 1250889195456679911171593

theorem tailTrace_3654147 : CollatzResearch.WordTrace tailWord_3654147 prefixEnd_3654147 1250889195456679911171593 := by
  unfold tailWord_3654147
  simp only [CollatzResearch.WordTrace]
  refine ⟨133277690292656972467272695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88851793528437981644848463 133277690292656972467272695)
  ·
    refine ⟨199916535438985458700909043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133277690292656972467272695 199916535438985458700909043)
    ·
      refine ⟨299874803158478188051363565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199916535438985458700909043 299874803158478188051363565)
      ·
        refine ⟨112453051184429320519261337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299874803158478188051363565 112453051184429320519261337)
        ·
          refine ⟨84339788388321990389446003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112453051184429320519261337 84339788388321990389446003)
          ·
            refine ⟨126509682582482985584169005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84339788388321990389446003 126509682582482985584169005)
            ·
              refine ⟨47441130968431119594063377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126509682582482985584169005 47441130968431119594063377)
              ·
                refine ⟨35580848226323339695547533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47441130968431119594063377 35580848226323339695547533)
                ·
                  refine ⟨13342818084871252385830325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35580848226323339695547533 13342818084871252385830325)
                  ·
                    refine ⟨1250889195456679911171593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13342818084871252385830325 1250889195456679911171593)
                    ·
                      rfl

theorem cell22_3654147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_3654147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654147 prefixEnd_3654147 := by exact prefixLift 3654147
  have htrace : WordTrace (prefixWord ++ tailWord_3654147) baseStart_3654147 baseEnd_3654147 := by
    simpa [prefixWord, tailWord_3654147, baseEnd_3654147] using wordTrace_append hprefix tailTrace_3654147
  have hstable : (prefixWord ++ tailWord_3654147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654147).length < 2 ^ (prefixWord ++ tailWord_3654147).sum := by decide
  have hdescent : baseEnd_3654147 < baseStart_3654147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654179 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 1, 6]
def baseStart_3654179 : Nat := 118140960795 + 3654179 * 2 ^ 59
def prefixEnd_3654179 : Nat := 4983230072969 + 3 ^ 40 * 3654179 * 2
def baseEnd_3654179 : Nat := 1250900149710642494371495

theorem tailTrace_3654179 : CollatzResearch.WordTrace tailWord_3654179 prefixEnd_3654179 1250900149710642494371495 := by
  unfold tailWord_3654179
  simp only [CollatzResearch.WordTrace]
  refine ⟨133278857428541041932437591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88852571619027361288291727 133278857428541041932437591)
  ·
    refine ⟨199918286142811562898656387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133278857428541041932437591 199918286142811562898656387)
    ·
      refine ⟨299877429214217344347984581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199918286142811562898656387 299877429214217344347984581)
      ·
        refine ⟨56227017977665752065247109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299877429214217344347984581 56227017977665752065247109)
        ·
          refine ⟨10542565870812328512233833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56227017977665752065247109 10542565870812328512233833)
          ·
            refine ⟨7906924403109246384175375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10542565870812328512233833 7906924403109246384175375)
            ·
              refine ⟨11860386604663869576263063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906924403109246384175375 11860386604663869576263063)
              ·
                refine ⟨17790579906995804364394595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860386604663869576263063 17790579906995804364394595)
                ·
                  refine ⟨26685869860493706546591893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17790579906995804364394595 26685869860493706546591893)
                  ·
                    refine ⟨1250900149710642494371495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26685869860493706546591893 1250900149710642494371495)
                    ·
                      rfl

theorem cell22_3654179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_3654179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654179 prefixEnd_3654179 := by exact prefixLift 3654179
  have htrace : WordTrace (prefixWord ++ tailWord_3654179) baseStart_3654179 baseEnd_3654179 := by
    simpa [prefixWord, tailWord_3654179, baseEnd_3654179] using wordTrace_append hprefix tailTrace_3654179
  have hstable : (prefixWord ++ tailWord_3654179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654179).length < 2 ^ (prefixWord ++ tailWord_3654179).sum := by decide
  have hdescent : baseEnd_3654179 < baseStart_3654179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654198 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3654198 : Nat := 118140960795 + 3654198 * 2 ^ 59
def prefixEnd_3654198 : Nat := 4983230072969 + 3 ^ 40 * 3654198 * 2
def baseEnd_3654198 : Nat := 1250906653798932778146437

theorem tailTrace_3654198 : CollatzResearch.WordTrace tailWord_3654198 prefixEnd_3654198 1250906653798932778146437 := by
  unfold tailWord_3654198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329971900967013011086203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88853033610314805451586165 8329971900967013011086203)
  ·
    refine ⟨12494957851450519516629305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8329971900967013011086203 12494957851450519516629305)
    ·
      refine ⟨9371218388587889637471979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12494957851450519516629305 9371218388587889637471979)
      ·
        refine ⟨14056827582881834456207969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9371218388587889637471979 14056827582881834456207969)
        ·
          refine ⟨10542620687161375842155977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14056827582881834456207969 10542620687161375842155977)
          ·
            refine ⟨7906965515371031881616983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10542620687161375842155977 7906965515371031881616983)
            ·
              refine ⟨11860448273056547822425475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906965515371031881616983 11860448273056547822425475)
              ·
                refine ⟨17790672409584821733638213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860448273056547822425475 17790672409584821733638213)
                ·
                  refine ⟨3335751076797154075057165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17790672409584821733638213 3335751076797154075057165)
                  ·
                    refine ⟨1250906653798932778146437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335751076797154075057165 1250906653798932778146437)
                    ·
                      rfl

theorem cell22_3654198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3654198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654198 prefixEnd_3654198 := by exact prefixLift 3654198
  have htrace : WordTrace (prefixWord ++ tailWord_3654198) baseStart_3654198 baseEnd_3654198 := by
    simpa [prefixWord, tailWord_3654198, baseEnd_3654198] using wordTrace_append hprefix tailTrace_3654198
  have hstable : (prefixWord ++ tailWord_3654198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654198).length < 2 ^ (prefixWord ++ tailWord_3654198).sum := by decide
  have hdescent : baseEnd_3654198 < baseStart_3654198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654226 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3654226 : Nat := 118140960795 + 3654226 * 2 ^ 59
def prefixEnd_3654226 : Nat := 4983230072969 + 3 ^ 40 * 3654226 * 2
def baseEnd_3654226 : Nat := 1250916238771150038446351

theorem tailTrace_3654226 : CollatzResearch.WordTrace tailWord_3654226 prefixEnd_3654226 1250916238771150038446351 := by
  unfold tailWord_3654226
  simp only [CollatzResearch.WordTrace]
  refine ⟨33320142914842692239849633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88853714439580512639599021 33320142914842692239849633)
  ·
    refine ⟨24990107186132019179887225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33320142914842692239849633 24990107186132019179887225)
    ·
      refine ⟨18742580389599014384915419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24990107186132019179887225 18742580389599014384915419)
      ·
        refine ⟨28113870584398521577373129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18742580389599014384915419 28113870584398521577373129)
        ·
          refine ⟨21085402938298891183029847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28113870584398521577373129 21085402938298891183029847)
          ·
            refine ⟨31628104407448336774544771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21085402938298891183029847 31628104407448336774544771)
            ·
              refine ⟨47442156611172505161817157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31628104407448336774544771 47442156611172505161817157)
              ·
                refine ⟨8895404364594844717840717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47442156611172505161817157 8895404364594844717840717)
                ·
                  refine ⟨3335776636723066769190269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8895404364594844717840717 3335776636723066769190269)
                  ·
                    refine ⟨1250916238771150038446351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335776636723066769190269 1250916238771150038446351)
                    ·
                      rfl

theorem cell22_3654226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3654226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654226 prefixEnd_3654226 := by exact prefixLift 3654226
  have htrace : WordTrace (prefixWord ++ tailWord_3654226) baseStart_3654226 baseEnd_3654226 := by
    simpa [prefixWord, tailWord_3654226, baseEnd_3654226] using wordTrace_append hprefix tailTrace_3654226
  have hstable : (prefixWord ++ tailWord_3654226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654226).length < 2 ^ (prefixWord ++ tailWord_3654226).sum := by decide
  have hdescent : baseEnd_3654226 < baseStart_3654226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654286 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3654286 : Nat := 118140960795 + 3654286 * 2 ^ 59
def prefixEnd_3654286 : Nat := 4983230072969 + 3 ^ 40 * 3654286 * 2
def baseEnd_3654286 : Nat := 1250936777997329881946167

theorem tailTrace_3654286 : CollatzResearch.WordTrace tailWord_3654286 prefixEnd_3654286 1250936777997329881946167 := by
  unfold tailWord_3654286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16660345004894174900822839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88855173359435599471055141 16660345004894174900822839)
  ·
    refine ⟨24990517507341262351234259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16660345004894174900822839 24990517507341262351234259)
    ·
      refine ⟨37485776261011893526851389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24990517507341262351234259 37485776261011893526851389)
      ·
        refine ⟨14057166097879460072569271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37485776261011893526851389 14057166097879460072569271)
        ·
          refine ⟨21085749146819190108853907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14057166097879460072569271 21085749146819190108853907)
          ·
            refine ⟨31628623720228785163280861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21085749146819190108853907 31628623720228785163280861)
            ·
              refine ⟨11860733895085794436230323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31628623720228785163280861 11860733895085794436230323)
              ·
                refine ⟨17791100842628691654345485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860733895085794436230323 17791100842628691654345485)
                ·
                  refine ⟨6671662815985759370379557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17791100842628691654345485 6671662815985759370379557)
                  ·
                    refine ⟨1250936777997329881946167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6671662815985759370379557 1250936777997329881946167)
                    ·
                      rfl

theorem cell22_3654286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3654286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654286 prefixEnd_3654286 := by exact prefixLift 3654286
  have htrace : WordTrace (prefixWord ++ tailWord_3654286) baseStart_3654286 baseEnd_3654286 := by
    simpa [prefixWord, tailWord_3654286, baseEnd_3654286] using wordTrace_append hprefix tailTrace_3654286
  have hstable : (prefixWord ++ tailWord_3654286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654286).length < 2 ^ (prefixWord ++ tailWord_3654286).sum := by decide
  have hdescent : baseEnd_3654286 < baseStart_3654286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654311 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3654311 : Nat := 118140960795 + 3654311 * 2 ^ 59
def prefixEnd_3654311 : Nat := 4983230072969 + 3 ^ 40 * 3654311 * 2
def baseEnd_3654311 : Nat := 1250945336008238150071091

theorem tailTrace_3654311 : CollatzResearch.WordTrace tailWord_3654311 prefixEnd_3654311 1250945336008238150071091 := by
  unfold tailWord_3654311
  simp only [CollatzResearch.WordTrace]
  refine ⟨133283671864062828476242787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88855781242708552317495191 133283671864062828476242787)
  ·
    refine ⟨199925507796094242714364181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133283671864062828476242787 199925507796094242714364181)
    ·
      refine ⟨9371508177941917627235821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199925507796094242714364181 9371508177941917627235821)
      ·
        refine ⟨3514315566728219110213433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9371508177941917627235821 3514315566728219110213433)
        ·
          refine ⟨2635736675046164332660075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514315566728219110213433 2635736675046164332660075)
          ·
            refine ⟨3953605012569246498990113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635736675046164332660075 3953605012569246498990113)
            ·
              refine ⟨2965203759426934874242585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953605012569246498990113 2965203759426934874242585)
              ·
                refine ⟨2223902819570201155681939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965203759426934874242585 2223902819570201155681939)
                ·
                  refine ⟨3335854229355301733522909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223902819570201155681939 3335854229355301733522909)
                  ·
                    refine ⟨1250945336008238150071091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335854229355301733522909 1250945336008238150071091)
                    ·
                      rfl

theorem cell22_3654311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3654311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654311 prefixEnd_3654311 := by exact prefixLift 3654311
  have htrace : WordTrace (prefixWord ++ tailWord_3654311) baseStart_3654311 baseEnd_3654311 := by
    simpa [prefixWord, tailWord_3654311, baseEnd_3654311] using wordTrace_append hprefix tailTrace_3654311
  have hstable : (prefixWord ++ tailWord_3654311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654311).length < 2 ^ (prefixWord ++ tailWord_3654311).sum := by decide
  have hdescent : baseEnd_3654311 < baseStart_3654311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654333 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_3654333 : Nat := 118140960795 + 3654333 * 2 ^ 59
def prefixEnd_3654333 : Nat := 4983230072969 + 3 ^ 40 * 3654333 * 2
def baseEnd_3654333 : Nat := 1250952867057837426021023

theorem tailTrace_3654333 : CollatzResearch.WordTrace tailWord_3654333 prefixEnd_3654333 1250952867057837426021023 := by
  unfold tailWord_3654333
  simp only [CollatzResearch.WordTrace]
  refine ⟨133284474269983126233543653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88856316179988750822362435 133284474269983126233543653)
  ·
    refine ⟨24990838925621836168789435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133284474269983126233543653 24990838925621836168789435)
    ·
      refine ⟨37486258388432754253184153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24990838925621836168789435 37486258388432754253184153)
      ·
        refine ⟨28114693791324565689888115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37486258388432754253184153 28114693791324565689888115)
        ·
          refine ⟨42172040686986848534832173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28114693791324565689888115 42172040686986848534832173)
          ·
            refine ⟨15814515257620068200562065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42172040686986848534832173 15814515257620068200562065)
            ·
              refine ⟨11860886443215051150421549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15814515257620068200562065 11860886443215051150421549)
              ·
                refine ⟨4447832416205644181408081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11860886443215051150421549 4447832416205644181408081)
                ·
                  refine ⟨3335874312154233136056061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447832416205644181408081 3335874312154233136056061)
                  ·
                    refine ⟨1250952867057837426021023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335874312154233136056061 1250952867057837426021023)
                    ·
                      rfl

theorem cell22_3654333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_3654333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654333 prefixEnd_3654333 := by exact prefixLift 3654333
  have htrace : WordTrace (prefixWord ++ tailWord_3654333) baseStart_3654333 baseEnd_3654333 := by
    simpa [prefixWord, tailWord_3654333, baseEnd_3654333] using wordTrace_append hprefix tailTrace_3654333
  have hstable : (prefixWord ++ tailWord_3654333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654333).length < 2 ^ (prefixWord ++ tailWord_3654333).sum := by decide
  have hdescent : baseEnd_3654333 < baseStart_3654333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654348 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_3654348 : Nat := 118140960795 + 3654348 * 2 ^ 59
def prefixEnd_3654348 : Nat := 4983230072969 + 3 ^ 40 * 3654348 * 2
def baseEnd_3654348 : Nat := 1250958001864382386895977

theorem tailTrace_3654348 : CollatzResearch.WordTrace tailWord_3654348 prefixEnd_3654348 1250958001864382386895977 := by
  unfold tailWord_3654348
  simp only [CollatzResearch.WordTrace]
  refine ⟨66642510682464391897669849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88856680909952522530226465 66642510682464391897669849)
  ·
    refine ⟨49981883011848293923252387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66642510682464391897669849 49981883011848293923252387)
    ·
      refine ⟨74972824517772440884878581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49981883011848293923252387 74972824517772440884878581)
      ·
        refine ⟨7028702298541166332957367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74972824517772440884878581 7028702298541166332957367)
        ·
          refine ⟨10543053447811749499436051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028702298541166332957367 10543053447811749499436051)
          ·
            refine ⟨15814580171717624249154077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10543053447811749499436051 15814580171717624249154077)
            ·
              refine ⟨5930467564394109093432779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15814580171717624249154077 5930467564394109093432779)
              ·
                refine ⟨8895701346591163640149169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930467564394109093432779 8895701346591163640149169)
                ·
                  refine ⟨6671776009943372730111877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8895701346591163640149169 6671776009943372730111877)
                  ·
                    refine ⟨1250958001864382386895977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6671776009943372730111877 1250958001864382386895977)
                    ·
                      rfl

theorem cell22_3654348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_3654348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654348 prefixEnd_3654348 := by exact prefixLift 3654348
  have htrace : WordTrace (prefixWord ++ tailWord_3654348) baseStart_3654348 baseEnd_3654348 := by
    simpa [prefixWord, tailWord_3654348, baseEnd_3654348] using wordTrace_append hprefix tailTrace_3654348
  have hstable : (prefixWord ++ tailWord_3654348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654348).length < 2 ^ (prefixWord ++ tailWord_3654348).sum := by decide
  have hdescent : baseEnd_3654348 < baseStart_3654348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654361 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_3654361 : Nat := 118140960795 + 3654361 * 2 ^ 59
def prefixEnd_3654361 : Nat := 4983230072969 + 3 ^ 40 * 3654361 * 2
def baseEnd_3654361 : Nat := 1250962452030054686320937

theorem tailTrace_3654361 : CollatzResearch.WordTrace tailWord_3654361 prefixEnd_3654361 1250962452030054686320937 := by
  unfold tailWord_3654361
  simp only [CollatzResearch.WordTrace]
  refine ⟨133285495513881687015562937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88856997009254458010375291 133285495513881687015562937)
  ·
    refine ⟨99964121635411265261672203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133285495513881687015562937 99964121635411265261672203)
    ·
      refine ⟨149946182453116897892508305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99964121635411265261672203 149946182453116897892508305)
      ·
        refine ⟨112459636839837673419381229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149946182453116897892508305 112459636839837673419381229)
        ·
          refine ⟨42172363814939127532267961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112459636839837673419381229 42172363814939127532267961)
          ·
            refine ⟨31629272861204345649200971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42172363814939127532267961 31629272861204345649200971)
            ·
              refine ⟨47443909291806518473801457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31629272861204345649200971 47443909291806518473801457)
              ·
                refine ⟨35582931968854888855351093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47443909291806518473801457 35582931968854888855351093)
                ·
                  refine ⟨3335899872080145830189165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35582931968854888855351093 3335899872080145830189165)
                  ·
                    refine ⟨1250962452030054686320937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335899872080145830189165 1250962452030054686320937)
                    ·
                      rfl

theorem cell22_3654361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_3654361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654361 prefixEnd_3654361 := by exact prefixLift 3654361
  have htrace : WordTrace (prefixWord ++ tailWord_3654361) baseStart_3654361 baseEnd_3654361 := by
    simpa [prefixWord, tailWord_3654361, baseEnd_3654361] using wordTrace_append hprefix tailTrace_3654361
  have hstable : (prefixWord ++ tailWord_3654361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654361).length < 2 ^ (prefixWord ++ tailWord_3654361).sum := by decide
  have hdescent : baseEnd_3654361 < baseStart_3654361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654429 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3654429 : Nat := 118140960795 + 3654429 * 2 ^ 59
def prefixEnd_3654429 : Nat := 4983230072969 + 3 ^ 40 * 3654429 * 2
def baseEnd_3654429 : Nat := 1250985729819725175620729

theorem tailTrace_3654429 : CollatzResearch.WordTrace tailWord_3654429 prefixEnd_3654429 1250985729819725175620729 := by
  unfold tailWord_3654429
  simp only [CollatzResearch.WordTrace]
  refine ⟨133287975677635334629038341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88858650451756889752692227 133287975677635334629038341)
  ·
    refine ⟨24991495439556625242944689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133287975677635334629038341 24991495439556625242944689)
    ·
      refine ⟨18743621579667468932208517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24991495439556625242944689 18743621579667468932208517)
      ·
        refine ⟨3514429046187650424789097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18743621579667468932208517 3514429046187650424789097)
        ·
          refine ⟨2635821784640737818591823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514429046187650424789097 2635821784640737818591823)
          ·
            refine ⟨3953732676961106727887735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635821784640737818591823 3953732676961106727887735)
            ·
              refine ⟨5930599015441660091831603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953732676961106727887735 5930599015441660091831603)
              ·
                refine ⟨8895898523162490137747405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930599015441660091831603 8895898523162490137747405)
                ·
                  refine ⟨3335961946185933801655277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8895898523162490137747405 3335961946185933801655277)
                  ·
                    refine ⟨1250985729819725175620729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335961946185933801655277 1250985729819725175620729)
                    ·
                      rfl

theorem cell22_3654429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3654429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654429 prefixEnd_3654429 := by exact prefixLift 3654429
  have htrace : WordTrace (prefixWord ++ tailWord_3654429) baseStart_3654429 baseEnd_3654429 := by
    simpa [prefixWord, tailWord_3654429, baseEnd_3654429] using wordTrace_append hprefix tailTrace_3654429
  have hstable : (prefixWord ++ tailWord_3654429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654429).length < 2 ^ (prefixWord ++ tailWord_3654429).sum := by decide
  have hdescent : baseEnd_3654429 < baseStart_3654429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654481 : List Nat := [1, 2, 2, 1, 6, 10]
def baseStart_3654481 : Nat := 118140960795 + 3654481 * 2 ^ 59
def prefixEnd_3654481 : Nat := 4983230072969 + 3 ^ 40 * 3654481 * 2
def baseEnd_3654481 : Nat := 15444488030647091028649

theorem tailTrace_3654481 : CollatzResearch.WordTrace tailWord_3654481 prefixEnd_3654481 15444488030647091028649 := by
  unfold tailWord_3654481
  simp only [CollatzResearch.WordTrace]
  refine ⟨133289872273446947509931297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88859914848964631673287531 133289872273446947509931297)
  ·
    refine ⟨99967404205085210632448473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133289872273446947509931297 99967404205085210632448473)
    ·
      refine ⟨74975553153813907974336355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99967404205085210632448473 74975553153813907974336355)
      ·
        refine ⟨112463329730720861961504533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74975553153813907974336355 112463329730720861961504533)
        ·
          refine ⟨5271718581127540404445525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112463329730720861961504533 5271718581127540404445525)
          ·
            refine ⟨15444488030647091028649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5271718581127540404445525 15444488030647091028649)
            ·
              rfl

theorem cell22_3654481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 10].length) (baseStart_3654481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654481 prefixEnd_3654481 := by exact prefixLift 3654481
  have htrace : WordTrace (prefixWord ++ tailWord_3654481) baseStart_3654481 baseEnd_3654481 := by
    simpa [prefixWord, tailWord_3654481, baseEnd_3654481] using wordTrace_append hprefix tailTrace_3654481
  have hstable : (prefixWord ++ tailWord_3654481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654481).length < 2 ^ (prefixWord ++ tailWord_3654481).sum := by decide
  have hdescent : baseEnd_3654481 < baseStart_3654481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654485 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_3654485 : Nat := 118140960795 + 3654485 * 2 ^ 59
def prefixEnd_3654485 : Nat := 4983230072969 + 3 ^ 40 * 3654485 * 2
def baseEnd_3654485 : Nat := 1251004899764159696220557

theorem tailTrace_3654485 : CollatzResearch.WordTrace tailWord_3654485 prefixEnd_3654485 1251004899764159696220557 := by
  unfold tailWord_3654485
  simp only [CollatzResearch.WordTrace]
  refine ⟨133290018165432456193076909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88860012110288304128717939 133290018165432456193076909)
  ·
    refine ⟨49983756812037171072403841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133290018165432456193076909 49983756812037171072403841)
    ·
      refine ⟨37487817609027878304302881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49983756812037171072403841 37487817609027878304302881)
      ·
        refine ⟨28115863206770908728227161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37487817609027878304302881 28115863206770908728227161)
        ·
          refine ⟨21086897405078181546170371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28115863206770908728227161 21086897405078181546170371)
          ·
            refine ⟨31630346107617272319255557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21086897405078181546170371 31630346107617272319255557)
            ·
              refine ⟨5930689895178238559860417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31630346107617272319255557 5930689895178238559860417)
              ·
                refine ⟨4448017421383678919895313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5930689895178238559860417 4448017421383678919895313)
                ·
                  refine ⟨3336013066037759189921485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4448017421383678919895313 3336013066037759189921485)
                  ·
                    refine ⟨1251004899764159696220557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336013066037759189921485 1251004899764159696220557)
                    ·
                      rfl

theorem cell22_3654485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_3654485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654485 prefixEnd_3654485 := by exact prefixLift 3654485
  have htrace : WordTrace (prefixWord ++ tailWord_3654485) baseStart_3654485 baseEnd_3654485 := by
    simpa [prefixWord, tailWord_3654485, baseEnd_3654485] using wordTrace_append hprefix tailTrace_3654485
  have hstable : (prefixWord ++ tailWord_3654485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654485).length < 2 ^ (prefixWord ++ tailWord_3654485).sum := by decide
  have hdescent : baseEnd_3654485 < baseStart_3654485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654487 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 4]
def baseStart_3654487 : Nat := 118140960795 + 3654487 * 2 ^ 59
def prefixEnd_3654487 : Nat := 4983230072969 + 3 ^ 40 * 3654487 * 2
def baseEnd_3654487 : Nat := 417001861468344119223517

theorem tailTrace_3654487 : CollatzResearch.WordTrace tailWord_3654487 prefixEnd_3654487 417001861468344119223517 := by
  unfold tailWord_3654487
  simp only [CollatzResearch.WordTrace]
  refine ⟨133290091111425210534649715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88860060740950140356433143 133290091111425210534649715)
  ·
    refine ⟨199935136667137815801974573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133290091111425210534649715 199935136667137815801974573)
    ·
      refine ⟨74975676250176680925740465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199935136667137815801974573 74975676250176680925740465)
      ·
        refine ⟨56231757187632510694305349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74975676250176680925740465 56231757187632510694305349)
        ·
          refine ⟨10543454472681095755182253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56231757187632510694305349 10543454472681095755182253)
          ·
            refine ⟨3953795427255410908193345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10543454472681095755182253 3953795427255410908193345)
            ·
              refine ⟨2965346570441558181145009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953795427255410908193345 2965346570441558181145009)
              ·
                refine ⟨2224009927831168635858757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965346570441558181145009 2224009927831168635858757)
                ·
                  refine ⟨417001861468344119223517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2224009927831168635858757 417001861468344119223517)
                  ·
                    rfl

theorem cell22_3654487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 4].length) (baseStart_3654487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654487 prefixEnd_3654487 := by exact prefixLift 3654487
  have htrace : WordTrace (prefixWord ++ tailWord_3654487) baseStart_3654487 baseEnd_3654487 := by
    simpa [prefixWord, tailWord_3654487, baseEnd_3654487] using wordTrace_append hprefix tailTrace_3654487
  have hstable : (prefixWord ++ tailWord_3654487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654487).length < 2 ^ (prefixWord ++ tailWord_3654487).sum := by decide
  have hdescent : baseEnd_3654487 < baseStart_3654487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654513 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_3654513 : Nat := 118140960795 + 3654513 * 2 ^ 59
def prefixEnd_3654513 : Nat := 4983230072969 + 3 ^ 40 * 3654513 * 2
def baseEnd_3654513 : Nat := 1251014484736376956520471

theorem tailTrace_3654513 : CollatzResearch.WordTrace tailWord_3654513 prefixEnd_3654513 1251014484736376956520471 := by
  unfold tailWord_3654513
  simp only [CollatzResearch.WordTrace]
  refine ⟨133291039409331016975096193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88860692939554011316730795 133291039409331016975096193)
  ·
    refine ⟨99968279556998262731322145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133291039409331016975096193 99968279556998262731322145)
    ·
      refine ⟨74976209667748697048491609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99968279556998262731322145 74976209667748697048491609)
      ·
        refine ⟨56232157250811522786368707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74976209667748697048491609 56232157250811522786368707)
        ·
          refine ⟨84348235876217284179553061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56232157250811522786368707 84348235876217284179553061)
          ·
            refine ⟨15815294226790740783666199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84348235876217284179553061 15815294226790740783666199)
            ·
              refine ⟨23722941340186111175499299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15815294226790740783666199 23722941340186111175499299)
              ·
                refine ⟨35584412010279166763248949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23722941340186111175499299 35584412010279166763248949)
                ·
                  refine ⟨3336038625963671884054589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35584412010279166763248949 3336038625963671884054589)
                  ·
                    refine ⟨1251014484736376956520471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336038625963671884054589 1251014484736376956520471)
                    ·
                      rfl

theorem cell22_3654513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_3654513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654513 prefixEnd_3654513 := by exact prefixLift 3654513
  have htrace : WordTrace (prefixWord ++ tailWord_3654513) baseStart_3654513 baseEnd_3654513 := by
    simpa [prefixWord, tailWord_3654513, baseEnd_3654513] using wordTrace_append hprefix tailTrace_3654513
  have hstable : (prefixWord ++ tailWord_3654513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654513).length < 2 ^ (prefixWord ++ tailWord_3654513).sum := by decide
  have hdescent : baseEnd_3654513 < baseStart_3654513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654590 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3654590 : Nat := 118140960795 + 3654590 * 2 ^ 59
def prefixEnd_3654590 : Nat := 4983230072969 + 3 ^ 40 * 3654590 * 2
def baseEnd_3654590 : Nat := 1251040843409974422345235

theorem tailTrace_3654590 : CollatzResearch.WordTrace tailWord_3654590 prefixEnd_3654590 1251040843409974422345235 := by
  unfold tailWord_3654590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661730978756507390706153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88862565220034706083766149 16661730978756507390706153)
  ·
    refine ⟨12496298234067380543029615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16661730978756507390706153 12496298234067380543029615)
    ·
      refine ⟨18744447351101070814544423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12496298234067380543029615 18744447351101070814544423)
      ·
        refine ⟨28116671026651606221816635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18744447351101070814544423 28116671026651606221816635)
        ·
          refine ⟨42175006539977409332724953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28116671026651606221816635 42175006539977409332724953)
          ·
            refine ⟨31631254904983056999543715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42175006539977409332724953 31631254904983056999543715)
            ·
              refine ⟨47446882357474585499315573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31631254904983056999543715 47446882357474585499315573)
              ·
                refine ⟨4448145221013242390560835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47446882357474585499315573 4448145221013242390560835)
                ·
                  refine ⟨6672217831519863585841253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448145221013242390560835 6672217831519863585841253)
                  ·
                    refine ⟨1251040843409974422345235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6672217831519863585841253 1251040843409974422345235)
                    ·
                      rfl

theorem cell22_3654590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3654590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654590 prefixEnd_3654590 := by exact prefixLift 3654590
  have htrace : WordTrace (prefixWord ++ tailWord_3654590) baseStart_3654590 baseEnd_3654590 := by
    simpa [prefixWord, tailWord_3654590, baseEnd_3654590] using wordTrace_append hprefix tailTrace_3654590
  have hstable : (prefixWord ++ tailWord_3654590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654590).length < 2 ^ (prefixWord ++ tailWord_3654590).sum := by decide
  have hdescent : baseEnd_3654590 < baseStart_3654590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654663 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3654663 : Nat := 118140960795 + 3654663 * 2 ^ 59
def prefixEnd_3654663 : Nat := 4983230072969 + 3 ^ 40 * 3654663 * 2
def baseEnd_3654663 : Nat := 1251065832801826565270011

theorem tailTrace_3654663 : CollatzResearch.WordTrace tailWord_3654663 prefixEnd_3654663 1251065832801826565270011 := by
  unfold tailWord_3654663
  simp only [CollatzResearch.WordTrace]
  refine ⟨133296510358787592593056643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88864340239191728395371095 133296510358787592593056643)
  ·
    refine ⟨199944765538181388889584965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133296510358787592593056643 199944765538181388889584965)
    ·
      refine ⟨37489643538409010416797181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199944765538181388889584965 37489643538409010416797181)
      ·
        refine ⟨14058616326903378906298943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37489643538409010416797181 14058616326903378906298943)
        ·
          refine ⟨21087924490355068359448415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14058616326903378906298943 21087924490355068359448415)
          ·
            refine ⟨31631886735532602539172623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21087924490355068359448415 31631886735532602539172623)
            ·
              refine ⟨47447830103298903808758935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31631886735532602539172623 47447830103298903808758935)
              ·
                refine ⟨71171745154948355713138403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47447830103298903808758935 71171745154948355713138403)
                ·
                  refine ⟨106757617732422533569707605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71171745154948355713138403 106757617732422533569707605)
                  ·
                    refine ⟨1251065832801826565270011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106757617732422533569707605 1251065832801826565270011)
                    ·
                      rfl

theorem cell22_3654663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3654663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654663 prefixEnd_3654663 := by exact prefixLift 3654663
  have htrace : WordTrace (prefixWord ++ tailWord_3654663) baseStart_3654663 baseEnd_3654663 := by
    simpa [prefixWord, tailWord_3654663, baseEnd_3654663] using wordTrace_append hprefix tailTrace_3654663
  have hstable : (prefixWord ++ tailWord_3654663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654663).length < 2 ^ (prefixWord ++ tailWord_3654663).sum := by decide
  have hdescent : baseEnd_3654663 < baseStart_3654663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654693 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3654693 : Nat := 118140960795 + 3654693 * 2 ^ 59
def prefixEnd_3654693 : Nat := 4983230072969 + 3 ^ 40 * 3654693 * 2
def baseEnd_3654693 : Nat := 1251076102414916487019919

theorem tailTrace_3654693 : CollatzResearch.WordTrace tailWord_3654693 prefixEnd_3654693 1251076102414916487019919 := by
  unfold tailWord_3654693
  simp only [CollatzResearch.WordTrace]
  refine ⟨133297604548678907716648733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88865069699119271811099155 133297604548678907716648733)
  ·
    refine ⟨49986601705754590393743275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133297604548678907716648733 49986601705754590393743275)
    ·
      refine ⟨74979902558631885590614913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49986601705754590393743275 74979902558631885590614913)
      ·
        refine ⟨56234926918973914192961185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74979902558631885590614913 56234926918973914192961185)
        ·
          refine ⟨42176195189230435644720889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56234926918973914192961185 42176195189230435644720889)
          ·
            refine ⟨31632146391922826733540667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42176195189230435644720889 31632146391922826733540667)
            ·
              refine ⟨47448219587884240100311001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31632146391922826733540667 47448219587884240100311001)
              ·
                refine ⟨35586164690913180075233251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47448219587884240100311001 35586164690913180075233251)
                ·
                  refine ⟨53379247036369770112849877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35586164690913180075233251 53379247036369770112849877)
                  ·
                    refine ⟨1251076102414916487019919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53379247036369770112849877 1251076102414916487019919)
                    ·
                      rfl

theorem cell22_3654693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3654693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654693 prefixEnd_3654693 := by exact prefixLift 3654693
  have htrace : WordTrace (prefixWord ++ tailWord_3654693) baseStart_3654693 baseEnd_3654693 := by
    simpa [prefixWord, tailWord_3654693, baseEnd_3654693] using wordTrace_append hprefix tailTrace_3654693
  have hstable : (prefixWord ++ tailWord_3654693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654693).length < 2 ^ (prefixWord ++ tailWord_3654693).sum := by decide
  have hdescent : baseEnd_3654693 < baseStart_3654693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654712 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 5]
def baseStart_3654712 : Nat := 118140960795 + 3654712 * 2 ^ 59
def prefixEnd_3654712 : Nat := 4983230072969 + 3 ^ 40 * 3654712 * 2
def baseEnd_3654712 : Nat := 417027535501068923598287

theorem tailTrace_3654712 : CollatzResearch.WordTrace tailWord_3654712 prefixEnd_3654712 417027535501068923598287 := by
  unfold tailWord_3654712
  simp only [CollatzResearch.WordTrace]
  refine ⟨66649148767805036980795195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88865531690406715974393593 66649148767805036980795195)
  ·
    refine ⟨99973723151707555471192793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66649148767805036980795195 99973723151707555471192793)
    ·
      refine ⟨74980292363780666603394595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99973723151707555471192793 74980292363780666603394595)
      ·
        refine ⟨112470438545670999905091893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74980292363780666603394595 112470438545670999905091893)
        ·
          refine ⟨10544103613656656241102365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112470438545670999905091893 10544103613656656241102365)
          ·
            refine ⟨3954038855121246090413387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10544103613656656241102365 3954038855121246090413387)
            ·
              refine ⟨5931058282681869135620081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954038855121246090413387 5931058282681869135620081)
              ·
                refine ⟨4448293712011401851715061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931058282681869135620081 4448293712011401851715061)
                ·
                  refine ⟨417027535501068923598287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4448293712011401851715061 417027535501068923598287)
                  ·
                    rfl

theorem cell22_3654712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_3654712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654712 prefixEnd_3654712 := by exact prefixLift 3654712
  have htrace : WordTrace (prefixWord ++ tailWord_3654712) baseStart_3654712 baseEnd_3654712 := by
    simpa [prefixWord, tailWord_3654712, baseEnd_3654712] using wordTrace_append hprefix tailTrace_3654712
  have hstable : (prefixWord ++ tailWord_3654712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654712).length < 2 ^ (prefixWord ++ tailWord_3654712).sum := by decide
  have hdescent : baseEnd_3654712 < baseStart_3654712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654740 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3654740 : Nat := 118140960795 + 3654740 * 2 ^ 59
def prefixEnd_3654740 : Nat := 4983230072969 + 3 ^ 40 * 3654740 * 2
def baseEnd_3654740 : Nat := 417030730491808010364925

theorem tailTrace_3654740 : CollatzResearch.WordTrace tailWord_3654740 prefixEnd_3654740 417030730491808010364925 := by
  unfold tailWord_3654740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66649659389754317371804837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88866212519672423162406449 66649659389754317371804837)
  ·
    refine ⟨12496811135578934507213407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66649659389754317371804837 12496811135578934507213407)
    ·
      refine ⟨18745216703368401760820111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12496811135578934507213407 18745216703368401760820111)
      ·
        refine ⟨28117825055052602641230167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18745216703368401760820111 28117825055052602641230167)
        ·
          refine ⟨42176737582578903961845251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28117825055052602641230167 42176737582578903961845251)
          ·
            refine ⟨63265106373868355942767877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42176737582578903961845251 63265106373868355942767877)
            ·
              refine ⟨11862207445100316739268977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63265106373868355942767877 11862207445100316739268977)
              ·
                refine ⟨8896655583825237554451733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862207445100316739268977 8896655583825237554451733)
                ·
                  refine ⟨417030730491808010364925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8896655583825237554451733 417030730491808010364925)
                  ·
                    rfl

theorem cell22_3654740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3654740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654740 prefixEnd_3654740 := by exact prefixLift 3654740
  have htrace : WordTrace (prefixWord ++ tailWord_3654740) baseStart_3654740 baseEnd_3654740 := by
    simpa [prefixWord, tailWord_3654740, baseEnd_3654740] using wordTrace_append hprefix tailTrace_3654740
  have hstable : (prefixWord ++ tailWord_3654740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654740).length < 2 ^ (prefixWord ++ tailWord_3654740).sum := by decide
  have hdescent : baseEnd_3654740 < baseStart_3654740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654750 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3654750 : Nat := 118140960795 + 3654750 * 2 ^ 59
def prefixEnd_3654750 : Nat := 4983230072969 + 3 ^ 40 * 3654750 * 2
def baseEnd_3654750 : Nat := 1251095614679787338344745

theorem tailTrace_3654750 : CollatzResearch.WordTrace tailWord_3654750 prefixEnd_3654750 1251095614679787338344745 := by
  unfold tailWord_3654750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662460438684050806434213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88866455672981604300982469 16662460438684050806434213)
  ·
    refine ⟨3124211332253259526206415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16662460438684050806434213 3124211332253259526206415)
    ·
      refine ⟨4686316998379889289309623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124211332253259526206415 4686316998379889289309623)
      ·
        refine ⟨7029475497569833933964435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686316998379889289309623 7029475497569833933964435)
        ·
          refine ⟨10544213246354750900946653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029475497569833933964435 10544213246354750900946653)
          ·
            refine ⟨3954079967383031587854995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10544213246354750900946653 3954079967383031587854995)
            ·
              refine ⟨5931119951074547381782493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954079967383031587854995 5931119951074547381782493)
              ·
                refine ⟨2224169981652955268168435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5931119951074547381782493 2224169981652955268168435)
                ·
                  refine ⟨3336254972479432902252653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224169981652955268168435 3336254972479432902252653)
                  ·
                    refine ⟨1251095614679787338344745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336254972479432902252653 1251095614679787338344745)
                    ·
                      rfl

theorem cell22_3654750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3654750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654750 prefixEnd_3654750 := by exact prefixLift 3654750
  have htrace : WordTrace (prefixWord ++ tailWord_3654750) baseStart_3654750 baseEnd_3654750 := by
    simpa [prefixWord, tailWord_3654750, baseEnd_3654750] using wordTrace_append hprefix tailTrace_3654750
  have hstable : (prefixWord ++ tailWord_3654750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654750).length < 2 ^ (prefixWord ++ tailWord_3654750).sum := by decide
  have hdescent : baseEnd_3654750 < baseStart_3654750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654785 : List Nat := [1, 2, 4, 2, 2, 1, 1, 9]
def baseStart_3654785 : Nat := 118140960795 + 3654785 * 2 ^ 59
def prefixEnd_3654785 : Nat := 4983230072969 + 3 ^ 40 * 3654785 * 2
def baseEnd_3654785 : Nat := 139011955099450990413293

theorem tailTrace_3654785 : CollatzResearch.WordTrace tailWord_3654785 prefixEnd_3654785 139011955099450990413293 := by
  unfold tailWord_3654785
  simp only [CollatzResearch.WordTrace]
  refine ⟨133300960064345607428997809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88867306709563738285998539 133300960064345607428997809)
  ·
    refine ⟨99975720048259205571748357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133300960064345607428997809 99975720048259205571748357)
    ·
      refine ⟨18745447509048601044702817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99975720048259205571748357 18745447509048601044702817)
      ·
        refine ⟨14059085631786450783527113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18745447509048601044702817 14059085631786450783527113)
        ·
          refine ⟨10544314223839838087645335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14059085631786450783527113 10544314223839838087645335)
          ·
            refine ⟨15816471335759757131468003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544314223839838087645335 15816471335759757131468003)
            ·
              refine ⟨23724707003639635697202005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15816471335759757131468003 23724707003639635697202005)
              ·
                refine ⟨139011955099450990413293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23724707003639635697202005 139011955099450990413293)
                ·
                  rfl

theorem cell22_3654785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 9].length) (baseStart_3654785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654785 prefixEnd_3654785 := by exact prefixLift 3654785
  have htrace : WordTrace (prefixWord ++ tailWord_3654785) baseStart_3654785 baseEnd_3654785 := by
    simpa [prefixWord, tailWord_3654785, baseEnd_3654785] using wordTrace_append hprefix tailTrace_3654785
  have hstable : (prefixWord ++ tailWord_3654785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654785).length < 2 ^ (prefixWord ++ tailWord_3654785).sum := by decide
  have hdescent : baseEnd_3654785 < baseStart_3654785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654789 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_3654789 : Nat := 118140960795 + 3654789 * 2 ^ 59
def prefixEnd_3654789 : Nat := 4983230072969 + 3 ^ 40 * 3654789 * 2
def baseEnd_3654789 : Nat := 1251108965176804236619625

theorem tailTrace_3654789 : CollatzResearch.WordTrace tailWord_3654789 prefixEnd_3654789 1251108965176804236619625 := by
  unfold tailWord_3654789
  simp only [CollatzResearch.WordTrace]
  refine ⟨133301105956331116112143421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88867403970887410741428947 133301105956331116112143421)
  ·
    refine ⟨49987914733624168542053783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133301105956331116112143421 49987914733624168542053783)
    ·
      refine ⟨74981872100436252813080675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49987914733624168542053783 74981872100436252813080675)
      ·
        refine ⟨112472808150654379219621013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74981872100436252813080675 112472808150654379219621013)
        ·
          refine ⟨5272162882061924025919735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112472808150654379219621013 5272162882061924025919735)
          ·
            refine ⟨7908244323092886038879603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272162882061924025919735 7908244323092886038879603)
            ·
              refine ⟨11862366484639329058319405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908244323092886038879603 11862366484639329058319405)
              ·
                refine ⟨4448387431739748396869777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11862366484639329058319405 4448387431739748396869777)
                ·
                  refine ⟨3336290573804811297652333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4448387431739748396869777 3336290573804811297652333)
                  ·
                    refine ⟨1251108965176804236619625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336290573804811297652333 1251108965176804236619625)
                    ·
                      rfl

theorem cell22_3654789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_3654789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654789 prefixEnd_3654789 := by exact prefixLift 3654789
  have htrace : WordTrace (prefixWord ++ tailWord_3654789) baseStart_3654789 baseEnd_3654789 := by
    simpa [prefixWord, tailWord_3654789, baseEnd_3654789] using wordTrace_append hprefix tailTrace_3654789
  have hstable : (prefixWord ++ tailWord_3654789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654789).length < 2 ^ (prefixWord ++ tailWord_3654789).sum := by decide
  have hdescent : baseEnd_3654789 < baseStart_3654789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654845 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3654845 : Nat := 118140960795 + 3654845 * 2 ^ 59
def prefixEnd_3654845 : Nat := 4983230072969 + 3 ^ 40 * 3654845 * 2
def baseEnd_3654845 : Nat := 1251128135121238757219453

theorem tailTrace_3654845 : CollatzResearch.WordTrace tailWord_3654845 prefixEnd_3654845 1251128135121238757219453 := by
  unfold tailWord_3654845
  simp only [CollatzResearch.WordTrace]
  refine ⟨133303148444128237676181989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88868765629418825117454659 133303148444128237676181989)
  ·
    refine ⟨24994340333274044564284123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133303148444128237676181989 24994340333274044564284123)
    ·
      refine ⟨37491510499911066846426185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24994340333274044564284123 37491510499911066846426185)
      ·
        refine ⟨28118632874933300134819639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37491510499911066846426185 28118632874933300134819639)
        ·
          refine ⟨42177949312399950202229459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28118632874933300134819639 42177949312399950202229459)
          ·
            refine ⟨63266923968599925303344189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42177949312399950202229459 63266923968599925303344189)
            ·
              refine ⟨23725096488224971988754071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63266923968599925303344189 23725096488224971988754071)
              ·
                refine ⟨35587644732337457983131107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23725096488224971988754071 35587644732337457983131107)
                ·
                  refine ⟨53381467098506186974696661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35587644732337457983131107 53381467098506186974696661)
                  ·
                    refine ⟨1251128135121238757219453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53381467098506186974696661 1251128135121238757219453)
                    ·
                      rfl

theorem cell22_3654845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3654845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654845 prefixEnd_3654845 := by exact prefixLift 3654845
  have htrace : WordTrace (prefixWord ++ tailWord_3654845) baseStart_3654845 baseEnd_3654845 := by
    simpa [prefixWord, tailWord_3654845, baseEnd_3654845] using wordTrace_append hprefix tailTrace_3654845
  have hstable : (prefixWord ++ tailWord_3654845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654845).length < 2 ^ (prefixWord ++ tailWord_3654845).sum := by decide
  have hdescent : baseEnd_3654845 < baseStart_3654845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654892 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_3654892 : Nat := 118140960795 + 3654892 * 2 ^ 59
def prefixEnd_3654892 : Nat := 4983230072969 + 3 ^ 40 * 3654892 * 2
def baseEnd_3654892 : Nat := 417048074727248767098103

theorem tailTrace_3654892 : CollatzResearch.WordTrace tailWord_3654892 prefixEnd_3654892 417048074727248767098103 := by
  unfold tailWord_3654892
  simp only [CollatzResearch.WordTrace]
  refine ⟨66652431337478982351571465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88869908449971976468761953 66652431337478982351571465)
  ·
    refine ⟨49989323503109236763678599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66652431337478982351571465 49989323503109236763678599)
    ·
      refine ⟨74983985254663855145517899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49989323503109236763678599 74983985254663855145517899)
      ·
        refine ⟨112475977881995782718276849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74983985254663855145517899 112475977881995782718276849)
        ·
          refine ⟨84356983411496837038707637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112475977881995782718276849 84356983411496837038707637)
          ·
            refine ⟨7908467194827828472378841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84356983411496837038707637 7908467194827828472378841)
            ·
              refine ⟨5931350396120871354284131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7908467194827828472378841 5931350396120871354284131)
              ·
                refine ⟨8897025594181307031426197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931350396120871354284131 8897025594181307031426197)
                ·
                  refine ⟨417048074727248767098103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8897025594181307031426197 417048074727248767098103)
                  ·
                    rfl

theorem cell22_3654892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_3654892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654892 prefixEnd_3654892 := by exact prefixLift 3654892
  have htrace : WordTrace (prefixWord ++ tailWord_3654892) baseStart_3654892 baseEnd_3654892 := by
    simpa [prefixWord, tailWord_3654892, baseEnd_3654892] using wordTrace_append hprefix tailTrace_3654892
  have hstable : (prefixWord ++ tailWord_3654892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654892).length < 2 ^ (prefixWord ++ tailWord_3654892).sum := by decide
  have hdescent : baseEnd_3654892 < baseStart_3654892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654905 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_3654905 : Nat := 118140960795 + 3654905 * 2 ^ 59
def prefixEnd_3654905 : Nat := 4983230072969 + 3 ^ 40 * 3654905 * 2
def baseEnd_3654905 : Nat := 1251148674347418600719269

theorem tailTrace_3654905 : CollatzResearch.WordTrace tailWord_3654905 prefixEnd_3654905 1251148674347418600719269 := by
  unfold tailWord_3654905
  simp only [CollatzResearch.WordTrace]
  refine ⟨133305336823910867923366169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88870224549273911948910779 133305336823910867923366169)
  ·
    refine ⟨99979002617933150942524627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133305336823910867923366169 99979002617933150942524627)
    ·
      refine ⟨149968503926899726413786941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99979002617933150942524627 149968503926899726413786941)
      ·
        refine ⟨56238188972587397405170103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149968503926899726413786941 56238188972587397405170103)
        ·
          refine ⟨84357283458881096107755155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56238188972587397405170103 84357283458881096107755155)
          ·
            refine ⟨126535925188321644161632733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84357283458881096107755155 126535925188321644161632733)
            ·
              refine ⟨47450971945620616560612275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126535925188321644161632733 47450971945620616560612275)
              ·
                refine ⟨71176457918430924840918413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47450971945620616560612275 71176457918430924840918413)
                ·
                  refine ⟨26691171719411596815344405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71176457918430924840918413 26691171719411596815344405)
                  ·
                    refine ⟨1251148674347418600719269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26691171719411596815344405 1251148674347418600719269)
                    ·
                      rfl

theorem cell22_3654905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_3654905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654905 prefixEnd_3654905 := by exact prefixLift 3654905
  have htrace : WordTrace (prefixWord ++ tailWord_3654905) baseStart_3654905 baseEnd_3654905 := by
    simpa [prefixWord, tailWord_3654905, baseEnd_3654905] using wordTrace_append hprefix tailTrace_3654905
  have hstable : (prefixWord ++ tailWord_3654905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654905).length < 2 ^ (prefixWord ++ tailWord_3654905).sum := by decide
  have hdescent : baseEnd_3654905 < baseStart_3654905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654922 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3654922 : Nat := 118140960795 + 3654922 * 2 ^ 59
def prefixEnd_3654922 : Nat := 4983230072969 + 3 ^ 40 * 3654922 * 2
def baseEnd_3654922 : Nat := 1251154493794836223044217

theorem tailTrace_3654922 : CollatzResearch.WordTrace tailWord_3654922 prefixEnd_3654922 1251154493794836223044217 := by
  unfold tailWord_3654922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33326489216212319956683755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88870637909899519884490013 33326489216212319956683755)
  ·
    refine ⟨49989733824318479935025633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33326489216212319956683755 49989733824318479935025633)
    ·
      refine ⟨37492300368238859951269225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49989733824318479935025633 37492300368238859951269225)
      ·
        refine ⟨28119225276179144963451919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37492300368238859951269225 28119225276179144963451919)
        ·
          refine ⟨42178837914268717445177879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28119225276179144963451919 42178837914268717445177879)
          ·
            refine ⟨63268256871403076167766819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42178837914268717445177879 63268256871403076167766819)
            ·
              refine ⟨94902385307104614251650229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63268256871403076167766819 94902385307104614251650229)
              ·
                refine ⟨8897098622541057586092209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94902385307104614251650229 8897098622541057586092209)
                ·
                  refine ⟨6672823966905793189569157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8897098622541057586092209 6672823966905793189569157)
                  ·
                    refine ⟨1251154493794836223044217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6672823966905793189569157 1251154493794836223044217)
                    ·
                      rfl

theorem cell22_3654922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3654922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654922 prefixEnd_3654922 := by exact prefixLift 3654922
  have htrace : WordTrace (prefixWord ++ tailWord_3654922) baseStart_3654922 baseEnd_3654922 := by
    simpa [prefixWord, tailWord_3654922, baseEnd_3654922] using wordTrace_append hprefix tailTrace_3654922
  have hstable : (prefixWord ++ tailWord_3654922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654922).length < 2 ^ (prefixWord ++ tailWord_3654922).sum := by decide
  have hdescent : baseEnd_3654922 < baseStart_3654922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654926 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_3654926 : Nat := 118140960795 + 3654926 * 2 ^ 59
def prefixEnd_3654926 : Nat := 4983230072969 + 3 ^ 40 * 3654926 * 2
def baseEnd_3654926 : Nat := 417051954358860515314735

theorem tailTrace_3654926 : CollatzResearch.WordTrace tailWord_3654926 prefixEnd_3654926 417051954358860515314735 := by
  unfold tailWord_3654926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663262844604348563735079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88870735171223192339920421 16663262844604348563735079)
  ·
    refine ⟨24994894266906522845602619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16663262844604348563735079 24994894266906522845602619)
    ·
      refine ⟨37492341400359784268403929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24994894266906522845602619 37492341400359784268403929)
      ·
        refine ⟨28119256050269838201302947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37492341400359784268403929 28119256050269838201302947)
        ·
          refine ⟨42178884075404757301954421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28119256050269838201302947 42178884075404757301954421)
          ·
            refine ⟨3954270382069195997058227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42178884075404757301954421 3954270382069195997058227)
            ·
              refine ⟨5931405573103793995587341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954270382069195997058227 5931405573103793995587341)
              ·
                refine ⟨2224277089913922748345253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5931405573103793995587341 2224277089913922748345253)
                ·
                  refine ⟨417051954358860515314735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2224277089913922748345253 417051954358860515314735)
                  ·
                    rfl

theorem cell22_3654926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_3654926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654926 prefixEnd_3654926 := by exact prefixLift 3654926
  have htrace : WordTrace (prefixWord ++ tailWord_3654926) baseStart_3654926 baseEnd_3654926 := by
    simpa [prefixWord, tailWord_3654926, baseEnd_3654926] using wordTrace_append hprefix tailTrace_3654926
  have hstable : (prefixWord ++ tailWord_3654926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654926).length < 2 ^ (prefixWord ++ tailWord_3654926).sum := by decide
  have hdescent : baseEnd_3654926 < baseStart_3654926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654954 : List Nat := [3, 1, 4, 2, 1, 2, 2, 7]
def baseStart_3654954 : Nat := 118140960795 + 3654954 * 2 ^ 59
def prefixEnd_3654954 : Nat := 4983230072969 + 3 ^ 40 * 3654954 * 2
def baseEnd_3654954 : Nat := 139018383116533200693791

theorem tailTrace_3654954 : CollatzResearch.WordTrace tailWord_3654954 prefixEnd_3654954 139018383116533200693791 := by
  unfold tailWord_3654954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33326781000183337322974979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88871416000488899527933277 33326781000183337322974979)
  ·
    refine ⟨49990171500275005984462469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33326781000183337322974979 49990171500275005984462469)
    ·
      refine ⟨9373157156301563622086713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49990171500275005984462469 9373157156301563622086713)
      ·
        refine ⟨7029867867226172716565035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9373157156301563622086713 7029867867226172716565035)
        ·
          refine ⟨10544801800839259074847553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029867867226172716565035 10544801800839259074847553)
          ·
            refine ⟨7908601350629444306135665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544801800839259074847553 7908601350629444306135665)
            ·
              refine ⟨5931451012972083229601749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7908601350629444306135665 5931451012972083229601749)
              ·
                refine ⟨139018383116533200693791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5931451012972083229601749 139018383116533200693791)
                ·
                  rfl

theorem cell22_3654954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_3654954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654954 prefixEnd_3654954 := by exact prefixLift 3654954
  have htrace : WordTrace (prefixWord ++ tailWord_3654954) baseStart_3654954 baseEnd_3654954 := by
    simpa [prefixWord, tailWord_3654954, baseEnd_3654954] using wordTrace_append hprefix tailTrace_3654954
  have hstable : (prefixWord ++ tailWord_3654954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654954).length < 2 ^ (prefixWord ++ tailWord_3654954).sum := by decide
  have hdescent : baseEnd_3654954 < baseStart_3654954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654999 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 5]
def baseStart_3654999 : Nat := 118140960795 + 3654999 * 2 ^ 59
def prefixEnd_3654999 : Nat := 4983230072969 + 3 ^ 40 * 3654999 * 2
def baseEnd_3654999 : Nat := 417060284156144562956327

theorem tailTrace_3654999 : CollatzResearch.WordTrace tailWord_3654999 prefixEnd_3654999 417060284156144562956327 := by
  unfold tailWord_3654999
  simp only [CollatzResearch.WordTrace]
  refine ⟨133308765285570321977288051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88872510190380214651525367 133308765285570321977288051)
  ·
    refine ⟨199963147928355482965932077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133308765285570321977288051 199963147928355482965932077)
    ·
      refine ⟨74986180473133306112224529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199963147928355482965932077 74986180473133306112224529)
      ·
        refine ⟨56239635354849979584168397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74986180473133306112224529 56239635354849979584168397)
        ·
          refine ⟨21089863258068742344063149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56239635354849979584168397 21089863258068742344063149)
          ·
            refine ⟨7908698721775778379023681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21089863258068742344063149 7908698721775778379023681)
            ·
              refine ⟨5931524041331833784267761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7908698721775778379023681 5931524041331833784267761)
              ·
                refine ⟨4448643030998875338200821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931524041331833784267761 4448643030998875338200821)
                ·
                  refine ⟨417060284156144562956327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4448643030998875338200821 417060284156144562956327)
                  ·
                    rfl

theorem cell22_3654999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 5].length) (baseStart_3654999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3654999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3654999 prefixEnd_3654999 := by exact prefixLift 3654999
  have htrace : WordTrace (prefixWord ++ tailWord_3654999) baseStart_3654999 baseEnd_3654999 := by
    simpa [prefixWord, tailWord_3654999, baseEnd_3654999] using wordTrace_append hprefix tailTrace_3654999
  have hstable : (prefixWord ++ tailWord_3654999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654999).length < 2 ^ (prefixWord ++ tailWord_3654999).sum := by decide
  have hdescent : baseEnd_3654999 < baseStart_3654999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655005 : List Nat := [1, 4, 5, 1, 2, 1, 1, 7]
def baseStart_3655005 : Nat := 118140960795 + 3655005 * 2 ^ 59
def prefixEnd_3655005 : Nat := 4983230072969 + 3 ^ 40 * 3655005 * 2
def baseEnd_3655005 : Nat := 139020322932339074802107

theorem tailTrace_3655005 : CollatzResearch.WordTrace tailWord_3655005 prefixEnd_3655005 139020322932339074802107 := by
  unfold tailWord_3655005
  simp only [CollatzResearch.WordTrace]
  refine ⟨133308984123548585002006469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88872656082365723334670979 133308984123548585002006469)
  ·
    refine ⟨24995434523165359687876213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133308984123548585002006469 24995434523165359687876213)
    ·
      refine ⟨2343321986546752470738395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24995434523165359687876213 2343321986546752470738395)
      ·
        refine ⟨3514982979820128706107593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343321986546752470738395 3514982979820128706107593)
        ·
          refine ⟨2636237234865096529580695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514982979820128706107593 2636237234865096529580695)
          ·
            refine ⟨3954355852297644794371043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636237234865096529580695 3954355852297644794371043)
            ·
              refine ⟨5931533778446467191556565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954355852297644794371043 5931533778446467191556565)
              ·
                refine ⟨139020322932339074802107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5931533778446467191556565 139020322932339074802107)
                ·
                  rfl

theorem cell22_3655005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 7].length) (baseStart_3655005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655005 prefixEnd_3655005 := by exact prefixLift 3655005
  have htrace : WordTrace (prefixWord ++ tailWord_3655005) baseStart_3655005 baseEnd_3655005 := by
    simpa [prefixWord, tailWord_3655005, baseEnd_3655005] using wordTrace_append hprefix tailTrace_3655005
  have hstable : (prefixWord ++ tailWord_3655005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655005).length < 2 ^ (prefixWord ++ tailWord_3655005).sum := by decide
  have hdescent : baseEnd_3655005 < baseStart_3655005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655072 : List Nat := [2, 1, 1, 4, 1, 2, 2, 9]
def baseStart_3655072 : Nat := 118140960795 + 3655072 * 2 ^ 59
def prefixEnd_3655072 : Nat := 4983230072969 + 3 ^ 40 * 3655072 * 2
def baseEnd_3655072 : Nat := 139022871317809536865973

theorem tailTrace_3655072 : CollatzResearch.WordTrace tailWord_3655072 prefixEnd_3655072 139022871317809536865973 := by
  unfold tailWord_3655072
  simp only [CollatzResearch.WordTrace]
  refine ⟨66655713907152927722347735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88874285209537236963130313 66655713907152927722347735)
  ·
    refine ⟨99983570860729391583521603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66655713907152927722347735 99983570860729391583521603)
    ·
      refine ⟨149975356291094087375282405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99983570860729391583521603 149975356291094087375282405)
      ·
        refine ⟨28120379304580141382865451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149975356291094087375282405 28120379304580141382865451)
        ·
          refine ⟨42180568956870212074298177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28120379304580141382865451 42180568956870212074298177)
          ·
            refine ⟨31635426717652659055723633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42180568956870212074298177 31635426717652659055723633)
            ·
              refine ⟨23726570038239494291792725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31635426717652659055723633 23726570038239494291792725)
              ·
                refine ⟨139022871317809536865973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23726570038239494291792725 139022871317809536865973)
                ·
                  rfl

theorem cell22_3655072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_3655072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655072 prefixEnd_3655072 := by exact prefixLift 3655072
  have htrace : WordTrace (prefixWord ++ tailWord_3655072) baseStart_3655072 baseEnd_3655072 := by
    simpa [prefixWord, tailWord_3655072, baseEnd_3655072] using wordTrace_append hprefix tailTrace_3655072
  have hstable : (prefixWord ++ tailWord_3655072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655072).length < 2 ^ (prefixWord ++ tailWord_3655072).sum := by decide
  have hdescent : baseEnd_3655072 < baseStart_3655072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655074 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3655074 : Nat := 118140960795 + 3655074 * 2 ^ 59
def prefixEnd_3655074 : Nat := 4983230072969 + 3 ^ 40 * 3655074 * 2
def baseEnd_3655074 : Nat := 1251206526501158493243751

theorem tailTrace_3655074 : CollatzResearch.WordTrace tailWord_3655074 prefixEnd_3655074 1251206526501158493243751 := by
  unfold tailWord_3655074
  simp only [CollatzResearch.WordTrace]
  refine ⟨33327875190074652446567069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88874333840199073190845517 33327875190074652446567069)
  ·
    refine ⟨12497953196277994667462651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33327875190074652446567069 12497953196277994667462651)
    ·
      refine ⟨18746929794416992001193977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12497953196277994667462651 18746929794416992001193977)
      ·
        refine ⟨14060197345812744000895483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18746929794416992001193977 14060197345812744000895483)
        ·
          refine ⟨21090296018719116001343225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14060197345812744000895483 21090296018719116001343225)
          ·
            refine ⟨15817722014039337001007419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21090296018719116001343225 15817722014039337001007419)
            ·
              refine ⟨23726583021059005501511129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15817722014039337001007419 23726583021059005501511129)
              ·
                refine ⟨17794937265794254126133347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23726583021059005501511129 17794937265794254126133347)
                ·
                  refine ⟨26692405898691381189200021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17794937265794254126133347 26692405898691381189200021)
                  ·
                    refine ⟨1251206526501158493243751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26692405898691381189200021 1251206526501158493243751)
                    ·
                      rfl

theorem cell22_3655074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3655074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655074 prefixEnd_3655074 := by exact prefixLift 3655074
  have htrace : WordTrace (prefixWord ++ tailWord_3655074) baseStart_3655074 baseEnd_3655074 := by
    simpa [prefixWord, tailWord_3655074, baseEnd_3655074] using wordTrace_append hprefix tailTrace_3655074
  have hstable : (prefixWord ++ tailWord_3655074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655074).length < 2 ^ (prefixWord ++ tailWord_3655074).sum := by decide
  have hdescent : baseEnd_3655074 < baseStart_3655074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655104 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_3655104 : Nat := 118140960795 + 3655104 * 2 ^ 59
def prefixEnd_3655104 : Nat := 4983230072969 + 3 ^ 40 * 3655104 * 2
def baseEnd_3655104 : Nat := 1251216796114248414993659

theorem tailTrace_3655104 : CollatzResearch.WordTrace tailWord_3655104 prefixEnd_3655104 1251216796114248414993659 := by
  unfold tailWord_3655104
  simp only [CollatzResearch.WordTrace]
  refine ⟨66656297475094962454930183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88875063300126616606573577 66656297475094962454930183)
  ·
    refine ⟨99984446212642443682395275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66656297475094962454930183 99984446212642443682395275)
    ·
      refine ⟨149976669318963665523592913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99984446212642443682395275 149976669318963665523592913)
      ·
        refine ⟨112482501989222749142694685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149976669318963665523592913 112482501989222749142694685)
        ·
          refine ⟨42180938245958530928510507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112482501989222749142694685 42180938245958530928510507)
          ·
            refine ⟨63271407368937796392765761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42180938245958530928510507 63271407368937796392765761)
            ·
              refine ⟨47453555526703347294574321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63271407368937796392765761 47453555526703347294574321)
              ·
                refine ⟨35590166645027510470930741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47453555526703347294574321 35590166645027510470930741)
                ·
                  refine ⟨3336578122971329106649757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35590166645027510470930741 3336578122971329106649757)
                  ·
                    refine ⟨1251216796114248414993659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336578122971329106649757 1251216796114248414993659)
                    ·
                      rfl

theorem cell22_3655104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_3655104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655104 prefixEnd_3655104 := by exact prefixLift 3655104
  have htrace : WordTrace (prefixWord ++ tailWord_3655104) baseStart_3655104 baseEnd_3655104 := by
    simpa [prefixWord, tailWord_3655104, baseEnd_3655104] using wordTrace_append hprefix tailTrace_3655104
  have hstable : (prefixWord ++ tailWord_3655104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655104).length < 2 ^ (prefixWord ++ tailWord_3655104).sum := by decide
  have hdescent : baseEnd_3655104 < baseStart_3655104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655224 : List Nat := [2, 1, 2, 1, 4, 3, 9]
def baseStart_3655224 : Nat := 118140960795 + 3655224 * 2 ^ 59
def prefixEnd_3655224 : Nat := 4983230072969 + 3 ^ 40 * 3655224 * 2
def baseEnd_3655224 : Nat := 46342884243207707481233

theorem tailTrace_3655224 : CollatzResearch.WordTrace tailWord_3655224 prefixEnd_3655224 46342884243207707481233 := by
  unfold tailWord_3655224
  simp only [CollatzResearch.WordTrace]
  refine ⟨66658485854877592702114363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88877981139836790269485817 66658485854877592702114363)
  ·
    refine ⟨99987728782316389053171545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66658485854877592702114363 99987728782316389053171545)
    ·
      refine ⟨74990796586737291789878659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99987728782316389053171545 74990796586737291789878659)
      ·
        refine ⟨112486194880105937684817989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74990796586737291789878659 112486194880105937684817989)
        ·
          refine ⟨21091161540019863315903373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112486194880105937684817989 21091161540019863315903373)
          ·
            refine ⟨7909185577507448743463765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21091161540019863315903373 7909185577507448743463765)
            ·
              refine ⟨46342884243207707481233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7909185577507448743463765 46342884243207707481233)
              ·
                rfl

theorem cell22_3655224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 9].length) (baseStart_3655224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655224 prefixEnd_3655224 := by exact prefixLift 3655224
  have htrace : WordTrace (prefixWord ++ tailWord_3655224) baseStart_3655224 baseEnd_3655224 := by
    simpa [prefixWord, tailWord_3655224, baseEnd_3655224] using wordTrace_append hprefix tailTrace_3655224
  have hstable : (prefixWord ++ tailWord_3655224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655224).length < 2 ^ (prefixWord ++ tailWord_3655224).sum := by decide
  have hdescent : baseEnd_3655224 < baseStart_3655224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655228 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_3655228 : Nat := 118140960795 + 3655228 * 2 ^ 59
def prefixEnd_3655228 : Nat := 4983230072969 + 3 ^ 40 * 3655228 * 2
def baseEnd_3655228 : Nat := 1251259243848353424893279

theorem tailTrace_3655228 : CollatzResearch.WordTrace tailWord_3655228 prefixEnd_3655228 1251259243848353424893279 := by
  unfold tailWord_3655228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66658558800870347043687169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88878078401160462724916225 66658558800870347043687169)
  ·
    refine ⟨49993919100652760282765377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66658558800870347043687169 49993919100652760282765377)
    ·
      refine ⟨37495439325489570212074033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49993919100652760282765377 37495439325489570212074033)
      ·
        refine ⟨28121579494117177659055525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37495439325489570212074033 28121579494117177659055525)
        ·
          refine ⟨5272796155146970811072911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28121579494117177659055525 5272796155146970811072911)
          ·
            refine ⟨7909194232720456216609367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272796155146970811072911 7909194232720456216609367)
            ·
              refine ⟨11863791349080684324914051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909194232720456216609367 11863791349080684324914051)
              ·
                refine ⟨17795687023621026487371077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11863791349080684324914051 17795687023621026487371077)
                ·
                  refine ⟨3336691316928942466382077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17795687023621026487371077 3336691316928942466382077)
                  ·
                    refine ⟨1251259243848353424893279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336691316928942466382077 1251259243848353424893279)
                    ·
                      rfl

theorem cell22_3655228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_3655228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655228 prefixEnd_3655228 := by exact prefixLift 3655228
  have htrace : WordTrace (prefixWord ++ tailWord_3655228) baseStart_3655228 baseEnd_3655228 := by
    simpa [prefixWord, tailWord_3655228, baseEnd_3655228] using wordTrace_append hprefix tailTrace_3655228
  have hstable : (prefixWord ++ tailWord_3655228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655228).length < 2 ^ (prefixWord ++ tailWord_3655228).sum := by decide
  have hdescent : baseEnd_3655228 < baseStart_3655228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655245 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3655245 : Nat := 118140960795 + 3655245 * 2 ^ 59
def prefixEnd_3655245 : Nat := 4983230072969 + 3 ^ 40 * 3655245 * 2
def baseEnd_3655245 : Nat := 1251265063295771047218227

theorem tailTrace_3655245 : CollatzResearch.WordTrace tailWord_3655245 prefixEnd_3655245 1251265063295771047218227 := by
  unfold tailWord_3655245
  simp only [CollatzResearch.WordTrace]
  refine ⟨133317737642679105990743189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88878491761786070660495459 133317737642679105990743189)
  ·
    refine ⟨6249268952000583093316087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133317737642679105990743189 6249268952000583093316087)
    ·
      refine ⟨9373903428000874639974131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6249268952000583093316087 9373903428000874639974131)
      ·
        refine ⟨14060855142001311959961197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9373903428000874639974131 14060855142001311959961197)
        ·
          refine ⟨5272820678250491984985449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14060855142001311959961197 5272820678250491984985449)
          ·
            refine ⟨3954615508687868988739087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5272820678250491984985449 3954615508687868988739087)
            ·
              refine ⟨5931923263031803483108631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954615508687868988739087 5931923263031803483108631)
              ·
                refine ⟨8897884894547705224662947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931923263031803483108631 8897884894547705224662947)
                ·
                  refine ⟨13346827341821557836994421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8897884894547705224662947 13346827341821557836994421)
                  ·
                    refine ⟨1251265063295771047218227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13346827341821557836994421 1251265063295771047218227)
                    ·
                      rfl

theorem cell22_3655245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3655245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655245 prefixEnd_3655245 := by exact prefixLift 3655245
  have htrace : WordTrace (prefixWord ++ tailWord_3655245) baseStart_3655245 baseEnd_3655245 := by
    simpa [prefixWord, tailWord_3655245, baseEnd_3655245] using wordTrace_append hprefix tailTrace_3655245
  have hstable : (prefixWord ++ tailWord_3655245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655245).length < 2 ^ (prefixWord ++ tailWord_3655245).sum := by decide
  have hdescent : baseEnd_3655245 < baseStart_3655245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655299 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_3655299 : Nat := 118140960795 + 3655299 * 2 ^ 59
def prefixEnd_3655299 : Nat := 4983230072969 + 3 ^ 40 * 3655299 * 2
def baseEnd_3655299 : Nat := 1251283548599332906368061

theorem tailTrace_3655299 : CollatzResearch.WordTrace tailWord_3655299 prefixEnd_3655299 1251283548599332906368061 := by
  unfold tailWord_3655299
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319707184483473213208951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88879804789655648808805967 133319707184483473213208951)
  ·
    refine ⟨199979560776725209819813427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133319707184483473213208951 199979560776725209819813427)
    ·
      refine ⟨299969341165087814729720141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199979560776725209819813427 299969341165087814729720141)
      ·
        refine ⟨112488502936907930523645053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299969341165087814729720141 112488502936907930523645053)
        ·
          refine ⟨42183188601340473946366895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112488502936907930523645053 42183188601340473946366895)
          ·
            refine ⟨63274782902010710919550343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42183188601340473946366895 63274782902010710919550343)
            ·
              refine ⟨94912174353016066379325515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63274782902010710919550343 94912174353016066379325515)
              ·
                refine ⟨142368261529524099568988273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94912174353016066379325515 142368261529524099568988273)
                ·
                  refine ⟨106776196147143074676741205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142368261529524099568988273 106776196147143074676741205)
                  ·
                    refine ⟨1251283548599332906368061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106776196147143074676741205 1251283548599332906368061)
                    ·
                      rfl

theorem cell22_3655299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_3655299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655299 prefixEnd_3655299 := by exact prefixLift 3655299
  have htrace : WordTrace (prefixWord ++ tailWord_3655299) baseStart_3655299 baseEnd_3655299 := by
    simpa [prefixWord, tailWord_3655299, baseEnd_3655299] using wordTrace_append hprefix tailTrace_3655299
  have hstable : (prefixWord ++ tailWord_3655299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655299).length < 2 ^ (prefixWord ++ tailWord_3655299).sum := by decide
  have hdescent : baseEnd_3655299 < baseStart_3655299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655303 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 5]
def baseStart_3655303 : Nat := 118140960795 + 3655303 * 2 ^ 59
def prefixEnd_3655303 : Nat := 4983230072969 + 3 ^ 40 * 3655303 * 2
def baseEnd_3655303 : Nat := 417094972627026076422683

theorem tailTrace_3655303 : CollatzResearch.WordTrace tailWord_3655303 prefixEnd_3655303 417094972627026076422683 := by
  unfold tailWord_3655303
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319853076468981896354563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88879902050979321264236375 133319853076468981896354563)
  ·
    refine ⟨199979779614703472844531845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133319853076468981896354563 199979779614703472844531845)
    ·
      refine ⟨37496208677756901158349721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199979779614703472844531845 37496208677756901158349721)
      ·
        refine ⟨28122156508317675868762291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37496208677756901158349721 28122156508317675868762291)
        ·
          refine ⟨42183234762476513803143437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28122156508317675868762291 42183234762476513803143437)
          ·
            refine ⟨15818713035928692676178789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42183234762476513803143437 15818713035928692676178789)
            ·
              refine ⟨2966008694236629876783523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15818713035928692676178789 2966008694236629876783523)
              ·
                refine ⟨4449013041354944815175285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966008694236629876783523 4449013041354944815175285)
                ·
                  refine ⟨417094972627026076422683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449013041354944815175285 417094972627026076422683)
                  ·
                    rfl

theorem cell22_3655303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 5].length) (baseStart_3655303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655303 prefixEnd_3655303 := by exact prefixLift 3655303
  have htrace : WordTrace (prefixWord ++ tailWord_3655303) baseStart_3655303 baseEnd_3655303 := by
    simpa [prefixWord, tailWord_3655303, baseEnd_3655303] using wordTrace_append hprefix tailTrace_3655303
  have hstable : (prefixWord ++ tailWord_3655303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655303).length < 2 ^ (prefixWord ++ tailWord_3655303).sum := by decide
  have hdescent : baseEnd_3655303 < baseStart_3655303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655350 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3655350 : Nat := 118140960795 + 3655350 * 2 ^ 59
def prefixEnd_3655350 : Nat := 4983230072969 + 3 ^ 40 * 3655350 * 2
def baseEnd_3655350 : Nat := 1251301006941585773342905

theorem tailTrace_3655350 : CollatzResearch.WordTrace tailWord_3655350 prefixEnd_3655350 1251301006941585773342905 := by
  unfold tailWord_3655350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332597956706169307707219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88881044871532472615543669 8332597956706169307707219)
  ·
    refine ⟨12498896935059253961560829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8332597956706169307707219 12498896935059253961560829)
    ·
      refine ⟨4687086350647220235585311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12498896935059253961560829 4687086350647220235585311)
      ·
        refine ⟨7030629525970830353377967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687086350647220235585311 7030629525970830353377967)
        ·
          refine ⟨10545944288956245530066951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030629525970830353377967 10545944288956245530066951)
          ·
            refine ⟨15818916433434368295100427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10545944288956245530066951 15818916433434368295100427)
            ·
              refine ⟨23728374650151552442650641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15818916433434368295100427 23728374650151552442650641)
              ·
                refine ⟨17796280987613664331987981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23728374650151552442650641 17796280987613664331987981)
                ·
                  refine ⟨6673605370355124124495493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17796280987613664331987981 6673605370355124124495493)
                  ·
                    refine ⟨1251301006941585773342905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673605370355124124495493 1251301006941585773342905)
                    ·
                      rfl

theorem cell22_3655350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3655350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655350 prefixEnd_3655350 := by exact prefixLift 3655350
  have htrace : WordTrace (prefixWord ++ tailWord_3655350) baseStart_3655350 baseEnd_3655350 := by
    simpa [prefixWord, tailWord_3655350, baseEnd_3655350] using wordTrace_append hprefix tailTrace_3655350
  have hstable : (prefixWord ++ tailWord_3655350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655350).length < 2 ^ (prefixWord ++ tailWord_3655350).sum := by decide
  have hdescent : baseEnd_3655350 < baseStart_3655350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655378 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3655378 : Nat := 118140960795 + 3655378 * 2 ^ 59
def prefixEnd_3655378 : Nat := 4983230072969 + 3 ^ 40 * 3655378 * 2
def baseEnd_3655378 : Nat := 1251310591913803033642819

theorem tailTrace_3655378 : CollatzResearch.WordTrace tailWord_3655378 prefixEnd_3655378 1251310591913803033642819 := by
  unfold tailWord_3655378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330647137799317426333697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88881725700798179803556525 33330647137799317426333697)
  ·
    refine ⟨24997985353349488069750273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33330647137799317426333697 24997985353349488069750273)
    ·
      refine ⟨18748489015012116052312705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24997985353349488069750273 18748489015012116052312705)
      ·
        refine ⟨14061366761259087039234529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18748489015012116052312705 14061366761259087039234529)
        ·
          refine ⟨10546025070944315279425897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14061366761259087039234529 10546025070944315279425897)
          ·
            refine ⟨7909518803208236459569423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10546025070944315279425897 7909518803208236459569423)
            ·
              refine ⟨11864278204812354689354135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909518803208236459569423 11864278204812354689354135)
              ·
                refine ⟨17796417307218532034031203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864278204812354689354135 17796417307218532034031203)
                ·
                  refine ⟨26694625960827798051046805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17796417307218532034031203 26694625960827798051046805)
                  ·
                    refine ⟨1251310591913803033642819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26694625960827798051046805 1251310591913803033642819)
                    ·
                      rfl

theorem cell22_3655378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3655378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655378 prefixEnd_3655378 := by exact prefixLift 3655378
  have htrace : WordTrace (prefixWord ++ tailWord_3655378) baseStart_3655378 baseEnd_3655378 := by
    simpa [prefixWord, tailWord_3655378, baseEnd_3655378] using wordTrace_append hprefix tailTrace_3655378
  have hstable : (prefixWord ++ tailWord_3655378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655378).length < 2 ^ (prefixWord ++ tailWord_3655378).sum := by decide
  have hdescent : baseEnd_3655378 < baseStart_3655378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655436 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_3655436 : Nat := 118140960795 + 3655436 * 2 ^ 59
def prefixEnd_3655436 : Nat := 4983230072969 + 3 ^ 40 * 3655436 * 2
def baseEnd_3655436 : Nat := 1251330446499110215692641

theorem tailTrace_3655436 : CollatzResearch.WordTrace tailWord_3655436 prefixEnd_3655436 1251330446499110215692641 := by
  unfold tailWord_3655436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662351992493572805473081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88883135989991430407297441 66662351992493572805473081)
  ·
    refine ⟨49996763994370179604104811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66662351992493572805473081 49996763994370179604104811)
    ·
      refine ⟨74995145991555269406157217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49996763994370179604104811 74995145991555269406157217)
      ·
        refine ⟨56246359493666452054617913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74995145991555269406157217 56246359493666452054617913)
        ·
          refine ⟨42184769620249839040963435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56246359493666452054617913 42184769620249839040963435)
          ·
            refine ⟨63277154430374758561445153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42184769620249839040963435 63277154430374758561445153)
            ·
              refine ⟨47457865822781068921083865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63277154430374758561445153 47457865822781068921083865)
              ·
                refine ⟨35593399367085801690812899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47457865822781068921083865 35593399367085801690812899)
                ·
                  refine ⟨53390099050628702536219349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35593399367085801690812899 53390099050628702536219349)
                  ·
                    refine ⟨1251330446499110215692641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53390099050628702536219349 1251330446499110215692641)
                    ·
                      rfl

theorem cell22_3655436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_3655436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655436 prefixEnd_3655436 := by exact prefixLift 3655436
  have htrace : WordTrace (prefixWord ++ tailWord_3655436) baseStart_3655436 baseEnd_3655436 := by
    simpa [prefixWord, tailWord_3655436, baseEnd_3655436] using wordTrace_append hprefix tailTrace_3655436
  have hstable : (prefixWord ++ tailWord_3655436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655436).length < 2 ^ (prefixWord ++ tailWord_3655436).sum := by decide
  have hdescent : baseEnd_3655436 < baseStart_3655436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655444 : List Nat := [2, 4, 4, 1, 2, 1, 8]
def baseStart_3655444 : Nat := 118140960795 + 3655444 * 2 ^ 59
def prefixEnd_3655444 : Nat := 4983230072969 + 3 ^ 40 * 3655444 * 2
def baseEnd_3655444 : Nat := 46345673520837068944171

theorem tailTrace_3655444 : CollatzResearch.WordTrace tailWord_3655444 prefixEnd_3655444 46345673520837068944171 := by
  unfold tailWord_3655444
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662497884479081488618693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88883330512638775318158257 66662497884479081488618693)
  ·
    refine ⟨12499218353339827779116005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66662497884479081488618693 12499218353339827779116005)
    ·
      refine ⟨2343603441251217708584251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12499218353339827779116005 2343603441251217708584251)
      ·
        refine ⟨3515405161876826562876377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343603441251217708584251 3515405161876826562876377)
        ·
          refine ⟨2636553871407619922157283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515405161876826562876377 2636553871407619922157283)
          ·
            refine ⟨3954830807111429883235925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636553871407619922157283 3954830807111429883235925)
            ·
              refine ⟨46345673520837068944171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3954830807111429883235925 46345673520837068944171)
              ·
                rfl

theorem cell22_3655444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 8].length) (baseStart_3655444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655444 prefixEnd_3655444 := by exact prefixLift 3655444
  have htrace : WordTrace (prefixWord ++ tailWord_3655444) baseStart_3655444 baseEnd_3655444 := by
    simpa [prefixWord, tailWord_3655444, baseEnd_3655444] using wordTrace_append hprefix tailTrace_3655444
  have hstable : (prefixWord ++ tailWord_3655444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655444).length < 2 ^ (prefixWord ++ tailWord_3655444).sum := by decide
  have hdescent : baseEnd_3655444 < baseStart_3655444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655485 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3655485 : Nat := 118140960795 + 3655485 * 2 ^ 59
def prefixEnd_3655485 : Nat := 4983230072969 + 3 ^ 40 * 3655485 * 2
def baseEnd_3655485 : Nat := 1251347220200490421217491

theorem tailTrace_3655485 : CollatzResearch.WordTrace tailWord_3655485 prefixEnd_3655485 1251347220200490421217491 := by
  unfold tailWord_3655485
  simp only [CollatzResearch.WordTrace]
  refine ⟨133326491161809626979479909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88884327441206417986319939 133326491161809626979479909)
  ·
    refine ⟨24998717092839305058652483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133326491161809626979479909 24998717092839305058652483)
    ·
      refine ⟨37498075639258957587978725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24998717092839305058652483 37498075639258957587978725)
      ·
        refine ⟨7030889182361054547746011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37498075639258957587978725 7030889182361054547746011)
        ·
          refine ⟨10546333773541581821619017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030889182361054547746011 10546333773541581821619017)
          ·
            refine ⟨7909750330156186366214263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10546333773541581821619017 7909750330156186366214263)
            ·
              refine ⟨11864625495234279549321395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909750330156186366214263 11864625495234279549321395)
              ·
                refine ⟨17796938242851419323982093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864625495234279549321395 17796938242851419323982093)
                ·
                  refine ⟨6673851841069282246493285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17796938242851419323982093 6673851841069282246493285)
                  ·
                    refine ⟨1251347220200490421217491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673851841069282246493285 1251347220200490421217491)
                    ·
                      rfl

theorem cell22_3655485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3655485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655485 prefixEnd_3655485 := by exact prefixLift 3655485
  have htrace : WordTrace (prefixWord ++ tailWord_3655485) baseStart_3655485 baseEnd_3655485 := by
    simpa [prefixWord, tailWord_3655485, baseEnd_3655485] using wordTrace_append hprefix tailTrace_3655485
  have hstable : (prefixWord ++ tailWord_3655485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655485).length < 2 ^ (prefixWord ++ tailWord_3655485).sum := by decide
  have hdescent : baseEnd_3655485 < baseStart_3655485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655498 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3655498 : Nat := 118140960795 + 3655498 * 2 ^ 59
def prefixEnd_3655498 : Nat := 4983230072969 + 3 ^ 40 * 3655498 * 2
def baseEnd_3655498 : Nat := 1251351670366162720642451

theorem tailTrace_3655498 : CollatzResearch.WordTrace tailWord_3655498 prefixEnd_3655498 1251351670366162720642451 := by
  unfold tailWord_3655498
  simp only [CollatzResearch.WordTrace]
  refine ⟨33331741327690632549925787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88884643540508353466468765 33331741327690632549925787)
  ·
    refine ⟨49997611991535948824888681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33331741327690632549925787 49997611991535948824888681)
    ·
      refine ⟨37498208993651961618666511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49997611991535948824888681 37498208993651961618666511)
      ·
        refine ⟨56247313490477942427999767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37498208993651961618666511 56247313490477942427999767)
        ·
          refine ⟨84370970235716913641999651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56247313490477942427999767 84370970235716913641999651)
          ·
            refine ⟨126556455353575370462999477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84370970235716913641999651 126556455353575370462999477)
            ·
              refine ⟨11864667689397690980906201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126556455353575370462999477 11864667689397690980906201)
              ·
                refine ⟨8898500767048268235679651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11864667689397690980906201 8898500767048268235679651)
                ·
                  refine ⟨13347751150572402353519477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898500767048268235679651 13347751150572402353519477)
                  ·
                    refine ⟨1251351670366162720642451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13347751150572402353519477 1251351670366162720642451)
                    ·
                      rfl

theorem cell22_3655498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3655498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655498 prefixEnd_3655498 := by exact prefixLift 3655498
  have htrace : WordTrace (prefixWord ++ tailWord_3655498) baseStart_3655498 baseEnd_3655498 := by
    simpa [prefixWord, tailWord_3655498, baseEnd_3655498] using wordTrace_append hprefix tailTrace_3655498
  have hstable : (prefixWord ++ tailWord_3655498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655498).length < 2 ^ (prefixWord ++ tailWord_3655498).sum := by decide
  have hdescent : baseEnd_3655498 < baseStart_3655498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655511 : List Nat := [1, 1, 3, 2, 15]
def baseStart_3655511 : Nat := 118140960795 + 3655511 * 2 ^ 59
def prefixEnd_3655511 : Nat := 4983230072969 + 3 ^ 40 * 3655511 * 2
def baseEnd_3655511 : Nat := 5149613664740061810977

theorem tailTrace_3655511 : CollatzResearch.WordTrace tailWord_3655511 prefixEnd_3655511 5149613664740061810977 := by
  unfold tailWord_3655511
  simp only [CollatzResearch.WordTrace]
  refine ⟨133327439459715433419926387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88884959639810288946617591 133327439459715433419926387)
  ·
    refine ⟨199991159189573150129889581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133327439459715433419926387 199991159189573150129889581)
    ·
      refine ⟨74996684696089931298708593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199991159189573150129889581 74996684696089931298708593)
      ·
        refine ⟨56247513522067448474031445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74996684696089931298708593 56247513522067448474031445)
        ·
          refine ⟨5149613664740061810977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 56247513522067448474031445 5149613664740061810977)
          ·
            rfl

theorem cell22_3655511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 15].length) (baseStart_3655511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655511 prefixEnd_3655511 := by exact prefixLift 3655511
  have htrace : WordTrace (prefixWord ++ tailWord_3655511) baseStart_3655511 baseEnd_3655511 := by
    simpa [prefixWord, tailWord_3655511, baseEnd_3655511] using wordTrace_append hprefix tailTrace_3655511
  have hstable : (prefixWord ++ tailWord_3655511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655511).length < 2 ^ (prefixWord ++ tailWord_3655511).sum := by decide
  have hdescent : baseEnd_3655511 < baseStart_3655511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655513 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_3655513 : Nat := 118140960795 + 3655513 * 2 ^ 59
def prefixEnd_3655513 : Nat := 4983230072969 + 3 ^ 40 * 3655513 * 2
def baseEnd_3655513 : Nat := 1251356805172707681517405

theorem tailTrace_3655513 : CollatzResearch.WordTrace tailWord_3655513 prefixEnd_3655513 1251356805172707681517405 := by
  unfold tailWord_3655513
  simp only [CollatzResearch.WordTrace]
  refine ⟨133327512405708187761499193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88885008270472125174332795 133327512405708187761499193)
  ·
    refine ⟨99995634304281140821124395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133327512405708187761499193 99995634304281140821124395)
    ·
      refine ⟨149993451456421711231686593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99995634304281140821124395 149993451456421711231686593)
      ·
        refine ⟨112495088592316283423764945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149993451456421711231686593 112495088592316283423764945)
        ·
          refine ⟨84371316444237212567823709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112495088592316283423764945 84371316444237212567823709)
          ·
            refine ⟨31639243666588954712933891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84371316444237212567823709 31639243666588954712933891)
            ·
              refine ⟨47458865499883432069400837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31639243666588954712933891 47458865499883432069400837)
              ·
                refine ⟨8898537281228143513012657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47458865499883432069400837 8898537281228143513012657)
                ·
                  refine ⟨6673902960921107634759493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8898537281228143513012657 6673902960921107634759493)
                  ·
                    refine ⟨1251356805172707681517405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6673902960921107634759493 1251356805172707681517405)
                    ·
                      rfl

theorem cell22_3655513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_3655513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655513 prefixEnd_3655513 := by exact prefixLift 3655513
  have htrace : WordTrace (prefixWord ++ tailWord_3655513) baseStart_3655513 baseEnd_3655513 := by
    simpa [prefixWord, tailWord_3655513, baseEnd_3655513] using wordTrace_append hprefix tailTrace_3655513
  have hstable : (prefixWord ++ tailWord_3655513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655513).length < 2 ^ (prefixWord ++ tailWord_3655513).sum := by decide
  have hdescent : baseEnd_3655513 < baseStart_3655513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655566 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_3655566 : Nat := 118140960795 + 3655566 * 2 ^ 59
def prefixEnd_3655566 : Nat := 4983230072969 + 3 ^ 40 * 3655566 * 2
def baseEnd_3655566 : Nat := 1251374948155833209942243

theorem tailTrace_3655566 : CollatzResearch.WordTrace tailWord_3655566 prefixEnd_3655566 1251374948155833209942243 := by
  unfold tailWord_3655566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16666180684314522226647319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88886296983010785208785701 16666180684314522226647319)
  ·
    refine ⟨24999271026471783339970979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16666180684314522226647319 24999271026471783339970979)
    ·
      refine ⟨37498906539707675009956469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24999271026471783339970979 37498906539707675009956469)
      ·
        refine ⟨3515522488097594532183419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37498906539707675009956469 3515522488097594532183419)
        ·
          refine ⟨5273283732146391798275129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515522488097594532183419 5273283732146391798275129)
          ·
            refine ⟨3954962799109793848706347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5273283732146391798275129 3954962799109793848706347)
            ·
              refine ⟨5932444198664690773059521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954962799109793848706347 5932444198664690773059521)
              ·
                refine ⟨4449333148998518079794641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932444198664690773059521 4449333148998518079794641)
                ·
                  refine ⟨3336999861748888559845981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449333148998518079794641 3336999861748888559845981)
                  ·
                    refine ⟨1251374948155833209942243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336999861748888559845981 1251374948155833209942243)
                    ·
                      rfl

theorem cell22_3655566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_3655566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655566 prefixEnd_3655566 := by exact prefixLift 3655566
  have htrace : WordTrace (prefixWord ++ tailWord_3655566) baseStart_3655566 baseEnd_3655566 := by
    simpa [prefixWord, tailWord_3655566, baseEnd_3655566] using wordTrace_append hprefix tailTrace_3655566
  have hstable : (prefixWord ++ tailWord_3655566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655566).length < 2 ^ (prefixWord ++ tailWord_3655566).sum := by decide
  have hdescent : baseEnd_3655566 < baseStart_3655566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655573 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 7]
def baseStart_3655573 : Nat := 118140960795 + 3655573 * 2 ^ 59
def prefixEnd_3655573 : Nat := 4983230072969 + 3 ^ 40 * 3655573 * 2
def baseEnd_3655573 : Nat := 417125781466295841672407

theorem tailTrace_3655573 : CollatzResearch.WordTrace tailWord_3655573 prefixEnd_3655573 417125781466295841672407 := by
  unfold tailWord_3655573
  simp only [CollatzResearch.WordTrace]
  refine ⟨133329700785490818008683373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88886467190327212005788915 133329700785490818008683373)
  ·
    refine ⟨49998637794559056753256265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133329700785490818008683373 49998637794559056753256265)
    ·
      refine ⟨37498978345919292564942199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49998637794559056753256265 37498978345919292564942199)
      ·
        refine ⟨56248467518878938847413299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37498978345919292564942199 56248467518878938847413299)
        ·
          refine ⟨84372701278318408271119949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56248467518878938847413299 84372701278318408271119949)
          ·
            refine ⟨31639762979369403101669981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84372701278318408271119949 31639762979369403101669981)
            ·
              refine ⟨11864911117263526163126243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31639762979369403101669981 11864911117263526163126243)
              ·
                refine ⟨17797366675895289244689365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864911117263526163126243 17797366675895289244689365)
                ·
                  refine ⟨417125781466295841672407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17797366675895289244689365 417125781466295841672407)
                  ·
                    rfl

theorem cell22_3655573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_3655573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655573 prefixEnd_3655573 := by exact prefixLift 3655573
  have htrace : WordTrace (prefixWord ++ tailWord_3655573) baseStart_3655573 baseEnd_3655573 := by
    simpa [prefixWord, tailWord_3655573, baseEnd_3655573] using wordTrace_append hprefix tailTrace_3655573
  have hstable : (prefixWord ++ tailWord_3655573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655573).length < 2 ^ (prefixWord ++ tailWord_3655573).sum := by decide
  have hdescent : baseEnd_3655573 < baseStart_3655573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655577 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 1, 3]
def baseStart_3655577 : Nat := 118140960795 + 3655577 * 2 ^ 59
def prefixEnd_3655577 : Nat := 4983230072969 + 3 ^ 40 * 3655577 * 2
def baseEnd_3655577 : Nat := 1251378713680632847917209

theorem tailTrace_3655577 : CollatzResearch.WordTrace tailWord_3655577 prefixEnd_3655577 1251378713680632847917209 := by
  unfold tailWord_3655577
  simp only [CollatzResearch.WordTrace]
  refine ⟨133329846677476326691828985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88886564451650884461219323 133329846677476326691828985)
  ·
    refine ⟨99997385008107245018871739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133329846677476326691828985 99997385008107245018871739)
    ·
      refine ⟨149996077512160867528307609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99997385008107245018871739 149996077512160867528307609)
      ·
        refine ⟨112497058134120650646230707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149996077512160867528307609 112497058134120650646230707)
        ·
          refine ⟨168745587201180975969346061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112497058134120650646230707 168745587201180975969346061)
          ·
            refine ⟨63279595200442865988504773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168745587201180975969346061 63279595200442865988504773)
            ·
              refine ⟨11864924100083037372844645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63279595200442865988504773 11864924100083037372844645)
              ·
                refine ⟨2224673268765569507408371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11864924100083037372844645 2224673268765569507408371)
                ·
                  refine ⟨3337009903148354261112557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224673268765569507408371 3337009903148354261112557)
                  ·
                    refine ⟨1251378713680632847917209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337009903148354261112557 1251378713680632847917209)
                    ·
                      rfl

theorem cell22_3655577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_3655577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655577 prefixEnd_3655577 := by exact prefixLift 3655577
  have htrace : WordTrace (prefixWord ++ tailWord_3655577) baseStart_3655577 baseEnd_3655577 := by
    simpa [prefixWord, tailWord_3655577, baseEnd_3655577] using wordTrace_append hprefix tailTrace_3655577
  have hstable : (prefixWord ++ tailWord_3655577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655577).length < 2 ^ (prefixWord ++ tailWord_3655577).sum := by decide
  have hdescent : baseEnd_3655577 < baseStart_3655577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655633 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_3655633 : Nat := 118140960795 + 3655633 * 2 ^ 59
def prefixEnd_3655633 : Nat := 4983230072969 + 3 ^ 40 * 3655633 * 2
def baseEnd_3655633 : Nat := 1251397883625067368517037

theorem tailTrace_3655633 : CollatzResearch.WordTrace tailWord_3655633 prefixEnd_3655633 1251397883625067368517037 := by
  unfold tailWord_3655633
  simp only [CollatzResearch.WordTrace]
  refine ⟨133331889165273448255867553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88887926110182298837245035 133331889165273448255867553)
  ·
    refine ⟨99998916873955086191900665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133331889165273448255867553 99998916873955086191900665)
    ·
      refine ⟨74999187655466314643925499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99998916873955086191900665 74999187655466314643925499)
      ·
        refine ⟨112498781483199471965888249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74999187655466314643925499 112498781483199471965888249)
        ·
          refine ⟨84374086112399603974416187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112498781483199471965888249 84374086112399603974416187)
          ·
            refine ⟨126561129168599405961624281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84374086112399603974416187 126561129168599405961624281)
            ·
              refine ⟨94920846876449554471218211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126561129168599405961624281 94920846876449554471218211)
              ·
                refine ⟨142381270314674331706827317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94920846876449554471218211 142381270314674331706827317)
                ·
                  refine ⟨13348244092000718597515061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142381270314674331706827317 13348244092000718597515061)
                  ·
                    refine ⟨1251397883625067368517037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13348244092000718597515061 1251397883625067368517037)
                    ·
                      rfl

theorem cell22_3655633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_3655633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655633 prefixEnd_3655633 := by exact prefixLift 3655633
  have htrace : WordTrace (prefixWord ++ tailWord_3655633) baseStart_3655633 baseEnd_3655633 := by
    simpa [prefixWord, tailWord_3655633, baseEnd_3655633] using wordTrace_append hprefix tailTrace_3655633
  have hstable : (prefixWord ++ tailWord_3655633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655633).length < 2 ^ (prefixWord ++ tailWord_3655633).sum := by decide
  have hdescent : baseEnd_3655633 < baseStart_3655633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655648 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_3655648 : Nat := 118140960795 + 3655648 * 2 ^ 59
def prefixEnd_3655648 : Nat := 4983230072969 + 3 ^ 40 * 3655648 * 2
def baseEnd_3655648 : Nat := 1251403018431612329391991

theorem tailTrace_3655648 : CollatzResearch.WordTrace tailWord_3655648 prefixEnd_3655648 1251403018431612329391991 := by
  unfold tailWord_3655648
  simp only [CollatzResearch.WordTrace]
  refine ⟨66666218130109552908831799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88888290840146070545109065 66666218130109552908831799)
  ·
    refine ⟨99999327195164329363247699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66666218130109552908831799 99999327195164329363247699)
    ·
      refine ⟨149998990792746494044871549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99999327195164329363247699 149998990792746494044871549)
      ·
        refine ⟨56249621547279935266826831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149998990792746494044871549 56249621547279935266826831)
        ·
          refine ⟨84374432320919902900240247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56249621547279935266826831 84374432320919902900240247)
          ·
            refine ⟨126561648481379854350360371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84374432320919902900240247 126561648481379854350360371)
            ·
              refine ⟨189842472722069781525540557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126561648481379854350360371 189842472722069781525540557)
              ·
                refine ⟨71190927270776168072077709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189842472722069781525540557 71190927270776168072077709)
                ·
                  refine ⟨26696597726541063027029141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71190927270776168072077709 26696597726541063027029141)
                  ·
                    refine ⟨1251403018431612329391991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26696597726541063027029141 1251403018431612329391991)
                    ·
                      rfl

theorem cell22_3655648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_3655648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655648 prefixEnd_3655648 := by exact prefixLift 3655648
  have htrace : WordTrace (prefixWord ++ tailWord_3655648) baseStart_3655648 baseEnd_3655648 := by
    simpa [prefixWord, tailWord_3655648, baseEnd_3655648] using wordTrace_append hprefix tailTrace_3655648
  have hstable : (prefixWord ++ tailWord_3655648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655648).length < 2 ^ (prefixWord ++ tailWord_3655648).sum := by decide
  have hdescent : baseEnd_3655648 < baseStart_3655648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655663 : List Nat := [1, 1, 2, 1, 4, 2, 1, 10]
def baseStart_3655663 : Nat := 118140960795 + 3655663 * 2 ^ 59
def prefixEnd_3655663 : Nat := 4983230072969 + 3 ^ 40 * 3655663 * 2
def baseEnd_3655663 : Nat := 139045350359795254474105

theorem tailTrace_3655663 : CollatzResearch.WordTrace tailWord_3655663 prefixEnd_3655663 139045350359795254474105 := by
  unfold tailWord_3655663
  simp only [CollatzResearch.WordTrace]
  refine ⟨133332983355164763379459643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88888655570109842252973095 133332983355164763379459643)
  ·
    refine ⟨199999475032747145069189465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133332983355164763379459643 199999475032747145069189465)
    ·
      refine ⟨149999606274560358801892099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199999475032747145069189465 149999606274560358801892099)
      ·
        refine ⟨224999409411840538202838149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149999606274560358801892099 224999409411840538202838149)
        ·
          refine ⟨42187389264720100913032153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224999409411840538202838149 42187389264720100913032153)
          ·
            refine ⟨31640541948540075684774115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42187389264720100913032153 31640541948540075684774115)
            ·
              refine ⟨47460812922810113527161173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31640541948540075684774115 47460812922810113527161173)
              ·
                refine ⟨139045350359795254474105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47460812922810113527161173 139045350359795254474105)
                ·
                  rfl

theorem cell22_3655663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 10].length) (baseStart_3655663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655663 prefixEnd_3655663 := by exact prefixLift 3655663
  have htrace : WordTrace (prefixWord ++ tailWord_3655663) baseStart_3655663 baseEnd_3655663 := by
    simpa [prefixWord, tailWord_3655663, baseEnd_3655663] using wordTrace_append hprefix tailTrace_3655663
  have hstable : (prefixWord ++ tailWord_3655663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655663).length < 2 ^ (prefixWord ++ tailWord_3655663).sum := by decide
  have hdescent : baseEnd_3655663 < baseStart_3655663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655716 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_3655716 : Nat := 118140960795 + 3655716 * 2 ^ 59
def prefixEnd_3655716 : Nat := 4983230072969 + 3 ^ 40 * 3655716 * 2
def baseEnd_3655716 : Nat := 1251426296221282818691783

theorem tailTrace_3655716 : CollatzResearch.WordTrace tailWord_3655716 prefixEnd_3655716 1251426296221282818691783 := by
  unfold tailWord_3655716
  simp only [CollatzResearch.WordTrace]
  refine ⟨66667458211986376715569501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88889944282648502287426001 66667458211986376715569501)
  ·
    refine ⟨25000296829494891268338563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66667458211986376715569501 25000296829494891268338563)
    ·
      refine ⟨37500445244242336902507845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25000296829494891268338563 37500445244242336902507845)
      ·
        refine ⟨7031333483295438169220221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37500445244242336902507845 7031333483295438169220221)
        ·
          refine ⟨2636750056235789313457583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7031333483295438169220221 2636750056235789313457583)
          ·
            refine ⟨3955125084353683970186375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636750056235789313457583 3955125084353683970186375)
            ·
              refine ⟨5932687626530525955279563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955125084353683970186375 5932687626530525955279563)
              ·
                refine ⟨8899031439795788932919345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932687626530525955279563 8899031439795788932919345)
                ·
                  refine ⟨6674273579846841699689509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8899031439795788932919345 6674273579846841699689509)
                  ·
                    refine ⟨1251426296221282818691783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674273579846841699689509 1251426296221282818691783)
                    ·
                      rfl

theorem cell22_3655716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_3655716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655716 prefixEnd_3655716 := by exact prefixLift 3655716
  have htrace : WordTrace (prefixWord ++ tailWord_3655716) baseStart_3655716 baseEnd_3655716 := by
    simpa [prefixWord, tailWord_3655716, baseEnd_3655716] using wordTrace_append hprefix tailTrace_3655716
  have hstable : (prefixWord ++ tailWord_3655716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655716).length < 2 ^ (prefixWord ++ tailWord_3655716).sum := by decide
  have hdescent : baseEnd_3655716 < baseStart_3655716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655729 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 1, 3]
def baseStart_3655729 : Nat := 118140960795 + 3655729 * 2 ^ 59
def prefixEnd_3655729 : Nat := 4983230072969 + 3 ^ 40 * 3655729 * 2
def baseEnd_3655729 : Nat := 1251430746386955118116743

theorem tailTrace_3655729 : CollatzResearch.WordTrace tailWord_3655729 prefixEnd_3655729 1251430746386955118116743 := by
  unfold tailWord_3655729
  simp only [CollatzResearch.WordTrace]
  refine ⟨133335390572925656651362241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88890260381950437767574827 133335390572925656651362241)
  ·
    refine ⟨100001542929694242488521681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133335390572925656651362241 100001542929694242488521681)
    ·
      refine ⟨75001157197270681866391261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100001542929694242488521681 75001157197270681866391261)
      ·
        refine ⟨28125433948976505699896723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75001157197270681866391261 28125433948976505699896723)
        ·
          refine ⟨42188150923464758549845085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28125433948976505699896723 42188150923464758549845085)
          ·
            refine ⟨15820556596299284456191907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42188150923464758549845085 15820556596299284456191907)
            ·
              refine ⟨23730834894448926684287861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15820556596299284456191907 23730834894448926684287861)
              ·
                refine ⟨2224765771354586876651987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23730834894448926684287861 2224765771354586876651987)
                ·
                  refine ⟨3337148657031880314977981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224765771354586876651987 3337148657031880314977981)
                  ·
                    refine ⟨1251430746386955118116743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337148657031880314977981 1251430746386955118116743)
                    ·
                      rfl

theorem cell22_3655729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_3655729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655729 prefixEnd_3655729 := by exact prefixLift 3655729
  have htrace : WordTrace (prefixWord ++ tailWord_3655729) baseStart_3655729 baseEnd_3655729 := by
    simpa [prefixWord, tailWord_3655729, baseEnd_3655729] using wordTrace_append hprefix tailTrace_3655729
  have hstable : (prefixWord ++ tailWord_3655729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655729).length < 2 ^ (prefixWord ++ tailWord_3655729).sum := by decide
  have hdescent : baseEnd_3655729 < baseStart_3655729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655740 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3655740 : Nat := 118140960795 + 3655740 * 2 ^ 59
def prefixEnd_3655740 : Nat := 4983230072969 + 3 ^ 40 * 3655740 * 2
def baseEnd_3655740 : Nat := 1251434511911754756091709

theorem tailTrace_3655740 : CollatzResearch.WordTrace tailWord_3655740 prefixEnd_3655740 1251434511911754756091709 := by
  unfold tailWord_3655740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66667895887942902765006337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88890527850590537020008449 66667895887942902765006337)
  ·
    refine ⟨50000921915957177073754753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66667895887942902765006337 50000921915957177073754753)
    ·
      refine ⟨37500691436967882805316065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50000921915957177073754753 37500691436967882805316065)
      ·
        refine ⟨28125518577725912103987049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37500691436967882805316065 28125518577725912103987049)
        ·
          refine ⟨21094138933294434077990287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28125518577725912103987049 21094138933294434077990287)
          ·
            refine ⟨31641208399941651116985431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21094138933294434077990287 31641208399941651116985431)
            ·
              refine ⟨47461812599912476675478147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31641208399941651116985431 47461812599912476675478147)
              ·
                refine ⟨71192718899868715013217221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47461812599912476675478147 71192718899868715013217221)
                ·
                  refine ⟨13348634793725384064978229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71192718899868715013217221 13348634793725384064978229)
                  ·
                    refine ⟨1251434511911754756091709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13348634793725384064978229 1251434511911754756091709)
                    ·
                      rfl

theorem cell22_3655740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3655740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655740 prefixEnd_3655740 := by exact prefixLift 3655740
  have htrace : WordTrace (prefixWord ++ tailWord_3655740) baseStart_3655740 baseEnd_3655740 := by
    simpa [prefixWord, tailWord_3655740, baseEnd_3655740] using wordTrace_append hprefix tailTrace_3655740
  have hstable : (prefixWord ++ tailWord_3655740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655740).length < 2 ^ (prefixWord ++ tailWord_3655740).sum := by decide
  have hdescent : baseEnd_3655740 < baseStart_3655740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655757 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3655757 : Nat := 118140960795 + 3655757 * 2 ^ 59
def prefixEnd_3655757 : Nat := 4983230072969 + 3 ^ 40 * 3655757 * 2
def baseEnd_3655757 : Nat := 1251440331359172378416657

theorem tailTrace_3655757 : CollatzResearch.WordTrace tailWord_3655757 prefixEnd_3655757 1251440331359172378416657 := by
  unfold tailWord_3655757
  simp only [CollatzResearch.WordTrace]
  refine ⟨133336411816824217433381525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88890941211216144955587683 133336411816824217433381525)
  ·
    refine ⟨6250144303913635192189759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133336411816824217433381525 6250144303913635192189759)
    ·
      refine ⟨9375216455870452788284639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6250144303913635192189759 9375216455870452788284639)
      ·
        refine ⟨14062824683805679182426959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9375216455870452788284639 14062824683805679182426959)
        ·
          refine ⟨21094237025708518773640439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14062824683805679182426959 21094237025708518773640439)
          ·
            refine ⟨31641355538562778160460659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21094237025708518773640439 31641355538562778160460659)
            ·
              refine ⟨47462033307844167240690989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31641355538562778160460659 47462033307844167240690989)
              ·
                refine ⟨17798262490441562715259121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47462033307844167240690989 17798262490441562715259121)
                ·
                  refine ⟨13348696867831172036444341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17798262490441562715259121 13348696867831172036444341)
                  ·
                    refine ⟨1251440331359172378416657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13348696867831172036444341 1251440331359172378416657)
                    ·
                      rfl

theorem cell22_3655757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3655757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655757 prefixEnd_3655757 := by exact prefixLift 3655757
  have htrace : WordTrace (prefixWord ++ tailWord_3655757) baseStart_3655757 baseEnd_3655757 := by
    simpa [prefixWord, tailWord_3655757, baseEnd_3655757] using wordTrace_append hprefix tailTrace_3655757
  have hstable : (prefixWord ++ tailWord_3655757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655757).length < 2 ^ (prefixWord ++ tailWord_3655757).sum := by decide
  have hdescent : baseEnd_3655757 < baseStart_3655757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655770 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_3655770 : Nat := 118140960795 + 3655770 * 2 ^ 59
def prefixEnd_3655770 : Nat := 4983230072969 + 3 ^ 40 * 3655770 * 2
def baseEnd_3655770 : Nat := 417148260508281559280539

theorem tailTrace_3655770 : CollatzResearch.WordTrace tailWord_3655770 prefixEnd_3655770 417148260508281559280539 := by
  unfold tailWord_3655770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33334221491444280163401191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88891257310518080435736509 33334221491444280163401191)
  ·
    refine ⟨50001332237166420245101787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33334221491444280163401191 50001332237166420245101787)
    ·
      refine ⟨75001998355749630367652681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50001332237166420245101787 75001998355749630367652681)
      ·
        refine ⟨56251498766812222775739511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75001998355749630367652681 56251498766812222775739511)
        ·
          refine ⟨84377248150218334163609267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56251498766812222775739511 84377248150218334163609267)
          ·
            refine ⟨126565872225327501245413901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84377248150218334163609267 126565872225327501245413901)
            ·
              refine ⟨47462202084497812967030213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126565872225327501245413901 47462202084497812967030213)
              ·
                refine ⟨8899162890843339931318165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47462202084497812967030213 8899162890843339931318165)
                ·
                  refine ⟨417148260508281559280539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8899162890843339931318165 417148260508281559280539)
                  ·
                    rfl

theorem cell22_3655770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_3655770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655770 prefixEnd_3655770 := by exact prefixLift 3655770
  have htrace : WordTrace (prefixWord ++ tailWord_3655770) baseStart_3655770 baseEnd_3655770 := by
    simpa [prefixWord, tailWord_3655770, baseEnd_3655770] using wordTrace_append hprefix tailTrace_3655770
  have hstable : (prefixWord ++ tailWord_3655770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655770).length < 2 ^ (prefixWord ++ tailWord_3655770).sum := by decide
  have hdescent : baseEnd_3655770 < baseStart_3655770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655785 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_3655785 : Nat := 118140960795 + 3655785 * 2 ^ 59
def prefixEnd_3655785 : Nat := 4983230072969 + 3 ^ 40 * 3655785 * 2
def baseEnd_3655785 : Nat := 1251449916331389638716571

theorem tailTrace_3655785 : CollatzResearch.WordTrace tailWord_3655785 prefixEnd_3655785 1251449916331389638716571 := by
  unfold tailWord_3655785
  simp only [CollatzResearch.WordTrace]
  refine ⟨133337433060722778215400809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88891622040481852143600539 133337433060722778215400809)
  ·
    refine ⟨100003074795542083661550607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133337433060722778215400809 100003074795542083661550607)
    ·
      refine ⟨150004612193313125492325911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100003074795542083661550607 150004612193313125492325911)
      ·
        refine ⟨225006918289969688238488867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150004612193313125492325911 225006918289969688238488867)
        ·
          refine ⟨337510377434954532357733301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225006918289969688238488867 337510377434954532357733301)
          ·
            refine ⟨31641597884526987408537497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337510377434954532357733301 31641597884526987408537497)
            ·
              refine ⟨23731198413395240556403123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31641597884526987408537497 23731198413395240556403123)
              ·
                refine ⟨35596797620092860834604685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23731198413395240556403123 35596797620092860834604685)
                ·
                  refine ⟨13348799107534822812976757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35596797620092860834604685 13348799107534822812976757)
                  ·
                    refine ⟨1251449916331389638716571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13348799107534822812976757 1251449916331389638716571)
                    ·
                      rfl

theorem cell22_3655785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_3655785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655785 prefixEnd_3655785 := by exact prefixLift 3655785
  have htrace : WordTrace (prefixWord ++ tailWord_3655785) baseStart_3655785 baseEnd_3655785 := by
    simpa [prefixWord, tailWord_3655785, baseEnd_3655785] using wordTrace_append hprefix tailTrace_3655785
  have hstable : (prefixWord ++ tailWord_3655785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655785).length < 2 ^ (prefixWord ++ tailWord_3655785).sum := by decide
  have hdescent : baseEnd_3655785 < baseStart_3655785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655815 : List Nat := [1, 1, 4, 2, 1, 1, 3, 9]
def baseStart_3655815 : Nat := 118140960795 + 3655815 * 2 ^ 59
def prefixEnd_3655815 : Nat := 4983230072969 + 3 ^ 40 * 3655815 * 2
def baseEnd_3655815 : Nat := 139051131771608840051831

theorem tailTrace_3655815 : CollatzResearch.WordTrace tailWord_3655815 prefixEnd_3655815 139051131771608840051831 := by
  unfold tailWord_3655815
  simp only [CollatzResearch.WordTrace]
  refine ⟨133338527250614093338992899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88892351500409395559328599 133338527250614093338992899)
  ·
    refine ⟨200007790875921140008489349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133338527250614093338992899 200007790875921140008489349)
    ·
      refine ⟨37501460789235213751591753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200007790875921140008489349 37501460789235213751591753)
      ·
        refine ⟨28126095591926410313693815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37501460789235213751591753 28126095591926410313693815)
        ·
          refine ⟨42189143387889615470540723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28126095591926410313693815 42189143387889615470540723)
          ·
            refine ⟨63283715081834423205811085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42189143387889615470540723 63283715081834423205811085)
            ·
              refine ⟨23731393155687908702179157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63283715081834423205811085 23731393155687908702179157)
              ·
                refine ⟨139051131771608840051831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23731393155687908702179157 139051131771608840051831)
                ·
                  rfl

theorem cell22_3655815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 9].length) (baseStart_3655815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655815 prefixEnd_3655815 := by exact prefixLift 3655815
  have htrace : WordTrace (prefixWord ++ tailWord_3655815) baseStart_3655815 baseEnd_3655815 := by
    simpa [prefixWord, tailWord_3655815, baseEnd_3655815] using wordTrace_append hprefix tailTrace_3655815
  have hstable : (prefixWord ++ tailWord_3655815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655815).length < 2 ^ (prefixWord ++ tailWord_3655815).sum := by decide
  have hdescent : baseEnd_3655815 < baseStart_3655815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
