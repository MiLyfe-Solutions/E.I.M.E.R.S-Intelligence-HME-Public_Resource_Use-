import V185TrunkScan23Chunk1403

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8316359 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_8316359 : Nat := 118140960795 + 8316359 * 2 ^ 59
def prefixEnd_8316359 : Nat := 4983230072969 + 3 ^ 40 * 8316359 * 2
def baseEnd_8316359 : Nat := 4270289462344532940866267

theorem tailTrace_8316359 : CollatzResearch.WordTrace tailWord_8316359 prefixEnd_8316359 4270289462344532940866267 := by
  unfold tailWord_8316359
  simp only [CollatzResearch.WordTrace]
  refine ⟨303322531678259138884776131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202215021118839425923184087 303322531678259138884776131)
  ·
    refine ⟨454983797517388708327164197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303322531678259138884776131 454983797517388708327164197)
    ·
      refine ⟨85309462034510382811343287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454983797517388708327164197 85309462034510382811343287)
      ·
        refine ⟨127964193051765574217014931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85309462034510382811343287 127964193051765574217014931)
        ·
          refine ⟨191946289577648361325522397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127964193051765574217014931 191946289577648361325522397)
          ·
            refine ⟨71979858591618135497070899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191946289577648361325522397 71979858591618135497070899)
            ·
              refine ⟨107969787887427203245606349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71979858591618135497070899 107969787887427203245606349)
              ·
                refine ⟨40488670457785201217102381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107969787887427203245606349 40488670457785201217102381)
                ·
                  refine ⟨15183251421669450456413393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40488670457785201217102381 15183251421669450456413393)
                  ·
                    refine ⟨11387438566252087842310045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15183251421669450456413393 11387438566252087842310045)
                    ·
                      refine ⟨4270289462344532940866267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387438566252087842310045 4270289462344532940866267)
                      ·
                        rfl

theorem cell23_8316359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_8316359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316359 prefixEnd_8316359 := by exact prefixLift 8316359
  have htrace : WordTrace (prefixWord ++ tailWord_8316359) baseStart_8316359 baseEnd_8316359 := by
    simpa [prefixWord, tailWord_8316359, baseEnd_8316359] using wordTrace_append hprefix tailTrace_8316359
  have hstable : (prefixWord ++ tailWord_8316359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316359).length < 2 ^ (prefixWord ++ tailWord_8316359).sum := by decide
  have hdescent : baseEnd_8316359 < baseStart_8316359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316503 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 5]
def baseStart_8316503 : Nat := 118140960795 + 8316503 * 2 ^ 59
def prefixEnd_8316503 : Nat := 4983230072969 + 3 ^ 40 * 8316503 * 2
def baseEnd_8316503 : Nat := 474484822617642264162845

theorem tailTrace_8316503 : CollatzResearch.WordTrace tailWord_8316503 prefixEnd_8316503 474484822617642264162845 := by
  unfold tailWord_8316503
  simp only [CollatzResearch.WordTrace]
  refine ⟨303327783789737451478018163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202218522526491634318678775 303327783789737451478018163)
  ·
    refine ⟨454991675684606177217027245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303327783789737451478018163 454991675684606177217027245)
    ·
      refine ⟨170621878381727316456385217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454991675684606177217027245 170621878381727316456385217)
      ·
        refine ⟨127966408786295487342288913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170621878381727316456385217 127966408786295487342288913)
        ·
          refine ⟨95974806589721615506716685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127966408786295487342288913 95974806589721615506716685)
          ·
            refine ⟨35990552471145605815018757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95974806589721615506716685 35990552471145605815018757)
            ·
              refine ⟨6748228588339801090316017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35990552471145605815018757 6748228588339801090316017)
              ·
                refine ⟨5061171441254850817737013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748228588339801090316017 5061171441254850817737013)
                ·
                  refine ⟨474484822617642264162845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5061171441254850817737013 474484822617642264162845)
                  ·
                    rfl

theorem cell23_8316503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 5].length) (baseStart_8316503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316503 prefixEnd_8316503 := by exact prefixLift 8316503
  have htrace : WordTrace (prefixWord ++ tailWord_8316503) baseStart_8316503 baseEnd_8316503 := by
    simpa [prefixWord, tailWord_8316503, baseEnd_8316503] using wordTrace_append hprefix tailTrace_8316503
  have hstable : (prefixWord ++ tailWord_8316503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316503).length < 2 ^ (prefixWord ++ tailWord_8316503).sum := by decide
  have hdescent : baseEnd_8316503 < baseStart_8316503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316533 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_8316533 : Nat := 118140960795 + 8316533 * 2 ^ 59
def prefixEnd_8316533 : Nat := 4983230072969 + 3 ^ 40 * 8316533 * 2
def baseEnd_8316533 : Nat := 1423459602659471753363489

theorem tailTrace_8316533 : CollatzResearch.WordTrace tailWord_8316533 prefixEnd_8316533 1423459602659471753363489 := by
  unfold tailWord_8316533
  simp only [CollatzResearch.WordTrace]
  refine ⟨303328877979628766601610253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202219251986419177734406835 303328877979628766601610253)
  ·
    refine ⟨113748329242360787475603845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303328877979628766601610253 113748329242360787475603845)
    ·
      refine ⟨21327811732942647651675721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113748329242360787475603845 21327811732942647651675721)
      ·
        refine ⟨15995858799706985738756791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21327811732942647651675721 15995858799706985738756791)
        ·
          refine ⟨23993788199560478608135187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15995858799706985738756791 23993788199560478608135187)
          ·
            refine ⟨35990682299340717912202781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23993788199560478608135187 35990682299340717912202781)
            ·
              refine ⟨13496505862252769217076043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35990682299340717912202781 13496505862252769217076043)
              ·
                refine ⟨20244758793379153825614065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13496505862252769217076043 20244758793379153825614065)
                ·
                  refine ⟨15183569095034365369210549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20244758793379153825614065 15183569095034365369210549)
                  ·
                    refine ⟨1423459602659471753363489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15183569095034365369210549 1423459602659471753363489)
                    ·
                      rfl

theorem cell23_8316533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_8316533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316533 prefixEnd_8316533 := by exact prefixLift 8316533
  have htrace : WordTrace (prefixWord ++ tailWord_8316533) baseStart_8316533 baseEnd_8316533 := by
    simpa [prefixWord, tailWord_8316533, baseEnd_8316533] using wordTrace_append hprefix tailTrace_8316533
  have hstable : (prefixWord ++ tailWord_8316533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316533).length < 2 ^ (prefixWord ++ tailWord_8316533).sum := by decide
  have hdescent : baseEnd_8316533 < baseStart_8316533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316536 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 6, 4, 2]
def baseStart_8316536 : Nat := 118140960795 + 8316536 * 2 ^ 59
def prefixEnd_8316536 : Nat := 4983230072969 + 3 ^ 40 * 8316536 * 2
def baseEnd_8316536 : Nat := 4270380348420378748352953

theorem tailTrace_8316536 : CollatzResearch.WordTrace tailWord_8316536 prefixEnd_8316536 4270380348420378748352953 := by
  unfold tailWord_8316536
  simp only [CollatzResearch.WordTrace]
  refine ⟨151664493699308949056984731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202219324932411932075979641 151664493699308949056984731)
  ·
    refine ⟨227496740548963423585477097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151664493699308949056984731 227496740548963423585477097)
    ·
      refine ⟨170622555411722567689107823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227496740548963423585477097 170622555411722567689107823)
      ·
        refine ⟨255933833117583851533661735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170622555411722567689107823 255933833117583851533661735)
        ·
          refine ⟨383900749676375777300492603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255933833117583851533661735 383900749676375777300492603)
          ·
            refine ⟨575851124514563665950738905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383900749676375777300492603 575851124514563665950738905)
            ·
              refine ⟨431888343385922749463054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575851124514563665950738905 431888343385922749463054179)
              ·
                refine ⟨647832515078884124194581269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431888343385922749463054179 647832515078884124194581269)
                ·
                  refine ⟨30367149144322693321620997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 647832515078884124194581269 30367149144322693321620997)
                  ·
                    refine ⟨5693840464560504997803937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30367149144322693321620997 5693840464560504997803937)
                    ·
                      refine ⟨4270380348420378748352953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693840464560504997803937 4270380348420378748352953)
                      ·
                        rfl

theorem cell23_8316536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_8316536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316536 prefixEnd_8316536 := by exact prefixLift 8316536
  have htrace : WordTrace (prefixWord ++ tailWord_8316536) baseStart_8316536 baseEnd_8316536 := by
    simpa [prefixWord, tailWord_8316536, baseEnd_8316536] using wordTrace_append hprefix tailTrace_8316536
  have hstable : (prefixWord ++ tailWord_8316536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316536).length < 2 ^ (prefixWord ++ tailWord_8316536).sum := by decide
  have hdescent : baseEnd_8316536 < baseStart_8316536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316549 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_8316549 : Nat := 118140960795 + 8316549 * 2 ^ 59
def prefixEnd_8316549 : Nat := 4983230072969 + 3 ^ 40 * 8316549 * 2
def baseEnd_8316549 : Nat := 4270387023668887197490393

theorem tailTrace_8316549 : CollatzResearch.WordTrace tailWord_8316549 prefixEnd_8316549 4270387023668887197490393 := by
  unfold tailWord_8316549
  simp only [CollatzResearch.WordTrace]
  refine ⟨303329461547570801334192701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202219641031713867556128467 303329461547570801334192701)
  ·
    refine ⟨113748548080339050500322263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303329461547570801334192701 113748548080339050500322263)
    ·
      refine ⟨170622822120508575750483395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113748548080339050500322263 170622822120508575750483395)
      ·
        refine ⟨255934233180762863625725093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170622822120508575750483395 255934233180762863625725093)
        ·
          refine ⟨47987668721393036929823455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255934233180762863625725093 47987668721393036929823455)
          ·
            refine ⟨71981503082089555394735183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47987668721393036929823455 71981503082089555394735183)
            ·
              refine ⟨107972254623134333092102775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71981503082089555394735183 107972254623134333092102775)
              ·
                refine ⟨161958381934701499638154163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107972254623134333092102775 161958381934701499638154163)
                ·
                  refine ⟨242937572902052249457231245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161958381934701499638154163 242937572902052249457231245)
                  ·
                    refine ⟨91101589838269593546461717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242937572902052249457231245 91101589838269593546461717)
                    ·
                      refine ⟨4270387023668887197490393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91101589838269593546461717 4270387023668887197490393)
                      ·
                        rfl

theorem cell23_8316549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_8316549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316549 prefixEnd_8316549 := by exact prefixLift 8316549
  have htrace : WordTrace (prefixWord ++ tailWord_8316549) baseStart_8316549 baseEnd_8316549 := by
    simpa [prefixWord, tailWord_8316549, baseEnd_8316549] using wordTrace_append hprefix tailTrace_8316549
  have hstable : (prefixWord ++ tailWord_8316549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316549).length < 2 ^ (prefixWord ++ tailWord_8316549).sum := by decide
  have hdescent : baseEnd_8316549 < baseStart_8316549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316556 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_8316556 : Nat := 118140960795 + 8316556 * 2 ^ 59
def prefixEnd_8316556 : Nat := 4983230072969 + 3 ^ 40 * 8316556 * 2
def baseEnd_8316556 : Nat := 4270390618033468670102861

theorem tailTrace_8316556 : CollatzResearch.WordTrace tailWord_8316556 prefixEnd_8316556 4270390618033468670102861 := by
  unfold tailWord_8316556
  simp only [CollatzResearch.WordTrace]
  refine ⟨151664858429272720764848761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202219811239030294353131681 151664858429272720764848761)
  ·
    refine ⟨113748643821954540573636571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151664858429272720764848761 113748643821954540573636571)
    ·
      refine ⟨170622965732931810860454857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113748643821954540573636571 170622965732931810860454857)
      ·
        refine ⟨127967224299698858145341143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170622965732931810860454857 127967224299698858145341143)
        ·
          refine ⟨191950836449548287218011715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127967224299698858145341143 191950836449548287218011715)
          ·
            refine ⟨287926254674322430827017573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191950836449548287218011715 287926254674322430827017573)
            ·
              refine ⟨53986172751435455780065795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287926254674322430827017573 53986172751435455780065795)
              ·
                refine ⟨80979259127153183670098693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53986172751435455780065795 80979259127153183670098693)
                ·
                  refine ⟨15183611086341221938143505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80979259127153183670098693 15183611086341221938143505)
                  ·
                    refine ⟨11387708314755916453607629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15183611086341221938143505 11387708314755916453607629)
                    ·
                      refine ⟨4270390618033468670102861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387708314755916453607629 4270390618033468670102861)
                      ·
                        rfl

theorem cell23_8316556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_8316556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316556 prefixEnd_8316556 := by exact prefixLift 8316556
  have htrace : WordTrace (prefixWord ++ tailWord_8316556) baseStart_8316556 baseEnd_8316556 := by
    simpa [prefixWord, tailWord_8316556, baseEnd_8316556] using wordTrace_append hprefix tailTrace_8316556
  have hstable : (prefixWord ++ tailWord_8316556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316556).length < 2 ^ (prefixWord ++ tailWord_8316556).sum := by decide
  have hdescent : baseEnd_8316556 < baseStart_8316556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316579 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_8316579 : Nat := 118140960795 + 8316579 * 2 ^ 59
def prefixEnd_8316579 : Nat := 4983230072969 + 3 ^ 40 * 8316579 * 2
def baseEnd_8316579 : Nat := 4270402428088522080115255

theorem tailTrace_8316579 : CollatzResearch.WordTrace tailWord_8316579 prefixEnd_8316579 4270402428088522080115255 := by
  unfold tailWord_8316579
  simp only [CollatzResearch.WordTrace]
  refine ⟨303330555737462116457784791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202220370491641410971856527 303330555737462116457784791)
  ·
    refine ⟨454995833606193174686677187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303330555737462116457784791 454995833606193174686677187)
    ·
      refine ⟨682493750409289762030015781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454995833606193174686677187 682493750409289762030015781)
      ·
        refine ⟨127967578201741830380627959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682493750409289762030015781 127967578201741830380627959)
        ·
          refine ⟨191951367302612745570941939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127967578201741830380627959 191951367302612745570941939)
          ·
            refine ⟨287927050953919118356412909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191951367302612745570941939 287927050953919118356412909)
            ·
              refine ⟨107972644107719669383654841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287927050953919118356412909 107972644107719669383654841)
              ·
                refine ⟨80979483080789752037741131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107972644107719669383654841 80979483080789752037741131)
                ·
                  refine ⟨121469224621184628056611697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80979483080789752037741131 121469224621184628056611697)
                  ·
                    refine ⟨91101918465888471042458773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121469224621184628056611697 91101918465888471042458773)
                    ·
                      refine ⟨4270402428088522080115255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91101918465888471042458773 4270402428088522080115255)
                      ·
                        rfl

theorem cell23_8316579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_8316579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316579 prefixEnd_8316579 := by exact prefixLift 8316579
  have htrace : WordTrace (prefixWord ++ tailWord_8316579) baseStart_8316579 baseEnd_8316579 := by
    simpa [prefixWord, tailWord_8316579, baseEnd_8316579] using wordTrace_append hprefix tailTrace_8316579
  have hstable : (prefixWord ++ tailWord_8316579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316579).length < 2 ^ (prefixWord ++ tailWord_8316579).sum := by decide
  have hdescent : baseEnd_8316579 < baseStart_8316579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316613 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 2, 3, 2]
def baseStart_8316613 : Nat := 118140960795 + 8316613 * 2 ^ 59
def prefixEnd_8316613 : Nat := 4983230072969 + 3 ^ 40 * 8316613 * 2
def baseEnd_8316613 : Nat := 4270419886430774947090099

theorem tailTrace_8316613 : CollatzResearch.WordTrace tailWord_8316613 prefixEnd_8316613 4270419886430774947090099 := by
  unfold tailWord_8316613
  simp only [CollatzResearch.WordTrace]
  refine ⟨303331795819338940264522493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202221197212892626843014995 303331795819338940264522493)
  ·
    refine ⟨113749423432252102599195935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303331795819338940264522493 113749423432252102599195935)
    ·
      refine ⟨170624135148378153898793903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113749423432252102599195935 170624135148378153898793903)
      ·
        refine ⟨255936202722567230848190855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170624135148378153898793903 255936202722567230848190855)
        ·
          refine ⟨383904304083850846272286283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255936202722567230848190855 383904304083850846272286283)
          ·
            refine ⟨575856456125776269408429425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383904304083850846272286283 575856456125776269408429425)
            ·
              refine ⟨431892342094332202056322069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575856456125776269408429425 431892342094332202056322069)
              ·
                refine ⟨20244953535671821971390097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 431892342094332202056322069 20244953535671821971390097)
                ·
                  refine ⟨15183715151753866478542573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20244953535671821971390097 15183715151753866478542573)
                  ·
                    refine ⟨5693893181907699929453465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15183715151753866478542573 5693893181907699929453465)
                    ·
                      refine ⟨4270419886430774947090099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693893181907699929453465 4270419886430774947090099)
                      ·
                        rfl

theorem cell23_8316613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_8316613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316613 prefixEnd_8316613 := by exact prefixLift 8316613
  have htrace : WordTrace (prefixWord ++ tailWord_8316613) baseStart_8316613 baseEnd_8316613 := by
    simpa [prefixWord, tailWord_8316613, baseEnd_8316613] using wordTrace_append hprefix tailTrace_8316613
  have hstable : (prefixWord ++ tailWord_8316613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316613).length < 2 ^ (prefixWord ++ tailWord_8316613).sum := by decide
  have hdescent : baseEnd_8316613 < baseStart_8316613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316614 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_8316614 : Nat := 118140960795 + 8316614 * 2 ^ 59
def prefixEnd_8316614 : Nat := 4983230072969 + 3 ^ 40 * 8316614 * 2
def baseEnd_8316614 : Nat := 1423473466637143147725865

theorem tailTrace_8316614 : CollatzResearch.WordTrace tailWord_8316614 prefixEnd_8316614 1423473466637143147725865 := by
  unfold tailWord_8316614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479119759135478669853403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202221221528223544956872597 9479119759135478669853403)
  ·
    refine ⟨14218679638703218004780105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9479119759135478669853403 14218679638703218004780105)
    ·
      refine ⟨10664009729027413503585079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14218679638703218004780105 10664009729027413503585079)
      ·
        refine ⟨15996014593541120255377619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664009729027413503585079 15996014593541120255377619)
        ·
          refine ⟨23994021890311680383066429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15996014593541120255377619 23994021890311680383066429)
          ·
            refine ⟨8997758208866880143649911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23994021890311680383066429 8997758208866880143649911)
            ·
              refine ⟨13496637313300320215474867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997758208866880143649911 13496637313300320215474867)
              ·
                refine ⟨20244955969950480323212301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13496637313300320215474867 20244955969950480323212301)
                ·
                  refine ⟨7591858488731430121204613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20244955969950480323212301 7591858488731430121204613)
                  ·
                    refine ⟨1423473466637143147725865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7591858488731430121204613 1423473466637143147725865)
                    ·
                      rfl

theorem cell23_8316614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_8316614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316614 prefixEnd_8316614 := by exact prefixLift 8316614
  have htrace : WordTrace (prefixWord ++ tailWord_8316614) baseStart_8316614 baseEnd_8316614 := by
    simpa [prefixWord, tailWord_8316614, baseEnd_8316614] using wordTrace_append hprefix tailTrace_8316614
  have hstable : (prefixWord ++ tailWord_8316614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316614).length < 2 ^ (prefixWord ++ tailWord_8316614).sum := by decide
  have hdescent : baseEnd_8316614 < baseStart_8316614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316653 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_8316653 : Nat := 118140960795 + 8316653 * 2 ^ 59
def prefixEnd_8316653 : Nat := 4983230072969 + 3 ^ 40 * 8316653 * 2
def baseEnd_8316653 : Nat := 1423480141885651596863305

theorem tailTrace_8316653 : CollatzResearch.WordTrace tailWord_8316653 prefixEnd_8316653 1423480141885651596863305 := by
  unfold tailWord_8316653
  simp only [CollatzResearch.WordTrace]
  refine ⟨303333254739194027095978613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202222169826129351397319075 303333254739194027095978613)
  ·
    refine ⟨28437492631799440040247995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303333254739194027095978613 28437492631799440040247995)
    ·
      refine ⟨42656238947699160060371993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28437492631799440040247995 42656238947699160060371993)
      ·
        refine ⟨31992179210774370045278995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42656238947699160060371993 31992179210774370045278995)
        ·
          refine ⟨47988268816161555067918493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31992179210774370045278995 47988268816161555067918493)
          ·
            refine ⟨17995600806060583150469435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47988268816161555067918493 17995600806060583150469435)
            ·
              refine ⟨26993401209090874725704153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17995600806060583150469435 26993401209090874725704153)
              ·
                refine ⟨20245050906818156044278115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26993401209090874725704153 20245050906818156044278115)
                ·
                  refine ⟨30367576360227234066417173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20245050906818156044278115 30367576360227234066417173)
                  ·
                    refine ⟨1423480141885651596863305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30367576360227234066417173 1423480141885651596863305)
                    ·
                      rfl

theorem cell23_8316653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_8316653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316653 prefixEnd_8316653 := by exact prefixLift 8316653
  have htrace : WordTrace (prefixWord ++ tailWord_8316653) baseStart_8316653 baseEnd_8316653 := by
    simpa [prefixWord, tailWord_8316653, baseEnd_8316653] using wordTrace_append hprefix tailTrace_8316653
  have hstable : (prefixWord ++ tailWord_8316653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316653).length < 2 ^ (prefixWord ++ tailWord_8316653).sum := by decide
  have hdescent : baseEnd_8316653 < baseStart_8316653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316663 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_8316663 : Nat := 118140960795 + 8316663 * 2 ^ 59
def prefixEnd_8316663 : Nat := 4983230072969 + 3 ^ 40 * 8316663 * 2
def baseEnd_8316663 : Nat := 4270445560463499751464869

theorem tailTrace_8316663 : CollatzResearch.WordTrace tailWord_8316663 prefixEnd_8316663 4270445560463499751464869 := by
  unfold tailWord_8316663
  simp only [CollatzResearch.WordTrace]
  refine ⟨303333619469157798803842643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202222412979438532535895095 303333619469157798803842643)
  ·
    refine ⟨455000429203736698205763965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303333619469157798803842643 455000429203736698205763965)
    ·
      refine ⟨170625160951401261827161487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455000429203736698205763965 170625160951401261827161487)
      ·
        refine ⟨255937741427101892740742231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170625160951401261827161487 255937741427101892740742231)
        ·
          refine ⟨383906612140652839111113347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255937741427101892740742231 383906612140652839111113347)
          ·
            refine ⟨575859918210979258666670021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383906612140652839111113347 575859918210979258666670021)
            ·
              refine ⟨107973734664558611000000629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575859918210979258666670021 107973734664558611000000629)
              ·
                refine ⟨10122537624802369781250059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107973734664558611000000629 10122537624802369781250059)
                ·
                  refine ⟨15183806437203554671875089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10122537624802369781250059 15183806437203554671875089)
                  ·
                    refine ⟨11387854827902666003906317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15183806437203554671875089 11387854827902666003906317)
                    ·
                      refine ⟨4270445560463499751464869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387854827902666003906317 4270445560463499751464869)
                      ·
                        rfl

theorem cell23_8316663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_8316663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316663 prefixEnd_8316663 := by exact prefixLift 8316663
  have htrace : WordTrace (prefixWord ++ tailWord_8316663) baseStart_8316663 baseEnd_8316663 := by
    simpa [prefixWord, tailWord_8316663, baseEnd_8316663] using wordTrace_append hprefix tailTrace_8316663
  have hstable : (prefixWord ++ tailWord_8316663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316663).length < 2 ^ (prefixWord ++ tailWord_8316663).sum := by decide
  have hdescent : baseEnd_8316663 < baseStart_8316663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316686 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_8316686 : Nat := 118140960795 + 8316686 * 2 ^ 59
def prefixEnd_8316686 : Nat := 4983230072969 + 3 ^ 40 * 8316686 * 2
def baseEnd_8316686 : Nat := 4270457370518553161477263

theorem tailTrace_8316686 : CollatzResearch.WordTrace tailWord_8316686 prefixEnd_8316686 4270457370518553161477263 := by
  unfold tailWord_8316686
  simp only [CollatzResearch.WordTrace]
  refine ⟨37916807293509309216491239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202222972232049649154619941 37916807293509309216491239)
  ·
    refine ⟨56875210940263963824736859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37916807293509309216491239 56875210940263963824736859)
    ·
      refine ⟨85312816410395945737105289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56875210940263963824736859 85312816410395945737105289)
      ·
        refine ⟨63984612307796959302828967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85312816410395945737105289 63984612307796959302828967)
        ·
          refine ⟨95976918461695438954243451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63984612307796959302828967 95976918461695438954243451)
          ·
            refine ⟨143965377692543158431365177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95976918461695438954243451 143965377692543158431365177)
            ·
              refine ⟨107974033269407368823523883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143965377692543158431365177 107974033269407368823523883)
              ·
                refine ⟨161961049904111053235285825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107974033269407368823523883 161961049904111053235285825)
                ·
                  refine ⟨121470787428083289926464369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161961049904111053235285825 121470787428083289926464369)
                  ·
                    refine ⟨91103090571062467444848277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121470787428083289926464369 91103090571062467444848277)
                    ·
                      refine ⟨4270457370518553161477263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91103090571062467444848277 4270457370518553161477263)
                      ·
                        rfl

theorem cell23_8316686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_8316686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316686 prefixEnd_8316686 := by exact prefixLift 8316686
  have htrace : WordTrace (prefixWord ++ tailWord_8316686) baseStart_8316686 baseEnd_8316686 := by
    simpa [prefixWord, tailWord_8316686, baseEnd_8316686] using wordTrace_append hprefix tailTrace_8316686
  have hstable : (prefixWord ++ tailWord_8316686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316686).length < 2 ^ (prefixWord ++ tailWord_8316686).sum := by decide
  have hdescent : baseEnd_8316686 < baseStart_8316686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316690 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8316690 : Nat := 118140960795 + 8316690 * 2 ^ 59
def prefixEnd_8316690 : Nat := 4983230072969 + 3 ^ 40 * 8316690 * 2
def baseEnd_8316690 : Nat := 4270459424441171145827245

theorem tailTrace_8316690 : CollatzResearch.WordTrace tailWord_8316690 prefixEnd_8316690 4270459424441171145827245 := by
  unfold tailWord_8316690
  simp only [CollatzResearch.WordTrace]
  refine ⟨75833651060014995603768881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202223069493373321610050349 75833651060014995603768881)
  ·
    refine ⟨56875238295011246702826661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75833651060014995603768881 56875238295011246702826661)
    ·
      refine ⟨10664107180314608756779999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56875238295011246702826661 10664107180314608756779999)
      ·
        refine ⟨15996160770471913135169999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664107180314608756779999 15996160770471913135169999)
        ·
          refine ⟨23994241155707869702754999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15996160770471913135169999 23994241155707869702754999)
          ·
            refine ⟨35991361733561804554132499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23994241155707869702754999 35991361733561804554132499)
            ·
              refine ⟨53987042600342706831198749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35991361733561804554132499 53987042600342706831198749)
              ·
                refine ⟨20245140975128515061699531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53987042600342706831198749 20245140975128515061699531)
                ·
                  refine ⟨30367711462692772592549297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20245140975128515061699531 30367711462692772592549297)
                  ·
                    refine ⟨22775783597019579444411973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30367711462692772592549297 22775783597019579444411973)
                    ·
                      refine ⟨4270459424441171145827245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22775783597019579444411973 4270459424441171145827245)
                      ·
                        rfl

theorem cell23_8316690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8316690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316690 prefixEnd_8316690 := by exact prefixLift 8316690
  have htrace : WordTrace (prefixWord ++ tailWord_8316690) baseStart_8316690 baseEnd_8316690 := by
    simpa [prefixWord, tailWord_8316690, baseEnd_8316690] using wordTrace_append hprefix tailTrace_8316690
  have hstable : (prefixWord ++ tailWord_8316690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316690).length < 2 ^ (prefixWord ++ tailWord_8316690).sum := by decide
  have hdescent : baseEnd_8316690 < baseStart_8316690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316693 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_8316693 : Nat := 118140960795 + 8316693 * 2 ^ 59
def prefixEnd_8316693 : Nat := 4983230072969 + 3 ^ 40 * 8316693 * 2
def baseEnd_8316693 : Nat := 4270460964883134634089731

theorem tailTrace_8316693 : CollatzResearch.WordTrace tailWord_8316693 prefixEnd_8316693 4270460964883134634089731 := by
  unfold tailWord_8316693
  simp only [CollatzResearch.WordTrace]
  refine ⟨303334713659049113927434733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202223142439366075951623155 303334713659049113927434733)
  ·
    refine ⟨113750517622143417722788025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303334713659049113927434733 113750517622143417722788025)
    ·
      refine ⟨85312888216607563292091019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113750517622143417722788025 85312888216607563292091019)
      ·
        refine ⟨127969332324911344938136529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85312888216607563292091019 127969332324911344938136529)
        ·
          refine ⟨95976999243683508703602397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127969332324911344938136529 95976999243683508703602397)
          ·
            refine ⟨35991374716381315763850899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95976999243683508703602397 35991374716381315763850899)
            ·
              refine ⟨53987062074571973645776349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35991374716381315763850899 53987062074571973645776349)
              ·
                refine ⟨20245148277964490117166131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53987062074571973645776349 20245148277964490117166131)
                ·
                  refine ⟨30367722416946735175749197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20245148277964490117166131 30367722416946735175749197)
                  ·
                    refine ⟨11387895906355025690905949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30367722416946735175749197 11387895906355025690905949)
                    ·
                      refine ⟨4270460964883134634089731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387895906355025690905949 4270460964883134634089731)
                      ·
                        rfl

theorem cell23_8316693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_8316693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316693 prefixEnd_8316693 := by exact prefixLift 8316693
  have htrace : WordTrace (prefixWord ++ tailWord_8316693) baseStart_8316693 baseEnd_8316693 := by
    simpa [prefixWord, tailWord_8316693, baseEnd_8316693] using wordTrace_append hprefix tailTrace_8316693
  have hstable : (prefixWord ++ tailWord_8316693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316693).length < 2 ^ (prefixWord ++ tailWord_8316693).sum := by decide
  have hdescent : baseEnd_8316693 < baseStart_8316693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316736 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_8316736 : Nat := 118140960795 + 8316736 * 2 ^ 59
def prefixEnd_8316736 : Nat := 4983230072969 + 3 ^ 40 * 8316736 * 2
def baseEnd_8316736 : Nat := 4270483044551277965852033

theorem tailTrace_8316736 : CollatzResearch.WordTrace tailWord_8316736 prefixEnd_8316736 4270483044551277965852033 := by
  unfold tailWord_8316736
  simp only [CollatzResearch.WordTrace]
  refine ⟨151668140998946666135625031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202224187998595554847500041 151668140998946666135625031)
  ·
    refine ⟨227502211498419999203437547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151668140998946666135625031 227502211498419999203437547)
    ·
      refine ⟨341253317247629998805156321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227502211498419999203437547 341253317247629998805156321)
      ·
        refine ⟨255939987935722499103867241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341253317247629998805156321 255939987935722499103867241)
        ·
          refine ⟨191954990951791874327900431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255939987935722499103867241 191954990951791874327900431)
          ·
            refine ⟨287932486427687811491850647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191954990951791874327900431 287932486427687811491850647)
            ·
              refine ⟨431898729641531717237775971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287932486427687811491850647 431898729641531717237775971)
              ·
                refine ⟨647848094462297575856663957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431898729641531717237775971 647848094462297575856663957)
                ·
                  refine ⟨30367879427920198868281123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 647848094462297575856663957 30367879427920198868281123)
                  ·
                    refine ⟨45551819141880298302421685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30367879427920198868281123 45551819141880298302421685)
                    ·
                      refine ⟨4270483044551277965852033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45551819141880298302421685 4270483044551277965852033)
                      ·
                        rfl

theorem cell23_8316736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_8316736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316736 prefixEnd_8316736 := by exact prefixLift 8316736
  have htrace : WordTrace (prefixWord ++ tailWord_8316736) baseStart_8316736 baseEnd_8316736 := by
    simpa [prefixWord, tailWord_8316736, baseEnd_8316736] using wordTrace_append hprefix tailTrace_8316736
  have hstable : (prefixWord ++ tailWord_8316736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316736).length < 2 ^ (prefixWord ++ tailWord_8316736).sum := by decide
  have hdescent : baseEnd_8316736 < baseStart_8316736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316770 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_8316770 : Nat := 118140960795 + 8316770 * 2 ^ 59
def prefixEnd_8316770 : Nat := 4983230072969 + 3 ^ 40 * 8316770 * 2
def baseEnd_8316770 : Nat := 4270500502893530832826877

theorem tailTrace_8316770 : CollatzResearch.WordTrace tailWord_8316770 prefixEnd_8316770 4270500502893530832826877 := by
  unfold tailWord_8316770
  simp only [CollatzResearch.WordTrace]
  refine ⟨75834380519942539019496941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202225014719846770718658509 75834380519942539019496941)
  ·
    refine ⟨28437892694978452132311353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75834380519942539019496941 28437892694978452132311353)
    ·
      refine ⟨21328419521233839099233515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28437892694978452132311353 21328419521233839099233515)
      ·
        refine ⟨31992629281850758648850273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21328419521233839099233515 31992629281850758648850273)
        ·
          refine ⟨23994471961388068986637705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31992629281850758648850273 23994471961388068986637705)
          ·
            refine ⟨17995853971041051739978279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23994471961388068986637705 17995853971041051739978279)
            ·
              refine ⟨26993780956561577609967419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17995853971041051739978279 26993780956561577609967419)
              ·
                refine ⟨40490671434842366414951129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26993780956561577609967419 40490671434842366414951129)
                ·
                  refine ⟨30368003576131774811213347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40490671434842366414951129 30368003576131774811213347)
                  ·
                    refine ⟨45552005364197662216820021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30368003576131774811213347 45552005364197662216820021)
                    ·
                      refine ⟨4270500502893530832826877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45552005364197662216820021 4270500502893530832826877)
                      ·
                        rfl

theorem cell23_8316770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_8316770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316770 prefixEnd_8316770 := by exact prefixLift 8316770
  have htrace : WordTrace (prefixWord ++ tailWord_8316770) baseStart_8316770 baseEnd_8316770 := by
    simpa [prefixWord, tailWord_8316770, baseEnd_8316770] using wordTrace_append hprefix tailTrace_8316770
  have hstable : (prefixWord ++ tailWord_8316770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316770).length < 2 ^ (prefixWord ++ tailWord_8316770).sum := by decide
  have hdescent : baseEnd_8316770 < baseStart_8316770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316801 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_8316801 : Nat := 118140960795 + 8316801 * 2 ^ 59
def prefixEnd_8316801 : Nat := 4983230072969 + 3 ^ 40 * 8316801 * 2
def baseEnd_8316801 : Nat := 4270516420793820211539235

theorem tailTrace_8316801 : CollatzResearch.WordTrace tailWord_8316801 prefixEnd_8316801 4270516420793820211539235 := by
  unfold tailWord_8316801
  simp only [CollatzResearch.WordTrace]
  refine ⟨303338652742657848372366257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202225768495105232248244171 303338652742657848372366257)
  ·
    refine ⟨227503989556993386279274693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303338652742657848372366257 227503989556993386279274693)
    ·
      refine ⟨42656998041936259927364005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227503989556993386279274693 42656998041936259927364005)
      ·
        refine ⟨7998187132863048736380751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42656998041936259927364005 7998187132863048736380751)
        ·
          refine ⟨11997280699294573104571127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998187132863048736380751 11997280699294573104571127)
          ·
            refine ⟨17995921048941859656856691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997280699294573104571127 17995921048941859656856691)
            ·
              refine ⟨26993881573412789485285037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17995921048941859656856691 26993881573412789485285037)
              ·
                refine ⟨10122705590029796056981889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26993881573412789485285037 10122705590029796056981889)
                ·
                  refine ⟨7592029192522347042736417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10122705590029796056981889 7592029192522347042736417)
                  ·
                    refine ⟨5694021894391760282052313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592029192522347042736417 5694021894391760282052313)
                    ·
                      refine ⟨4270516420793820211539235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694021894391760282052313 4270516420793820211539235)
                      ·
                        rfl

theorem cell23_8316801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_8316801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316801 prefixEnd_8316801 := by exact prefixLift 8316801
  have htrace : WordTrace (prefixWord ++ tailWord_8316801) baseStart_8316801 baseEnd_8316801 := by
    simpa [prefixWord, tailWord_8316801, baseEnd_8316801] using wordTrace_append hprefix tailTrace_8316801
  have hstable : (prefixWord ++ tailWord_8316801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316801).length < 2 ^ (prefixWord ++ tailWord_8316801).sum := by decide
  have hdescent : baseEnd_8316801 < baseStart_8316801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316816 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_8316816 : Nat := 118140960795 + 8316816 * 2 ^ 59
def prefixEnd_8316816 : Nat := 4983230072969 + 3 ^ 40 * 8316816 * 2
def baseEnd_8316816 : Nat := 1423508041001212550950555

theorem tailTrace_8316816 : CollatzResearch.WordTrace tailWord_8316816 prefixEnd_8316816 1423508041001212550950555 := by
  unfold tailWord_8316816
  simp only [CollatzResearch.WordTrace]
  refine ⟨151669599918801752967081151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202226133225069003956108201 151669599918801752967081151)
  ·
    refine ⟨227504399878202629450621727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151669599918801752967081151 227504399878202629450621727)
    ·
      refine ⟨341256599817303944175932591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227504399878202629450621727 341256599817303944175932591)
      ·
        refine ⟨511884899725955916263898887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341256599817303944175932591 511884899725955916263898887)
        ·
          refine ⟨767827349588933874395848331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511884899725955916263898887 767827349588933874395848331)
          ·
            refine ⟨1151741024383400811593772497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767827349588933874395848331 1151741024383400811593772497)
            ·
              refine ⟨863805768287550608695329373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151741024383400811593772497 863805768287550608695329373)
              ·
                refine ⟨323927163107831478260748515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863805768287550608695329373 323927163107831478260748515)
                ·
                  refine ⟨485890744661747217391122773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323927163107831478260748515 485890744661747217391122773)
                  ·
                    refine ⟨1423508041001212550950555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 485890744661747217391122773 1423508041001212550950555)
                    ·
                      rfl

theorem cell23_8316816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_8316816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316816 prefixEnd_8316816 := by exact prefixLift 8316816
  have htrace : WordTrace (prefixWord ++ tailWord_8316816) baseStart_8316816 baseEnd_8316816 := by
    simpa [prefixWord, tailWord_8316816, baseEnd_8316816] using wordTrace_append hprefix tailTrace_8316816
  have hstable : (prefixWord ++ tailWord_8316816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316816).length < 2 ^ (prefixWord ++ tailWord_8316816).sum := by decide
  have hdescent : baseEnd_8316816 < baseStart_8316816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316820 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_8316820 : Nat := 118140960795 + 8316820 * 2 ^ 59
def prefixEnd_8316820 : Nat := 4983230072969 + 3 ^ 40 * 8316820 * 2
def baseEnd_8316820 : Nat := 1423508725642085212400549

theorem tailTrace_8316820 : CollatzResearch.WordTrace tailWord_8316820 prefixEnd_8316820 1423508725642085212400549 := by
  unfold tailWord_8316820
  simp only [CollatzResearch.WordTrace]
  refine ⟨151669672864794507308653957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202226230486392676411538609 151669672864794507308653957)
  ·
    refine ⟨28438063662148970120372617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151669672864794507308653957 28438063662148970120372617)
    ·
      refine ⟨21328547746611727590279463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28438063662148970120372617 21328547746611727590279463)
      ·
        refine ⟨31992821619917591385419195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21328547746611727590279463 31992821619917591385419195)
        ·
          refine ⟨47989232429876387078128793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31992821619917591385419195 47989232429876387078128793)
          ·
            refine ⟨35991924322407290308596595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47989232429876387078128793 35991924322407290308596595)
            ·
              refine ⟨53987886483610935462894893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35991924322407290308596595 53987886483610935462894893)
              ·
                refine ⟨20245457431354100798585585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53987886483610935462894893 20245457431354100798585585)
                ·
                  refine ⟨15184093073515575598939189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20245457431354100798585585 15184093073515575598939189)
                  ·
                    refine ⟨1423508725642085212400549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15184093073515575598939189 1423508725642085212400549)
                    ·
                      rfl

theorem cell23_8316820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_8316820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316820 prefixEnd_8316820 := by exact prefixLift 8316820
  have htrace : WordTrace (prefixWord ++ tailWord_8316820) baseStart_8316820 baseEnd_8316820 := by
    simpa [prefixWord, tailWord_8316820, baseEnd_8316820] using wordTrace_append hprefix tailTrace_8316820
  have hstable : (prefixWord ++ tailWord_8316820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316820).length < 2 ^ (prefixWord ++ tailWord_8316820).sum := by decide
  have hdescent : baseEnd_8316820 < baseStart_8316820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316863 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 6]
def baseStart_8316863 : Nat := 118140960795 + 8316863 * 2 ^ 59
def prefixEnd_8316863 : Nat := 4983230072969 + 3 ^ 40 * 8316863 * 2
def baseEnd_8316863 : Nat := 474505361843822107662661

theorem tailTrace_8316863 : CollatzResearch.WordTrace tailWord_8316863 prefixEnd_8316863 474505361843822107662661 := by
  unfold tailWord_8316863
  simp only [CollatzResearch.WordTrace]
  refine ⟨303340914068433232961123243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202227276045622155307415495 303340914068433232961123243)
  ·
    refine ⟨455011371102649849441684865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303340914068433232961123243 455011371102649849441684865)
    ·
      refine ⟨341258528326987387081263649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455011371102649849441684865 341258528326987387081263649)
      ·
        refine ⟨255943896245240540310947737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341258528326987387081263649 255943896245240540310947737)
        ·
          refine ⟨191957922183930405233210803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255943896245240540310947737 191957922183930405233210803)
          ·
            refine ⟨287936883275895607849816205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191957922183930405233210803 287936883275895607849816205)
            ·
              refine ⟨107976331228460852943681077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287936883275895607849816205 107976331228460852943681077)
              ·
                refine ⟨10122781052668204963470101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107976331228460852943681077 10122781052668204963470101)
                ·
                  refine ⟨474505361843822107662661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10122781052668204963470101 474505361843822107662661)
                  ·
                    rfl

theorem cell23_8316863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 6].length) (baseStart_8316863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316863 prefixEnd_8316863 := by exact prefixLift 8316863
  have htrace : WordTrace (prefixWord ++ tailWord_8316863) baseStart_8316863 baseEnd_8316863 := by
    simpa [prefixWord, tailWord_8316863, baseEnd_8316863] using wordTrace_append hprefix tailTrace_8316863
  have hstable : (prefixWord ++ tailWord_8316863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316863).length < 2 ^ (prefixWord ++ tailWord_8316863).sum := by decide
  have hdescent : baseEnd_8316863 < baseStart_8316863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316873 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_8316873 : Nat := 118140960795 + 8316873 * 2 ^ 59
def prefixEnd_8316873 : Nat := 4983230072969 + 3 ^ 40 * 8316873 * 2
def baseEnd_8316873 : Nat := 4270553391400943929838903

theorem tailTrace_8316873 : CollatzResearch.WordTrace tailWord_8316873 prefixEnd_8316873 4270553391400943929838903 := by
  unfold tailWord_8316873
  simp only [CollatzResearch.WordTrace]
  refine ⟨303341278798397004668987273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202227519198931336445991515 303341278798397004668987273)
  ·
    refine ⟨227505959098797753501740455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303341278798397004668987273 227505959098797753501740455)
    ·
      refine ⟨341258938648196630252610683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227505959098797753501740455 341258938648196630252610683)
      ·
        refine ⟨511888407972294945378916025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341258938648196630252610683 511888407972294945378916025)
        ·
          refine ⟨383916305979221209034187019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511888407972294945378916025 383916305979221209034187019)
          ·
            refine ⟨575874458968831813551280529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383916305979221209034187019 575874458968831813551280529)
            ·
              refine ⟨431905844226623860163460397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575874458968831813551280529 431905844226623860163460397)
              ·
                refine ⟨161964691584983947561297649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431905844226623860163460397 161964691584983947561297649)
                ·
                  refine ⟨121473518688737960670973237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161964691584983947561297649 121473518688737960670973237)
                  ·
                    refine ⟨11388142377069183812903741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121473518688737960670973237 11388142377069183812903741)
                    ·
                      refine ⟨4270553391400943929838903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11388142377069183812903741 4270553391400943929838903)
                      ·
                        rfl

theorem cell23_8316873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_8316873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316873 prefixEnd_8316873 := by exact prefixLift 8316873
  have htrace : WordTrace (prefixWord ++ tailWord_8316873) baseStart_8316873 baseEnd_8316873 := by
    simpa [prefixWord, tailWord_8316873, baseEnd_8316873] using wordTrace_append hprefix tailTrace_8316873
  have hstable : (prefixWord ++ tailWord_8316873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316873).length < 2 ^ (prefixWord ++ tailWord_8316873).sum := by decide
  have hdescent : baseEnd_8316873 < baseStart_8316873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316884 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_8316884 : Nat := 118140960795 + 8316884 * 2 ^ 59
def prefixEnd_8316884 : Nat := 4983230072969 + 3 ^ 40 * 8316884 * 2
def baseEnd_8316884 : Nat := 1423519679896047795600451

theorem tailTrace_8316884 : CollatzResearch.WordTrace tailWord_8316884 prefixEnd_8316884 1423519679896047795600451 := by
  unfold tailWord_8316884
  simp only [CollatzResearch.WordTrace]
  refine ⟨151670840000678576773818853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202227786667571435698425137 151670840000678576773818853)
  ·
    refine ⟨28438282500127233145091035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151670840000678576773818853 28438282500127233145091035)
    ·
      refine ⟨42657423750190849717636553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28438282500127233145091035 42657423750190849717636553)
      ·
        refine ⟨31993067812643137288227415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42657423750190849717636553 31993067812643137288227415)
        ·
          refine ⟨47989601718964705932341123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31993067812643137288227415 47989601718964705932341123)
          ·
            refine ⟨71984402578447058898511685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47989601718964705932341123 71984402578447058898511685)
            ·
              refine ⟨13497075483458823543470941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71984402578447058898511685 13497075483458823543470941)
              ·
                refine ⟨5061403306297058828801603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13497075483458823543470941 5061403306297058828801603)
                ·
                  refine ⟨7592104959445588243202405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061403306297058828801603 7592104959445588243202405)
                  ·
                    refine ⟨1423519679896047795600451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592104959445588243202405 1423519679896047795600451)
                    ·
                      rfl

theorem cell23_8316884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_8316884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316884 prefixEnd_8316884 := by exact prefixLift 8316884
  have htrace : WordTrace (prefixWord ++ tailWord_8316884) baseStart_8316884 baseEnd_8316884 := by
    simpa [prefixWord, tailWord_8316884, baseEnd_8316884] using wordTrace_append hprefix tailTrace_8316884
  have hstable : (prefixWord ++ tailWord_8316884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316884).length < 2 ^ (prefixWord ++ tailWord_8316884).sum := by decide
  have hdescent : baseEnd_8316884 < baseStart_8316884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316940 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_8316940 : Nat := 118140960795 + 8316940 * 2 ^ 59
def prefixEnd_8316940 : Nat := 4983230072969 + 3 ^ 40 * 8316940 * 2
def baseEnd_8316940 : Nat := 1423529264868265055900365

theorem tailTrace_8316940 : CollatzResearch.WordTrace tailWord_8316940 prefixEnd_8316940 1423529264868265055900365 := by
  unfold tailWord_8316940
  simp only [CollatzResearch.WordTrace]
  refine ⟨151671861244577137555838137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202229148326102850074450849 151671861244577137555838137)
  ·
    refine ⟨113753895933432853166878603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151671861244577137555838137 113753895933432853166878603)
    ·
      refine ⟨170630843900149279750317905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113753895933432853166878603 170630843900149279750317905)
      ·
        refine ⟨127973132925111959812738429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170630843900149279750317905 127973132925111959812738429)
        ·
          refine ⟨47989924846916984929776911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127973132925111959812738429 47989924846916984929776911)
          ·
            refine ⟨71984887270375477394665367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47989924846916984929776911 71984887270375477394665367)
            ·
              refine ⟨107977330905563216091998051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71984887270375477394665367 107977330905563216091998051)
              ·
                refine ⟨161965996358344824137997077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107977330905563216091998051 161965996358344824137997077)
                ·
                  refine ⟨7592156079297413631468613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161965996358344824137997077 7592156079297413631468613)
                  ·
                    refine ⟨1423529264868265055900365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592156079297413631468613 1423529264868265055900365)
                    ·
                      rfl

theorem cell23_8316940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_8316940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316940 prefixEnd_8316940 := by exact prefixLift 8316940
  have htrace : WordTrace (prefixWord ++ tailWord_8316940) baseStart_8316940 baseEnd_8316940 := by
    simpa [prefixWord, tailWord_8316940, baseEnd_8316940] using wordTrace_append hprefix tailTrace_8316940
  have hstable : (prefixWord ++ tailWord_8316940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316940).length < 2 ^ (prefixWord ++ tailWord_8316940).sum := by decide
  have hdescent : baseEnd_8316940 < baseStart_8316940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316947 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 5, 2, 2]
def baseStart_8316947 : Nat := 118140960795 + 8316947 * 2 ^ 59
def prefixEnd_8316947 : Nat := 4983230072969 + 3 ^ 40 * 8316947 * 2
def baseEnd_8316947 : Nat := 4270591388969376640313563

theorem tailTrace_8316947 : CollatzResearch.WordTrace tailWord_8316947 prefixEnd_8316947 4270591388969376640313563 := by
  unfold tailWord_8316947
  simp only [CollatzResearch.WordTrace]
  refine ⟨303343977800128915307181095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202229318533419276871454063 303343977800128915307181095)
  ·
    refine ⟨455015966700193372960771643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303343977800128915307181095 455015966700193372960771643)
    ·
      refine ⟨682523950050290059441157465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455015966700193372960771643 682523950050290059441157465)
      ·
        refine ⟨511892962537717544580868099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682523950050290059441157465 511892962537717544580868099)
        ·
          refine ⟨767839443806576316871302149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511892962537717544580868099 767839443806576316871302149)
          ·
            refine ⟨143969895713733059413369153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 767839443806576316871302149 143969895713733059413369153)
            ·
              refine ⟨107977421785299794560026865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143969895713733059413369153 107977421785299794560026865)
              ·
                refine ⟨80983066338974845920020149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107977421785299794560026865 80983066338974845920020149)
                ·
                  refine ⟨7592162469278891805001889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80983066338974845920020149 7592162469278891805001889)
                  ·
                    refine ⟨5694121851959168853751417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592162469278891805001889 5694121851959168853751417)
                    ·
                      refine ⟨4270591388969376640313563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694121851959168853751417 4270591388969376640313563)
                      ·
                        rfl

theorem cell23_8316947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 2, 2].length) (baseStart_8316947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316947 prefixEnd_8316947 := by exact prefixLift 8316947
  have htrace : WordTrace (prefixWord ++ tailWord_8316947) baseStart_8316947 baseEnd_8316947 := by
    simpa [prefixWord, tailWord_8316947, baseEnd_8316947] using wordTrace_append hprefix tailTrace_8316947
  have hstable : (prefixWord ++ tailWord_8316947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316947).length < 2 ^ (prefixWord ++ tailWord_8316947).sum := by decide
  have hdescent : baseEnd_8316947 < baseStart_8316947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316957 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_8316957 : Nat := 118140960795 + 8316957 * 2 ^ 59
def prefixEnd_8316957 : Nat := 4983230072969 + 3 ^ 40 * 8316957 * 2
def baseEnd_8316957 : Nat := 1423532174591973867062839

theorem tailTrace_8316957 : CollatzResearch.WordTrace tailWord_8316957 prefixEnd_8316957 1423532174591973867062839 := by
  unfold tailWord_8316957
  simp only [CollatzResearch.WordTrace]
  refine ⟨303344342530092687015045125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202229561686728458010030083 303344342530092687015045125)
  ·
    refine ⟨56877064224392378815320961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303344342530092687015045125 56877064224392378815320961)
    ·
      refine ⟨42657798168294284111490721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56877064224392378815320961 42657798168294284111490721)
      ·
        refine ⟨31993348626220713083618041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42657798168294284111490721 31993348626220713083618041)
        ·
          refine ⟨23995011469665534812713531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31993348626220713083618041 23995011469665534812713531)
          ·
            refine ⟨35992517204498302219070297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23995011469665534812713531 35992517204498302219070297)
            ·
              refine ⟨26994387903373726664302723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35992517204498302219070297 26994387903373726664302723)
              ·
                refine ⟨40491581855060589996454085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26994387903373726664302723 40491581855060589996454085)
                ·
                  refine ⟨7592171597823860624335141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40491581855060589996454085 7592171597823860624335141)
                  ·
                    refine ⟨1423532174591973867062839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592171597823860624335141 1423532174591973867062839)
                    ·
                      rfl

theorem cell23_8316957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_8316957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316957 prefixEnd_8316957 := by exact prefixLift 8316957
  have htrace : WordTrace (prefixWord ++ tailWord_8316957) baseStart_8316957 baseEnd_8316957 := by
    simpa [prefixWord, tailWord_8316957, baseEnd_8316957] using wordTrace_append hprefix tailTrace_8316957
  have hstable : (prefixWord ++ tailWord_8316957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316957).length < 2 ^ (prefixWord ++ tailWord_8316957).sum := by decide
  have hdescent : baseEnd_8316957 < baseStart_8316957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316970 : List Nat := [3, 1, 4, 1, 2, 1, 1, 10]
def baseStart_8316970 : Nat := 118140960795 + 8316970 * 2 ^ 59
def prefixEnd_8316970 : Nat := 4983230072969 + 3 ^ 40 * 8316970 * 2
def baseEnd_8316970 : Nat := 158170488852756668530591

theorem tailTrace_8316970 : CollatzResearch.WordTrace tailWord_8316970 prefixEnd_8316970 158170488852756668530591 := by
  unfold tailWord_8316970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75836204169761397558817091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202229877786030393490178909 75836204169761397558817091)
  ·
    refine ⟨113754306254642096338225637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75836204169761397558817091 113754306254642096338225637)
    ·
      refine ⟨21328932422745393063417307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113754306254642096338225637 21328932422745393063417307)
      ·
        refine ⟨31993398634118089595125961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21328932422745393063417307 31993398634118089595125961)
        ·
          refine ⟨23995048975588567196344471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31993398634118089595125961 23995048975588567196344471)
          ·
            refine ⟨35992573463382850794516707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23995048975588567196344471 35992573463382850794516707)
            ·
              refine ⟨53988860195074276191775061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35992573463382850794516707 53988860195074276191775061)
              ·
                refine ⟨158170488852756668530591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53988860195074276191775061 158170488852756668530591)
                ·
                  rfl

theorem cell23_8316970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_8316970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316970 prefixEnd_8316970 := by exact prefixLift 8316970
  have htrace : WordTrace (prefixWord ++ tailWord_8316970) baseStart_8316970 baseEnd_8316970 := by
    simpa [prefixWord, tailWord_8316970, baseEnd_8316970] using wordTrace_append hprefix tailTrace_8316970
  have hstable : (prefixWord ++ tailWord_8316970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316970).length < 2 ^ (prefixWord ++ tailWord_8316970).sum := by decide
  have hdescent : baseEnd_8316970 < baseStart_8316970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316974 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_8316974 : Nat := 118140960795 + 8316974 * 2 ^ 59
def prefixEnd_8316974 : Nat := 4983230072969 + 3 ^ 40 * 8316974 * 2
def baseEnd_8316974 : Nat := 1423535084315682678225313

theorem tailTrace_8316974 : CollatzResearch.WordTrace tailWord_8316974 prefixEnd_8316974 1423535084315682678225313 := by
  unfold tailWord_8316974
  simp only [CollatzResearch.WordTrace]
  refine ⟨37918120321378887364801747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202229975047354065945609317 37918120321378887364801747)
  ·
    refine ⟨56877180482068331047202621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37918120321378887364801747 56877180482068331047202621)
    ·
      refine ⟨21328942680775624142700983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56877180482068331047202621 21328942680775624142700983)
      ·
        refine ⟨31993414021163436214051475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21328942680775624142700983 31993414021163436214051475)
        ·
          refine ⟨47990121031745154321077213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31993414021163436214051475 47990121031745154321077213)
          ·
            refine ⟨17996295386904432870403955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47990121031745154321077213 17996295386904432870403955)
            ·
              refine ⟨26994443080356649305605933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996295386904432870403955 26994443080356649305605933)
              ·
                refine ⟨10122916155133743489602225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26994443080356649305605933 10122916155133743489602225)
                ·
                  refine ⟨7592187116350307617201669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10122916155133743489602225 7592187116350307617201669)
                  ·
                    refine ⟨1423535084315682678225313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592187116350307617201669 1423535084315682678225313)
                    ·
                      rfl

theorem cell23_8316974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_8316974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316974 prefixEnd_8316974 := by exact prefixLift 8316974
  have htrace : WordTrace (prefixWord ++ tailWord_8316974) baseStart_8316974 baseEnd_8316974 := by
    simpa [prefixWord, tailWord_8316974, baseEnd_8316974] using wordTrace_append hprefix tailTrace_8316974
  have hstable : (prefixWord ++ tailWord_8316974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316974).length < 2 ^ (prefixWord ++ tailWord_8316974).sum := by decide
  have hdescent : baseEnd_8316974 < baseStart_8316974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317003 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_8317003 : Nat := 118140960795 + 8317003 * 2 ^ 59
def prefixEnd_8317003 : Nat := 4983230072969 + 3 ^ 40 * 8317003 * 2
def baseEnd_8317003 : Nat := 4270620143886028421213305

theorem tailTrace_8317003 : CollatzResearch.WordTrace tailWord_8317003 prefixEnd_8317003 4270620143886028421213305 := by
  unfold tailWord_8317003
  simp only [CollatzResearch.WordTrace]
  refine ⟨303346020287926036871219663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202230680191950691247479775 303346020287926036871219663)
  ·
    refine ⟨455019030431889055306829495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303346020287926036871219663 455019030431889055306829495)
    ·
      refine ⟨682528545647833582960244243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455019030431889055306829495 682528545647833582960244243)
      ·
        refine ⟨1023792818471750374440366365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682528545647833582960244243 1023792818471750374440366365)
        ·
          refine ⟨383922306926906390415137387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1023792818471750374440366365 383922306926906390415137387)
          ·
            refine ⟨575883460390359585622706081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383922306926906390415137387 575883460390359585622706081)
            ·
              refine ⟨431912595292769689217029561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575883460390359585622706081 431912595292769689217029561)
              ·
                refine ⟨323934446469577266912772171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431912595292769689217029561 323934446469577266912772171)
                ·
                  refine ⟨485901669704365900369158257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323934446469577266912772171 485901669704365900369158257)
                  ·
                    refine ⟨364426252278274425276868693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 485901669704365900369158257 364426252278274425276868693)
                    ·
                      refine ⟨4270620143886028421213305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 364426252278274425276868693 4270620143886028421213305)
                      ·
                        rfl

theorem cell23_8317003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_8317003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317003 prefixEnd_8317003 := by exact prefixLift 8317003
  have htrace : WordTrace (prefixWord ++ tailWord_8317003) baseStart_8317003 baseEnd_8317003 := by
    simpa [prefixWord, tailWord_8317003, baseEnd_8317003] using wordTrace_append hprefix tailTrace_8317003
  have hstable : (prefixWord ++ tailWord_8317003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317003).length < 2 ^ (prefixWord ++ tailWord_8317003).sum := by decide
  have hdescent : baseEnd_8317003 < baseStart_8317003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317060 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 9]
def baseStart_8317060 : Nat := 118140960795 + 8317060 * 2 ^ 59
def prefixEnd_8317060 : Nat := 4983230072969 + 3 ^ 40 * 8317060 * 2
def baseEnd_8317060 : Nat := 474516601364814966466727

theorem tailTrace_8317060 : CollatzResearch.WordTrace tailWord_8317060 prefixEnd_8317060 474516601364814966466727 := by
  unfold tailWord_8317060
  simp only [CollatzResearch.WordTrace]
  refine ⟨151674049624359767803022317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202232066165813023737363089 151674049624359767803022317)
  ·
    refine ⟨56877768609134912926133369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151674049624359767803022317 56877768609134912926133369)
    ·
      refine ⟨42658326456851184694600027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56877768609134912926133369 42658326456851184694600027)
      ·
        refine ⟨63987489685276777041900041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42658326456851184694600027 63987489685276777041900041)
        ·
          refine ⟨47990617263957582781425031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63987489685276777041900041 47990617263957582781425031)
          ·
            refine ⟨71985925895936374172137547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47990617263957582781425031 71985925895936374172137547)
            ·
              refine ⟨107978888843904561258206321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71985925895936374172137547 107978888843904561258206321)
              ·
                refine ⟨80984166632928420943654741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107978888843904561258206321 80984166632928420943654741)
                ·
                  refine ⟨474516601364814966466727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80984166632928420943654741 474516601364814966466727)
                  ·
                    rfl

theorem cell23_8317060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_8317060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317060 prefixEnd_8317060 := by exact prefixLift 8317060
  have htrace : WordTrace (prefixWord ++ tailWord_8317060) baseStart_8317060 baseEnd_8317060 := by
    simpa [prefixWord, tailWord_8317060, baseEnd_8317060] using wordTrace_append hprefix tailTrace_8317060
  have hstable : (prefixWord ++ tailWord_8317060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317060).length < 2 ^ (prefixWord ++ tailWord_8317060).sum := by decide
  have hdescent : baseEnd_8317060 < baseStart_8317060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317077 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 5]
def baseStart_8317077 : Nat := 118140960795 + 8317077 * 2 ^ 59
def prefixEnd_8317077 : Nat := 4983230072969 + 3 ^ 40 * 8317077 * 2
def baseEnd_8317077 : Nat := 474517571272717903520885

theorem tailTrace_8317077 : CollatzResearch.WordTrace tailWord_8317077 prefixEnd_8317077 474517571272717903520885 := by
  unfold tailWord_8317077
  simp only [CollatzResearch.WordTrace]
  refine ⟨303348719289657947509413485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202232479526438631672942323 303348719289657947509413485)
  ·
    refine ⟨113755769733621730316030057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303348719289657947509413485 113755769733621730316030057)
    ·
      refine ⟨85316827300216297737022543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113755769733621730316030057 85316827300216297737022543)
      ·
        refine ⟨127975240950324446605533815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85316827300216297737022543 127975240950324446605533815)
        ·
          refine ⟨191962861425486669908300723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127975240950324446605533815 191962861425486669908300723)
          ·
            refine ⟨287944292138230004862451085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191962861425486669908300723 287944292138230004862451085)
            ·
              refine ⟨107979109551836251823419157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287944292138230004862451085 107979109551836251823419157)
              ·
                refine ⟨5061520760242324304222773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107979109551836251823419157 5061520760242324304222773)
                ·
                  refine ⟨474517571272717903520885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5061520760242324304222773 474517571272717903520885)
                  ·
                    rfl

theorem cell23_8317077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_8317077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317077 prefixEnd_8317077 := by exact prefixLift 8317077
  have htrace : WordTrace (prefixWord ++ tailWord_8317077) baseStart_8317077 baseEnd_8317077 := by
    simpa [prefixWord, tailWord_8317077, baseEnd_8317077] using wordTrace_append hprefix tailTrace_8317077
  have hstable : (prefixWord ++ tailWord_8317077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317077).length < 2 ^ (prefixWord ++ tailWord_8317077).sum := by decide
  have hdescent : baseEnd_8317077 < baseStart_8317077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317088 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 2, 2, 2]
def baseStart_8317088 : Nat := 118140960795 + 8317088 * 2 ^ 59
def prefixEnd_8317088 : Nat := 4983230072969 + 3 ^ 40 * 8317088 * 2
def baseEnd_8317088 : Nat := 4270663789741660588650415

theorem tailTrace_8317088 : CollatzResearch.WordTrace tailWord_8317088 prefixEnd_8317088 4270663789741660588650415 := by
  unfold tailWord_8317088
  simp only [CollatzResearch.WordTrace]
  refine ⟨151674560246309048194031959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202232746995078730925375945 151674560246309048194031959)
  ·
    refine ⟨227511840369463572291047939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151674560246309048194031959 227511840369463572291047939)
    ·
      refine ⟨341267760554195358436571909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227511840369463572291047939 341267760554195358436571909)
      ·
        refine ⟨63987705103911629706857233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341267760554195358436571909 63987705103911629706857233)
        ·
          refine ⟨47990778827933722280142925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63987705103911629706857233 47990778827933722280142925)
          ·
            refine ⟨17996542060475145855053597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47990778827933722280142925 17996542060475145855053597)
            ·
              refine ⟨6748703272678179695645099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17996542060475145855053597 6748703272678179695645099)
              ·
                refine ⟨10123054909017269543467649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6748703272678179695645099 10123054909017269543467649)
                ·
                  refine ⟨7592291181762952157600737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10123054909017269543467649 7592291181762952157600737)
                  ·
                    refine ⟨5694218386322214118200553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592291181762952157600737 5694218386322214118200553)
                    ·
                      refine ⟨4270663789741660588650415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694218386322214118200553 4270663789741660588650415)
                      ·
                        rfl

theorem cell23_8317088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_8317088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317088 prefixEnd_8317088 := by exact prefixLift 8317088
  have htrace : WordTrace (prefixWord ++ tailWord_8317088) baseStart_8317088 baseEnd_8317088 := by
    simpa [prefixWord, tailWord_8317088, baseEnd_8317088] using wordTrace_append hprefix tailTrace_8317088
  have hstable : (prefixWord ++ tailWord_8317088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317088).length < 2 ^ (prefixWord ++ tailWord_8317088).sum := by decide
  have hdescent : baseEnd_8317088 < baseStart_8317088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317108 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_8317108 : Nat := 118140960795 + 8317108 * 2 ^ 59
def prefixEnd_8317108 : Nat := 4983230072969 + 3 ^ 40 * 8317108 * 2
def baseEnd_8317108 : Nat := 4270674059354750510400323

theorem tailTrace_8317108 : CollatzResearch.WordTrace tailWord_8317108 prefixEnd_8317108 4270674059354750510400323 := by
  unfold tailWord_8317108
  simp only [CollatzResearch.WordTrace]
  refine ⟨151674924976272819901895989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202233233301697093202527985 151674924976272819901895989)
  ·
    refine ⟨14219524216525576865802749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151674924976272819901895989 14219524216525576865802749)
    ·
      refine ⟨5332321581197091324676031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14219524216525576865802749 5332321581197091324676031)
      ·
        refine ⟨7998482371795636987014047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332321581197091324676031 7998482371795636987014047)
        ·
          refine ⟨11997723557693455480521071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998482371795636987014047 11997723557693455480521071)
          ·
            refine ⟨17996585336540183220781607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997723557693455480521071 17996585336540183220781607)
            ·
              refine ⟨26994878004810274831172411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996585336540183220781607 26994878004810274831172411)
              ·
                refine ⟨40492317007215412246758617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26994878004810274831172411 40492317007215412246758617)
                ·
                  refine ⟨30369237755411559185068963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40492317007215412246758617 30369237755411559185068963)
                  ·
                    refine ⟨45553856633117338777603445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30369237755411559185068963 45553856633117338777603445)
                    ·
                      refine ⟨4270674059354750510400323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45553856633117338777603445 4270674059354750510400323)
                      ·
                        rfl

theorem cell23_8317108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_8317108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317108 prefixEnd_8317108 := by exact prefixLift 8317108
  have htrace : WordTrace (prefixWord ++ tailWord_8317108) baseStart_8317108 baseEnd_8317108 := by
    simpa [prefixWord, tailWord_8317108, baseEnd_8317108] using wordTrace_append hprefix tailTrace_8317108
  have hstable : (prefixWord ++ tailWord_8317108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317108).length < 2 ^ (prefixWord ++ tailWord_8317108).sum := by decide
  have hdescent : baseEnd_8317108 < baseStart_8317108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317124 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_8317124 : Nat := 118140960795 + 8317124 * 2 ^ 59
def prefixEnd_8317124 : Nat := 4983230072969 + 3 ^ 40 * 8317124 * 2
def baseEnd_8317124 : Nat := 1423560758348407482600083

theorem tailTrace_8317124 : CollatzResearch.WordTrace tailWord_8317124 prefixEnd_8317124 1423560758348407482600083 := by
  unfold tailWord_8317124
  simp only [CollatzResearch.WordTrace]
  refine ⟨151675216760243837268187213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202233622346991783024249617 151675216760243837268187213)
  ·
    refine ⟨56878206285091438975570205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151675216760243837268187213 56878206285091438975570205)
    ·
      refine ⟨21329327356909289615838827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56878206285091438975570205 21329327356909289615838827)
      ·
        refine ⟨31993991035363934423758241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21329327356909289615838827 31993991035363934423758241)
        ·
          refine ⟨23995493276522950817818681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31993991035363934423758241 23995493276522950817818681)
          ·
            refine ⟨17996619957392213113364011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23995493276522950817818681 17996619957392213113364011)
            ·
              refine ⟨26994929936088319670046017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996619957392213113364011 26994929936088319670046017)
              ·
                refine ⟨20246197452066239752534513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26994929936088319670046017 20246197452066239752534513)
                ·
                  refine ⟨15184648089049679814400885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20246197452066239752534513 15184648089049679814400885)
                  ·
                    refine ⟨1423560758348407482600083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15184648089049679814400885 1423560758348407482600083)
                    ·
                      rfl

theorem cell23_8317124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_8317124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317124 prefixEnd_8317124 := by exact prefixLift 8317124
  have htrace : WordTrace (prefixWord ++ tailWord_8317124) baseStart_8317124 baseEnd_8317124 := by
    simpa [prefixWord, tailWord_8317124, baseEnd_8317124] using wordTrace_append hprefix tailTrace_8317124
  have hstable : (prefixWord ++ tailWord_8317124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317124).length < 2 ^ (prefixWord ++ tailWord_8317124).sum := by decide
  have hdescent : baseEnd_8317124 < baseStart_8317124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317164 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_8317164 : Nat := 118140960795 + 8317164 * 2 ^ 59
def prefixEnd_8317164 : Nat := 4983230072969 + 3 ^ 40 * 8317164 * 2
def baseEnd_8317164 : Nat := 4270702814271402291300065

theorem tailTrace_8317164 : CollatzResearch.WordTrace tailWord_8317164 prefixEnd_8317164 4270702814271402291300065 := by
  unfold tailWord_8317164
  simp only [CollatzResearch.WordTrace]
  refine ⟨151675946220171380683915273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202234594960228507578553697 151675946220171380683915273)
  ·
    refine ⟨113756959665128535512936455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151675946220171380683915273 113756959665128535512936455)
    ·
      refine ⟨170635439497692803269404683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113756959665128535512936455 170635439497692803269404683)
      ·
        refine ⟨255953159246539204904107025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170635439497692803269404683 255953159246539204904107025)
        ·
          refine ⟨191964869434904403678080269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255953159246539204904107025 191964869434904403678080269)
          ·
            refine ⟨71986826038089151379280101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191964869434904403678080269 71986826038089151379280101)
            ·
              refine ⟨13497529882141715883615019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71986826038089151379280101 13497529882141715883615019)
              ·
                refine ⟨20246294823212573825422529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13497529882141715883615019 20246294823212573825422529)
                ·
                  refine ⟨15184721117409430369066897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20246294823212573825422529 15184721117409430369066897)
                  ·
                    refine ⟨11388540838057072776800173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15184721117409430369066897 11388540838057072776800173)
                    ·
                      refine ⟨4270702814271402291300065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11388540838057072776800173 4270702814271402291300065)
                      ·
                        rfl

theorem cell23_8317164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_8317164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317164 prefixEnd_8317164 := by exact prefixLift 8317164
  have htrace : WordTrace (prefixWord ++ tailWord_8317164) baseStart_8317164 baseEnd_8317164 := by
    simpa [prefixWord, tailWord_8317164, baseEnd_8317164] using wordTrace_append hprefix tailTrace_8317164
  have hstable : (prefixWord ++ tailWord_8317164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317164).length < 2 ^ (prefixWord ++ tailWord_8317164).sum := by decide
  have hdescent : baseEnd_8317164 < baseStart_8317164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317188 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_8317188 : Nat := 118140960795 + 8317188 * 2 ^ 59
def prefixEnd_8317188 : Nat := 4983230072969 + 3 ^ 40 * 8317188 * 2
def baseEnd_8317188 : Nat := 1423571712602370065799985

theorem tailTrace_8317188 : CollatzResearch.WordTrace tailWord_8317188 prefixEnd_8317188 1423571712602370065799985 := by
  unfold tailWord_8317188
  simp only [CollatzResearch.WordTrace]
  refine ⟨151676383896127906733352109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202235178528170542311136145 151676383896127906733352109)
  ·
    refine ⟨56878643961047965025007041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151676383896127906733352109 56878643961047965025007041)
    ·
      refine ⟨42658982970785973768755281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56878643961047965025007041 42658982970785973768755281)
      ·
        refine ⟨31994237228089480326566461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42658982970785973768755281 31994237228089480326566461)
        ·
          refine ⟨11997838960533555122462423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31994237228089480326566461 11997838960533555122462423)
          ·
            refine ⟨17996758440800332683693635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997838960533555122462423 17996758440800332683693635)
            ·
              refine ⟨26995137661200499025540453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996758440800332683693635 26995137661200499025540453)
              ·
                refine ⟨5061588311475093567288835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26995137661200499025540453 5061588311475093567288835)
                ·
                  refine ⟨7592382467212640350933253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061588311475093567288835 7592382467212640350933253)
                  ·
                    refine ⟨1423571712602370065799985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592382467212640350933253 1423571712602370065799985)
                    ·
                      rfl

theorem cell23_8317188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_8317188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317188 prefixEnd_8317188 := by exact prefixLift 8317188
  have htrace : WordTrace (prefixWord ++ tailWord_8317188) baseStart_8317188 baseEnd_8317188 := by
    simpa [prefixWord, tailWord_8317188, baseEnd_8317188] using wordTrace_append hprefix tailTrace_8317188
  have hstable : (prefixWord ++ tailWord_8317188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317188).length < 2 ^ (prefixWord ++ tailWord_8317188).sum := by decide
  have hdescent : baseEnd_8317188 < baseStart_8317188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317221 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 1, 5, 2]
def baseStart_8317221 : Nat := 118140960795 + 8317221 * 2 ^ 59
def prefixEnd_8317221 : Nat := 4983230072969 + 3 ^ 40 * 8317221 * 2
def baseEnd_8317221 : Nat := 4270732082668708568287303

theorem tailTrace_8317221 : CollatzResearch.WordTrace tailWord_8317221 prefixEnd_8317221 4270732082668708568287303 := by
  unfold tailWord_8317221
  simp only [CollatzResearch.WordTrace]
  refine ⟨303353971401136260102655517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202235980934090840068437011 303353971401136260102655517)
  ·
    refine ⟨113757739275426097538495819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303353971401136260102655517 113757739275426097538495819)
    ·
      refine ⟨170636608913139146307743729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113757739275426097538495819 170636608913139146307743729)
      ·
        refine ⟨127977456684854359730807797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170636608913139146307743729 127977456684854359730807797)
        ·
          refine ⟨11997886564205096224763231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127977456684854359730807797 11997886564205096224763231)
          ·
            refine ⟨17996829846307644337144847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997886564205096224763231 17996829846307644337144847)
            ·
              refine ⟨26995244769461466505717271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996829846307644337144847 26995244769461466505717271)
              ·
                refine ⟨40492867154192199758575907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26995244769461466505717271 40492867154192199758575907)
                ·
                  refine ⟨60739300731288299637863861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40492867154192199758575907 60739300731288299637863861)
                  ·
                    refine ⟨5694309443558278091049737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60739300731288299637863861 5694309443558278091049737)
                    ·
                      refine ⟨4270732082668708568287303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694309443558278091049737 4270732082668708568287303)
                      ·
                        rfl

theorem cell23_8317221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_8317221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317221 prefixEnd_8317221 := by exact prefixLift 8317221
  have htrace : WordTrace (prefixWord ++ tailWord_8317221) baseStart_8317221 baseEnd_8317221 := by
    simpa [prefixWord, tailWord_8317221, baseEnd_8317221] using wordTrace_append hprefix tailTrace_8317221
  have hstable : (prefixWord ++ tailWord_8317221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317221).length < 2 ^ (prefixWord ++ tailWord_8317221).sum := by decide
  have hdescent : baseEnd_8317221 < baseStart_8317221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317244 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_8317244 : Nat := 118140960795 + 8317244 * 2 ^ 59
def prefixEnd_8317244 : Nat := 4983230072969 + 3 ^ 40 * 8317244 * 2
def baseEnd_8317244 : Nat := 1423581297574587326099899

theorem tailTrace_8317244 : CollatzResearch.WordTrace tailWord_8317244 prefixEnd_8317244 1423581297574587326099899 := by
  unfold tailWord_8317244
  simp only [CollatzResearch.WordTrace]
  refine ⟨151677405140026467515371393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202236540186701956687161857 151677405140026467515371393)
  ·
    refine ⟨113758053855019850636528545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151677405140026467515371393 113758053855019850636528545)
    ·
      refine ⟨85318540391264887977396409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113758053855019850636528545 85318540391264887977396409)
      ·
        refine ⟨63988905293448665983047307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85318540391264887977396409 63988905293448665983047307)
        ·
          refine ⟨95983357940172998974570961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63988905293448665983047307 95983357940172998974570961)
          ·
            refine ⟨71987518455129749230928221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95983357940172998974570961 71987518455129749230928221)
            ·
              refine ⟨26995319420673655961598083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71987518455129749230928221 26995319420673655961598083)
              ·
                refine ⟨40492979131010483942397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26995319420673655961598083 40492979131010483942397125)
                ·
                  refine ⟨7592433587064465739199461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40492979131010483942397125 7592433587064465739199461)
                  ·
                    refine ⟨1423581297574587326099899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592433587064465739199461 1423581297574587326099899)
                    ·
                      rfl

theorem cell23_8317244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_8317244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317244 prefixEnd_8317244 := by exact prefixLift 8317244
  have htrace : WordTrace (prefixWord ++ tailWord_8317244) baseStart_8317244 baseEnd_8317244 := by
    simpa [prefixWord, tailWord_8317244, baseEnd_8317244] using wordTrace_append hprefix tailTrace_8317244
  have hstable : (prefixWord ++ tailWord_8317244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317244).length < 2 ^ (prefixWord ++ tailWord_8317244).sum := by decide
  have hdescent : baseEnd_8317244 < baseStart_8317244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317247 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_8317247 : Nat := 118140960795 + 8317247 * 2 ^ 59
def prefixEnd_8317247 : Nat := 4983230072969 + 3 ^ 40 * 8317247 * 2
def baseEnd_8317247 : Nat := 4270745433165725466562183

theorem tailTrace_8317247 : CollatzResearch.WordTrace tailWord_8317247 prefixEnd_8317247 4270745433165725466562183 := by
  unfold tailWord_8317247
  simp only [CollatzResearch.WordTrace]
  refine ⟨303354919699042066543101995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202236613132694711028734663 303354919699042066543101995)
  ·
    refine ⟨455032379548563099814652993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303354919699042066543101995 455032379548563099814652993)
    ·
      refine ⟨341274284661422324860989745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455032379548563099814652993 341274284661422324860989745)
      ·
        refine ⟨255955713496066743645742309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341274284661422324860989745 255955713496066743645742309)
        ·
          refine ⟨47991696280512514433576683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255955713496066743645742309 47991696280512514433576683)
          ·
            refine ⟨71987544420768771650365025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47991696280512514433576683 71987544420768771650365025)
            ·
              refine ⟨53990658315576578737773769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71987544420768771650365025 53990658315576578737773769)
              ·
                refine ⟨40492993736682434053330327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53990658315576578737773769 40492993736682434053330327)
                ·
                  refine ⟨60739490605023651079995491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40492993736682434053330327 60739490605023651079995491)
                  ·
                    refine ⟨91109235907535476619993237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60739490605023651079995491 91109235907535476619993237)
                    ·
                      refine ⟨4270745433165725466562183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91109235907535476619993237 4270745433165725466562183)
                      ·
                        rfl

theorem cell23_8317247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_8317247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317247 prefixEnd_8317247 := by exact prefixLift 8317247
  have htrace : WordTrace (prefixWord ++ tailWord_8317247) baseStart_8317247 baseEnd_8317247 := by
    simpa [prefixWord, tailWord_8317247, baseEnd_8317247] using wordTrace_append hprefix tailTrace_8317247
  have hstable : (prefixWord ++ tailWord_8317247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317247).length < 2 ^ (prefixWord ++ tailWord_8317247).sum := by decide
  have hdescent : baseEnd_8317247 < baseStart_8317247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317251 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2]
def baseStart_8317251 : Nat := 118140960795 + 8317251 * 2 ^ 59
def prefixEnd_8317251 : Nat := 4983230072969 + 3 ^ 40 * 8317251 * 2
def baseEnd_8317251 : Nat := 4270747487088343450912165

theorem tailTrace_8317251 : CollatzResearch.WordTrace tailWord_8317251 prefixEnd_8317251 4270747487088343450912165 := by
  unfold tailWord_8317251
  simp only [CollatzResearch.WordTrace]
  refine ⟨303355065591027575226247607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202236710394018383484165071 303355065591027575226247607)
  ·
    refine ⟨455032598386541362839371411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303355065591027575226247607 455032598386541362839371411)
    ·
      refine ⟨682548897579812044259057117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455032598386541362839371411 682548897579812044259057117)
      ·
        refine ⟨255955836592429516597146419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682548897579812044259057117 255955836592429516597146419)
        ·
          refine ⟨383933754888644274895719629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255955836592429516597146419 383933754888644274895719629)
          ·
            refine ⟨143975158083241603085894861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383933754888644274895719629 143975158083241603085894861)
            ·
              refine ⟨53990684281215601157210573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143975158083241603085894861 53990684281215601157210573)
              ·
                refine ⟨20246506605455850433953965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53990684281215601157210573 20246506605455850433953965)
                ·
                  refine ⟨7592439977045943912732737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20246506605455850433953965 7592439977045943912732737)
                  ·
                    refine ⟨5694329982784457934549553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592439977045943912732737 5694329982784457934549553)
                    ·
                      refine ⟨4270747487088343450912165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694329982784457934549553 4270747487088343450912165)
                      ·
                        rfl

theorem cell23_8317251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_8317251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317251 prefixEnd_8317251 := by exact prefixLift 8317251
  have htrace : WordTrace (prefixWord ++ tailWord_8317251) baseStart_8317251 baseEnd_8317251 := by
    simpa [prefixWord, tailWord_8317251, baseEnd_8317251] using wordTrace_append hprefix tailTrace_8317251
  have hstable : (prefixWord ++ tailWord_8317251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317251).length < 2 ^ (prefixWord ++ tailWord_8317251).sum := by decide
  have hdescent : baseEnd_8317251 < baseStart_8317251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317264 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_8317264 : Nat := 118140960795 + 8317264 * 2 ^ 59
def prefixEnd_8317264 : Nat := 4983230072969 + 3 ^ 40 * 8317264 * 2
def baseEnd_8317264 : Nat := 4270754162336851900049605

theorem tailTrace_8317264 : CollatzResearch.WordTrace tailWord_8317264 prefixEnd_8317264 4270754162336851900049605 := by
  unfold tailWord_8317264
  simp only [CollatzResearch.WordTrace]
  refine ⟨151677769869990239223235423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202237026493320318964313897 151677769869990239223235423)
  ·
    refine ⟨227516654804985358834853135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151677769869990239223235423 227516654804985358834853135)
    ·
      refine ⟨341274982207478038252279703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227516654804985358834853135 341274982207478038252279703)
      ·
        refine ⟨511912473311217057378419555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341274982207478038252279703 511912473311217057378419555)
        ·
          refine ⟨767868709966825586067629333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511912473311217057378419555 767868709966825586067629333)
          ·
            refine ⟨35993845779694949346920125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 767868709966825586067629333 35993845779694949346920125)
            ·
              refine ⟨13497692167385606005095047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35993845779694949346920125 13497692167385606005095047)
              ·
                refine ⟨20246538251078409007642571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13497692167385606005095047 20246538251078409007642571)
                ·
                  refine ⟨30369807376617613511463857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20246538251078409007642571 30369807376617613511463857)
                  ·
                    refine ⟨22777355532463210133597893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30369807376617613511463857 22777355532463210133597893)
                    ·
                      refine ⟨4270754162336851900049605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22777355532463210133597893 4270754162336851900049605)
                      ·
                        rfl

theorem cell23_8317264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_8317264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317264 prefixEnd_8317264 := by exact prefixLift 8317264
  have htrace : WordTrace (prefixWord ++ tailWord_8317264) baseStart_8317264 baseEnd_8317264 := by
    simpa [prefixWord, tailWord_8317264, baseEnd_8317264] using wordTrace_append hprefix tailTrace_8317264
  have hstable : (prefixWord ++ tailWord_8317264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317264).length < 2 ^ (prefixWord ++ tailWord_8317264).sum := by decide
  have hdescent : baseEnd_8317264 < baseStart_8317264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317268 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_8317268 : Nat := 118140960795 + 8317268 * 2 ^ 59
def prefixEnd_8317268 : Nat := 4983230072969 + 3 ^ 40 * 8317268 * 2
def baseEnd_8317268 : Nat := 4270756216259469884399587

theorem tailTrace_8317268 : CollatzResearch.WordTrace tailWord_8317268 prefixEnd_8317268 4270756216259469884399587 := by
  unfold tailWord_8317268
  simp only [CollatzResearch.WordTrace]
  refine ⟨151677842815982993564808229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202237123754643991419744305 151677842815982993564808229)
  ·
    refine ⟨28439595527996811293401543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151677842815982993564808229 28439595527996811293401543)
    ·
      refine ⟨42659393291995216940102315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28439595527996811293401543 42659393291995216940102315)
      ·
        refine ⟨63989089937992825410153473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42659393291995216940102315 63989089937992825410153473)
        ·
          refine ⟨47991817453494619057615105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63989089937992825410153473 47991817453494619057615105)
          ·
            refine ⟨35993863090120964293211329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47991817453494619057615105 35993863090120964293211329)
            ·
              refine ⟨26995397317590723219908497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35993863090120964293211329 26995397317590723219908497)
              ·
                refine ⟨20246547988193042414931373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26995397317590723219908497 20246547988193042414931373)
                ·
                  refine ⟨7592455495572390905599265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20246547988193042414931373 7592455495572390905599265)
                  ·
                    refine ⟨5694341621679293179199449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592455495572390905599265 5694341621679293179199449)
                    ·
                      refine ⟨4270756216259469884399587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694341621679293179199449 4270756216259469884399587)
                      ·
                        rfl

theorem cell23_8317268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_8317268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317268 prefixEnd_8317268 := by exact prefixLift 8317268
  have htrace : WordTrace (prefixWord ++ tailWord_8317268) baseStart_8317268 baseEnd_8317268 := by
    simpa [prefixWord, tailWord_8317268, baseEnd_8317268] using wordTrace_append hprefix tailTrace_8317268
  have hstable : (prefixWord ++ tailWord_8317268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317268).length < 2 ^ (prefixWord ++ tailWord_8317268).sum := by decide
  have hdescent : baseEnd_8317268 < baseStart_8317268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317271 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_8317271 : Nat := 118140960795 + 8317271 * 2 ^ 59
def prefixEnd_8317271 : Nat := 4983230072969 + 3 ^ 40 * 8317271 * 2
def baseEnd_8317271 : Nat := 4270757756701433372662073

theorem tailTrace_8317271 : CollatzResearch.WordTrace tailWord_8317271 prefixEnd_8317271 4270757756701433372662073 := by
  unfold tailWord_8317271
  simp only [CollatzResearch.WordTrace]
  refine ⟨303355795050955118641975667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202237196700636745761317111 303355795050955118641975667)
  ·
    refine ⟨455033692576432677962963501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303355795050955118641975667 455033692576432677962963501)
    ·
      refine ⟨170637634716162254236111313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455033692576432677962963501 170637634716162254236111313)
      ·
        refine ⟨127978226037121690677083485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170637634716162254236111313 127978226037121690677083485)
        ·
          refine ⟨47991834763920634003906307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127978226037121690677083485 47991834763920634003906307)
          ·
            refine ⟨71987752145880951005859461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47991834763920634003906307 71987752145880951005859461)
            ·
              refine ⟨13497703527352678313598649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71987752145880951005859461 13497703527352678313598649)
              ·
                refine ⟨10123277645514508735198987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13497703527352678313598649 10123277645514508735198987)
                ·
                  refine ⟨15184916468271763102798481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123277645514508735198987 15184916468271763102798481)
                  ·
                    refine ⟨11388687351203822327098861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15184916468271763102798481 11388687351203822327098861)
                    ·
                      refine ⟨4270757756701433372662073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11388687351203822327098861 4270757756701433372662073)
                      ·
                        rfl

theorem cell23_8317271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_8317271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317271 prefixEnd_8317271 := by exact prefixLift 8317271
  have htrace : WordTrace (prefixWord ++ tailWord_8317271) baseStart_8317271 baseEnd_8317271 := by
    simpa [prefixWord, tailWord_8317271, baseEnd_8317271] using wordTrace_append hprefix tailTrace_8317271
  have hstable : (prefixWord ++ tailWord_8317271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317271).length < 2 ^ (prefixWord ++ tailWord_8317271).sum := by decide
  have hdescent : baseEnd_8317271 < baseStart_8317271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317284 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_8317284 : Nat := 118140960795 + 8317284 * 2 ^ 59
def prefixEnd_8317284 : Nat := 4983230072969 + 3 ^ 40 * 8317284 * 2
def baseEnd_8317284 : Nat := 4270764431949941821799513

theorem tailTrace_8317284 : CollatzResearch.WordTrace tailWord_8317284 prefixEnd_8317284 4270764431949941821799513 := by
  unfold tailWord_8317284
  simp only [CollatzResearch.WordTrace]
  refine ⟨151678134599954010931099453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202237512799938681241465937 151678134599954010931099453)
  ·
    refine ⟨56879300474982754099162295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151678134599954010931099453 56879300474982754099162295)
    ·
      refine ⟨85318950712474131148743443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56879300474982754099162295 85318950712474131148743443)
      ·
        refine ⟨127978426068711196723115165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85318950712474131148743443 127978426068711196723115165)
        ·
          refine ⟨47991909775766698771168187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127978426068711196723115165 47991909775766698771168187)
          ·
            refine ⟨71987864663650048156752281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47991909775766698771168187 71987864663650048156752281)
            ·
              refine ⟨53990898497737536117564211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71987864663650048156752281 53990898497737536117564211)
              ·
                refine ⟨80986347746606304176346317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53990898497737536117564211 80986347746606304176346317)
                ·
                  refine ⟨30369880404977364066129869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80986347746606304176346317 30369880404977364066129869)
                  ·
                    refine ⟨11388705151866511524798701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30369880404977364066129869 11388705151866511524798701)
                    ·
                      refine ⟨4270764431949941821799513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11388705151866511524798701 4270764431949941821799513)
                      ·
                        rfl

theorem cell23_8317284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_8317284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317284 prefixEnd_8317284 := by exact prefixLift 8317284
  have htrace : WordTrace (prefixWord ++ tailWord_8317284) baseStart_8317284 baseEnd_8317284 := by
    simpa [prefixWord, tailWord_8317284, baseEnd_8317284] using wordTrace_append hprefix tailTrace_8317284
  have hstable : (prefixWord ++ tailWord_8317284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317284).length < 2 ^ (prefixWord ++ tailWord_8317284).sum := by decide
  have hdescent : baseEnd_8317284 < baseStart_8317284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317285 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 1, 2, 2]
def baseStart_8317285 : Nat := 118140960795 + 8317285 * 2 ^ 59
def prefixEnd_8317285 : Nat := 4983230072969 + 3 ^ 40 * 8317285 * 2
def baseEnd_8317285 : Nat := 4270764945430596317887009

theorem tailTrace_8317285 : CollatzResearch.WordTrace tailWord_8317285 prefixEnd_8317285 4270764945430596317887009 := by
  unfold tailWord_8317285
  simp only [CollatzResearch.WordTrace]
  refine ⟨303356305672904399032985309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202237537115269599355323539 303356305672904399032985309)
  ·
    refine ⟨113758614627339149637369491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303356305672904399032985309 113758614627339149637369491)
    ·
      refine ⟨170637921941008724456054237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113758614627339149637369491 170637921941008724456054237)
      ·
        refine ⟨63989220727878271671020339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170637921941008724456054237 63989220727878271671020339)
        ·
          refine ⟨95983831091817407506530509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63989220727878271671020339 95983831091817407506530509)
          ·
            refine ⟨35993936659431527814948941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95983831091817407506530509 35993936659431527814948941)
            ·
              refine ⟨13497726247286822930605853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35993936659431527814948941 13497726247286822930605853)
              ·
                refine ⟨5061647342732558598977195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13497726247286822930605853 5061647342732558598977195)
                ·
                  refine ⟨7592471014098837898465793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061647342732558598977195 7592471014098837898465793)
                  ·
                    refine ⟨5694353260574128423849345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592471014098837898465793 5694353260574128423849345)
                    ·
                      refine ⟨4270764945430596317887009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694353260574128423849345 4270764945430596317887009)
                      ·
                        rfl

theorem cell23_8317285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_8317285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317285 prefixEnd_8317285 := by exact prefixLift 8317285
  have htrace : WordTrace (prefixWord ++ tailWord_8317285) baseStart_8317285 baseEnd_8317285 := by
    simpa [prefixWord, tailWord_8317285, baseEnd_8317285] using wordTrace_append hprefix tailTrace_8317285
  have hstable : (prefixWord ++ tailWord_8317285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317285).length < 2 ^ (prefixWord ++ tailWord_8317285).sum := by decide
  have hdescent : baseEnd_8317285 < baseStart_8317285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317297 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_8317297 : Nat := 118140960795 + 8317297 * 2 ^ 59
def prefixEnd_8317297 : Nat := 4983230072969 + 3 ^ 40 * 8317297 * 2
def baseEnd_8317297 : Nat := 4270771107198450270936953

theorem tailTrace_8317297 : CollatzResearch.WordTrace tailWord_8317297 prefixEnd_8317297 4270771107198450270936953 := by
  unfold tailWord_8317297
  simp only [CollatzResearch.WordTrace]
  refine ⟨303356743348860925082422145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202237828899240616721614763 303356743348860925082422145)
  ·
    refine ⟨227517557511645693811816609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303356743348860925082422145 227517557511645693811816609)
    ·
      refine ⟨170638168133734270358862457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227517557511645693811816609 170638168133734270358862457)
      ·
        refine ⟨127978626100300702769146843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170638168133734270358862457 127978626100300702769146843)
        ·
          refine ⟨191967939150451054153720265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127978626100300702769146843 191967939150451054153720265)
          ·
            refine ⟨143975954362838290615290199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191967939150451054153720265 143975954362838290615290199)
            ·
              refine ⟨215963931544257435922935299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143975954362838290615290199 215963931544257435922935299)
              ·
                refine ⟨323945897316386153884402949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215963931544257435922935299 323945897316386153884402949)
                ·
                  refine ⟨60739855746822403853325553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323945897316386153884402949 60739855746822403853325553)
                  ·
                    refine ⟨45554891810116802889994165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60739855746822403853325553 45554891810116802889994165)
                    ·
                      refine ⟨4270771107198450270936953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45554891810116802889994165 4270771107198450270936953)
                      ·
                        rfl

theorem cell23_8317297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_8317297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317297 prefixEnd_8317297 := by exact prefixLift 8317297
  have htrace : WordTrace (prefixWord ++ tailWord_8317297) baseStart_8317297 baseEnd_8317297 := by
    simpa [prefixWord, tailWord_8317297, baseEnd_8317297] using wordTrace_append hprefix tailTrace_8317297
  have hstable : (prefixWord ++ tailWord_8317297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317297).length < 2 ^ (prefixWord ++ tailWord_8317297).sum := by decide
  have hdescent : baseEnd_8317297 < baseStart_8317297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317317 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_8317317 : Nat := 118140960795 + 8317317 * 2 ^ 59
def prefixEnd_8317317 : Nat := 4983230072969 + 3 ^ 40 * 8317317 * 2
def baseEnd_8317317 : Nat := 1423593792270513397562287

theorem tailTrace_8317317 : CollatzResearch.WordTrace tailWord_8317317 prefixEnd_8317317 1423593792270513397562287 := by
  unfold tailWord_8317317
  simp only [CollatzResearch.WordTrace]
  refine ⟨303357472808788468498150205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202238315205858978998766803 303357472808788468498150205)
  ·
    refine ⟨113759052303295675686806327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303357472808788468498150205 113759052303295675686806327)
    ·
      refine ⟨170638578454943513530209491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113759052303295675686806327 170638578454943513530209491)
      ·
        refine ⟨255957867682415270295314237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170638578454943513530209491 255957867682415270295314237)
        ·
          refine ⟨95984200380905726360742839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255957867682415270295314237 95984200380905726360742839)
          ·
            refine ⟨143976300571358589541114259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95984200380905726360742839 143976300571358589541114259)
            ·
              refine ⟨215964450857037884311671389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143976300571358589541114259 215964450857037884311671389)
              ·
                refine ⟨80986669071389206616876771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215964450857037884311671389 80986669071389206616876771)
                ·
                  refine ⟨121480003607083809925315157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80986669071389206616876771 121480003607083809925315157)
                  ·
                    refine ⟨1423593792270513397562287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121480003607083809925315157 1423593792270513397562287)
                    ·
                      rfl

theorem cell23_8317317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_8317317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317317 prefixEnd_8317317 := by exact prefixLift 8317317
  have htrace : WordTrace (prefixWord ++ tailWord_8317317) baseStart_8317317 baseEnd_8317317 := by
    simpa [prefixWord, tailWord_8317317, baseEnd_8317317] using wordTrace_append hprefix tailTrace_8317317
  have hstable : (prefixWord ++ tailWord_8317317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317317).length < 2 ^ (prefixWord ++ tailWord_8317317).sum := by decide
  have hdescent : baseEnd_8317317 < baseStart_8317317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317322 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_8317322 : Nat := 118140960795 + 8317322 * 2 ^ 59
def prefixEnd_8317322 : Nat := 4983230072969 + 3 ^ 40 * 8317322 * 2
def baseEnd_8317322 : Nat := 4270783944214812673124339

theorem tailTrace_8317322 : CollatzResearch.WordTrace tailWord_8317322 prefixEnd_8317322 4270783944214812673124339 := by
  unfold tailWord_8317322
  simp only [CollatzResearch.WordTrace]
  refine ⟨75839413793442588588020555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202238436782513569568054813 75839413793442588588020555)
  ·
    refine ⟨113759120690163882882030833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75839413793442588588020555 113759120690163882882030833)
    ·
      refine ⟨85319340517622912161523125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113759120690163882882030833 85319340517622912161523125)
      ·
        refine ⟨7998688173527148015142793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85319340517622912161523125 7998688173527148015142793)
        ·
          refine ⟨5999016130145361011357095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7998688173527148015142793 5999016130145361011357095)
          ·
            refine ⟨8998524195218041517035643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999016130145361011357095 8998524195218041517035643)
            ·
              refine ⟨13497786292827062275553465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8998524195218041517035643 13497786292827062275553465)
              ·
                refine ⟨10123339719620296706665099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13497786292827062275553465 10123339719620296706665099)
                ·
                  refine ⟨15185009579430445059997649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123339719620296706665099 15185009579430445059997649)
                  ·
                    refine ⟨11388757184572833794998237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15185009579430445059997649 11388757184572833794998237)
                    ·
                      refine ⟨4270783944214812673124339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11388757184572833794998237 4270783944214812673124339)
                      ·
                        rfl

theorem cell23_8317322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_8317322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317322 prefixEnd_8317322 := by exact prefixLift 8317322
  have htrace : WordTrace (prefixWord ++ tailWord_8317322) baseStart_8317322 baseEnd_8317322 := by
    simpa [prefixWord, tailWord_8317322, baseEnd_8317322] using wordTrace_append hprefix tailTrace_8317322
  have hstable : (prefixWord ++ tailWord_8317322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317322).length < 2 ^ (prefixWord ++ tailWord_8317322).sum := by decide
  have hdescent : baseEnd_8317322 < baseStart_8317322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317344 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_8317344 : Nat := 118140960795 + 8317344 * 2 ^ 59
def prefixEnd_8317344 : Nat := 4983230072969 + 3 ^ 40 * 8317344 * 2
def baseEnd_8317344 : Nat := 4270795240789211587049237

theorem tailTrace_8317344 : CollatzResearch.WordTrace tailWord_8317344 prefixEnd_8317344 4270795240789211587049237 := by
  unfold tailWord_8317344
  simp only [CollatzResearch.WordTrace]
  refine ⟨151679228789845326054691543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202238971719793768072922057 151679228789845326054691543)
  ·
    refine ⟨227518843184767989082037315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151679228789845326054691543 227518843184767989082037315)
    ·
      refine ⟨341278264777151983623055973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227518843184767989082037315 341278264777151983623055973)
      ·
        refine ⟨63989674645715996929322995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341278264777151983623055973 63989674645715996929322995)
        ·
          refine ⟨95984511968573995393984493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63989674645715996929322995 95984511968573995393984493)
          ·
            refine ⟨35994191988215248272744185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95984511968573995393984493 35994191988215248272744185)
            ·
              refine ⟨26995643991161436204558139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35994191988215248272744185 26995643991161436204558139)
              ·
                refine ⟨40493465986742154306837209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26995643991161436204558139 40493465986742154306837209)
                ·
                  refine ⟨30370099490056615730127907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40493465986742154306837209 30370099490056615730127907)
                  ·
                    refine ⟨45555149235084923595191861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30370099490056615730127907 45555149235084923595191861)
                    ·
                      refine ⟨4270795240789211587049237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45555149235084923595191861 4270795240789211587049237)
                      ·
                        rfl

theorem cell23_8317344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_8317344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317344 prefixEnd_8317344 := by exact prefixLift 8317344
  have htrace : WordTrace (prefixWord ++ tailWord_8317344) baseStart_8317344 baseEnd_8317344 := by
    simpa [prefixWord, tailWord_8317344, baseEnd_8317344] using wordTrace_append hprefix tailTrace_8317344
  have hstable : (prefixWord ++ tailWord_8317344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317344).length < 2 ^ (prefixWord ++ tailWord_8317344).sum := by decide
  have hdescent : baseEnd_8317344 < baseStart_8317344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317451 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 3]
def baseStart_8317451 : Nat := 118140960795 + 8317451 * 2 ^ 59
def prefixEnd_8317451 : Nat := 4983230072969 + 3 ^ 40 * 8317451 * 2
def baseEnd_8317451 : Nat := 4270850183219242668411245

theorem tailTrace_8317451 : CollatzResearch.WordTrace tailWord_8317451 prefixEnd_8317451 4270850183219242668411245 := by
  unfold tailWord_8317451
  simp only [CollatzResearch.WordTrace]
  refine ⟨303362360190303009383528207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202241573460202006255685471 303362360190303009383528207)
  ·
    refine ⟨455043540285454514075292311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303362360190303009383528207 455043540285454514075292311)
    ·
      refine ⟨682565310428181771112938467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455043540285454514075292311 682565310428181771112938467)
      ·
        refine ⟨1023847965642272656669407701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682565310428181771112938467 1023847965642272656669407701)
        ·
          refine ⟨23996436694740765390689243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1023847965642272656669407701 23996436694740765390689243)
          ·
            refine ⟨35994655042111148086033865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23996436694740765390689243 35994655042111148086033865)
            ·
              refine ⟨26995991281583361064525399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35994655042111148086033865 26995991281583361064525399)
              ·
                refine ⟨40493986922375041596788099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26995991281583361064525399 40493986922375041596788099)
                ·
                  refine ⟨60740980383562562395182149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40493986922375041596788099 60740980383562562395182149)
                  ·
                    refine ⟨11388933821917980449096653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60740980383562562395182149 11388933821917980449096653)
                    ·
                      refine ⟨4270850183219242668411245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11388933821917980449096653 4270850183219242668411245)
                      ·
                        rfl

theorem cell23_8317451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 3].length) (baseStart_8317451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317451 prefixEnd_8317451 := by exact prefixLift 8317451
  have htrace : WordTrace (prefixWord ++ tailWord_8317451) baseStart_8317451 baseEnd_8317451 := by
    simpa [prefixWord, tailWord_8317451, baseEnd_8317451] using wordTrace_append hprefix tailTrace_8317451
  have hstable : (prefixWord ++ tailWord_8317451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317451).length < 2 ^ (prefixWord ++ tailWord_8317451).sum := by decide
  have hdescent : baseEnd_8317451 < baseStart_8317451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317468 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_8317468 : Nat := 118140960795 + 8317468 * 2 ^ 59
def prefixEnd_8317468 : Nat := 4983230072969 + 3 ^ 40 * 8317468 * 2
def baseEnd_8317468 : Nat := 4270858912390369101898667

theorem tailTrace_8317468 : CollatzResearch.WordTrace tailWord_8317468 prefixEnd_8317468 4270858912390369101898667 := by
  unfold tailWord_8317468
  simp only [CollatzResearch.WordTrace]
  refine ⟨151681490115620710643448529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202241986820827614191264705 151681490115620710643448529)
  ·
    refine ⟨113761117586715532982586397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151681490115620710643448529 113761117586715532982586397)
    ·
      refine ⟨42660419095018324868469899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113761117586715532982586397 42660419095018324868469899)
      ·
        refine ⟨63990628642527487302704849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42660419095018324868469899 63990628642527487302704849)
        ·
          refine ⟨47992971481895615477028637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63990628642527487302704849 47992971481895615477028637)
          ·
            refine ⟨17997364305710855803885739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47992971481895615477028637 17997364305710855803885739)
            ·
              refine ⟨26996046458566283705828609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17997364305710855803885739 26996046458566283705828609)
              ·
                refine ⟨20247034843924712779371457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26996046458566283705828609 20247034843924712779371457)
                ·
                  refine ⟨15185276132943534584528593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20247034843924712779371457 15185276132943534584528593)
                  ·
                    refine ⟨11388957099707650938396445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15185276132943534584528593 11388957099707650938396445)
                    ·
                      refine ⟨4270858912390369101898667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11388957099707650938396445 4270858912390369101898667)
                      ·
                        rfl

theorem cell23_8317468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_8317468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317468 prefixEnd_8317468 := by exact prefixLift 8317468
  have htrace : WordTrace (prefixWord ++ tailWord_8317468) baseStart_8317468 baseEnd_8317468 := by
    simpa [prefixWord, tailWord_8317468, baseEnd_8317468] using wordTrace_append hprefix tailTrace_8317468
  have hstable : (prefixWord ++ tailWord_8317468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317468).length < 2 ^ (prefixWord ++ tailWord_8317468).sum := by decide
  have hdescent : baseEnd_8317468 < baseStart_8317468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317502 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_8317502 : Nat := 118140960795 + 8317502 * 2 ^ 59
def prefixEnd_8317502 : Nat := 4983230072969 + 3 ^ 40 * 8317502 * 2
def baseEnd_8317502 : Nat := 4270876370732621968873511

theorem tailTrace_8317502 : CollatzResearch.WordTrace tailWord_8317502 prefixEnd_8317502 4270876370732621968873511 := by
  unfold tailWord_8317502
  simp only [CollatzResearch.WordTrace]
  refine ⟨37920527539139780636704345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202242813542078830062423173 37920527539139780636704345)
  ·
    refine ⟨28440395654354835477528259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37920527539139780636704345 28440395654354835477528259)
    ·
      refine ⟨42660593481532253216292389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28440395654354835477528259 42660593481532253216292389)
      ·
        refine ⟨7998861277787297478054823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42660593481532253216292389 7998861277787297478054823)
        ·
          refine ⟨11998291916680946217082235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998861277787297478054823 11998291916680946217082235)
          ·
            refine ⟨17997437875021419325623353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11998291916680946217082235 17997437875021419325623353)
            ·
              refine ⟨13498078406266064494217515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17997437875021419325623353 13498078406266064494217515)
              ·
                refine ⟨20247117609399096741326273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13498078406266064494217515 20247117609399096741326273)
                ·
                  refine ⟨15185338207049322555994705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20247117609399096741326273 15185338207049322555994705)
                  ·
                    refine ⟨11389003655286991916996029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15185338207049322555994705 11389003655286991916996029)
                    ·
                      refine ⟨4270876370732621968873511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11389003655286991916996029 4270876370732621968873511)
                      ·
                        rfl

theorem cell23_8317502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_8317502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317502 prefixEnd_8317502 := by exact prefixLift 8317502
  have htrace : WordTrace (prefixWord ++ tailWord_8317502) baseStart_8317502 baseEnd_8317502 := by
    simpa [prefixWord, tailWord_8317502, baseEnd_8317502] using wordTrace_append hprefix tailTrace_8317502
  have hstable : (prefixWord ++ tailWord_8317502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317502).length < 2 ^ (prefixWord ++ tailWord_8317502).sum := by decide
  have hdescent : baseEnd_8317502 < baseStart_8317502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317548 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_8317548 : Nat := 118140960795 + 8317548 * 2 ^ 59
def prefixEnd_8317548 : Nat := 4983230072969 + 3 ^ 40 * 8317548 * 2
def baseEnd_8317548 : Nat := 1423633330280909596299433

theorem tailTrace_8317548 : CollatzResearch.WordTrace tailWord_8317548 prefixEnd_8317548 1423633330280909596299433 := by
  unfold tailWord_8317548
  simp only [CollatzResearch.WordTrace]
  refine ⟨151682949035475797474904649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202243932047301063299872865 151682949035475797474904649)
  ·
    refine ⟨113762211776606848106178487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151682949035475797474904649 113762211776606848106178487)
    ·
      refine ⟨170643317664910272159267731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113762211776606848106178487 170643317664910272159267731)
      ·
        refine ⟨255964976497365408238901597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170643317664910272159267731 255964976497365408238901597)
        ·
          refine ⟨95986866186512028089588099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255964976497365408238901597 95986866186512028089588099)
          ·
            refine ⟨143980299279768042134382149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95986866186512028089588099 143980299279768042134382149)
            ·
              refine ⟨26996306114956507900196653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143980299279768042134382149 26996306114956507900196653)
              ·
                refine ⟨10123614793108690462573745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26996306114956507900196653 10123614793108690462573745)
                ·
                  refine ⟨7592711094831517846930309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10123614793108690462573745 7592711094831517846930309)
                  ·
                    refine ⟨1423633330280909596299433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592711094831517846930309 1423633330280909596299433)
                    ·
                      rfl

theorem cell23_8317548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_8317548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317548 prefixEnd_8317548 := by exact prefixLift 8317548
  have htrace : WordTrace (prefixWord ++ tailWord_8317548) baseStart_8317548 baseEnd_8317548 := by
    simpa [prefixWord, tailWord_8317548, baseEnd_8317548] using wordTrace_append hprefix tailTrace_8317548
  have hstable : (prefixWord ++ tailWord_8317548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317548).length < 2 ^ (prefixWord ++ tailWord_8317548).sum := by decide
  have hdescent : baseEnd_8317548 < baseStart_8317548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317551 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_8317551 : Nat := 118140960795 + 8317551 * 2 ^ 59
def prefixEnd_8317551 : Nat := 4983230072969 + 3 ^ 40 * 8317551 * 2
def baseEnd_8317551 : Nat := 4270901531284692277160785

theorem tailTrace_8317551 : CollatzResearch.WordTrace tailWord_8317551 prefixEnd_8317551 4270901531284692277160785 := by
  unfold tailWord_8317551
  simp only [CollatzResearch.WordTrace]
  refine ⟨303366007489940726462168507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202244004993293817641445671 303366007489940726462168507)
  ·
    refine ⟨455049011234911089693252761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303366007489940726462168507 455049011234911089693252761)
    ·
      refine ⟨341286758426183317269939571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455049011234911089693252761 341286758426183317269939571)
      ·
        refine ⟨511930137639274975904909357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341286758426183317269939571 511930137639274975904909357)
        ·
          refine ⟨191973801614728115964341009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511930137639274975904909357 191973801614728115964341009)
          ·
            refine ⟨143980351211046086973255757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191973801614728115964341009 143980351211046086973255757)
            ·
              refine ⟨53992631704142282614970909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143980351211046086973255757 53992631704142282614970909)
              ·
                refine ⟨20247236889053355980614091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53992631704142282614970909 20247236889053355980614091)
                ·
                  refine ⟨30370855333580033970921137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20247236889053355980614091 30370855333580033970921137)
                  ·
                    refine ⟨22778141500185025478190853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30370855333580033970921137 22778141500185025478190853)
                    ·
                      refine ⟨4270901531284692277160785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22778141500185025478190853 4270901531284692277160785)
                      ·
                        rfl

theorem cell23_8317551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_8317551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317551 prefixEnd_8317551 := by exact prefixLift 8317551
  have htrace : WordTrace (prefixWord ++ tailWord_8317551) baseStart_8317551 baseEnd_8317551 := by
    simpa [prefixWord, tailWord_8317551, baseEnd_8317551] using wordTrace_append hprefix tailTrace_8317551
  have hstable : (prefixWord ++ tailWord_8317551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317551).length < 2 ^ (prefixWord ++ tailWord_8317551).sum := by decide
  have hdescent : baseEnd_8317551 < baseStart_8317551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317572 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_8317572 : Nat := 118140960795 + 8317572 * 2 ^ 59
def prefixEnd_8317572 : Nat := 4983230072969 + 3 ^ 40 * 8317572 * 2
def baseEnd_8317572 : Nat := 4270912314378436694998189

theorem tailTrace_8317572 : CollatzResearch.WordTrace tailWord_8317572 prefixEnd_8317572 4270912314378436694998189 := by
  unfold tailWord_8317572
  simp only [CollatzResearch.WordTrace]
  refine ⟨151683386711432323524341485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202244515615243098032455313 151683386711432323524341485)
  ·
    refine ⟨56881270016787121321628057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151683386711432323524341485 56881270016787121321628057)
    ·
      refine ⟨42660952512590340991221043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56881270016787121321628057 42660952512590340991221043)
      ·
        refine ⟨63991428768885511486831565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42660952512590340991221043 63991428768885511486831565)
        ·
          refine ⟨23996785788332066807561837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63991428768885511486831565 23996785788332066807561837)
          ·
            refine ⟨8998794670624525052835689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23996785788332066807561837 8998794670624525052835689)
            ·
              refine ⟨6749096002968393789626767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8998794670624525052835689 6749096002968393789626767)
              ·
                refine ⟨10123644004452590684440151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749096002968393789626767 10123644004452590684440151)
                ·
                  refine ⟨15185466006678886026660227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123644004452590684440151 15185466006678886026660227)
                  ·
                    refine ⟨22778199010018329039990341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15185466006678886026660227 22778199010018329039990341)
                    ·
                      refine ⟨4270912314378436694998189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22778199010018329039990341 4270912314378436694998189)
                      ·
                        rfl

theorem cell23_8317572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_8317572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317572 prefixEnd_8317572 := by exact prefixLift 8317572
  have htrace : WordTrace (prefixWord ++ tailWord_8317572) baseStart_8317572 baseEnd_8317572 := by
    simpa [prefixWord, tailWord_8317572, baseEnd_8317572] using wordTrace_append hprefix tailTrace_8317572
  have hstable : (prefixWord ++ tailWord_8317572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317572).length < 2 ^ (prefixWord ++ tailWord_8317572).sum := by decide
  have hdescent : baseEnd_8317572 < baseStart_8317572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317615 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 1, 3, 2]
def baseStart_8317615 : Nat := 118140960795 + 8317615 * 2 ^ 59
def prefixEnd_8317615 : Nat := 4983230072969 + 3 ^ 40 * 8317615 * 2
def baseEnd_8317615 : Nat := 4270934394046580026760491

theorem tailTrace_8317615 : CollatzResearch.WordTrace tailWord_8317615 prefixEnd_8317615 4270934394046580026760491 := by
  unfold tailWord_8317615
  simp only [CollatzResearch.WordTrace]
  refine ⟨303368341761708865392498299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202245561174472576928332199 303368341761708865392498299)
  ·
    refine ⟨455052512642563298088747449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303368341761708865392498299 455052512642563298088747449)
    ·
      refine ⟨341289384481922473566560587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455052512642563298088747449 341289384481922473566560587)
      ·
        refine ⟨511934076722883710349840881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341289384481922473566560587 511934076722883710349840881)
        ·
          refine ⟨383950557542162782762380661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511934076722883710349840881 383950557542162782762380661)
          ·
            refine ⟨35995364769577760883973187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383950557542162782762380661 35995364769577760883973187)
            ·
              refine ⟨53993047154366641325959781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35995364769577760883973187 53993047154366641325959781)
              ·
                refine ⟨10123696341443745248617459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53993047154366641325959781 10123696341443745248617459)
                ·
                  refine ⟨15185544512165617872926189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123696341443745248617459 15185544512165617872926189)
                  ·
                    refine ⟨5694579192062106702347321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15185544512165617872926189 5694579192062106702347321)
                    ·
                      refine ⟨4270934394046580026760491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694579192062106702347321 4270934394046580026760491)
                      ·
                        rfl

theorem cell23_8317615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 3, 2].length) (baseStart_8317615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317615 prefixEnd_8317615 := by exact prefixLift 8317615
  have htrace : WordTrace (prefixWord ++ tailWord_8317615) baseStart_8317615 baseEnd_8317615 := by
    simpa [prefixWord, tailWord_8317615, baseEnd_8317615] using wordTrace_append hprefix tailTrace_8317615
  have hstable : (prefixWord ++ tailWord_8317615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317615).length < 2 ^ (prefixWord ++ tailWord_8317615).sum := by decide
  have hdescent : baseEnd_8317615 < baseStart_8317615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317631 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_8317631 : Nat := 118140960795 + 8317631 * 2 ^ 59
def prefixEnd_8317631 : Nat := 4983230072969 + 3 ^ 40 * 8317631 * 2
def baseEnd_8317631 : Nat := 4270942609737051964160417

theorem tailTrace_8317631 : CollatzResearch.WordTrace tailWord_8317631 prefixEnd_8317631 4270942609737051964160417 := by
  unfold tailWord_8317631
  simp only [CollatzResearch.WordTrace]
  refine ⟨303368925329650900125080747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202245950219767266750053831 303368925329650900125080747)
  ·
    refine ⟨455053387994476350187621121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303368925329650900125080747 455053387994476350187621121)
    ·
      refine ⟨341290040995857262640715841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455053387994476350187621121 341290040995857262640715841)
      ·
        refine ⟨255967530746892946980536881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341290040995857262640715841 255967530746892946980536881)
        ·
          refine ⟨191975648060169710235402661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255967530746892946980536881 191975648060169710235402661)
          ·
            refine ⟨35995434011281820669137999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191975648060169710235402661 35995434011281820669137999)
            ·
              refine ⟨53993151016922731003706999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35995434011281820669137999 53993151016922731003706999)
              ·
                refine ⟨80989726525384096505560499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53993151016922731003706999 80989726525384096505560499)
                ·
                  refine ⟨121484589788076144758340749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80989726525384096505560499 121484589788076144758340749)
                  ·
                    refine ⟨45556721170528554284377781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121484589788076144758340749 45556721170528554284377781)
                    ·
                      refine ⟨4270942609737051964160417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45556721170528554284377781 4270942609737051964160417)
                      ·
                        rfl

theorem cell23_8317631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_8317631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317631 prefixEnd_8317631 := by exact prefixLift 8317631
  have htrace : WordTrace (prefixWord ++ tailWord_8317631) baseStart_8317631 baseEnd_8317631 := by
    simpa [prefixWord, tailWord_8317631, baseEnd_8317631] using wordTrace_append hprefix tailTrace_8317631
  have hstable : (prefixWord ++ tailWord_8317631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317631).length < 2 ^ (prefixWord ++ tailWord_8317631).sum := by decide
  have hdescent : baseEnd_8317631 < baseStart_8317631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317732 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_8317732 : Nat := 118140960795 + 8317732 * 2 ^ 59
def prefixEnd_8317732 : Nat := 4983230072969 + 3 ^ 40 * 8317732 * 2
def baseEnd_8317732 : Nat := 1423664823761052022999151

theorem tailTrace_8317732 : CollatzResearch.WordTrace tailWord_8317732 prefixEnd_8317732 1423664823761052022999151 := by
  unfold tailWord_8317732
  simp only [CollatzResearch.WordTrace]
  refine ⟨151686304551142497187253725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202248406068189996249671633 151686304551142497187253725)
  ·
    refine ⟨56882364206678436445220147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151686304551142497187253725 56882364206678436445220147)
    ·
      refine ⟨85323546310017654667830221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56882364206678436445220147 85323546310017654667830221)
      ·
        refine ⟨31996329866256620500436333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85323546310017654667830221 31996329866256620500436333)
        ·
          refine ⟨11998623699846232687663625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31996329866256620500436333 11998623699846232687663625)
          ·
            refine ⟨8998967774884674515747719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11998623699846232687663625 8998967774884674515747719)
            ·
              refine ⟨13498451662327011773621579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8998967774884674515747719 13498451662327011773621579)
              ·
                refine ⟨20247677493490517660432369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13498451662327011773621579 20247677493490517660432369)
                ·
                  refine ⟨15185758120117888245324277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20247677493490517660432369 15185758120117888245324277)
                  ·
                    refine ⟨1423664823761052022999151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15185758120117888245324277 1423664823761052022999151)
                    ·
                      rfl

theorem cell23_8317732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_8317732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317732 prefixEnd_8317732 := by exact prefixLift 8317732
  have htrace : WordTrace (prefixWord ++ tailWord_8317732) baseStart_8317732 baseEnd_8317732 := by
    simpa [prefixWord, tailWord_8317732, baseEnd_8317732] using wordTrace_append hprefix tailTrace_8317732
  have hstable : (prefixWord ++ tailWord_8317732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317732).length < 2 ^ (prefixWord ++ tailWord_8317732).sum := by decide
  have hdescent : baseEnd_8317732 < baseStart_8317732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317778 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_8317778 : Nat := 118140960795 + 8317778 * 2 ^ 59
def prefixEnd_8317778 : Nat := 4983230072969 + 3 ^ 40 * 8317778 * 2
def baseEnd_8317778 : Nat := 4271018091393262889022241

theorem tailTrace_8317778 : CollatzResearch.WordTrace tailWord_8317778 prefixEnd_8317778 4271018091393262889022241 := by
  unfold tailWord_8317778
  simp only [CollatzResearch.WordTrace]
  refine ⟨75843571715029586057670497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202249524573412229487121325 75843571715029586057670497)
  ·
    refine ⟨56882678786272189543252873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75843571715029586057670497 56882678786272189543252873)
    ·
      refine ⟨42662009089704142157439655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56882678786272189543252873 42662009089704142157439655)
      ·
        refine ⟨63993013634556213236159483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42662009089704142157439655 63993013634556213236159483)
        ·
          refine ⟨95989520451834319854239225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63993013634556213236159483 95989520451834319854239225)
          ·
            refine ⟨71992140338875739890679419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95989520451834319854239225 71992140338875739890679419)
            ·
              refine ⟨107988210508313609836019129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71992140338875739890679419 107988210508313609836019129)
              ·
                refine ⟨80991157881235207377014347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107988210508313609836019129 80991157881235207377014347)
                ·
                  refine ⟨121486736821852811065521521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80991157881235207377014347 121486736821852811065521521)
                  ·
                    refine ⟨91115052616389608299141141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121486736821852811065521521 91115052616389608299141141)
                    ·
                      refine ⟨4271018091393262889022241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91115052616389608299141141 4271018091393262889022241)
                      ·
                        rfl

theorem cell23_8317778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_8317778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317778 prefixEnd_8317778 := by exact prefixLift 8317778
  have htrace : WordTrace (prefixWord ++ tailWord_8317778) baseStart_8317778 baseEnd_8317778 := by
    simpa [prefixWord, tailWord_8317778, baseEnd_8317778] using wordTrace_append hprefix tailTrace_8317778
  have hstable : (prefixWord ++ tailWord_8317778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317778).length < 2 ^ (prefixWord ++ tailWord_8317778).sum := by decide
  have hdescent : baseEnd_8317778 < baseStart_8317778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317852 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_8317852 : Nat := 118140960795 + 8317852 * 2 ^ 59
def prefixEnd_8317852 : Nat := 4983230072969 + 3 ^ 40 * 8317852 * 2
def baseEnd_8317852 : Nat := 1423685362987231866498967

theorem tailTrace_8317852 : CollatzResearch.WordTrace tailWord_8317852 prefixEnd_8317852 1423685362987231866498967 := by
  unfold tailWord_8317852
  simp only [CollatzResearch.WordTrace]
  refine ⟨151688492930925127434437905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202251323907900169912583873 151688492930925127434437905)
  ·
    refine ⟨113766369698193845575828429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151688492930925127434437905 113766369698193845575828429)
    ·
      refine ⟨42662388636822692090935661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113766369698193845575828429 42662388636822692090935661)
      ·
        refine ⟨15998395738808509534100873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42662388636822692090935661 15998395738808509534100873)
        ·
          refine ⟨11998796804106382150575655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15998395738808509534100873 11998796804106382150575655)
          ·
            refine ⟨17998195206159573225863483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11998796804106382150575655 17998195206159573225863483)
            ·
              refine ⟨26997292809239359838795225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17998195206159573225863483 26997292809239359838795225)
              ·
                refine ⟨20247969606929519879096419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26997292809239359838795225 20247969606929519879096419)
                ·
                  refine ⟨30371954410394279818644629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20247969606929519879096419 30371954410394279818644629)
                  ·
                    refine ⟨1423685362987231866498967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30371954410394279818644629 1423685362987231866498967)
                    ·
                      rfl

theorem cell23_8317852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_8317852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317852 prefixEnd_8317852 := by exact prefixLift 8317852
  have htrace : WordTrace (prefixWord ++ tailWord_8317852) baseStart_8317852 baseEnd_8317852 := by
    simpa [prefixWord, tailWord_8317852, baseEnd_8317852] using wordTrace_append hprefix tailTrace_8317852
  have hstable : (prefixWord ++ tailWord_8317852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317852).length < 2 ^ (prefixWord ++ tailWord_8317852).sum := by decide
  have hdescent : baseEnd_8317852 < baseStart_8317852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317855 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_8317855 : Nat := 118140960795 + 8317855 * 2 ^ 59
def prefixEnd_8317855 : Nat := 4983230072969 + 3 ^ 40 * 8317855 * 2
def baseEnd_8317855 : Nat := 4271057629403659087759387

theorem tailTrace_8317855 : CollatzResearch.WordTrace tailWord_8317855 prefixEnd_8317855 4271057629403659087759387 := by
  unfold tailWord_8317855
  simp only [CollatzResearch.WordTrace]
  refine ⟨303377095280839386381235019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202251396853892924254156679 303377095280839386381235019)
  ·
    refine ⟨455065642921259079571852529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303377095280839386381235019 455065642921259079571852529)
    ·
      refine ⟨341299232190944309678889397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455065642921259079571852529 341299232190944309678889397)
      ·
        refine ⟨31996803017901029032395881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 341299232190944309678889397 31996803017901029032395881)
        ·
          refine ⟨23997602263425771774296911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31996803017901029032395881 23997602263425771774296911)
          ·
            refine ⟨35996403395138657661445367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23997602263425771774296911 35996403395138657661445367)
            ·
              refine ⟨53994605092707986492168051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35996403395138657661445367 53994605092707986492168051)
              ·
                refine ⟨80991907639061979738252077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53994605092707986492168051 80991907639061979738252077)
                ·
                  refine ⟨30371965364648242401844529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80991907639061979738252077 30371965364648242401844529)
                  ·
                    refine ⟨22778974023486181801383397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30371965364648242401844529 22778974023486181801383397)
                    ·
                      refine ⟨4271057629403659087759387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22778974023486181801383397 4271057629403659087759387)
                      ·
                        rfl

theorem cell23_8317855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_8317855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317855 prefixEnd_8317855 := by exact prefixLift 8317855
  have htrace : WordTrace (prefixWord ++ tailWord_8317855) baseStart_8317855 baseEnd_8317855 := by
    simpa [prefixWord, tailWord_8317855, baseEnd_8317855] using wordTrace_append hprefix tailTrace_8317855
  have hstable : (prefixWord ++ tailWord_8317855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317855).length < 2 ^ (prefixWord ++ tailWord_8317855).sum := by decide
  have hdescent : baseEnd_8317855 < baseStart_8317855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317910 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_8317910 : Nat := 118140960795 + 8317910 * 2 ^ 59
def prefixEnd_8317910 : Nat := 4983230072969 + 3 ^ 40 * 8317910 * 2
def baseEnd_8317910 : Nat := 4271085870839656372571635

theorem tailTrace_8317910 : CollatzResearch.WordTrace tailWord_8317910 prefixEnd_8317910 4271085870839656372571635 := by
  unfold tailWord_8317910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18961193830977508173405449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202252734197093420516324789 18961193830977508173405449)
  ·
    refine ⟨14220895373233131130054087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18961193830977508173405449 14220895373233131130054087)
    ·
      refine ⟨21331343059849696695081131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14220895373233131130054087 21331343059849696695081131)
      ·
        refine ⟨31997014589774545042621697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21331343059849696695081131 31997014589774545042621697)
        ·
          refine ⟨23997760942330908781966273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31997014589774545042621697 23997760942330908781966273)
          ·
            refine ⟨17998320706748181586474705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23997760942330908781966273 17998320706748181586474705)
            ·
              refine ⟨13498740530061136189856029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17998320706748181586474705 13498740530061136189856029)
              ·
                refine ⟨5062027698772926071196011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13498740530061136189856029 5062027698772926071196011)
                ·
                  refine ⟨7593041548159389106794017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062027698772926071196011 7593041548159389106794017)
                  ·
                    refine ⟨5694781161119541830095513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7593041548159389106794017 5694781161119541830095513)
                    ·
                      refine ⟨4271085870839656372571635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694781161119541830095513 4271085870839656372571635)
                      ·
                        rfl

theorem cell23_8317910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_8317910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317910 prefixEnd_8317910 := by exact prefixLift 8317910
  have htrace : WordTrace (prefixWord ++ tailWord_8317910) baseStart_8317910 baseEnd_8317910 := by
    simpa [prefixWord, tailWord_8317910, baseEnd_8317910] using wordTrace_append hprefix tailTrace_8317910
  have hstable : (prefixWord ++ tailWord_8317910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317910).length < 2 ^ (prefixWord ++ tailWord_8317910).sum := by decide
  have hdescent : baseEnd_8317910 < baseStart_8317910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317940 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8317940 : Nat := 118140960795 + 8317940 * 2 ^ 59
def prefixEnd_8317940 : Nat := 4983230072969 + 3 ^ 40 * 8317940 * 2
def baseEnd_8317940 : Nat := 4271101275259291255196497

theorem tailTrace_8317940 : CollatzResearch.WordTrace tailWord_8317940 prefixEnd_8317940 4271101275259291255196497 := by
  unfold tailWord_8317940
  simp only [CollatzResearch.WordTrace]
  refine ⟨151690097742765722949039637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202253463657020963932052849 151690097742765722949039637)
  ·
    refine ⟨7110473331692143263236233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151690097742765722949039637 7110473331692143263236233)
    ·
      refine ⟨5332854998769107447427175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7110473331692143263236233 5332854998769107447427175)
      ·
        refine ⟨7999282498153661171140763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332854998769107447427175 7999282498153661171140763)
        ·
          refine ⟨11998923747230491756711145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7999282498153661171140763 11998923747230491756711145)
          ·
            refine ⟨8999192810422868817533359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11998923747230491756711145 8999192810422868817533359)
            ·
              refine ⟨13498789215634303226300039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999192810422868817533359 13498789215634303226300039)
              ·
                refine ⟨20248183823451454839450059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13498789215634303226300039 20248183823451454839450059)
                ·
                  refine ⟨30372275735177182259175089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20248183823451454839450059 30372275735177182259175089)
                  ·
                    refine ⟨22779206801382886694381317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30372275735177182259175089 22779206801382886694381317)
                    ·
                      refine ⟨4271101275259291255196497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22779206801382886694381317 4271101275259291255196497)
                      ·
                        rfl

theorem cell23_8317940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8317940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317940 prefixEnd_8317940 := by exact prefixLift 8317940
  have htrace : WordTrace (prefixWord ++ tailWord_8317940) baseStart_8317940 baseEnd_8317940 := by
    simpa [prefixWord, tailWord_8317940, baseEnd_8317940] using wordTrace_append hprefix tailTrace_8317940
  have hstable : (prefixWord ++ tailWord_8317940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317940).length < 2 ^ (prefixWord ++ tailWord_8317940).sum := by decide
  have hdescent : baseEnd_8317940 < baseStart_8317940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317942 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_8317942 : Nat := 118140960795 + 8317942 * 2 ^ 59
def prefixEnd_8317942 : Nat := 4983230072969 + 3 ^ 40 * 8317942 * 2
def baseEnd_8317942 : Nat := 1423700767406866749123829

theorem tailTrace_8317942 : CollatzResearch.WordTrace tailWord_8317942 prefixEnd_8317942 1423700767406866749123829 := by
  unfold tailWord_8317942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18961266776970262514978255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202253512287682800159768053 18961266776970262514978255)
  ·
    refine ⟨28441900165455393772467383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18961266776970262514978255 28441900165455393772467383)
    ·
      refine ⟨42662850248183090658701075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28441900165455393772467383 42662850248183090658701075)
      ·
        refine ⟨63994275372274635988051613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42662850248183090658701075 63994275372274635988051613)
        ·
          refine ⟨23997853264602988495519355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63994275372274635988051613 23997853264602988495519355)
          ·
            refine ⟨35996779896904482743279033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23997853264602988495519355 35996779896904482743279033)
            ·
              refine ⟨26997584922678362057459275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35996779896904482743279033 26997584922678362057459275)
              ·
                refine ⟨40496377384017543086188913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26997584922678362057459275 40496377384017543086188913)
                ·
                  refine ⟨30372283038013157314641685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40496377384017543086188913 30372283038013157314641685)
                  ·
                    refine ⟨1423700767406866749123829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30372283038013157314641685 1423700767406866749123829)
                    ·
                      rfl

theorem cell23_8317942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_8317942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317942 prefixEnd_8317942 := by exact prefixLift 8317942
  have htrace : WordTrace (prefixWord ++ tailWord_8317942) baseStart_8317942 baseEnd_8317942 := by
    simpa [prefixWord, tailWord_8317942, baseEnd_8317942] using wordTrace_append hprefix tailTrace_8317942
  have hstable : (prefixWord ++ tailWord_8317942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317942).length < 2 ^ (prefixWord ++ tailWord_8317942).sum := by decide
  have hdescent : baseEnd_8317942 < baseStart_8317942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317945 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_8317945 : Nat := 118140960795 + 8317945 * 2 ^ 59
def prefixEnd_8317945 : Nat := 4983230072969 + 3 ^ 40 * 8317945 * 2
def baseEnd_8317945 : Nat := 4271103842662563735633973

theorem tailTrace_8317945 : CollatzResearch.WordTrace tailWord_8317945 prefixEnd_8317945 4271103842662563735633973 := by
  unfold tailWord_8317945
  simp only [CollatzResearch.WordTrace]
  refine ⟨303380377850513331752011289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202253585233675554501340859 303380377850513331752011289)
  ·
    refine ⟨227535283387884998814008467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303380377850513331752011289 227535283387884998814008467)
    ·
      refine ⟨341302925081827498221012701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227535283387884998814008467 341302925081827498221012701)
      ·
        refine ⟨127988596905685311832879763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341302925081827498221012701 127988596905685311832879763)
        ·
          refine ⟨191982895358527967749319645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127988596905685311832879763 191982895358527967749319645)
          ·
            refine ⟨71993585759447987905994867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191982895358527967749319645 71993585759447987905994867)
            ·
              refine ⟨107990378639171981858992301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71993585759447987905994867 107990378639171981858992301)
              ·
                refine ⟨40496391989689493197122113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107990378639171981858992301 40496391989689493197122113)
                ·
                  refine ⟨30372293992267119897841585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40496391989689493197122113 30372293992267119897841585)
                  ·
                    refine ⟨22779220494200339923381189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30372293992267119897841585 22779220494200339923381189)
                    ·
                      refine ⟨4271103842662563735633973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22779220494200339923381189 4271103842662563735633973)
                      ·
                        rfl

theorem cell23_8317945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_8317945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317945 prefixEnd_8317945 := by exact prefixLift 8317945
  have htrace : WordTrace (prefixWord ++ tailWord_8317945) baseStart_8317945 baseEnd_8317945 := by
    simpa [prefixWord, tailWord_8317945, baseEnd_8317945] using wordTrace_append hprefix tailTrace_8317945
  have hstable : (prefixWord ++ tailWord_8317945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317945).length < 2 ^ (prefixWord ++ tailWord_8317945).sum := by decide
  have hdescent : baseEnd_8317945 < baseStart_8317945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317989 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 5]
def baseStart_8317989 : Nat := 118140960795 + 8317989 * 2 ^ 59
def prefixEnd_8317989 : Nat := 4983230072969 + 3 ^ 40 * 8317989 * 2
def baseEnd_8317989 : Nat := 474569603979040173720419

theorem tailTrace_8317989 : CollatzResearch.WordTrace tailWord_8317989 prefixEnd_8317989 474569603979040173720419 := by
  unfold tailWord_8317989
  simp only [CollatzResearch.WordTrace]
  refine ⟨303381982662353927266613021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202254655108235951511075347 303381982662353927266613021)
  ·
    refine ⟨113768243498382722724979883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303381982662353927266613021 113768243498382722724979883)
    ·
      refine ⟨170652365247574084087469825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113768243498382722724979883 170652365247574084087469825)
      ·
        refine ⟨127989273935680563065602369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170652365247574084087469825 127989273935680563065602369)
        ·
          refine ⟨95991955451760422299201777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127989273935680563065602369 95991955451760422299201777)
          ·
            refine ⟨71993966588820316724401333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95991955451760422299201777 71993966588820316724401333)
            ·
              refine ⟨6749434367701904692912625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71993966588820316724401333 6749434367701904692912625)
              ·
                refine ⟨5062075775776428519684469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6749434367701904692912625 5062075775776428519684469)
                ·
                  refine ⟨474569603979040173720419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5062075775776428519684469 474569603979040173720419)
                  ·
                    rfl

theorem cell23_8317989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_8317989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317989 prefixEnd_8317989 := by exact prefixLift 8317989
  have htrace : WordTrace (prefixWord ++ tailWord_8317989) baseStart_8317989 baseEnd_8317989 := by
    simpa [prefixWord, tailWord_8317989, baseEnd_8317989] using wordTrace_append hprefix tailTrace_8317989
  have hstable : (prefixWord ++ tailWord_8317989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317989).length < 2 ^ (prefixWord ++ tailWord_8317989).sum := by decide
  have hdescent : baseEnd_8317989 < baseStart_8317989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8317995 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5]
def baseStart_8317995 : Nat := 118140960795 + 8317995 * 2 ^ 59
def prefixEnd_8317995 : Nat := 4983230072969 + 3 ^ 40 * 8317995 * 2
def baseEnd_8317995 : Nat := 4271129516695288540008743

theorem tailTrace_8317995 : CollatzResearch.WordTrace tailWord_8317995 prefixEnd_8317995 4271129516695288540008743 := by
  unfold tailWord_8317995
  simp only [CollatzResearch.WordTrace]
  refine ⟨303382201500332190291331439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202254801000221460194220959 303382201500332190291331439)
  ·
    refine ⟨455073302250498285436997159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303382201500332190291331439 455073302250498285436997159)
    ·
      refine ⟨682609953375747428155495739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455073302250498285436997159 682609953375747428155495739)
      ·
        refine ⟨1023914930063621142233243609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682609953375747428155495739 1023914930063621142233243609)
        ·
          refine ⟨767936197547715856674932707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1023914930063621142233243609 767936197547715856674932707)
          ·
            refine ⟨1151904296321573785012399061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767936197547715856674932707 1151904296321573785012399061)
            ·
              refine ⟨26997756945036885586228103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1151904296321573785012399061 26997756945036885586228103)
              ·
                refine ⟨40496635417555328379342155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26997756945036885586228103 40496635417555328379342155)
                ·
                  refine ⟨60744953126332992569013233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40496635417555328379342155 60744953126332992569013233)
                  ·
                    refine ⟨45558714844749744426759925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60744953126332992569013233 45558714844749744426759925)
                    ·
                      refine ⟨4271129516695288540008743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45558714844749744426759925 4271129516695288540008743)
                      ·
                        rfl

theorem cell23_8317995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_8317995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8317995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8317995 prefixEnd_8317995 := by exact prefixLift 8317995
  have htrace : WordTrace (prefixWord ++ tailWord_8317995) baseStart_8317995 baseEnd_8317995 := by
    simpa [prefixWord, tailWord_8317995, baseEnd_8317995] using wordTrace_append hprefix tailTrace_8317995
  have hstable : (prefixWord ++ tailWord_8317995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8317995).length < 2 ^ (prefixWord ++ tailWord_8317995).sum := by decide
  have hdescent : baseEnd_8317995 < baseStart_8317995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8317995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318042 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_8318042 : Nat := 118140960795 + 8318042 * 2 ^ 59
def prefixEnd_8318042 : Nat := 4983230072969 + 3 ^ 40 * 8318042 * 2
def baseEnd_8318042 : Nat := 4271153650286049856121027

theorem tailTrace_8318042 : CollatzResearch.WordTrace tailWord_8318042 prefixEnd_8318042 4271153650286049856121027 := by
  unfold tailWord_8318042
  simp only [CollatzResearch.WordTrace]
  refine ⟨75845978932790479329573095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202255943820774611545528253 75845978932790479329573095)
  ·
    refine ⟨113768968399185718994359643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75845978932790479329573095 113768968399185718994359643)
    ·
      refine ⟨170653452598778578491539465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113768968399185718994359643 170653452598778578491539465)
      ·
        refine ⟨127990089449083933868654599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170653452598778578491539465 127990089449083933868654599)
        ·
          refine ⟨191985134173625900802981899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127990089449083933868654599 191985134173625900802981899)
          ·
            refine ⟨287977701260438851204472849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191985134173625900802981899 287977701260438851204472849)
            ·
              refine ⟨215983275945329138403354637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287977701260438851204472849 215983275945329138403354637)
              ·
                refine ⟨80993728479498426901257989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215983275945329138403354637 80993728479498426901257989)
                ·
                  refine ⟨15186324089905955043985873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80993728479498426901257989 15186324089905955043985873)
                  ·
                    refine ⟨11389743067429466282989405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15186324089905955043985873 11389743067429466282989405)
                    ·
                      refine ⟨4271153650286049856121027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11389743067429466282989405 4271153650286049856121027)
                      ·
                        rfl

theorem cell23_8318042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_8318042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318042 prefixEnd_8318042 := by exact prefixLift 8318042
  have htrace : WordTrace (prefixWord ++ tailWord_8318042) baseStart_8318042 baseEnd_8318042 := by
    simpa [prefixWord, tailWord_8318042, baseEnd_8318042] using wordTrace_append hprefix tailTrace_8318042
  have hstable : (prefixWord ++ tailWord_8318042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318042).length < 2 ^ (prefixWord ++ tailWord_8318042).sum := by decide
  have hdescent : baseEnd_8318042 < baseStart_8318042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318046 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_8318046 : Nat := 118140960795 + 8318046 * 2 ^ 59
def prefixEnd_8318046 : Nat := 4983230072969 + 3 ^ 40 * 8318046 * 2
def baseEnd_8318046 : Nat := 4271155704208667840471009

theorem tailTrace_8318046 : CollatzResearch.WordTrace tailWord_8318046 prefixEnd_8318046 4271155704208667840471009 := by
  unfold tailWord_8318046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37923007702893428250179749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202256041082098284000958661 37923007702893428250179749)
  ·
    refine ⟨7110563944292517796908703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37923007702893428250179749 7110563944292517796908703)
    ·
      refine ⟨10665845916438776695363055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7110563944292517796908703 10665845916438776695363055)
      ·
        refine ⟨15998768874658165043044583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665845916438776695363055 15998768874658165043044583)
        ·
          refine ⟨23998153311987247564566875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998768874658165043044583 23998153311987247564566875)
          ·
            refine ⟨35997229967980871346850313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23998153311987247564566875 35997229967980871346850313)
            ·
              refine ⟨26997922475985653510137735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35997229967980871346850313 26997922475985653510137735)
              ·
                refine ⟨40496883713978480265206603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26997922475985653510137735 40496883713978480265206603)
                ·
                  refine ⟨60745325570967720397809905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40496883713978480265206603 60745325570967720397809905)
                  ·
                    refine ⟨45558994178225790298357429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60745325570967720397809905 45558994178225790298357429)
                    ·
                      refine ⟨4271155704208667840471009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45558994178225790298357429 4271155704208667840471009)
                      ·
                        rfl

theorem cell23_8318046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_8318046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318046 prefixEnd_8318046 := by exact prefixLift 8318046
  have htrace : WordTrace (prefixWord ++ tailWord_8318046) baseStart_8318046 baseEnd_8318046 := by
    simpa [prefixWord, tailWord_8318046, baseEnd_8318046] using wordTrace_append hprefix tailTrace_8318046
  have hstable : (prefixWord ++ tailWord_8318046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318046).length < 2 ^ (prefixWord ++ tailWord_8318046).sum := by decide
  have hdescent : baseEnd_8318046 < baseStart_8318046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318065 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_8318065 : Nat := 118140960795 + 8318065 * 2 ^ 59
def prefixEnd_8318065 : Nat := 4983230072969 + 3 ^ 40 * 8318065 * 2
def baseEnd_8318065 : Nat := 4271165460341103266133421

theorem tailTrace_8318065 : CollatzResearch.WordTrace tailWord_8318065 prefixEnd_8318065 4271165460341103266133421 := by
  unfold tailWord_8318065
  simp only [CollatzResearch.WordTrace]
  refine ⟨303384754610078592246379649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202256503073385728164253099 303384754610078592246379649)
  ·
    refine ⟨227538565957558944184784737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303384754610078592246379649 227538565957558944184784737)
    ·
      refine ⟨170653924468169208138588553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227538565957558944184784737 170653924468169208138588553)
      ·
        refine ⟨127990443351126906103941415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170653924468169208138588553 127990443351126906103941415)
        ·
          refine ⟨191985665026690359155912123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127990443351126906103941415 191985665026690359155912123)
          ·
            refine ⟨287978497540035538733868185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191985665026690359155912123 287978497540035538733868185)
            ·
              refine ⟨215983873155026654050401139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287978497540035538733868185 215983873155026654050401139)
              ·
                refine ⟨323975809732539981075601709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215983873155026654050401139 323975809732539981075601709)
                ·
                  refine ⟨121490928649702492903350641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323975809732539981075601709 121490928649702492903350641)
                  ·
                    refine ⟨91118196487276869677512981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121490928649702492903350641 91118196487276869677512981)
                    ·
                      refine ⟨4271165460341103266133421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91118196487276869677512981 4271165460341103266133421)
                      ·
                        rfl

theorem cell23_8318065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_8318065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318065 prefixEnd_8318065 := by exact prefixLift 8318065
  have htrace : WordTrace (prefixWord ++ tailWord_8318065) baseStart_8318065 baseEnd_8318065 := by
    simpa [prefixWord, tailWord_8318065, baseEnd_8318065] using wordTrace_append hprefix tailTrace_8318065
  have hstable : (prefixWord ++ tailWord_8318065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318065).length < 2 ^ (prefixWord ++ tailWord_8318065).sum := by decide
  have hdescent : baseEnd_8318065 < baseStart_8318065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318099 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 2, 3, 2]
def baseStart_8318099 : Nat := 118140960795 + 8318099 * 2 ^ 59
def prefixEnd_8318099 : Nat := 4983230072969 + 3 ^ 40 * 8318099 * 2
def baseEnd_8318099 : Nat := 4271182918683356133108265

theorem tailTrace_8318099 : CollatzResearch.WordTrace tailWord_8318099 prefixEnd_8318099 4271182918683356133108265 := by
  unfold tailWord_8318099
  simp only [CollatzResearch.WordTrace]
  refine ⟨303385994691955416053117351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202257329794636944035411567 303385994691955416053117351)
  ·
    refine ⟨455078992037933124079676027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303385994691955416053117351 455078992037933124079676027)
    ·
      refine ⟨682618488056899686119514041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455078992037933124079676027 682618488056899686119514041)
      ·
        refine ⟨511963866042674764589635531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682618488056899686119514041 511963866042674764589635531)
        ·
          refine ⟨767945799064012146884453297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511963866042674764589635531 767945799064012146884453297)
          ·
            refine ⟨575959349298009110163339973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767945799064012146884453297 575959349298009110163339973)
            ·
              refine ⟨107992377993376708155626245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575959349298009110163339973 107992377993376708155626245)
              ·
                refine ⟨20248570873758132779179921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107992377993376708155626245 20248570873758132779179921)
                ·
                  refine ⟨15186428155318599584384941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20248570873758132779179921 15186428155318599584384941)
                  ·
                    refine ⟨5694910558244474844144353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15186428155318599584384941 5694910558244474844144353)
                    ·
                      refine ⟨4271182918683356133108265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5694910558244474844144353 4271182918683356133108265)
                      ·
                        rfl

theorem cell23_8318099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3, 2].length) (baseStart_8318099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318099 prefixEnd_8318099 := by exact prefixLift 8318099
  have htrace : WordTrace (prefixWord ++ tailWord_8318099) baseStart_8318099 baseEnd_8318099 := by
    simpa [prefixWord, tailWord_8318099, baseEnd_8318099] using wordTrace_append hprefix tailTrace_8318099
  have hstable : (prefixWord ++ tailWord_8318099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318099).length < 2 ^ (prefixWord ++ tailWord_8318099).sum := by decide
  have hdescent : baseEnd_8318099 < baseStart_8318099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318105 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_8318105 : Nat := 118140960795 + 8318105 * 2 ^ 59
def prefixEnd_8318105 : Nat := 4983230072969 + 3 ^ 40 * 8318105 * 2
def baseEnd_8318105 : Nat := 1423728666522427703211079

theorem tailTrace_8318105 : CollatzResearch.WordTrace tailWord_8318105 prefixEnd_8318105 1423728666522427703211079 := by
  unfold tailWord_8318105
  simp only [CollatzResearch.WordTrace]
  refine ⟨303386213529933679077835769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202257475686622452718557179 303386213529933679077835769)
  ·
    refine ⟨227539660147450259308376827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303386213529933679077835769 227539660147450259308376827)
    ·
      refine ⟨341309490221175388962565241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227539660147450259308376827 341309490221175388962565241)
      ·
        refine ⟨255982117665881541721923931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341309490221175388962565241 255982117665881541721923931)
        ·
          refine ⟨383973176498822312582885897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255982117665881541721923931 383973176498822312582885897)
          ·
            refine ⟨287979882374116734437164423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383973176498822312582885897 287979882374116734437164423)
            ·
              refine ⟨431969823561175101655746635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287979882374116734437164423 431969823561175101655746635)
              ·
                refine ⟨647954735341762652483619953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431969823561175101655746635 647954735341762652483619953)
                ·
                  refine ⟨485966051506321989362714965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 647954735341762652483619953 485966051506321989362714965)
                  ·
                    refine ⟨1423728666522427703211079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 485966051506321989362714965 1423728666522427703211079)
                    ·
                      rfl

theorem cell23_8318105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_8318105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318105 prefixEnd_8318105 := by exact prefixLift 8318105
  have htrace : WordTrace (prefixWord ++ tailWord_8318105) baseStart_8318105 baseEnd_8318105 := by
    simpa [prefixWord, tailWord_8318105, baseEnd_8318105] using wordTrace_append hprefix tailTrace_8318105
  have hstable : (prefixWord ++ tailWord_8318105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318105).length < 2 ^ (prefixWord ++ tailWord_8318105).sum := by decide
  have hdescent : baseEnd_8318105 < baseStart_8318105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318106 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_8318106 : Nat := 118140960795 + 8318106 * 2 ^ 59
def prefixEnd_8318106 : Nat := 4983230072969 + 3 ^ 40 * 8318106 * 2
def baseEnd_8318106 : Nat := 4271186513047937605720733

theorem tailTrace_8318106 : CollatzResearch.WordTrace tailWord_8318106 prefixEnd_8318106 4271186513047937605720733 := by
  unfold tailWord_8318106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75846562500732514062155543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202257500001953370832414781 75846562500732514062155543)
  ·
    refine ⟨113769843751098771093233315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75846562500732514062155543 113769843751098771093233315)
    ·
      refine ⟨170654765626648156639849973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113769843751098771093233315 170654765626648156639849973)
      ·
        refine ⟨15998884277498264684985935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170654765626648156639849973 15998884277498264684985935)
        ·
          refine ⟨23998326416247397027478903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998884277498264684985935 23998326416247397027478903)
          ·
            refine ⟨35997489624371095541218355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23998326416247397027478903 35997489624371095541218355)
            ·
              refine ⟨53996234436556643311827533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35997489624371095541218355 53996234436556643311827533)
              ·
                refine ⟨20248587913708741241935325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53996234436556643311827533 20248587913708741241935325)
                ·
                  refine ⟨7593220467640777965725747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20248587913708741241935325 7593220467640777965725747)
                  ·
                    refine ⟨11389830701461166948588621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593220467640777965725747 11389830701461166948588621)
                    ·
                      refine ⟨4271186513047937605720733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11389830701461166948588621 4271186513047937605720733)
                      ·
                        rfl

theorem cell23_8318106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_8318106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318106 prefixEnd_8318106 := by exact prefixLift 8318106
  have htrace : WordTrace (prefixWord ++ tailWord_8318106) baseStart_8318106 baseEnd_8318106 := by
    simpa [prefixWord, tailWord_8318106, baseEnd_8318106] using wordTrace_append hprefix tailTrace_8318106
  have hstable : (prefixWord ++ tailWord_8318106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318106).length < 2 ^ (prefixWord ++ tailWord_8318106).sum := by decide
  have hdescent : baseEnd_8318106 < baseStart_8318106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318134 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_8318134 : Nat := 118140960795 + 8318134 * 2 ^ 59
def prefixEnd_8318134 : Nat := 4983230072969 + 3 ^ 40 * 8318134 * 2
def baseEnd_8318134 : Nat := 1423733630168754498723535

theorem tailTrace_8318134 : CollatzResearch.WordTrace tailWord_8318134 prefixEnd_8318134 1423733630168754498723535 := by
  unfold tailWord_8318134
  simp only [CollatzResearch.WordTrace]
  refine ⟨18961704452926788564415091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202258180831219078020427637 18961704452926788564415091)
  ·
    refine ⟨28442556679390182846622637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18961704452926788564415091 28442556679390182846622637)
    ·
      refine ⟨10665958754771318567483489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28442556679390182846622637 10665958754771318567483489)
      ·
        refine ⟨7999469066078488925612617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10665958754771318567483489 7999469066078488925612617)
        ·
          refine ⟨5999601799558866694209463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7999469066078488925612617 5999601799558866694209463)
          ·
            refine ⟨8999402699338300041314195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999601799558866694209463 8999402699338300041314195)
            ·
              refine ⟨13499104049007450061971293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999402699338300041314195 13499104049007450061971293)
              ·
                refine ⟨5062164018377793773239235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13499104049007450061971293 5062164018377793773239235)
                ·
                  refine ⟨7593246027566690659858853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062164018377793773239235 7593246027566690659858853)
                  ·
                    refine ⟨1423733630168754498723535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7593246027566690659858853 1423733630168754498723535)
                    ·
                      rfl

theorem cell23_8318134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_8318134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318134 prefixEnd_8318134 := by exact prefixLift 8318134
  have htrace : WordTrace (prefixWord ++ tailWord_8318134) baseStart_8318134 baseEnd_8318134 := by
    simpa [prefixWord, tailWord_8318134, baseEnd_8318134] using wordTrace_append hprefix tailTrace_8318134
  have hstable : (prefixWord ++ tailWord_8318134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318134).length < 2 ^ (prefixWord ++ tailWord_8318134).sum := by decide
  have hdescent : baseEnd_8318134 < baseStart_8318134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318140 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_8318140 : Nat := 118140960795 + 8318140 * 2 ^ 59
def prefixEnd_8318140 : Nat := 4983230072969 + 3 ^ 40 * 8318140 * 2
def baseEnd_8318140 : Nat := 4271203971390190472695577

theorem tailTrace_8318140 : CollatzResearch.WordTrace tailWord_8318140 prefixEnd_8318140 4271203971390190472695577 := by
  unfold tailWord_8318140
  simp only [CollatzResearch.WordTrace]
  refine ⟨151693745042403440027679937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202258326723204586703573249 151693745042403440027679937)
  ·
    refine ⟨113770308781802580020759953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151693745042403440027679937 113770308781802580020759953)
    ·
      refine ⟨85327731586351935015569965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113770308781802580020759953 85327731586351935015569965)
      ·
        refine ⟨31997899344881975630838737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85327731586351935015569965 31997899344881975630838737)
        ·
          refine ⟨23998424508661481723129053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31997899344881975630838737 23998424508661481723129053)
          ·
            refine ⟨8999409190748055646173395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23998424508661481723129053 8999409190748055646173395)
            ·
              refine ⟨13499113786122083469260093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999409190748055646173395 13499113786122083469260093)
              ·
                refine ⟨5062167669795781300972535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13499113786122083469260093 5062167669795781300972535)
                ·
                  refine ⟨7593251504693671951458803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062167669795781300972535 7593251504693671951458803)
                  ·
                    refine ⟨11389877257040507927188205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593251504693671951458803 11389877257040507927188205)
                    ·
                      refine ⟨4271203971390190472695577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11389877257040507927188205 4271203971390190472695577)
                      ·
                        rfl

theorem cell23_8318140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_8318140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318140 prefixEnd_8318140 := by exact prefixLift 8318140
  have htrace : WordTrace (prefixWord ++ tailWord_8318140) baseStart_8318140 baseEnd_8318140 := by
    simpa [prefixWord, tailWord_8318140, baseEnd_8318140] using wordTrace_append hprefix tailTrace_8318140
  have hstable : (prefixWord ++ tailWord_8318140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318140).length < 2 ^ (prefixWord ++ tailWord_8318140).sum := by decide
  have hdescent : baseEnd_8318140 < baseStart_8318140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318157 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_8318157 : Nat := 118140960795 + 8318157 * 2 ^ 59
def prefixEnd_8318157 : Nat := 4983230072969 + 3 ^ 40 * 8318157 * 2
def baseEnd_8318157 : Nat := 4271212700561316906182999

theorem tailTrace_8318157 : CollatzResearch.WordTrace tailWord_8318157 prefixEnd_8318157 4271212700561316906182999 := by
  unfold tailWord_8318157
  simp only [CollatzResearch.WordTrace]
  refine ⟨303388110125745291958728725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202258740083830194639152483 303388110125745291958728725)
  ·
    refine ⟨14221317662144310560565409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303388110125745291958728725 14221317662144310560565409)
    ·
      refine ⟨10665988246608232920424057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14221317662144310560565409 10665988246608232920424057)
      ·
        refine ⟨7999491184956174690318043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10665988246608232920424057 7999491184956174690318043)
        ·
          refine ⟨11999236777434262035477065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7999491184956174690318043 11999236777434262035477065)
          ·
            refine ⟨8999427583075696526607799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11999236777434262035477065 8999427583075696526607799)
            ·
              refine ⟨13499141374613544789911699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999427583075696526607799 13499141374613544789911699)
              ·
                refine ⟨20248712061920317184867549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13499141374613544789911699 20248712061920317184867549)
                ·
                  refine ⟨7593267023220118944325331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20248712061920317184867549 7593267023220118944325331)
                  ·
                    refine ⟨11389900534830178416487997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593267023220118944325331 11389900534830178416487997)
                    ·
                      refine ⟨4271212700561316906182999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11389900534830178416487997 4271212700561316906182999)
                      ·
                        rfl

theorem cell23_8318157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_8318157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318157 prefixEnd_8318157 := by exact prefixLift 8318157
  have htrace : WordTrace (prefixWord ++ tailWord_8318157) baseStart_8318157 baseEnd_8318157 := by
    simpa [prefixWord, tailWord_8318157, baseEnd_8318157] using wordTrace_append hprefix tailTrace_8318157
  have hstable : (prefixWord ++ tailWord_8318157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318157).length < 2 ^ (prefixWord ++ tailWord_8318157).sum := by decide
  have hdescent : baseEnd_8318157 < baseStart_8318157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318173 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_8318173 : Nat := 118140960795 + 8318173 * 2 ^ 59
def prefixEnd_8318173 : Nat := 4983230072969 + 3 ^ 40 * 8318173 * 2
def baseEnd_8318173 : Nat := 1423740305417262947860975

theorem tailTrace_8318173 : CollatzResearch.WordTrace tailWord_8318173 prefixEnd_8318173 1423740305417262947860975 := by
  unfold tailWord_8318173
  simp only [CollatzResearch.WordTrace]
  refine ⟨303388693693687326691311173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202259129129124884460874115 303388693693687326691311173)
  ·
    refine ⟨56885380067566373754620845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303388693693687326691311173 56885380067566373754620845)
    ·
      refine ⟨21332017525337390157982817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56885380067566373754620845 21332017525337390157982817)
      ·
        refine ⟨15999013144003042618487113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21332017525337390157982817 15999013144003042618487113)
        ·
          refine ⟨11999259858002281963865335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15999013144003042618487113 11999259858002281963865335)
          ·
            refine ⟨17998889787003422945798003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11999259858002281963865335 17998889787003422945798003)
            ·
              refine ⟨26998334680505134418697005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17998889787003422945798003 26998334680505134418697005)
              ·
                refine ⟨10124375505189425407011377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26998334680505134418697005 10124375505189425407011377)
                ·
                  refine ⟨7593281628892069055258533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10124375505189425407011377 7593281628892069055258533)
                  ·
                    refine ⟨1423740305417262947860975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7593281628892069055258533 1423740305417262947860975)
                    ·
                      rfl

theorem cell23_8318173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_8318173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318173 prefixEnd_8318173 := by exact prefixLift 8318173
  have htrace : WordTrace (prefixWord ++ tailWord_8318173) baseStart_8318173 baseEnd_8318173 := by
    simpa [prefixWord, tailWord_8318173, baseEnd_8318173] using wordTrace_append hprefix tailTrace_8318173
  have hstable : (prefixWord ++ tailWord_8318173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318173).length < 2 ^ (prefixWord ++ tailWord_8318173).sum := by decide
  have hdescent : baseEnd_8318173 < baseStart_8318173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318236 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_8318236 : Nat := 118140960795 + 8318236 * 2 ^ 59
def prefixEnd_8318236 : Nat := 4983230072969 + 3 ^ 40 * 8318236 * 2
def baseEnd_8318236 : Nat := 4271253265533022097095135

theorem tailTrace_8318236 : CollatzResearch.WordTrace tailWord_8318236 prefixEnd_8318236 4271253265533022097095135 := by
  unfold tailWord_8318236
  simp only [CollatzResearch.WordTrace]
  refine ⟨151695495746229544225427281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202260660994972725633903041 151695495746229544225427281)
  ·
    refine ⟨113771621809672158169070461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151695495746229544225427281 113771621809672158169070461)
    ·
      refine ⟨42664358178627059313401423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113771621809672158169070461 42664358178627059313401423)
      ·
        refine ⟨63996537267940588970102135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42664358178627059313401423 63996537267940588970102135)
        ·
          refine ⟨95994805901910883455153203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63996537267940588970102135 95994805901910883455153203)
          ·
            refine ⟨143992208852866325182729805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95994805901910883455153203 143992208852866325182729805)
            ·
              refine ⟨53997078319824871943523677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143992208852866325182729805 53997078319824871943523677)
              ·
                refine ⟨20248904369934326978821379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53997078319824871943523677 20248904369934326978821379)
                ·
                  refine ⟨30373356554901490468232069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20248904369934326978821379 30373356554901490468232069)
                  ·
                    refine ⟨5695004354044029462793513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30373356554901490468232069 5695004354044029462793513)
                    ·
                      refine ⟨4271253265533022097095135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695004354044029462793513 4271253265533022097095135)
                      ·
                        rfl

theorem cell23_8318236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_8318236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318236 prefixEnd_8318236 := by exact prefixLift 8318236
  have htrace : WordTrace (prefixWord ++ tailWord_8318236) baseStart_8318236 baseEnd_8318236 := by
    simpa [prefixWord, tailWord_8318236, baseEnd_8318236] using wordTrace_append hprefix tailTrace_8318236
  have hstable : (prefixWord ++ tailWord_8318236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318236).length < 2 ^ (prefixWord ++ tailWord_8318236).sum := by decide
  have hdescent : baseEnd_8318236 < baseStart_8318236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318252 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_8318252 : Nat := 118140960795 + 8318252 * 2 ^ 59
def prefixEnd_8318252 : Nat := 4983230072969 + 3 ^ 40 * 8318252 * 2
def baseEnd_8318252 : Nat := 4271261481223494034495061

theorem tailTrace_8318252 : CollatzResearch.WordTrace tailWord_8318252 prefixEnd_8318252 4271261481223494034495061 := by
  unfold tailWord_8318252
  simp only [CollatzResearch.WordTrace]
  refine ⟨151695787530200561591718505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202261050040267415455624673 151695787530200561591718505)
  ·
    refine ⟨113771840647650421193788879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151695787530200561591718505 113771840647650421193788879)
    ·
      refine ⟨170657760971475631790683319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113771840647650421193788879 170657760971475631790683319)
      ·
        refine ⟨255986641457213447686024979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170657760971475631790683319 255986641457213447686024979)
        ·
          refine ⟨383979962185820171529037469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255986641457213447686024979 383979962185820171529037469)
          ·
            refine ⟨143992485819682564323389051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383979962185820171529037469 143992485819682564323389051)
            ·
              refine ⟨215988728729523846485083577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143992485819682564323389051 215988728729523846485083577)
              ·
                refine ⟨161991546547142884863812683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215988728729523846485083577 161991546547142884863812683)
                ·
                  refine ⟨242987319820714327295719025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161991546547142884863812683 242987319820714327295719025)
                  ·
                    refine ⟨182240489865535745471789269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242987319820714327295719025 182240489865535745471789269)
                    ·
                      refine ⟨4271261481223494034495061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182240489865535745471789269 4271261481223494034495061)
                      ·
                        rfl

theorem cell23_8318252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_8318252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318252 prefixEnd_8318252 := by exact prefixLift 8318252
  have htrace : WordTrace (prefixWord ++ tailWord_8318252) baseStart_8318252 baseEnd_8318252 := by
    simpa [prefixWord, tailWord_8318252, baseEnd_8318252] using wordTrace_append hprefix tailTrace_8318252
  have hstable : (prefixWord ++ tailWord_8318252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318252).length < 2 ^ (prefixWord ++ tailWord_8318252).sum := by decide
  have hdescent : baseEnd_8318252 < baseStart_8318252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318276 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 7]
def baseStart_8318276 : Nat := 118140960795 + 8318276 * 2 ^ 59
def prefixEnd_8318276 : Nat := 4983230072969 + 3 ^ 40 * 8318276 * 2
def baseEnd_8318276 : Nat := 474585978306577993399439

theorem tailTrace_8318276 : CollatzResearch.WordTrace tailWord_8318276 prefixEnd_8318276 474585978306577993399439 := by
  unfold tailWord_8318276
  simp only [CollatzResearch.WordTrace]
  refine ⟨151696225206157087641155341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202261633608209450188207121 151696225206157087641155341)
  ·
    refine ⟨56886084452308907865433253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151696225206157087641155341 56886084452308907865433253)
    ·
      refine ⟨10666140834807920224768735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56886084452308907865433253 10666140834807920224768735)
      ·
        refine ⟨15999211252211880337153103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10666140834807920224768735 15999211252211880337153103)
        ·
          refine ⟨23998816878317820505729655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15999211252211880337153103 23998816878317820505729655)
          ·
            refine ⟨35998225317476730758594483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23998816878317820505729655 35998225317476730758594483)
            ·
              refine ⟨53997337976215096137891725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35998225317476730758594483 53997337976215096137891725)
              ·
                refine ⟨20249001741080661051709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53997337976215096137891725 20249001741080661051709397)
                ·
                  refine ⟨474585978306577993399439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20249001741080661051709397 474585978306577993399439)
                  ·
                    rfl

theorem cell23_8318276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_8318276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318276 prefixEnd_8318276 := by exact prefixLift 8318276
  have htrace : WordTrace (prefixWord ++ tailWord_8318276) baseStart_8318276 baseEnd_8318276 := by
    simpa [prefixWord, tailWord_8318276, baseEnd_8318276] using wordTrace_append hprefix tailTrace_8318276
  have hstable : (prefixWord ++ tailWord_8318276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318276).length < 2 ^ (prefixWord ++ tailWord_8318276).sum := by decide
  have hdescent : baseEnd_8318276 < baseStart_8318276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318306 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_8318306 : Nat := 118140960795 + 8318306 * 2 ^ 59
def prefixEnd_8318306 : Nat := 4983230072969 + 3 ^ 40 * 8318306 * 2
def baseEnd_8318306 : Nat := 1423763069726278941073271

theorem tailTrace_8318306 : CollatzResearch.WordTrace tailWord_8318306 prefixEnd_8318306 1423763069726278941073271 := by
  unfold tailWord_8318306
  simp only [CollatzResearch.WordTrace]
  refine ⟨75848386150551372601475693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202262363068136993603935181 75848386150551372601475693)
  ·
    refine ⟨28443144806456764725553385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75848386150551372601475693 28443144806456764725553385)
    ·
      refine ⟨21332358604842573544165039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28443144806456764725553385 21332358604842573544165039)
      ·
        refine ⟨31998537907263860316247559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21332358604842573544165039 31998537907263860316247559)
        ·
          refine ⟨47997806860895790474371339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31998537907263860316247559 47997806860895790474371339)
          ·
            refine ⟨71996710291343685711557009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47997806860895790474371339 71996710291343685711557009)
            ·
              refine ⟨53997532718507764283667757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71996710291343685711557009 53997532718507764283667757)
              ·
                refine ⟨20249074769440411606375409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53997532718507764283667757 20249074769440411606375409)
                ·
                  refine ⟨15186806077080308704781557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20249074769440411606375409 15186806077080308704781557)
                  ·
                    refine ⟨1423763069726278941073271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15186806077080308704781557 1423763069726278941073271)
                    ·
                      rfl

theorem cell23_8318306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_8318306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318306 prefixEnd_8318306 := by exact prefixLift 8318306
  have htrace : WordTrace (prefixWord ++ tailWord_8318306) baseStart_8318306 baseEnd_8318306 := by
    simpa [prefixWord, tailWord_8318306, baseEnd_8318306] using wordTrace_append hprefix tailTrace_8318306
  have hstable : (prefixWord ++ tailWord_8318306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318306).length < 2 ^ (prefixWord ++ tailWord_8318306).sum := by decide
  have hdescent : baseEnd_8318306 < baseStart_8318306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318309 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_8318309 : Nat := 118140960795 + 8318309 * 2 ^ 59
def prefixEnd_8318309 : Nat := 4983230072969 + 3 ^ 40 * 8318309 * 2
def baseEnd_8318309 : Nat := 4271290749620800311482299

theorem tailTrace_8318309 : CollatzResearch.WordTrace tailWord_8318309 prefixEnd_8318309 4271290749620800311482299 := by
  unfold tailWord_8318309
  simp only [CollatzResearch.WordTrace]
  refine ⟨303393654021194621918261981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202262436014129747945507987 303393654021194621918261981)
  ·
    refine ⟨113772620257947983219348243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303393654021194621918261981 113772620257947983219348243)
    ·
      refine ⟨170658930386921974829022365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113772620257947983219348243 170658930386921974829022365)
      ·
        refine ⟨63997098895095740560883387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170658930386921974829022365 63997098895095740560883387)
        ·
          refine ⟨95995648342643610841325081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63997098895095740560883387 95995648342643610841325081)
          ·
            refine ⟨71996736256982708130993811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95995648342643610841325081 71996736256982708130993811)
            ·
              refine ⟨107995104385474062196490717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71996736256982708130993811 107995104385474062196490717)
              ·
                refine ⟨40498164144552773323684019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107995104385474062196490717 40498164144552773323684019)
                ·
                  refine ⟨60747246216829159985526029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40498164144552773323684019 60747246216829159985526029)
                  ·
                    refine ⟨22780217331310934994572261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60747246216829159985526029 22780217331310934994572261)
                    ·
                      refine ⟨4271290749620800311482299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22780217331310934994572261 4271290749620800311482299)
                      ·
                        rfl

theorem cell23_8318309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_8318309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318309 prefixEnd_8318309 := by exact prefixLift 8318309
  have htrace : WordTrace (prefixWord ++ tailWord_8318309) baseStart_8318309 baseEnd_8318309 := by
    simpa [prefixWord, tailWord_8318309, baseEnd_8318309] using wordTrace_append hprefix tailTrace_8318309
  have hstable : (prefixWord ++ tailWord_8318309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318309).length < 2 ^ (prefixWord ++ tailWord_8318309).sum := by decide
  have hdescent : baseEnd_8318309 < baseStart_8318309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318416 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 6, 2]
def baseStart_8318416 : Nat := 118140960795 + 8318416 * 2 ^ 59
def prefixEnd_8318416 : Nat := 4983230072969 + 3 ^ 40 * 8318416 * 2
def baseEnd_8318416 : Nat := 4271345692050831392844307

theorem tailTrace_8318416 : CollatzResearch.WordTrace tailWord_8318416 prefixEnd_8318416 4271345692050831392844307 := by
  unfold tailWord_8318416
  simp only [CollatzResearch.WordTrace]
  refine ⟨151698778315903489596203551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202265037754537986128271401 151698778315903489596203551)
  ·
    refine ⟨227548167473855234394305327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151698778315903489596203551 227548167473855234394305327)
    ·
      refine ⟨341322251210782851591457991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227548167473855234394305327 341322251210782851591457991)
      ·
        refine ⟨511983376816174277387186987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341322251210782851591457991 511983376816174277387186987)
        ·
          refine ⟨767975065224261416080780481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511983376816174277387186987 767975065224261416080780481)
          ·
            refine ⟨575981298918196062060585361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767975065224261416080780481 575981298918196062060585361)
            ·
              refine ⟨431985974188647046545439021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575981298918196062060585361 431985974188647046545439021)
              ·
                refine ⟨161994740320742642454539633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431985974188647046545439021 161994740320742642454539633)
                ·
                  refine ⟨121496055240556981840904725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161994740320742642454539633 121496055240556981840904725)
                  ·
                    refine ⟨5695127589401108523792409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121496055240556981840904725 5695127589401108523792409)
                    ·
                      refine ⟨4271345692050831392844307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695127589401108523792409 4271345692050831392844307)
                      ·
                        rfl

theorem cell23_8318416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 6, 2].length) (baseStart_8318416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318416 prefixEnd_8318416 := by exact prefixLift 8318416
  have htrace : WordTrace (prefixWord ++ tailWord_8318416) baseStart_8318416 baseEnd_8318416 := by
    simpa [prefixWord, tailWord_8318416, baseEnd_8318416] using wordTrace_append hprefix tailTrace_8318416
  have hstable : (prefixWord ++ tailWord_8318416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318416).length < 2 ^ (prefixWord ++ tailWord_8318416).sum := by decide
  have hdescent : baseEnd_8318416 < baseStart_8318416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318420 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_8318420 : Nat := 118140960795 + 8318420 * 2 ^ 59
def prefixEnd_8318420 : Nat := 4983230072969 + 3 ^ 40 * 8318420 * 2
def baseEnd_8318420 : Nat := 4271347745973449377194289

theorem tailTrace_8318420 : CollatzResearch.WordTrace tailWord_8318420 prefixEnd_8318420 4271347745973449377194289 := by
  unfold tailWord_8318420
  simp only [CollatzResearch.WordTrace]
  refine ⟨151698851261896243937776357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202265135015861658583701809 151698851261896243937776357)
  ·
    refine ⟨28443534611605545738333067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151698851261896243937776357 28443534611605545738333067)
    ·
      refine ⟨42665301917408318607499601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28443534611605545738333067 42665301917408318607499601)
      ·
        refine ⟨31998976438056238955624701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42665301917408318607499601 31998976438056238955624701)
        ·
          refine ⟨11999616164271089608359263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31998976438056238955624701 11999616164271089608359263)
          ·
            refine ⟨17999424246406634412538895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11999616164271089608359263 17999424246406634412538895)
            ·
              refine ⟨26999136369609951618808343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17999424246406634412538895 26999136369609951618808343)
              ·
                refine ⟨40498704554414927428212515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26999136369609951618808343 40498704554414927428212515)
                ·
                  refine ⟨60748056831622391142318773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40498704554414927428212515 60748056831622391142318773)
                  ·
                    refine ⟨5695130327964599169592385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60748056831622391142318773 5695130327964599169592385)
                    ·
                      refine ⟨4271347745973449377194289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695130327964599169592385 4271347745973449377194289)
                      ·
                        rfl

theorem cell23_8318420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_8318420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318420 prefixEnd_8318420 := by exact prefixLift 8318420
  have htrace : WordTrace (prefixWord ++ tailWord_8318420) baseStart_8318420 baseEnd_8318420 := by
    simpa [prefixWord, tailWord_8318420, baseEnd_8318420] using wordTrace_append hprefix tailTrace_8318420
  have hstable : (prefixWord ++ tailWord_8318420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318420).length < 2 ^ (prefixWord ++ tailWord_8318420).sum := by decide
  have hdescent : baseEnd_8318420 < baseStart_8318420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318426 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_8318426 : Nat := 118140960795 + 8318426 * 2 ^ 59
def prefixEnd_8318426 : Nat := 4983230072969 + 3 ^ 40 * 8318426 * 2
def baseEnd_8318426 : Nat := 1423783608952458784573087

theorem tailTrace_8318426 : CollatzResearch.WordTrace tailWord_8318426 prefixEnd_8318426 1423783608952458784573087 := by
  unfold tailWord_8318426
  simp only [CollatzResearch.WordTrace]
  refine ⟨75849480340442687725067783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202265280907847167266847421 75849480340442687725067783)
  ·
    refine ⟨113774220510664031587601675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75849480340442687725067783 113774220510664031587601675)
    ·
      refine ⟨170661330765996047381402513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113774220510664031587601675 170661330765996047381402513)
      ·
        refine ⟨127995998074497035536051885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170661330765996047381402513 127995998074497035536051885)
        ·
          refine ⟨47998499277936388326019457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127995998074497035536051885 47998499277936388326019457)
          ·
            refine ⟨35998874458452291244514593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47998499277936388326019457 35998874458452291244514593)
            ·
              refine ⟨26999155843839218433385945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35998874458452291244514593 26999155843839218433385945)
              ·
                refine ⟨20249366882879413825039459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26999155843839218433385945 20249366882879413825039459)
                ·
                  refine ⟨30374050324319120737559189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20249366882879413825039459 30374050324319120737559189)
                  ·
                    refine ⟨1423783608952458784573087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30374050324319120737559189 1423783608952458784573087)
                    ·
                      rfl

theorem cell23_8318426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_8318426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318426 prefixEnd_8318426 := by exact prefixLift 8318426
  have htrace : WordTrace (prefixWord ++ tailWord_8318426) baseStart_8318426 baseEnd_8318426 := by
    simpa [prefixWord, tailWord_8318426, baseEnd_8318426] using wordTrace_append hprefix tailTrace_8318426
  have hstable : (prefixWord ++ tailWord_8318426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318426).length < 2 ^ (prefixWord ++ tailWord_8318426).sum := by decide
  have hdescent : baseEnd_8318426 < baseStart_8318426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318433 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_8318433 : Nat := 118140960795 + 8318433 * 2 ^ 59
def prefixEnd_8318433 : Nat := 4983230072969 + 3 ^ 40 * 8318433 * 2
def baseEnd_8318433 : Nat := 4271354421221957826331729

theorem tailTrace_8318433 : CollatzResearch.WordTrace tailWord_8318433 prefixEnd_8318433 4271354421221957826331729 := by
  unfold tailWord_8318433
  simp only [CollatzResearch.WordTrace]
  refine ⟨303398176672745391095775953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202265451115163594063850635 303398176672745391095775953)
  ·
    refine ⟨227548632504559043321831965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303398176672745391095775953 227548632504559043321831965)
    ·
      refine ⟨85330737189209641245686987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227548632504559043321831965 85330737189209641245686987)
      ·
        refine ⟨127996105783814461868530481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85330737189209641245686987 127996105783814461868530481)
        ·
          refine ⟨95997079337860846401397861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127996105783814461868530481 95997079337860846401397861)
          ·
            refine ⟨17999452375848908700262099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95997079337860846401397861 17999452375848908700262099)
            ·
              refine ⟨26999178563773363050393149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17999452375848908700262099 26999178563773363050393149)
              ·
                refine ⟨10124691961415011143897431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26999178563773363050393149 10124691961415011143897431)
                ·
                  refine ⟨15187037942122516715846147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10124691961415011143897431 15187037942122516715846147)
                  ·
                    refine ⟨22780556913183775073769221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15187037942122516715846147 22780556913183775073769221)
                    ·
                      refine ⟨4271354421221957826331729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22780556913183775073769221 4271354421221957826331729)
                      ·
                        rfl

theorem cell23_8318433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_8318433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318433 prefixEnd_8318433 := by exact prefixLift 8318433
  have htrace : WordTrace (prefixWord ++ tailWord_8318433) baseStart_8318433 baseEnd_8318433 := by
    simpa [prefixWord, tailWord_8318433, baseEnd_8318433] using wordTrace_append hprefix tailTrace_8318433
  have hstable : (prefixWord ++ tailWord_8318433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318433).length < 2 ^ (prefixWord ++ tailWord_8318433).sum := by decide
  have hdescent : baseEnd_8318433 < baseStart_8318433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318446 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_8318446 : Nat := 118140960795 + 8318446 * 2 ^ 59
def prefixEnd_8318446 : Nat := 4983230072969 + 3 ^ 40 * 8318446 * 2
def baseEnd_8318446 : Nat := 4271361096470466275469169

theorem tailTrace_8318446 : CollatzResearch.WordTrace tailWord_8318446 prefixEnd_8318446 4271361096470466275469169 := by
  unfold tailWord_8318446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37924831352712286789499899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202265767214465529543999461 37924831352712286789499899)
  ·
    refine ⟨56887247029068430184249849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37924831352712286789499899 56887247029068430184249849)
    ·
      refine ⟨42665435271801322638187387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56887247029068430184249849 42665435271801322638187387)
      ·
        refine ⟨63998152907701983957281081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42665435271801322638187387 63998152907701983957281081)
        ·
          refine ⟨47998614680776487967960811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63998152907701983957281081 47998614680776487967960811)
          ·
            refine ⟨71997922021164731951941217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47998614680776487967960811 71997922021164731951941217)
            ·
              refine ⟨53998441515873548963955913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71997922021164731951941217 53998441515873548963955913)
              ·
                refine ⟨40498831136905161722966935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53998441515873548963955913 40498831136905161722966935)
                ·
                  refine ⟨60748246705357742584450403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40498831136905161722966935 60748246705357742584450403)
                  ·
                    refine ⟨91122370058036613876675605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60748246705357742584450403 91122370058036613876675605)
                    ·
                      refine ⟨4271361096470466275469169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91122370058036613876675605 4271361096470466275469169)
                      ·
                        rfl

theorem cell23_8318446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_8318446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318446 prefixEnd_8318446 := by exact prefixLift 8318446
  have htrace : WordTrace (prefixWord ++ tailWord_8318446) baseStart_8318446 baseEnd_8318446 := by
    simpa [prefixWord, tailWord_8318446, baseEnd_8318446] using wordTrace_append hprefix tailTrace_8318446
  have hstable : (prefixWord ++ tailWord_8318446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318446).length < 2 ^ (prefixWord ++ tailWord_8318446).sum := by decide
  have hdescent : baseEnd_8318446 < baseStart_8318446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318453 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_8318453 : Nat := 118140960795 + 8318453 * 2 ^ 59
def prefixEnd_8318453 : Nat := 4983230072969 + 3 ^ 40 * 8318453 * 2
def baseEnd_8318453 : Nat := 4271364690835047748081637

theorem tailTrace_8318453 : CollatzResearch.WordTrace tailWord_8318453 prefixEnd_8318453 4271364690835047748081637 := by
  unfold tailWord_8318453
  simp only [CollatzResearch.WordTrace]
  refine ⟨303398906132672934511504013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202265937421781956341002675 303398906132672934511504013)
  ·
    refine ⟨113774589799752350441814005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303398906132672934511504013 113774589799752350441814005)
    ·
      refine ⟨10666367793726782853920063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113774589799752350441814005 10666367793726782853920063)
      ·
        refine ⟨15999551690590174280880095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10666367793726782853920063 15999551690590174280880095)
        ·
          refine ⟨23999327535885261421320143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15999551690590174280880095 23999327535885261421320143)
          ·
            refine ⟨35998991303827892131980215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23999327535885261421320143 35998991303827892131980215)
            ·
              refine ⟨53998486955741838197970323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35998991303827892131980215 53998486955741838197970323)
              ·
                refine ⟨80997730433612757296955485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53998486955741838197970323 80997730433612757296955485)
                ·
                  refine ⟨30374148912604783986358307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80997730433612757296955485 30374148912604783986358307)
                  ·
                    refine ⟨45561223368907175979537461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30374148912604783986358307 45561223368907175979537461)
                    ·
                      refine ⟨4271364690835047748081637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45561223368907175979537461 4271364690835047748081637)
                      ·
                        rfl

theorem cell23_8318453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_8318453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318453 prefixEnd_8318453 := by exact prefixLift 8318453
  have htrace : WordTrace (prefixWord ++ tailWord_8318453) baseStart_8318453 baseEnd_8318453 := by
    simpa [prefixWord, tailWord_8318453, baseEnd_8318453] using wordTrace_append hprefix tailTrace_8318453
  have hstable : (prefixWord ++ tailWord_8318453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318453).length < 2 ^ (prefixWord ++ tailWord_8318453).sum := by decide
  have hdescent : baseEnd_8318453 < baseStart_8318453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318459 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_8318459 : Nat := 118140960795 + 8318459 * 2 ^ 59
def prefixEnd_8318459 : Nat := 4983230072969 + 3 ^ 40 * 8318459 * 2
def baseEnd_8318459 : Nat := 4271367771718974724606609

theorem tailTrace_8318459 : CollatzResearch.WordTrace tailWord_8318459 prefixEnd_8318459 4271367771718974724606609 := by
  unfold tailWord_8318459
  simp only [CollatzResearch.WordTrace]
  refine ⟨303399124970651197536222431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202266083313767465024148287 303399124970651197536222431)
  ·
    refine ⟨455098687455976796304333647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303399124970651197536222431 455098687455976796304333647)
    ·
      refine ⟨682648031183965194456500471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455098687455976796304333647 682648031183965194456500471)
      ·
        refine ⟨1023972046775947791684750707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682648031183965194456500471 1023972046775947791684750707)
        ·
          refine ⟨1535958070163921687527126061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023972046775947791684750707 1535958070163921687527126061)
          ·
            refine ⟨575984276311470632822672273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1535958070163921687527126061 575984276311470632822672273)
            ·
              refine ⟨431988207233602974617004205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575984276311470632822672273 431988207233602974617004205)
              ·
                refine ⟨161995577712601115481376577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431988207233602974617004205 161995577712601115481376577)
                ·
                  refine ⟨121496683284450836611032433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161995577712601115481376577 121496683284450836611032433)
                  ·
                    refine ⟨91122512463338127458274325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121496683284450836611032433 91122512463338127458274325)
                    ·
                      refine ⟨4271367771718974724606609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91122512463338127458274325 4271367771718974724606609)
                      ·
                        rfl

theorem cell23_8318459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_8318459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318459 prefixEnd_8318459 := by exact prefixLift 8318459
  have htrace : WordTrace (prefixWord ++ tailWord_8318459) baseStart_8318459 baseEnd_8318459 := by
    simpa [prefixWord, tailWord_8318459, baseEnd_8318459] using wordTrace_append hprefix tailTrace_8318459
  have hstable : (prefixWord ++ tailWord_8318459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318459).length < 2 ^ (prefixWord ++ tailWord_8318459).sum := by decide
  have hdescent : baseEnd_8318459 < baseStart_8318459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318479 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_8318479 : Nat := 118140960795 + 8318479 * 2 ^ 59
def prefixEnd_8318479 : Nat := 4983230072969 + 3 ^ 40 * 8318479 * 2
def baseEnd_8318479 : Nat := 4271378041332064646356517

theorem tailTrace_8318479 : CollatzResearch.WordTrace tailWord_8318479 prefixEnd_8318479 4271378041332064646356517 := by
  unfold tailWord_8318479
  simp only [CollatzResearch.WordTrace]
  refine ⟨303399854430578740951950491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202266569620385827301300327 303399854430578740951950491)
  ·
    refine ⟨455099781645868111427925737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303399854430578740951950491 455099781645868111427925737)
    ·
      refine ⟨341324836234401083570944303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455099781645868111427925737 341324836234401083570944303)
      ·
        refine ⟨511987254351601625356416455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341324836234401083570944303 511987254351601625356416455)
        ·
          refine ⟨767980881527402438034624683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511987254351601625356416455 767980881527402438034624683)
          ·
            refine ⟨1151971322291103657051937025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767980881527402438034624683 1151971322291103657051937025)
            ·
              refine ⟨863978491718327742788952769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151971322291103657051937025 863978491718327742788952769)
              ·
                refine ⟨647983868788745807091714577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863978491718327742788952769 647983868788745807091714577)
                ·
                  refine ⟨485987901591559355318785933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 647983868788745807091714577 485987901591559355318785933)
                  ·
                    refine ⟨182245463096834758244544725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485987901591559355318785933 182245463096834758244544725)
                    ·
                      refine ⟨4271378041332064646356517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182245463096834758244544725 4271378041332064646356517)
                      ·
                        rfl

theorem cell23_8318479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_8318479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318479 prefixEnd_8318479 := by exact prefixLift 8318479
  have htrace : WordTrace (prefixWord ++ tailWord_8318479) baseStart_8318479 baseEnd_8318479 := by
    simpa [prefixWord, tailWord_8318479, baseEnd_8318479] using wordTrace_append hprefix tailTrace_8318479
  have hstable : (prefixWord ++ tailWord_8318479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318479).length < 2 ^ (prefixWord ++ tailWord_8318479).sum := by decide
  have hdescent : baseEnd_8318479 < baseStart_8318479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318483 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 3]
def baseStart_8318483 : Nat := 118140960795 + 8318483 * 2 ^ 59
def prefixEnd_8318483 : Nat := 4983230072969 + 3 ^ 40 * 8318483 * 2
def baseEnd_8318483 : Nat := 4271380095254682630706499

theorem tailTrace_8318483 : CollatzResearch.WordTrace tailWord_8318483 prefixEnd_8318483 4271380095254682630706499 := by
  unfold tailWord_8318483
  simp only [CollatzResearch.WordTrace]
  refine ⟨303400000322564249635096103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202266666881709499756730735 303400000322564249635096103)
  ·
    refine ⟨455100000483846374452644155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303400000322564249635096103 455100000483846374452644155)
    ·
      refine ⟨682650000725769561678966233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455100000483846374452644155 682650000725769561678966233)
      ·
        refine ⟨511987500544327171259224675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682650000725769561678966233 511987500544327171259224675)
        ·
          refine ⟨767981250816490756888837013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511987500544327171259224675 767981250816490756888837013)
          ·
            refine ⟨35999121132023004229164235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 767981250816490756888837013 35999121132023004229164235)
            ·
              refine ⟨53998681698034506343746353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35999121132023004229164235 53998681698034506343746353)
              ·
                refine ⟨40499011273525879757809765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53998681698034506343746353 40499011273525879757809765)
                ·
                  refine ⟨7593564613786102454589331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40499011273525879757809765 7593564613786102454589331)
                  ·
                    refine ⟨11390346920679153681883997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593564613786102454589331 11390346920679153681883997)
                    ·
                      refine ⟨4271380095254682630706499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11390346920679153681883997 4271380095254682630706499)
                      ·
                        rfl

theorem cell23_8318483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_8318483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318483 prefixEnd_8318483 := by exact prefixLift 8318483
  have htrace : WordTrace (prefixWord ++ tailWord_8318483) baseStart_8318483 baseEnd_8318483 := by
    simpa [prefixWord, tailWord_8318483, baseEnd_8318483] using wordTrace_append hprefix tailTrace_8318483
  have hstable : (prefixWord ++ tailWord_8318483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318483).length < 2 ^ (prefixWord ++ tailWord_8318483).sum := by decide
  have hdescent : baseEnd_8318483 < baseStart_8318483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318517 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_8318517 : Nat := 118140960795 + 8318517 * 2 ^ 59
def prefixEnd_8318517 : Nat := 4983230072969 + 3 ^ 40 * 8318517 * 2
def baseEnd_8318517 : Nat := 4271397553596935497681343

theorem tailTrace_8318517 : CollatzResearch.WordTrace tailWord_8318517 prefixEnd_8318517 4271397553596935497681343 := by
  unfold tailWord_8318517
  simp only [CollatzResearch.WordTrace]
  refine ⟨303401240404441073441833805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202267493602960715627889203 303401240404441073441833805)
  ·
    refine ⟨113775465151665402540687677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303401240404441073441833805 113775465151665402540687677)
    ·
      refine ⟨42665799431874525952757879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113775465151665402540687677 42665799431874525952757879)
      ·
        refine ⟨63998699147811788929136819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42665799431874525952757879 63998699147811788929136819)
        ·
          refine ⟨95998048721717683393705229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63998699147811788929136819 95998048721717683393705229)
          ·
            refine ⟨35999268270644131272639461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95998048721717683393705229 35999268270644131272639461)
            ·
              refine ⟨6749862800745774613619899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35999268270644131272639461 6749862800745774613619899)
              ·
                refine ⟨10124794201118661920429849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749862800745774613619899 10124794201118661920429849)
                ·
                  refine ⟨7593595650838996440322387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10124794201118661920429849 7593595650838996440322387)
                  ·
                    refine ⟨11390393476258494660483581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593595650838996440322387 11390393476258494660483581)
                    ·
                      refine ⟨4271397553596935497681343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11390393476258494660483581 4271397553596935497681343)
                      ·
                        rfl

theorem cell23_8318517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_8318517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318517 prefixEnd_8318517 := by exact prefixLift 8318517
  have htrace : WordTrace (prefixWord ++ tailWord_8318517) baseStart_8318517 baseEnd_8318517 := by
    simpa [prefixWord, tailWord_8318517, baseEnd_8318517] using wordTrace_append hprefix tailTrace_8318517
  have hstable : (prefixWord ++ tailWord_8318517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318517).length < 2 ^ (prefixWord ++ tailWord_8318517).sum := by decide
  have hdescent : baseEnd_8318517 < baseStart_8318517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318527 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 1, 3, 2]
def baseStart_8318527 : Nat := 118140960795 + 8318527 * 2 ^ 59
def prefixEnd_8318527 : Nat := 4983230072969 + 3 ^ 40 * 8318527 * 2
def baseEnd_8318527 : Nat := 4271402688403480458556297

theorem tailTrace_8318527 : CollatzResearch.WordTrace tailWord_8318527 prefixEnd_8318527 4271402688403480458556297 := by
  unfold tailWord_8318527
  simp only [CollatzResearch.WordTrace]
  refine ⟨303401605134404845149697835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202267736756269896766465223 303401605134404845149697835)
  ·
    refine ⟨455102407701607267724546753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303401605134404845149697835 455102407701607267724546753)
    ·
      refine ⟨341326805776205450793410065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455102407701607267724546753 341326805776205450793410065)
      ·
        refine ⟨255995104332154088095057549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341326805776205450793410065 255995104332154088095057549)
        ·
          refine ⟨95998164124557783035646581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255995104332154088095057549 95998164124557783035646581)
          ·
            refine ⟨8999827886677292159591867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95998164124557783035646581 8999827886677292159591867)
            ·
              refine ⟨13499741830015938239387801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999827886677292159591867 13499741830015938239387801)
              ·
                refine ⟨10124806372511953679540851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13499741830015938239387801 10124806372511953679540851)
                ·
                  refine ⟨15187209558767930519311277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10124806372511953679540851 15187209558767930519311277)
                  ·
                    refine ⟨5695203584537973944741729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15187209558767930519311277 5695203584537973944741729)
                    ·
                      refine ⟨4271402688403480458556297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695203584537973944741729 4271402688403480458556297)
                      ·
                        rfl

theorem cell23_8318527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_8318527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318527 prefixEnd_8318527 := by exact prefixLift 8318527
  have htrace : WordTrace (prefixWord ++ tailWord_8318527) baseStart_8318527 baseEnd_8318527 := by
    simpa [prefixWord, tailWord_8318527, baseEnd_8318527] using wordTrace_append hprefix tailTrace_8318527
  have hstable : (prefixWord ++ tailWord_8318527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318527).length < 2 ^ (prefixWord ++ tailWord_8318527).sum := by decide
  have hdescent : baseEnd_8318527 < baseStart_8318527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318536 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_8318536 : Nat := 118140960795 + 8318536 * 2 ^ 59
def prefixEnd_8318536 : Nat := 4983230072969 + 3 ^ 40 * 8318536 * 2
def baseEnd_8318536 : Nat := 4271407309729370923343755

theorem tailTrace_8318536 : CollatzResearch.WordTrace tailWord_8318536 prefixEnd_8318536 4271407309729370923343755 := by
  unfold tailWord_8318536
  simp only [CollatzResearch.WordTrace]
  refine ⟨151700966695686119843387731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202267955594248159791183641 151700966695686119843387731)
  ·
    refine ⟨227551450043529179765081597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151700966695686119843387731 227551450043529179765081597)
    ·
      refine ⟨85331793766323442411905599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227551450043529179765081597 85331793766323442411905599)
      ·
        refine ⟨127997690649485163617858399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85331793766323442411905599 127997690649485163617858399)
        ·
          refine ⟨191996535974227745426787599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127997690649485163617858399 191996535974227745426787599)
          ·
            refine ⟨287994803961341618140181399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191996535974227745426787599 287994803961341618140181399)
            ·
              refine ⟨431992205942012427210272099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287994803961341618140181399 431992205942012427210272099)
              ·
                refine ⟨647988308913018640815408149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431992205942012427210272099 647988308913018640815408149)
                ·
                  refine ⟨30374451980297748788222257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 647988308913018640815408149 30374451980297748788222257)
                  ·
                    refine ⟨22780838985223311591166693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30374451980297748788222257 22780838985223311591166693)
                    ·
                      refine ⟨4271407309729370923343755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22780838985223311591166693 4271407309729370923343755)
                      ·
                        rfl

theorem cell23_8318536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_8318536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318536 prefixEnd_8318536 := by exact prefixLift 8318536
  have htrace : WordTrace (prefixWord ++ tailWord_8318536) baseStart_8318536 baseEnd_8318536 := by
    simpa [prefixWord, tailWord_8318536, baseEnd_8318536] using wordTrace_append hprefix tailTrace_8318536
  have hstable : (prefixWord ++ tailWord_8318536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318536).length < 2 ^ (prefixWord ++ tailWord_8318536).sum := by decide
  have hdescent : baseEnd_8318536 < baseStart_8318536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318540 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 1, 4, 2]
def baseStart_8318540 : Nat := 118140960795 + 8318540 * 2 ^ 59
def prefixEnd_8318540 : Nat := 4983230072969 + 3 ^ 40 * 8318540 * 2
def baseEnd_8318540 : Nat := 4271409363651988907693737

theorem tailTrace_8318540 : CollatzResearch.WordTrace tailWord_8318540 prefixEnd_8318540 4271409363651988907693737 := by
  unfold tailWord_8318540
  simp only [CollatzResearch.WordTrace]
  refine ⟨151701039641678874184960537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202268052855571832246614049 151701039641678874184960537)
  ·
    refine ⟨113775779731259155638720403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151701039641678874184960537 113775779731259155638720403)
    ·
      refine ⟨170663669596888733458080605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113775779731259155638720403 170663669596888733458080605)
      ·
        refine ⟨63998876098833275046780227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170663669596888733458080605 63998876098833275046780227)
        ·
          refine ⟨95998314148249912570170341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63998876098833275046780227 95998314148249912570170341)
          ·
            refine ⟨17999683902796858606906939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95998314148249912570170341 17999683902796858606906939)
            ·
              refine ⟨26999525854195287910360409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17999683902796858606906939 26999525854195287910360409)
              ·
                refine ⟨20249644390646465932770307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26999525854195287910360409 20249644390646465932770307)
                ·
                  refine ⟨30374466585969698899155461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20249644390646465932770307 30374466585969698899155461)
                  ·
                    refine ⟨5695212484869318543591649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30374466585969698899155461 5695212484869318543591649)
                    ·
                      refine ⟨4271409363651988907693737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695212484869318543591649 4271409363651988907693737)
                      ·
                        rfl

theorem cell23_8318540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_8318540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318540 prefixEnd_8318540 := by exact prefixLift 8318540
  have htrace : WordTrace (prefixWord ++ tailWord_8318540) baseStart_8318540 baseEnd_8318540 := by
    simpa [prefixWord, tailWord_8318540, baseEnd_8318540] using wordTrace_append hprefix tailTrace_8318540
  have hstable : (prefixWord ++ tailWord_8318540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318540).length < 2 ^ (prefixWord ++ tailWord_8318540).sum := by decide
  have hdescent : baseEnd_8318540 < baseStart_8318540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318583 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 4, 5, 2]
def baseStart_8318583 : Nat := 118140960795 + 8318583 * 2 ^ 59
def prefixEnd_8318583 : Nat := 4983230072969 + 3 ^ 40 * 8318583 * 2
def baseEnd_8318583 : Nat := 4271431443320132239456039

theorem tailTrace_8318583 : CollatzResearch.WordTrace tailWord_8318583 prefixEnd_8318583 4271431443320132239456039 := by
  unfold tailWord_8318583
  simp only [CollatzResearch.WordTrace]
  refine ⟨303403647622201966713736403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202269098414801311142490935 303403647622201966713736403)
  ·
    refine ⟨455105471433302950070604605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303403647622201966713736403 455105471433302950070604605)
    ·
      refine ⟨170664551787488606276476727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455105471433302950070604605 170664551787488606276476727)
      ·
        refine ⟨255996827681232909414715091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170664551787488606276476727 255996827681232909414715091)
        ·
          refine ⟨383995241521849364122072637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255996827681232909414715091 383995241521849364122072637)
          ·
            refine ⟨143998215570693511545777239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383995241521849364122072637 143998215570693511545777239)
            ·
              refine ⟨215997323356040267318665859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143998215570693511545777239 215997323356040267318665859)
              ·
                refine ⟨323995985034060400977998789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215997323356040267318665859 323995985034060400977998789)
                ·
                  refine ⟨60749247193886325183374773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323995985034060400977998789 60749247193886325183374773)
                  ·
                    refine ⟨5695241924426842985941385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60749247193886325183374773 5695241924426842985941385)
                    ·
                      refine ⟨4271431443320132239456039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695241924426842985941385 4271431443320132239456039)
                      ·
                        rfl

theorem cell23_8318583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_8318583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318583 prefixEnd_8318583 := by exact prefixLift 8318583
  have htrace : WordTrace (prefixWord ++ tailWord_8318583) baseStart_8318583 baseEnd_8318583 := by
    simpa [prefixWord, tailWord_8318583, baseEnd_8318583] using wordTrace_append hprefix tailTrace_8318583
  have hstable : (prefixWord ++ tailWord_8318583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318583).length < 2 ^ (prefixWord ++ tailWord_8318583).sum := by decide
  have hdescent : baseEnd_8318583 < baseStart_8318583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318586 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_8318586 : Nat := 118140960795 + 8318586 * 2 ^ 59
def prefixEnd_8318586 : Nat := 4983230072969 + 3 ^ 40 * 8318586 * 2
def baseEnd_8318586 : Nat := 4271432983762095727718525

theorem tailTrace_8318586 : CollatzResearch.WordTrace tailWord_8318586 prefixEnd_8318586 4271432983762095727718525 := by
  unfold tailWord_8318586
  simp only [CollatzResearch.WordTrace]
  refine ⟨75850939260297774556523903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202269171360794065484063741 75850939260297774556523903)
  ·
    refine ⟨113776408890446661834785855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75850939260297774556523903 113776408890446661834785855)
    ·
      refine ⟨170664613335669992752178783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113776408890446661834785855 170664613335669992752178783)
      ·
        refine ⟨255996920003504989128268175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170664613335669992752178783 255996920003504989128268175)
        ·
          refine ⟨383995380005257483692402263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255996920003504989128268175 383995380005257483692402263)
          ·
            refine ⟨575993070007886225538603395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383995380005257483692402263 575993070007886225538603395)
            ·
              refine ⟨863989605011829338307905093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575993070007886225538603395 863989605011829338307905093)
              ·
                refine ⟨161998050939718000932732205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 863989605011829338307905093 161998050939718000932732205)
                ·
                  refine ⟨60749269102394250349774577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161998050939718000932732205 60749269102394250349774577)
                  ·
                    refine ⟨45561951826795687762330933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60749269102394250349774577 45561951826795687762330933)
                    ·
                      refine ⟨4271432983762095727718525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45561951826795687762330933 4271432983762095727718525)
                      ·
                        rfl

theorem cell23_8318586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_8318586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318586 prefixEnd_8318586 := by exact prefixLift 8318586
  have htrace : WordTrace (prefixWord ++ tailWord_8318586) baseStart_8318586 baseEnd_8318586 := by
    simpa [prefixWord, tailWord_8318586, baseEnd_8318586] using wordTrace_append hprefix tailTrace_8318586
  have hstable : (prefixWord ++ tailWord_8318586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318586).length < 2 ^ (prefixWord ++ tailWord_8318586).sum := by decide
  have hdescent : baseEnd_8318586 < baseStart_8318586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318593 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_8318593 : Nat := 118140960795 + 8318593 * 2 ^ 59
def prefixEnd_8318593 : Nat := 4983230072969 + 3 ^ 40 * 8318593 * 2
def baseEnd_8318593 : Nat := 1423812192708892400110331

theorem tailTrace_8318593 : CollatzResearch.WordTrace tailWord_8318593 prefixEnd_8318593 1423812192708892400110331 := by
  unfold tailWord_8318593
  simp only [CollatzResearch.WordTrace]
  refine ⟨303404012352165738421600433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202269341568110492281066955 303404012352165738421600433)
  ·
    refine ⟨227553009264124303816200325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303404012352165738421600433 227553009264124303816200325)
    ·
      refine ⟨42666189237023306965537561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227553009264124303816200325 42666189237023306965537561)
      ·
        refine ⟨31999641927767480224153171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42666189237023306965537561 31999641927767480224153171)
        ·
          refine ⟨47999462891651220336229757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31999641927767480224153171 47999462891651220336229757)
          ·
            refine ⟨17999798584369207626086159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47999462891651220336229757 17999798584369207626086159)
            ·
              refine ⟨26999697876553811439129239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17999798584369207626086159 26999697876553811439129239)
              ·
                refine ⟨40499546814830717158693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26999697876553811439129239 40499546814830717158693859)
                ·
                  refine ⟨60749320222246075738040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40499546814830717158693859 60749320222246075738040789)
                  ·
                    refine ⟨1423812192708892400110331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60749320222246075738040789 1423812192708892400110331)
                    ·
                      rfl

theorem cell23_8318593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_8318593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318593 prefixEnd_8318593 := by exact prefixLift 8318593
  have htrace : WordTrace (prefixWord ++ tailWord_8318593) baseStart_8318593 baseEnd_8318593 := by
    simpa [prefixWord, tailWord_8318593, baseEnd_8318593] using wordTrace_append hprefix tailTrace_8318593
  have hstable : (prefixWord ++ tailWord_8318593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318593).length < 2 ^ (prefixWord ++ tailWord_8318593).sum := by decide
  have hdescent : baseEnd_8318593 < baseStart_8318593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318613 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_8318613 : Nat := 118140960795 + 8318613 * 2 ^ 59
def prefixEnd_8318613 : Nat := 4983230072969 + 3 ^ 40 * 8318613 * 2
def baseEnd_8318613 : Nat := 4271446847739767122080901

theorem tailTrace_8318613 : CollatzResearch.WordTrace tailWord_8318613 prefixEnd_8318613 4271446847739767122080901 := by
  unfold tailWord_8318613
  simp only [CollatzResearch.WordTrace]
  refine ⟨303404741812093281837328493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202269827874728854558218995 303404741812093281837328493)
  ·
    refine ⟨113776778179534980688998185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303404741812093281837328493 113776778179534980688998185)
    ·
      refine ⟨85332583634651235516748639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113776778179534980688998185 85332583634651235516748639)
      ·
        refine ⟨127998875451976853275122959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85332583634651235516748639 127998875451976853275122959)
        ·
          refine ⟨191998313177965279912684439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127998875451976853275122959 191998313177965279912684439)
          ·
            refine ⟨287997469766947919869026659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191998313177965279912684439 287997469766947919869026659)
            ·
              refine ⟨431996204650421879803539989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287997469766947919869026659 431996204650421879803539989)
              ·
                refine ⟨20249822092988525615790937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 431996204650421879803539989 20249822092988525615790937)
                ·
                  refine ⟨15187366569741394211843203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20249822092988525615790937 15187366569741394211843203)
                  ·
                    refine ⟨22781049854612091317764805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15187366569741394211843203 22781049854612091317764805)
                    ·
                      refine ⟨4271446847739767122080901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22781049854612091317764805 4271446847739767122080901)
                      ·
                        rfl

theorem cell23_8318613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_8318613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318613 prefixEnd_8318613 := by exact prefixLift 8318613
  have htrace : WordTrace (prefixWord ++ tailWord_8318613) baseStart_8318613 baseEnd_8318613 := by
    simpa [prefixWord, tailWord_8318613, baseEnd_8318613] using wordTrace_append hprefix tailTrace_8318613
  have hstable : (prefixWord ++ tailWord_8318613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318613).length < 2 ^ (prefixWord ++ tailWord_8318613).sum := by decide
  have hdescent : baseEnd_8318613 < baseStart_8318613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318700 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_8318700 : Nat := 118140960795 + 8318700 * 2 ^ 59
def prefixEnd_8318700 : Nat := 4983230072969 + 3 ^ 40 * 8318700 * 2
def baseEnd_8318700 : Nat := 1423830506852236093897667

theorem tailTrace_8318700 : CollatzResearch.WordTrace tailWord_8318700 prefixEnd_8318700 1423830506852236093897667 := by
  unfold tailWord_8318700
  simp only [CollatzResearch.WordTrace]
  refine ⟨151703957481389047847872777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202271943308518730463830369 151703957481389047847872777)
  ·
    refine ⟨113777968111041785885904583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151703957481389047847872777 113777968111041785885904583)
    ·
      refine ⟨170666952166562678828856875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113777968111041785885904583 170666952166562678828856875)
      ·
        refine ⟨256000428249844018243285313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170666952166562678828856875 256000428249844018243285313)
        ·
          refine ⟨192000321187383013682463985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256000428249844018243285313 192000321187383013682463985)
          ·
            refine ⟨144000240890537260261847989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192000321187383013682463985 144000240890537260261847989)
            ·
              refine ⟨13500022583487868149548249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144000240890537260261847989 13500022583487868149548249)
              ·
                refine ⟨10125016937615901112161187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13500022583487868149548249 10125016937615901112161187)
                ·
                  refine ⟨15187525406423851668241781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125016937615901112161187 15187525406423851668241781)
                  ·
                    refine ⟨1423830506852236093897667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15187525406423851668241781 1423830506852236093897667)
                    ·
                      rfl

theorem cell23_8318700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_8318700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318700 prefixEnd_8318700 := by exact prefixLift 8318700
  have htrace : WordTrace (prefixWord ++ tailWord_8318700) baseStart_8318700 baseEnd_8318700 := by
    simpa [prefixWord, tailWord_8318700, baseEnd_8318700] using wordTrace_append hprefix tailTrace_8318700
  have hstable : (prefixWord ++ tailWord_8318700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318700).length < 2 ^ (prefixWord ++ tailWord_8318700).sum := by decide
  have hdescent : baseEnd_8318700 < baseStart_8318700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318737 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 3, 2, 2]
def baseStart_8318737 : Nat := 118140960795 + 8318737 * 2 ^ 59
def prefixEnd_8318737 : Nat := 4983230072969 + 3 ^ 40 * 8318737 * 2
def baseEnd_8318737 : Nat := 4271510519340924636930331

theorem tailTrace_8318737 : CollatzResearch.WordTrace tailWord_8318737 prefixEnd_8318737 4271510519340924636930331 := by
  unfold tailWord_8318737
  simp only [CollatzResearch.WordTrace]
  refine ⟨303409264463644051014842465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202272842975762700676561643 303409264463644051014842465)
  ·
    refine ⟨227556948347733038261131849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303409264463644051014842465 227556948347733038261131849)
    ·
      refine ⟨170667711260799778695848887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227556948347733038261131849 170667711260799778695848887)
      ·
        refine ⟨256001566891199668043773331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170667711260799778695848887 256001566891199668043773331)
        ·
          refine ⟨384002350336799502065659997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256001566891199668043773331 384002350336799502065659997)
          ·
            refine ⟨144000881376299813274622499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384002350336799502065659997 144000881376299813274622499)
            ·
              refine ⟨216001322064449719911933749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144000881376299813274622499 216001322064449719911933749)
              ·
                refine ⟨20250123943542161241743789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216001322064449719911933749 20250123943542161241743789)
                ·
                  refine ⟨7593796478828310465653921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20250123943542161241743789 7593796478828310465653921)
                  ·
                    refine ⟨5695347359121232849240441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7593796478828310465653921 5695347359121232849240441)
                    ·
                      refine ⟨4271510519340924636930331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695347359121232849240441 4271510519340924636930331)
                      ·
                        rfl

theorem cell23_8318737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_8318737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318737 prefixEnd_8318737 := by exact prefixLift 8318737
  have htrace : WordTrace (prefixWord ++ tailWord_8318737) baseStart_8318737 baseEnd_8318737 := by
    simpa [prefixWord, tailWord_8318737, baseEnd_8318737] using wordTrace_append hprefix tailTrace_8318737
  have hstable : (prefixWord ++ tailWord_8318737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318737).length < 2 ^ (prefixWord ++ tailWord_8318737).sum := by decide
  have hdescent : baseEnd_8318737 < baseStart_8318737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318754 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_8318754 : Nat := 118140960795 + 8318754 * 2 ^ 59
def prefixEnd_8318754 : Nat := 4983230072969 + 3 ^ 40 * 8318754 * 2
def baseEnd_8318754 : Nat := 4271519248512051070417753

theorem tailTrace_8318754 : CollatzResearch.WordTrace tailWord_8318754 prefixEnd_8318754 4271519248512051070417753 := by
  unfold tailWord_8318754
  simp only [CollatzResearch.WordTrace]
  refine ⟨75852471126145615729552829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202273256336388308612140877 75852471126145615729552829)
  ·
    refine ⟨28444676672304605898582311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75852471126145615729552829 28444676672304605898582311)
    ·
      refine ⟨42667015008456908847873467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28444676672304605898582311 42667015008456908847873467)
      ·
        refine ⟨64000522512685363271810201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42667015008456908847873467 64000522512685363271810201)
        ·
          refine ⟨48000391884514022453857651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64000522512685363271810201 48000391884514022453857651)
          ·
            refine ⟨72000587826771033680786477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48000391884514022453857651 72000587826771033680786477)
            ·
              refine ⟨27000220435039137630294929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72000587826771033680786477 27000220435039137630294929)
              ·
                refine ⟨20250165326279353222721197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27000220435039137630294929 20250165326279353222721197)
                ·
                  refine ⟨7593811997354757458520449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20250165326279353222721197 7593811997354757458520449)
                  ·
                    refine ⟨5695358998016068093890337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7593811997354757458520449 5695358998016068093890337)
                    ·
                      refine ⟨4271519248512051070417753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695358998016068093890337 4271519248512051070417753)
                      ·
                        rfl

theorem cell23_8318754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_8318754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318754 prefixEnd_8318754 := by exact prefixLift 8318754
  have htrace : WordTrace (prefixWord ++ tailWord_8318754) baseStart_8318754 baseEnd_8318754 := by
    simpa [prefixWord, tailWord_8318754, baseEnd_8318754] using wordTrace_append hprefix tailTrace_8318754
  have hstable : (prefixWord ++ tailWord_8318754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318754).length < 2 ^ (prefixWord ++ tailWord_8318754).sum := by decide
  have hdescent : baseEnd_8318754 < baseStart_8318754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318771 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 1, 1, 4]
def baseStart_8318771 : Nat := 118140960795 + 8318771 * 2 ^ 59
def prefixEnd_8318771 : Nat := 4983230072969 + 3 ^ 40 * 8318771 * 2
def baseEnd_8318771 : Nat := 4271527977683177503905175

theorem tailTrace_8318771 : CollatzResearch.WordTrace tailWord_8318771 prefixEnd_8318771 4271527977683177503905175 := by
  unfold tailWord_8318771
  simp only [CollatzResearch.WordTrace]
  refine ⟨303410504545520874821580167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202273669697013916547720111 303410504545520874821580167)
  ·
    refine ⟨455115756818281312232370251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303410504545520874821580167 455115756818281312232370251)
    ·
      refine ⟨682673635227421968348555377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455115756818281312232370251 682673635227421968348555377)
      ·
        refine ⟨512005226420566476261416533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682673635227421968348555377 512005226420566476261416533)
        ·
          refine ⟨6000061247116013393688475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 512005226420566476261416533 6000061247116013393688475)
          ·
            refine ⟨9000091870674020090532713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000061247116013393688475 9000091870674020090532713)
            ·
              refine ⟨6750068903005515067899535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000091870674020090532713 6750068903005515067899535)
              ·
                refine ⟨10125103354508272601849303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750068903005515067899535 10125103354508272601849303)
                ·
                  refine ⟨15187655031762408902773955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125103354508272601849303 15187655031762408902773955)
                  ·
                    refine ⟨22781482547643613354160933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15187655031762408902773955 22781482547643613354160933)
                    ·
                      refine ⟨4271527977683177503905175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22781482547643613354160933 4271527977683177503905175)
                      ·
                        rfl

theorem cell23_8318771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 1, 4].length) (baseStart_8318771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318771 prefixEnd_8318771 := by exact prefixLift 8318771
  have htrace : WordTrace (prefixWord ++ tailWord_8318771) baseStart_8318771 baseEnd_8318771 := by
    simpa [prefixWord, tailWord_8318771, baseEnd_8318771] using wordTrace_append hprefix tailTrace_8318771
  have hstable : (prefixWord ++ tailWord_8318771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318771).length < 2 ^ (prefixWord ++ tailWord_8318771).sum := by decide
  have hdescent : baseEnd_8318771 < baseStart_8318771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318787 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 3]
def baseStart_8318787 : Nat := 118140960795 + 8318787 * 2 ^ 59
def prefixEnd_8318787 : Nat := 4983230072969 + 3 ^ 40 * 8318787 * 2
def baseEnd_8318787 : Nat := 4271536193373649441305101

theorem tailTrace_8318787 : CollatzResearch.WordTrace tailWord_8318787 prefixEnd_8318787 4271536193373649441305101 := by
  unfold tailWord_8318787
  simp only [CollatzResearch.WordTrace]
  refine ⟨303411088113462909554162615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202274058742308606369441743 303411088113462909554162615)
  ·
    refine ⟨455116632170194364331243923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303411088113462909554162615 455116632170194364331243923)
    ·
      refine ⟨682674948255291546496865885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455116632170194364331243923 682674948255291546496865885)
      ·
        refine ⟨256003105595734329936324707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682674948255291546496865885 256003105595734329936324707)
        ·
          refine ⟨384004658393601494904487061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256003105595734329936324707 384004658393601494904487061)
          ·
            refine ⟨18000218362200070073647831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 384004658393601494904487061 18000218362200070073647831)
            ·
              refine ⟨27000327543300105110471747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18000218362200070073647831 27000327543300105110471747)
              ·
                refine ⟨40500491314950157665707621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27000327543300105110471747 40500491314950157665707621)
                ·
                  refine ⟨7593842121553154562320179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40500491314950157665707621 7593842121553154562320179)
                  ·
                    refine ⟨11390763182329731843480269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593842121553154562320179 11390763182329731843480269)
                    ·
                      refine ⟨4271536193373649441305101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11390763182329731843480269 4271536193373649441305101)
                      ·
                        rfl

theorem cell23_8318787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_8318787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318787 prefixEnd_8318787 := by exact prefixLift 8318787
  have htrace : WordTrace (prefixWord ++ tailWord_8318787) baseStart_8318787 baseEnd_8318787 := by
    simpa [prefixWord, tailWord_8318787, baseEnd_8318787] using wordTrace_append hprefix tailTrace_8318787
  have hstable : (prefixWord ++ tailWord_8318787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318787).length < 2 ^ (prefixWord ++ tailWord_8318787).sum := by decide
  have hdescent : baseEnd_8318787 < baseStart_8318787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318804 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_8318804 : Nat := 118140960795 + 8318804 * 2 ^ 59
def prefixEnd_8318804 : Nat := 4983230072969 + 3 ^ 40 * 8318804 * 2
def baseEnd_8318804 : Nat := 4271544922544775874792523

theorem tailTrace_8318804 : CollatzResearch.WordTrace tailWord_8318804 prefixEnd_8318804 4271544922544775874792523 := by
  unfold tailWord_8318804
  simp only [CollatzResearch.WordTrace]
  refine ⟨151705854077200660728765733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202274472102934214305020977 151705854077200660728765733)
  ·
    refine ⟨28444847639475123886643575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151705854077200660728765733 28444847639475123886643575)
    ·
      refine ⟨42667271459212685829965363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28444847639475123886643575 42667271459212685829965363)
      ·
        refine ⟨64000907188819028744948045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42667271459212685829965363 64000907188819028744948045)
        ·
          refine ⟨24000340195807135779355517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64000907188819028744948045 24000340195807135779355517)
          ·
            refine ⟨9000127573427675917258319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24000340195807135779355517 9000127573427675917258319)
            ·
              refine ⟨13500191360141513875887479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9000127573427675917258319 13500191360141513875887479)
              ·
                refine ⟨20250287040212270813831219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13500191360141513875887479 20250287040212270813831219)
                ·
                  refine ⟨30375430560318406220746829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20250287040212270813831219 30375430560318406220746829)
                  ·
                    refine ⟨11390786460119402332780061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30375430560318406220746829 11390786460119402332780061)
                    ·
                      refine ⟨4271544922544775874792523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11390786460119402332780061 4271544922544775874792523)
                      ·
                        rfl

theorem cell23_8318804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_8318804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318804 prefixEnd_8318804 := by exact prefixLift 8318804
  have htrace : WordTrace (prefixWord ++ tailWord_8318804) baseStart_8318804 baseEnd_8318804 := by
    simpa [prefixWord, tailWord_8318804, baseEnd_8318804] using wordTrace_append hprefix tailTrace_8318804
  have hstable : (prefixWord ++ tailWord_8318804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318804).length < 2 ^ (prefixWord ++ tailWord_8318804).sum := by decide
  have hdescent : baseEnd_8318804 < baseStart_8318804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318843 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_8318843 : Nat := 118140960795 + 8318843 * 2 ^ 59
def prefixEnd_8318843 : Nat := 4983230072969 + 3 ^ 40 * 8318843 * 2
def baseEnd_8318843 : Nat := 4271564948290301222204843

theorem tailTrace_8318843 : CollatzResearch.WordTrace tailWord_8318843 prefixEnd_8318843 4271564948290301222204843 := by
  unfold tailWord_8318843
  simp only [CollatzResearch.WordTrace]
  refine ⟨303413130601260031118201183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202275420400840020745467455 303413130601260031118201183)
  ·
    refine ⟨455119695901890046677301775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303413130601260031118201183 455119695901890046677301775)
    ·
      refine ⟨682679543852835070015952663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455119695901890046677301775 682679543852835070015952663)
      ·
        refine ⟨1024019315779252605023928995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682679543852835070015952663 1024019315779252605023928995)
        ·
          refine ⟨1536028973668878907535893493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024019315779252605023928995 1536028973668878907535893493)
          ·
            refine ⟨144002716281457397581490015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1536028973668878907535893493 144002716281457397581490015)
            ·
              refine ⟨216004074422186096372235023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144002716281457397581490015 216004074422186096372235023)
              ·
                refine ⟨324006111633279144558352535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216004074422186096372235023 324006111633279144558352535)
                ·
                  refine ⟨486009167449918716837528803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324006111633279144558352535 486009167449918716837528803)
                  ·
                    refine ⟨729013751174878075256293205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486009167449918716837528803 729013751174878075256293205)
                    ·
                      refine ⟨4271564948290301222204843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 729013751174878075256293205 4271564948290301222204843)
                      ·
                        rfl

theorem cell23_8318843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_8318843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318843 prefixEnd_8318843 := by exact prefixLift 8318843
  have htrace : WordTrace (prefixWord ++ tailWord_8318843) baseStart_8318843 baseEnd_8318843 := by
    simpa [prefixWord, tailWord_8318843, baseEnd_8318843] using wordTrace_append hprefix tailTrace_8318843
  have hstable : (prefixWord ++ tailWord_8318843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318843).length < 2 ^ (prefixWord ++ tailWord_8318843).sum := by decide
  have hdescent : baseEnd_8318843 < baseStart_8318843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318860 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_8318860 : Nat := 118140960795 + 8318860 * 2 ^ 59
def prefixEnd_8318860 : Nat := 4983230072969 + 3 ^ 40 * 8318860 * 2
def baseEnd_8318860 : Nat := 4271573677461427655692265

theorem tailTrace_8318860 : CollatzResearch.WordTrace tailWord_8318860 prefixEnd_8318860 4271573677461427655692265 := by
  unfold tailWord_8318860
  simp only [CollatzResearch.WordTrace]
  refine ⟨151706875321099221510785017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202275833761465628681046689 151706875321099221510785017)
  ·
    refine ⟨113780156490824416133088763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151706875321099221510785017 113780156490824416133088763)
    ·
      refine ⟨170670234736236624199633145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113780156490824416133088763 170670234736236624199633145)
      ·
        refine ⟨128002676052177468149724859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170670234736236624199633145 128002676052177468149724859)
        ·
          refine ⟨192004014078266202224587289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128002676052177468149724859 192004014078266202224587289)
          ·
            refine ⟨144003010558699651668440467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192004014078266202224587289 144003010558699651668440467)
            ·
              refine ⟨216004515838049477502660701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144003010558699651668440467 216004515838049477502660701)
              ·
                refine ⟨81001693439268554063497763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216004515838049477502660701 81001693439268554063497763)
                ·
                  refine ⟨121502540158902831095246645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81001693439268554063497763 121502540158902831095246645)
                  ·
                    refine ⟨11390863139897140415179373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121502540158902831095246645 11390863139897140415179373)
                    ·
                      refine ⟨4271573677461427655692265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11390863139897140415179373 4271573677461427655692265)
                      ·
                        rfl

theorem cell23_8318860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_8318860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318860 prefixEnd_8318860 := by exact prefixLift 8318860
  have htrace : WordTrace (prefixWord ++ tailWord_8318860) baseStart_8318860 baseEnd_8318860 := by
    simpa [prefixWord, tailWord_8318860, baseEnd_8318860] using wordTrace_append hprefix tailTrace_8318860
  have hstable : (prefixWord ++ tailWord_8318860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318860).length < 2 ^ (prefixWord ++ tailWord_8318860).sum := by decide
  have hdescent : baseEnd_8318860 < baseStart_8318860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318878 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_8318878 : Nat := 118140960795 + 8318878 * 2 ^ 59
def prefixEnd_8318878 : Nat := 4983230072969 + 3 ^ 40 * 8318878 * 2
def baseEnd_8318878 : Nat := 4271582920113208585267183

theorem tailTrace_8318878 : CollatzResearch.WordTrace tailWord_8318878 prefixEnd_8318878 4271582920113208585267183 := by
  unfold tailWord_8318878
  simp only [CollatzResearch.WordTrace]
  refine ⟨37926800894516654011965661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202276271437422154730483525 37926800894516654011965661)
  ·
    refine ⟨14222550335443745254487123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37926800894516654011965661 14222550335443745254487123)
    ·
      refine ⟨21333825503165617881730685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14222550335443745254487123 21333825503165617881730685)
      ·
        refine ⟨8000184563687106705649007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21333825503165617881730685 8000184563687106705649007)
        ·
          refine ⟨12000276845530660058473511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8000184563687106705649007 12000276845530660058473511)
          ·
            refine ⟨18000415268295990087710267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12000276845530660058473511 18000415268295990087710267)
            ·
              refine ⟨27000622902443985131565401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18000415268295990087710267 27000622902443985131565401)
              ·
                refine ⟨20250467176832988848674051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27000622902443985131565401 20250467176832988848674051)
                ·
                  refine ⟨30375700765249483273011077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20250467176832988848674051 30375700765249483273011077)
                  ·
                    refine ⟨5695443893484278113689577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30375700765249483273011077 5695443893484278113689577)
                    ·
                      refine ⟨4271582920113208585267183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695443893484278113689577 4271582920113208585267183)
                      ·
                        rfl

theorem cell23_8318878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_8318878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318878 prefixEnd_8318878 := by exact prefixLift 8318878
  have htrace : WordTrace (prefixWord ++ tailWord_8318878) baseStart_8318878 baseEnd_8318878 := by
    simpa [prefixWord, tailWord_8318878, baseEnd_8318878] using wordTrace_append hprefix tailTrace_8318878
  have hstable : (prefixWord ++ tailWord_8318878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318878).length < 2 ^ (prefixWord ++ tailWord_8318878).sum := by decide
  have hdescent : baseEnd_8318878 < baseStart_8318878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318897 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_8318897 : Nat := 118140960795 + 8318897 * 2 ^ 59
def prefixEnd_8318897 : Nat := 4983230072969 + 3 ^ 40 * 8318897 * 2
def baseEnd_8318897 : Nat := 1423864225415214670309865

theorem tailTrace_8318897 : CollatzResearch.WordTrace tailWord_8318897 prefixEnd_8318897 1423864225415214670309865 := by
  unfold tailWord_8318897
  simp only [CollatzResearch.WordTrace]
  refine ⟨303415100143064398340666945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202276733428709598893777963 303415100143064398340666945)
  ·
    refine ⟨227561325107298298755500209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303415100143064398340666945 227561325107298298755500209)
    ·
      refine ⟨170670993830473724066625157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227561325107298298755500209 170670993830473724066625157)
      ·
        refine ⟨32000811343213823262492217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170670993830473724066625157 32000811343213823262492217)
        ·
          refine ⟨24000608507410367446869163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32000811343213823262492217 24000608507410367446869163)
          ·
            refine ⟨36000912761115551170303745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24000608507410367446869163 36000912761115551170303745)
            ·
              refine ⟨27000684570836663377727809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36000912761115551170303745 27000684570836663377727809)
              ·
                refine ⟨20250513428127497533295857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27000684570836663377727809 20250513428127497533295857)
                ·
                  refine ⟨15187885071095623149971893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20250513428127497533295857 15187885071095623149971893)
                  ·
                    refine ⟨1423864225415214670309865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15187885071095623149971893 1423864225415214670309865)
                    ·
                      rfl

theorem cell23_8318897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_8318897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318897 prefixEnd_8318897 := by exact prefixLift 8318897
  have htrace : WordTrace (prefixWord ++ tailWord_8318897) baseStart_8318897 baseEnd_8318897 := by
    simpa [prefixWord, tailWord_8318897, baseEnd_8318897] using wordTrace_append hprefix tailTrace_8318897
  have hstable : (prefixWord ++ tailWord_8318897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318897).length < 2 ^ (prefixWord ++ tailWord_8318897).sum := by decide
  have hdescent : baseEnd_8318897 < baseStart_8318897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318901 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 5]
def baseStart_8318901 : Nat := 118140960795 + 8318901 * 2 ^ 59
def prefixEnd_8318901 : Nat := 4983230072969 + 3 ^ 40 * 8318901 * 2
def baseEnd_8318901 : Nat := 474621636685362443919953

theorem tailTrace_8318901 : CollatzResearch.WordTrace tailWord_8318901 prefixEnd_8318901 474621636685362443919953 := by
  unfold tailWord_8318901
  simp only [CollatzResearch.WordTrace]
  refine ⟨303415246035049907023812557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202276830690033271349208371 303415246035049907023812557)
  ·
    refine ⟨113780717263143715133929709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303415246035049907023812557 113780717263143715133929709)
    ·
      refine ⟨42667768973678893175223641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113780717263143715133929709 42667768973678893175223641)
      ·
        refine ⟨32000826730259169881417731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42667768973678893175223641 32000826730259169881417731)
        ·
          refine ⟨48001240095388754822126597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32000826730259169881417731 48001240095388754822126597)
          ·
            refine ⟨9000232517885391529148737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48001240095388754822126597 9000232517885391529148737)
            ·
              refine ⟨6750174388414043646861553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000232517885391529148737 6750174388414043646861553)
              ·
                refine ⟨5062630791310532735146165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750174388414043646861553 5062630791310532735146165)
                ·
                  refine ⟨474621636685362443919953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5062630791310532735146165 474621636685362443919953)
                  ·
                    rfl

theorem cell23_8318901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_8318901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318901 prefixEnd_8318901 := by exact prefixLift 8318901
  have htrace : WordTrace (prefixWord ++ tailWord_8318901) baseStart_8318901 baseEnd_8318901 := by
    simpa [prefixWord, tailWord_8318901, baseEnd_8318901] using wordTrace_append hprefix tailTrace_8318901
  have hstable : (prefixWord ++ tailWord_8318901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318901).length < 2 ^ (prefixWord ++ tailWord_8318901).sum := by decide
  have hdescent : baseEnd_8318901 < baseStart_8318901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318927 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 3, 4]
def baseStart_8318927 : Nat := 118140960795 + 8318927 * 2 ^ 59
def prefixEnd_8318927 : Nat := 4983230072969 + 3 ^ 40 * 8318927 * 2
def baseEnd_8318927 : Nat := 1423869360221759631184819

theorem tailTrace_8318927 : CollatzResearch.WordTrace tailWord_8318927 prefixEnd_8318927 1423869360221759631184819 := by
  unfold tailWord_8318927
  simp only [CollatzResearch.WordTrace]
  refine ⟨303416194332955713464259035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202277462888637142309506023 303416194332955713464259035)
  ·
    refine ⟨455124291499433570196388553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303416194332955713464259035 455124291499433570196388553)
    ·
      refine ⟨341343218624575177647291415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455124291499433570196388553 341343218624575177647291415)
      ·
        refine ⟨512014827936862766470937123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341343218624575177647291415 512014827936862766470937123)
        ·
          refine ⟨768022241905294149706405685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512014827936862766470937123 768022241905294149706405685)
          ·
            refine ⟨72002085178621326534975533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 768022241905294149706405685 72002085178621326534975533)
            ·
              refine ⟨27000781941982997450615825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72002085178621326534975533 27000781941982997450615825)
              ·
                refine ⟨20250586456487248087961869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27000781941982997450615825 20250586456487248087961869)
                ·
                  refine ⟨7593969921182718032985701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20250586456487248087961869 7593969921182718032985701)
                  ·
                    refine ⟨1423869360221759631184819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7593969921182718032985701 1423869360221759631184819)
                    ·
                      rfl

theorem cell23_8318927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_8318927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318927 prefixEnd_8318927 := by exact prefixLift 8318927
  have htrace : WordTrace (prefixWord ++ tailWord_8318927) baseStart_8318927 baseEnd_8318927 := by
    simpa [prefixWord, tailWord_8318927, baseEnd_8318927] using wordTrace_append hprefix tailTrace_8318927
  have hstable : (prefixWord ++ tailWord_8318927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318927).length < 2 ^ (prefixWord ++ tailWord_8318927).sum := by decide
  have hdescent : baseEnd_8318927 < baseStart_8318927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318960 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_8318960 : Nat := 118140960795 + 8318960 * 2 ^ 59
def prefixEnd_8318960 : Nat := 4983230072969 + 3 ^ 40 * 8318960 * 2
def baseEnd_8318960 : Nat := 4271625025526877264441805

theorem tailTrace_8318960 : CollatzResearch.WordTrace tailWord_8318960 prefixEnd_8318960 4271625025526877264441805 := by
  unfold tailWord_8318960
  simp only [CollatzResearch.WordTrace]
  refine ⟨151708698970918080050105167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202278265294557440066806889 151708698970918080050105167)
  ·
    refine ⟨227563048456377120075157751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151708698970918080050105167 227563048456377120075157751)
    ·
      refine ⟨341344572684565680112736627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227563048456377120075157751 341344572684565680112736627)
      ·
        refine ⟨512016859026848520169104941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341344572684565680112736627 512016859026848520169104941)
        ·
          refine ⟨192006322135068195063414353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512016859026848520169104941 192006322135068195063414353)
          ·
            refine ⟨144004741601301146297560765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192006322135068195063414353 144004741601301146297560765)
            ·
              refine ⟨54001778100487929861585287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144004741601301146297560765 54001778100487929861585287)
              ·
                refine ⟨81002667150731894792377931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54001778100487929861585287 81002667150731894792377931)
                ·
                  refine ⟨121504000726097842188566897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81002667150731894792377931 121504000726097842188566897)
                  ·
                    refine ⟨91128000544573381641425173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121504000726097842188566897 91128000544573381641425173)
                    ·
                      refine ⟨4271625025526877264441805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91128000544573381641425173 4271625025526877264441805)
                      ·
                        rfl

theorem cell23_8318960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_8318960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318960 prefixEnd_8318960 := by exact prefixLift 8318960
  have htrace : WordTrace (prefixWord ++ tailWord_8318960) baseStart_8318960 baseEnd_8318960 := by
    simpa [prefixWord, tailWord_8318960, baseEnd_8318960] using wordTrace_append hprefix tailTrace_8318960
  have hstable : (prefixWord ++ tailWord_8318960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318960).length < 2 ^ (prefixWord ++ tailWord_8318960).sum := by decide
  have hdescent : baseEnd_8318960 < baseStart_8318960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8318984 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_8318984 : Nat := 118140960795 + 8318984 * 2 ^ 59
def prefixEnd_8318984 : Nat := 4983230072969 + 3 ^ 40 * 8318984 * 2
def baseEnd_8318984 : Nat := 4271637349062585170541695

theorem tailTrace_8318984 : CollatzResearch.WordTrace tailWord_8318984 prefixEnd_8318984 4271637349062585170541695 := by
  unfold tailWord_8318984
  simp only [CollatzResearch.WordTrace]
  refine ⟨151709136646874606099542003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202278848862499474799389337 151709136646874606099542003)
  ·
    refine ⟨227563704970311909149313005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151709136646874606099542003 227563704970311909149313005)
    ·
      refine ⟨85336389363866965930992377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227563704970311909149313005 85336389363866965930992377)
      ·
        refine ⟨64002292022900224448244283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85336389363866965930992377 64002292022900224448244283)
        ·
          refine ⟨96003438034350336672366425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64002292022900224448244283 96003438034350336672366425)
          ·
            refine ⟨72002578525762752504274819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96003438034350336672366425 72002578525762752504274819)
            ·
              refine ⟨108003867788644128756412229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72002578525762752504274819 108003867788644128756412229)
              ·
                refine ⟨20250725210370774141827293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108003867788644128756412229 20250725210370774141827293)
                ·
                  refine ⟨7594021953889040303185235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20250725210370774141827293 7594021953889040303185235)
                  ·
                    refine ⟨11391032930833560454777853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594021953889040303185235 11391032930833560454777853)
                    ·
                      refine ⟨4271637349062585170541695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11391032930833560454777853 4271637349062585170541695)
                      ·
                        rfl

theorem cell23_8318984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_8318984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8318984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8318984 prefixEnd_8318984 := by exact prefixLift 8318984
  have htrace : WordTrace (prefixWord ++ tailWord_8318984) baseStart_8318984 baseEnd_8318984 := by
    simpa [prefixWord, tailWord_8318984, baseEnd_8318984] using wordTrace_append hprefix tailTrace_8318984
  have hstable : (prefixWord ++ tailWord_8318984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8318984).length < 2 ^ (prefixWord ++ tailWord_8318984).sum := by decide
  have hdescent : baseEnd_8318984 < baseStart_8318984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8318984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319004 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_8319004 : Nat := 118140960795 + 8319004 * 2 ^ 59
def prefixEnd_8319004 : Nat := 4983230072969 + 3 ^ 40 * 8319004 * 2
def baseEnd_8319004 : Nat := 1423882539558558364097201

theorem tailTrace_8319004 : CollatzResearch.WordTrace tailWord_8319004 prefixEnd_8319004 1423882539558558364097201 := by
  unfold tailWord_8319004
  simp only [CollatzResearch.WordTrace]
  refine ⟨151709501376838377807406033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202279335169117837076541377 151709501376838377807406033)
  ·
    refine ⟨113782126032628783355554525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151709501376838377807406033 113782126032628783355554525)
    ·
      refine ⟨42668297262235793758332947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113782126032628783355554525 42668297262235793758332947)
      ·
        refine ⟨64002445893353690637499421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42668297262235793758332947 64002445893353690637499421)
        ·
          refine ⟨24000917210007633989062283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64002445893353690637499421 24000917210007633989062283)
          ·
            refine ⟨36001375815011450983593425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24000917210007633989062283 36001375815011450983593425)
            ·
              refine ⟨27001031861258588237695069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36001375815011450983593425 27001031861258588237695069)
              ·
                refine ⟨10125386947971970589135651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27001031861258588237695069 10125386947971970589135651)
                ·
                  refine ⟨15188080421957955883703477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125386947971970589135651 15188080421957955883703477)
                  ·
                    refine ⟨1423882539558558364097201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15188080421957955883703477 1423882539558558364097201)
                    ·
                      rfl

theorem cell23_8319004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_8319004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319004 prefixEnd_8319004 := by exact prefixLift 8319004
  have htrace : WordTrace (prefixWord ++ tailWord_8319004) baseStart_8319004 baseEnd_8319004 := by
    simpa [prefixWord, tailWord_8319004, baseEnd_8319004] using wordTrace_append hprefix tailTrace_8319004
  have hstable : (prefixWord ++ tailWord_8319004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319004).length < 2 ^ (prefixWord ++ tailWord_8319004).sum := by decide
  have hdescent : baseEnd_8319004 < baseStart_8319004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319018 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_8319018 : Nat := 118140960795 + 8319018 * 2 ^ 59
def prefixEnd_8319018 : Nat := 4983230072969 + 3 ^ 40 * 8319018 * 2
def baseEnd_8319018 : Nat := 4271654807404838037516539

theorem tailTrace_8319018 : CollatzResearch.WordTrace tailWord_8319018 prefixEnd_8319018 4271654807404838037516539 := by
  unfold tailWord_8319018
  simp only [CollatzResearch.WordTrace]
  refine ⟨75854878343906509001455427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202279675583750690670547805 75854878343906509001455427)
  ·
    refine ⟨113782317515859763502183141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75854878343906509001455427 113782317515859763502183141)
    ·
      refine ⟨21334184534223705656659339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113782317515859763502183141 21334184534223705656659339)
      ·
        refine ⟨32001276801335558484989009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21334184534223705656659339 32001276801335558484989009)
        ·
          refine ⟨24000957601001668863741757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32001276801335558484989009 24000957601001668863741757)
          ·
            refine ⟨9000359100375625823903159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24000957601001668863741757 9000359100375625823903159)
            ·
              refine ⟨13500538650563438735854739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9000359100375625823903159 13500538650563438735854739)
              ·
                refine ⟨20250807975845158103782109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13500538650563438735854739 20250807975845158103782109)
                ·
                  refine ⟨7594052990941934288918291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20250807975845158103782109 7594052990941934288918291)
                  ·
                    refine ⟨11391079486412901433377437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594052990941934288918291 11391079486412901433377437)
                    ·
                      refine ⟨4271654807404838037516539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11391079486412901433377437 4271654807404838037516539)
                      ·
                        rfl

theorem cell23_8319018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_8319018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319018 prefixEnd_8319018 := by exact prefixLift 8319018
  have htrace : WordTrace (prefixWord ++ tailWord_8319018) baseStart_8319018 baseEnd_8319018 := by
    simpa [prefixWord, tailWord_8319018, baseEnd_8319018] using wordTrace_append hprefix tailTrace_8319018
  have hstable : (prefixWord ++ tailWord_8319018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319018).length < 2 ^ (prefixWord ++ tailWord_8319018).sum := by decide
  have hdescent : baseEnd_8319018 < baseStart_8319018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319027 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5]
def baseStart_8319027 : Nat := 118140960795 + 8319027 * 2 ^ 59
def prefixEnd_8319027 : Nat := 4983230072969 + 3 ^ 40 * 8319027 * 2
def baseEnd_8319027 : Nat := 4271659428730728502303997

theorem tailTrace_8319027 : CollatzResearch.WordTrace tailWord_8319027 prefixEnd_8319027 4271659428730728502303997 := by
  unfold tailWord_8319027
  simp only [CollatzResearch.WordTrace]
  refine ⟨303419841632593430542899335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202279894421728953695266223 303419841632593430542899335)
  ·
    refine ⟨455129762448890145814349003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303419841632593430542899335 455129762448890145814349003)
    ·
      refine ⟨682694643673335218721523505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455129762448890145814349003 682694643673335218721523505)
      ·
        refine ⟨512020982755001414041142629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682694643673335218721523505 512020982755001414041142629)
        ·
          refine ⟨96003934266562765132714243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512020982755001414041142629 96003934266562765132714243)
          ·
            refine ⟨144005901399844147699071365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96003934266562765132714243 144005901399844147699071365)
            ·
              refine ⟨27001106512470777693575881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144005901399844147699071365 27001106512470777693575881)
              ·
                refine ⟨20250829884353083270181911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27001106512470777693575881 20250829884353083270181911)
                ·
                  refine ⟨30376244826529624905272867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20250829884353083270181911 30376244826529624905272867)
                  ·
                    refine ⟨45564367239794437357909301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30376244826529624905272867 45564367239794437357909301)
                    ·
                      refine ⟨4271659428730728502303997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45564367239794437357909301 4271659428730728502303997)
                      ·
                        rfl

theorem cell23_8319027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_8319027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319027 prefixEnd_8319027 := by exact prefixLift 8319027
  have htrace : WordTrace (prefixWord ++ tailWord_8319027) baseStart_8319027 baseEnd_8319027 := by
    simpa [prefixWord, tailWord_8319027, baseEnd_8319027] using wordTrace_append hprefix tailTrace_8319027
  have hstable : (prefixWord ++ tailWord_8319027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319027).length < 2 ^ (prefixWord ++ tailWord_8319027).sum := by decide
  have hdescent : baseEnd_8319027 < baseStart_8319027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319037 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_8319037 : Nat := 118140960795 + 8319037 * 2 ^ 59
def prefixEnd_8319037 : Nat := 4983230072969 + 3 ^ 40 * 8319037 * 2
def baseEnd_8319037 : Nat := 4271664563537273463178951

theorem tailTrace_8319037 : CollatzResearch.WordTrace tailWord_8319037 prefixEnd_8319037 4271664563537273463178951 := by
  unfold tailWord_8319037
  simp only [CollatzResearch.WordTrace]
  refine ⟨303420206362557202250763365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202280137575038134833842243 303420206362557202250763365)
  ·
    refine ⟨56891288692979475422018131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303420206362557202250763365 56891288692979475422018131)
    ·
      refine ⟨85336933039469213133027197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56891288692979475422018131 85336933039469213133027197)
      ·
        refine ⟨32001349889800954924885199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85336933039469213133027197 32001349889800954924885199)
        ·
          refine ⟨48002024834701432387327799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32001349889800954924885199 48002024834701432387327799)
          ·
            refine ⟨72003037252052148580991699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48002024834701432387327799 72003037252052148580991699)
            ·
              refine ⟨108004555878078222871487549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72003037252052148580991699 108004555878078222871487549)
              ·
                refine ⟨40501708454279333576807831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108004555878078222871487549 40501708454279333576807831)
                ·
                  refine ⟨60752562681419000365211747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40501708454279333576807831 60752562681419000365211747)
                  ·
                    refine ⟨91128844022128500547817621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60752562681419000365211747 91128844022128500547817621)
                    ·
                      refine ⟨4271664563537273463178951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91128844022128500547817621 4271664563537273463178951)
                      ·
                        rfl

theorem cell23_8319037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_8319037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319037 prefixEnd_8319037 := by exact prefixLift 8319037
  have htrace : WordTrace (prefixWord ++ tailWord_8319037) baseStart_8319037 baseEnd_8319037 := by
    simpa [prefixWord, tailWord_8319037, baseEnd_8319037] using wordTrace_append hprefix tailTrace_8319037
  have hstable : (prefixWord ++ tailWord_8319037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319037).length < 2 ^ (prefixWord ++ tailWord_8319037).sum := by decide
  have hdescent : baseEnd_8319037 < baseStart_8319037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319038 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_8319038 : Nat := 118140960795 + 8319038 * 2 ^ 59
def prefixEnd_8319038 : Nat := 4983230072969 + 3 ^ 40 * 8319038 * 2
def baseEnd_8319038 : Nat := 1423888359005975986422149

theorem tailTrace_8319038 : CollatzResearch.WordTrace tailWord_8319038 prefixEnd_8319038 1423888359005975986422149 := by
  unfold tailWord_8319038
  simp only [CollatzResearch.WordTrace]
  refine ⟨37927530354444197427693721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202280161890369052947699845 37927530354444197427693721)
  ·
    refine ⟨28445647765833148070770291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37927530354444197427693721 28445647765833148070770291)
    ·
      refine ⟨42668471648749722106155437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28445647765833148070770291 42668471648749722106155437)
      ·
        refine ⟨16000676868281145789808289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42668471648749722106155437 16000676868281145789808289)
        ·
          refine ⟨12000507651210859342356217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16000676868281145789808289 12000507651210859342356217)
          ·
            refine ⟨9000380738408144506767163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12000507651210859342356217 9000380738408144506767163)
            ·
              refine ⟨13500571107612216760150745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9000380738408144506767163 13500571107612216760150745)
              ·
                refine ⟨10125428330709162570113059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13500571107612216760150745 10125428330709162570113059)
                ·
                  refine ⟨15188142496063743855169589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125428330709162570113059 15188142496063743855169589)
                  ·
                    refine ⟨1423888359005975986422149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15188142496063743855169589 1423888359005975986422149)
                    ·
                      rfl

theorem cell23_8319038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_8319038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319038 prefixEnd_8319038 := by exact prefixLift 8319038
  have htrace : WordTrace (prefixWord ++ tailWord_8319038) baseStart_8319038 baseEnd_8319038 := by
    simpa [prefixWord, tailWord_8319038, baseEnd_8319038] using wordTrace_append hprefix tailTrace_8319038
  have hstable : (prefixWord ++ tailWord_8319038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319038).length < 2 ^ (prefixWord ++ tailWord_8319038).sum := by decide
  have hdescent : baseEnd_8319038 < baseStart_8319038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319041 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_8319041 : Nat := 118140960795 + 8319041 * 2 ^ 59
def prefixEnd_8319041 : Nat := 4983230072969 + 3 ^ 40 * 8319041 * 2
def baseEnd_8319041 : Nat := 4271666617459891447528933

theorem tailTrace_8319041 : CollatzResearch.WordTrace tailWord_8319041 prefixEnd_8319041 4271666617459891447528933 := by
  unfold tailWord_8319041
  simp only [CollatzResearch.WordTrace]
  refine ⟨303420352254542710933908977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202280234836361807289272651 303420352254542710933908977)
  ·
    refine ⟨227565264190907033200431733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303420352254542710933908977 227565264190907033200431733)
    ·
      refine ⟨21334243517897534362540475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227565264190907033200431733 21334243517897534362540475)
      ·
        refine ⟨32001365276846301543810713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21334243517897534362540475 32001365276846301543810713)
        ·
          refine ⟨24001023957634726157858035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32001365276846301543810713 24001023957634726157858035)
          ·
            refine ⟨36001535936452089236787053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24001023957634726157858035 36001535936452089236787053)
            ·
              refine ⟨13500575976169533463795145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36001535936452089236787053 13500575976169533463795145)
              ·
                refine ⟨10125431982127150097846359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13500575976169533463795145 10125431982127150097846359)
                ·
                  refine ⟨15188147973190725146769539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125431982127150097846359 15188147973190725146769539)
                  ·
                    refine ⟨22782221959786087720154309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15188147973190725146769539 22782221959786087720154309)
                    ·
                      refine ⟨4271666617459891447528933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22782221959786087720154309 4271666617459891447528933)
                      ·
                        rfl

theorem cell23_8319041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_8319041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319041 prefixEnd_8319041 := by exact prefixLift 8319041
  have htrace : WordTrace (prefixWord ++ tailWord_8319041) baseStart_8319041 baseEnd_8319041 := by
    simpa [prefixWord, tailWord_8319041, baseEnd_8319041] using wordTrace_append hprefix tailTrace_8319041
  have hstable : (prefixWord ++ tailWord_8319041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319041).length < 2 ^ (prefixWord ++ tailWord_8319041).sum := by decide
  have hdescent : baseEnd_8319041 < baseStart_8319041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319054 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_8319054 : Nat := 118140960795 + 8319054 * 2 ^ 59
def prefixEnd_8319054 : Nat := 4983230072969 + 3 ^ 40 * 8319054 * 2
def baseEnd_8319054 : Nat := 4271673292708399896666373

theorem tailTrace_8319054 : CollatzResearch.WordTrace tailWord_8319054 prefixEnd_8319054 4271673292708399896666373 := by
  unfold tailWord_8319054
  simp only [CollatzResearch.WordTrace]
  refine ⟨37927603300436951769266527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202280550935663742769421477 37927603300436951769266527)
  ·
    refine ⟨56891404950655427653899791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37927603300436951769266527 56891404950655427653899791)
    ·
      refine ⟨85337107425983141480849687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56891404950655427653899791 85337107425983141480849687)
      ·
        refine ⟨128005661138974712221274531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85337107425983141480849687 128005661138974712221274531)
        ·
          refine ⟨192008491708462068331911797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128005661138974712221274531 192008491708462068331911797)
          ·
            refine ⟨18000796097668318906116731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192008491708462068331911797 18000796097668318906116731)
            ·
              refine ⟨27001194146502478359175097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18000796097668318906116731 27001194146502478359175097)
              ·
                refine ⟨20250895609876858769381323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27001194146502478359175097 20250895609876858769381323)
                ·
                  refine ⟨30376343414815288154071985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20250895609876858769381323 30376343414815288154071985)
                  ·
                    refine ⟨22782257561111466115553989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30376343414815288154071985 22782257561111466115553989)
                    ·
                      refine ⟨4271673292708399896666373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22782257561111466115553989 4271673292708399896666373)
                      ·
                        rfl

theorem cell23_8319054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_8319054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319054 prefixEnd_8319054 := by exact prefixLift 8319054
  have htrace : WordTrace (prefixWord ++ tailWord_8319054) baseStart_8319054 baseEnd_8319054 := by
    simpa [prefixWord, tailWord_8319054, baseEnd_8319054] using wordTrace_append hprefix tailTrace_8319054
  have hstable : (prefixWord ++ tailWord_8319054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319054).length < 2 ^ (prefixWord ++ tailWord_8319054).sum := by decide
  have hdescent : baseEnd_8319054 < baseStart_8319054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319058 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_8319058 : Nat := 118140960795 + 8319058 * 2 ^ 59
def prefixEnd_8319058 : Nat := 4983230072969 + 3 ^ 40 * 8319058 * 2
def baseEnd_8319058 : Nat := 4271675346631017881016355

theorem tailTrace_8319058 : CollatzResearch.WordTrace tailWord_8319058 prefixEnd_8319058 4271675346631017881016355 := by
  unfold tailWord_8319058
  simp only [CollatzResearch.WordTrace]
  refine ⟨75855243073870280709319457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202280648196987415224851885 75855243073870280709319457)
  ·
    refine ⟨56891432305402710531989593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75855243073870280709319457 56891432305402710531989593)
    ·
      refine ⟨42668574229052032898992195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56891432305402710531989593 42668574229052032898992195)
      ·
        refine ⟨64002861343578049348488293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42668574229052032898992195 64002861343578049348488293)
        ·
          refine ⟨12000536501920884252841555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64002861343578049348488293 12000536501920884252841555)
          ·
            refine ⟨18000804752881326379262333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12000536501920884252841555 18000804752881326379262333)
            ·
              refine ⟨6750301782330497392223375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18000804752881326379262333 6750301782330497392223375)
              ·
                refine ⟨10125452673495746088335063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750301782330497392223375 10125452673495746088335063)
                ·
                  refine ⟨15188179010243619132502595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125452673495746088335063 15188179010243619132502595)
                  ·
                    refine ⟨22782268515365428698753893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15188179010243619132502595 22782268515365428698753893)
                    ·
                      refine ⟨4271675346631017881016355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22782268515365428698753893 4271675346631017881016355)
                      ·
                        rfl

theorem cell23_8319058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_8319058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319058 prefixEnd_8319058 := by exact prefixLift 8319058
  have htrace : WordTrace (prefixWord ++ tailWord_8319058) baseStart_8319058 baseEnd_8319058 := by
    simpa [prefixWord, tailWord_8319058, baseEnd_8319058] using wordTrace_append hprefix tailTrace_8319058
  have hstable : (prefixWord ++ tailWord_8319058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319058).length < 2 ^ (prefixWord ++ tailWord_8319058).sum := by decide
  have hdescent : baseEnd_8319058 < baseStart_8319058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319075 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 1, 2, 2]
def baseStart_8319075 : Nat := 118140960795 + 8319075 * 2 ^ 59
def prefixEnd_8319075 : Nat := 4983230072969 + 3 ^ 40 * 8319075 * 2
def baseEnd_8319075 : Nat := 4271684075802144314503777

theorem tailTrace_8319075 : CollatzResearch.WordTrace tailWord_8319075 prefixEnd_8319075 4271684075802144314503777 := by
  unfold tailWord_8319075
  simp only [CollatzResearch.WordTrace]
  refine ⟨303421592336419534740646679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202281061557613023160431119 303421592336419534740646679)
  ·
    refine ⟨455132388504629302110970019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303421592336419534740646679 455132388504629302110970019)
    ·
      refine ⟨682698582756943953166455029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455132388504629302110970019 682698582756943953166455029)
      ·
        refine ⟨64002992133463495609355159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 682698582756943953166455029 64002992133463495609355159)
        ·
          refine ⟨96004488200195243414032739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64002992133463495609355159 96004488200195243414032739)
          ·
            refine ⟨144006732300292865121049109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96004488200195243414032739 144006732300292865121049109)
            ·
              refine ⟨6750315576576228052549177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144006732300292865121049109 6750315576576228052549177)
              ·
                refine ⟨5062736682432171039411883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750315576576228052549177 5062736682432171039411883)
                ·
                  refine ⟨7594105023648256559117825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062736682432171039411883 7594105023648256559117825)
                  ·
                    refine ⟨5695578767736192419338369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7594105023648256559117825 5695578767736192419338369)
                    ·
                      refine ⟨4271684075802144314503777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695578767736192419338369 4271684075802144314503777)
                      ·
                        rfl

theorem cell23_8319075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_8319075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319075 prefixEnd_8319075 := by exact prefixLift 8319075
  have htrace : WordTrace (prefixWord ++ tailWord_8319075) baseStart_8319075 baseEnd_8319075 := by
    simpa [prefixWord, tailWord_8319075, baseEnd_8319075] using wordTrace_append hprefix tailTrace_8319075
  have hstable : (prefixWord ++ tailWord_8319075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319075).length < 2 ^ (prefixWord ++ tailWord_8319075).sum := by decide
  have hdescent : baseEnd_8319075 < baseStart_8319075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319077 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_8319077 : Nat := 118140960795 + 8319077 * 2 ^ 59
def prefixEnd_8319077 : Nat := 4983230072969 + 3 ^ 40 * 8319077 * 2
def baseEnd_8319077 : Nat := 1423895034254484435559589

theorem tailTrace_8319077 : CollatzResearch.WordTrace tailWord_8319077 prefixEnd_8319077 1423895034254484435559589 := by
  unfold tailWord_8319077
  simp only [CollatzResearch.WordTrace]
  refine ⟨303421665282412289082219485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202281110188274859388146323 303421665282412289082219485)
  ·
    refine ⟨113783124480904608405832307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303421665282412289082219485 113783124480904608405832307)
    ·
      refine ⟨170674686721356912608748461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113783124480904608405832307 170674686721356912608748461)
      ·
        refine ⟨64003007520508842228280673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170674686721356912608748461 64003007520508842228280673)
        ·
          refine ⟨48002255640381631671210505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64003007520508842228280673 48002255640381631671210505)
          ·
            refine ⟨36001691730286223753407879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48002255640381631671210505 36001691730286223753407879)
            ·
              refine ⟨54002537595429335630111819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36001691730286223753407879 54002537595429335630111819)
              ·
                refine ⟨81003806393144003445167729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54002537595429335630111819 81003806393144003445167729)
                ·
                  refine ⟨60752854794858002583875797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81003806393144003445167729 60752854794858002583875797)
                  ·
                    refine ⟨1423895034254484435559589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60752854794858002583875797 1423895034254484435559589)
                    ·
                      rfl

theorem cell23_8319077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_8319077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319077 prefixEnd_8319077 := by exact prefixLift 8319077
  have htrace : WordTrace (prefixWord ++ tailWord_8319077) baseStart_8319077 baseEnd_8319077 := by
    simpa [prefixWord, tailWord_8319077, baseEnd_8319077] using wordTrace_append hprefix tailTrace_8319077
  have hstable : (prefixWord ++ tailWord_8319077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319077).length < 2 ^ (prefixWord ++ tailWord_8319077).sum := by decide
  have hdescent : baseEnd_8319077 < baseStart_8319077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319101 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_8319101 : Nat := 118140960795 + 8319101 * 2 ^ 59
def prefixEnd_8319101 : Nat := 4983230072969 + 3 ^ 40 * 8319101 * 2
def baseEnd_8319101 : Nat := 4271697426299161212778657

theorem tailTrace_8319101 : CollatzResearch.WordTrace tailWord_8319101 prefixEnd_8319101 4271697426299161212778657 := by
  unfold tailWord_8319101
  simp only [CollatzResearch.WordTrace]
  refine ⟨303422540634325341181093157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202281693756216894120728771 303422540634325341181093157)
  ·
    refine ⟨56891726368936001471454967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303422540634325341181093157 56891726368936001471454967)
    ·
      refine ⟨85337589553404002207182451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56891726368936001471454967 85337589553404002207182451)
      ·
        refine ⟨128006384330106003310773677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85337589553404002207182451 128006384330106003310773677)
        ·
          refine ⟨48002394123789751241540129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128006384330106003310773677 48002394123789751241540129)
          ·
            refine ⟨36001795592842313431155097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48002394123789751241540129 36001795592842313431155097)
            ·
              refine ⟨27001346694631735073366323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36001795592842313431155097 27001346694631735073366323)
              ·
                refine ⟨40502020041947602610049485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27001346694631735073366323 40502020041947602610049485)
                ·
                  refine ⟨15188257515730350978768557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40502020041947602610049485 15188257515730350978768557)
                  ·
                    refine ⟨5695596568398881617038209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15188257515730350978768557 5695596568398881617038209)
                    ·
                      refine ⟨4271697426299161212778657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695596568398881617038209 4271697426299161212778657)
                      ·
                        rfl

theorem cell23_8319101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_8319101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319101 prefixEnd_8319101 := by exact prefixLift 8319101
  have htrace : WordTrace (prefixWord ++ tailWord_8319101) baseStart_8319101 baseEnd_8319101 := by
    simpa [prefixWord, tailWord_8319101, baseEnd_8319101] using wordTrace_append hprefix tailTrace_8319101
  have hstable : (prefixWord ++ tailWord_8319101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319101).length < 2 ^ (prefixWord ++ tailWord_8319101).sum := by decide
  have hdescent : baseEnd_8319101 < baseStart_8319101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319126 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_8319126 : Nat := 118140960795 + 8319126 * 2 ^ 59
def prefixEnd_8319126 : Nat := 4983230072969 + 3 ^ 40 * 8319126 * 2
def baseEnd_8319126 : Nat := 4271710263315523614966043

theorem tailTrace_8319126 : CollatzResearch.WordTrace tailWord_8319126 prefixEnd_8319126 4271710263315523614966043 := by
  unfold tailWord_8319126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18963965778702173153172077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202282301639489846967168821 18963965778702173153172077)
  ·
    refine ⟨7111487167013314932439529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18963965778702173153172077 7111487167013314932439529)
    ·
      refine ⟨5333615375259986199329647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7111487167013314932439529 5333615375259986199329647)
      ·
        refine ⟨8000423062889979298994471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333615375259986199329647 8000423062889979298994471)
        ·
          refine ⟨12000634594334968948491707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8000423062889979298994471 12000634594334968948491707)
          ·
            refine ⟨18000951891502453422737561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12000634594334968948491707 18000951891502453422737561)
            ·
              refine ⟨13500713918626840067053171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18000951891502453422737561 13500713918626840067053171)
              ·
                refine ⟨20251070877940260100579757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13500713918626840067053171 20251070877940260100579757)
                ·
                  refine ⟨7594151579227597537717409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20251070877940260100579757 7594151579227597537717409)
                  ·
                    refine ⟨5695613684420698153288057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7594151579227597537717409 5695613684420698153288057)
                    ·
                      refine ⟨4271710263315523614966043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695613684420698153288057 4271710263315523614966043)
                      ·
                        rfl

theorem cell23_8319126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_8319126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319126 prefixEnd_8319126 := by exact prefixLift 8319126
  have htrace : WordTrace (prefixWord ++ tailWord_8319126) baseStart_8319126 baseEnd_8319126 := by
    simpa [prefixWord, tailWord_8319126, baseEnd_8319126] using wordTrace_append hprefix tailTrace_8319126
  have hstable : (prefixWord ++ tailWord_8319126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319126).length < 2 ^ (prefixWord ++ tailWord_8319126).sum := by decide
  have hdescent : baseEnd_8319126 < baseStart_8319126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319204 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_8319204 : Nat := 118140960795 + 8319204 * 2 ^ 59
def prefixEnd_8319204 : Nat := 4983230072969 + 3 ^ 40 * 8319204 * 2
def baseEnd_8319204 : Nat := 4271750314806574309790683

theorem tailTrace_8319204 : CollatzResearch.WordTrace tailWord_8319204 prefixEnd_8319204 4271750314806574309790683 := by
  unfold tailWord_8319204
  simp only [CollatzResearch.WordTrace]
  refine ⟨151713148676476094886046333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202284198235301459848061777 151713148676476094886046333)
  ·
    refine ⟨56892430753678535582267375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151713148676476094886046333 56892430753678535582267375)
    ·
      refine ⟨85338646130517803373401063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56892430753678535582267375 85338646130517803373401063)
      ·
        refine ⟨128007969195776705060101595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85338646130517803373401063 128007969195776705060101595)
        ·
          refine ⟨192011953793665057590152393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128007969195776705060101595 192011953793665057590152393)
          ·
            refine ⟨144008965345248793192614295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192011953793665057590152393 144008965345248793192614295)
            ·
              refine ⟨216013448017873189788921443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144008965345248793192614295 216013448017873189788921443)
              ·
                refine ⟨324020172026809784683382165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216013448017873189788921443 324020172026809784683382165)
                ·
                  refine ⟨15188445563756708657033539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 324020172026809784683382165 15188445563756708657033539)
                  ·
                    refine ⟨22782668345635062985550309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15188445563756708657033539 22782668345635062985550309)
                    ·
                      refine ⟨4271750314806574309790683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22782668345635062985550309 4271750314806574309790683)
                      ·
                        rfl

theorem cell23_8319204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_8319204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319204 prefixEnd_8319204 := by exact prefixLift 8319204
  have htrace : WordTrace (prefixWord ++ tailWord_8319204) baseStart_8319204 baseEnd_8319204 := by
    simpa [prefixWord, tailWord_8319204, baseEnd_8319204] using wordTrace_append hprefix tailTrace_8319204
  have hstable : (prefixWord ++ tailWord_8319204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319204).length < 2 ^ (prefixWord ++ tailWord_8319204).sum := by decide
  have hdescent : baseEnd_8319204 < baseStart_8319204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319224 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_8319224 : Nat := 118140960795 + 8319224 * 2 ^ 59
def prefixEnd_8319224 : Nat := 4983230072969 + 3 ^ 40 * 8319224 * 2
def baseEnd_8319224 : Nat := 4271760584419664231540591

theorem tailTrace_8319224 : CollatzResearch.WordTrace tailWord_8319224 prefixEnd_8319224 4271760584419664231540591 := by
  unfold tailWord_8319224
  simp only [CollatzResearch.WordTrace]
  refine ⟨151713513406439866593910363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202284684541919822125213817 151713513406439866593910363)
  ·
    refine ⟨227570270109659799890865545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151713513406439866593910363 227570270109659799890865545)
    ·
      refine ⟨170677702582244849918149159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227570270109659799890865545 170677702582244849918149159)
      ·
        refine ⟨256016553873367274877223739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170677702582244849918149159 256016553873367274877223739)
        ·
          refine ⟨384024830810050912315835609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256016553873367274877223739 384024830810050912315835609)
          ·
            refine ⟨288018623107538184236876707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384024830810050912315835609 288018623107538184236876707)
            ·
              refine ⟨432027934661307276355315061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288018623107538184236876707 432027934661307276355315061)
              ·
                refine ⟨40502618874497557158310787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432027934661307276355315061 40502618874497557158310787)
                ·
                  refine ⟨60753928311746335737466181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40502618874497557158310787 60753928311746335737466181)
                  ·
                    refine ⟨11391361558452437950774909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60753928311746335737466181 11391361558452437950774909)
                    ·
                      refine ⟨4271760584419664231540591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11391361558452437950774909 4271760584419664231540591)
                      ·
                        rfl

theorem cell23_8319224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_8319224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319224 prefixEnd_8319224 := by exact prefixLift 8319224
  have htrace : WordTrace (prefixWord ++ tailWord_8319224) baseStart_8319224 baseEnd_8319224 := by
    simpa [prefixWord, tailWord_8319224, baseEnd_8319224] using wordTrace_append hprefix tailTrace_8319224
  have hstable : (prefixWord ++ tailWord_8319224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319224).length < 2 ^ (prefixWord ++ tailWord_8319224).sum := by decide
  have hdescent : baseEnd_8319224 < baseStart_8319224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319241 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_8319241 : Nat := 118140960795 + 8319241 * 2 ^ 59
def prefixEnd_8319241 : Nat := 4983230072969 + 3 ^ 40 * 8319241 * 2
def baseEnd_8319241 : Nat := 4271769313590790665028013

theorem tailTrace_8319241 : CollatzResearch.WordTrace tailWord_8319241 prefixEnd_8319241 4271769313590790665028013 := by
  unfold tailWord_8319241
  simp only [CollatzResearch.WordTrace]
  refine ⟨303427646853818145091189577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202285097902545430060793051 303427646853818145091189577)
  ·
    refine ⟨227570735140363608818392183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303427646853818145091189577 227570735140363608818392183)
    ·
      refine ⟨341356102710545413227588275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227570735140363608818392183 341356102710545413227588275)
      ·
        refine ⟨512034154065818119841382413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341356102710545413227588275 512034154065818119841382413)
        ·
          refine ⟨192012807774681794940518405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512034154065818119841382413 192012807774681794940518405)
          ·
            refine ⟨36002401457752836551347201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192012807774681794940518405 36002401457752836551347201)
            ·
              refine ⟨27001801093314627413510401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36002401457752836551347201 27001801093314627413510401)
              ·
                refine ⟨20251350819985970560132801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27001801093314627413510401 20251350819985970560132801)
                ·
                  refine ⟨15188513114989477920099601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20251350819985970560132801 15188513114989477920099601)
                  ·
                    refine ⟨11391384836242108440074701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15188513114989477920099601 11391384836242108440074701)
                    ·
                      refine ⟨4271769313590790665028013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11391384836242108440074701 4271769313590790665028013)
                      ·
                        rfl

theorem cell23_8319241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_8319241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319241 prefixEnd_8319241 := by exact prefixLift 8319241
  have htrace : WordTrace (prefixWord ++ tailWord_8319241) baseStart_8319241 baseEnd_8319241 := by
    simpa [prefixWord, tailWord_8319241, baseEnd_8319241] using wordTrace_append hprefix tailTrace_8319241
  have hstable : (prefixWord ++ tailWord_8319241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319241).length < 2 ^ (prefixWord ++ tailWord_8319241).sum := by decide
  have hdescent : baseEnd_8319241 < baseStart_8319241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319304 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_8319304 : Nat := 118140960795 + 8319304 * 2 ^ 59
def prefixEnd_8319304 : Nat := 4983230072969 + 3 ^ 40 * 8319304 * 2
def baseEnd_8319304 : Nat := 1423933887624007972846741

theorem tailTrace_8319304 : CollatzResearch.WordTrace tailWord_8319304 prefixEnd_8319304 1423933887624007972846741 := by
  unfold tailWord_8319304
  simp only [CollatzResearch.WordTrace]
  refine ⟨151714972326294953425366483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202286629768393271233821977 151714972326294953425366483)
  ·
    refine ⟨227572458489442430138049725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151714972326294953425366483 227572458489442430138049725)
    ·
      refine ⟨85339671933540911301768647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227572458489442430138049725 85339671933540911301768647)
      ·
        refine ⟨128009507900311366952652971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85339671933540911301768647 128009507900311366952652971)
        ·
          refine ⟨192014261850467050428979457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128009507900311366952652971 192014261850467050428979457)
          ·
            refine ⟨144010696387850287821734593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192014261850467050428979457 144010696387850287821734593)
            ·
              refine ⟨108008022290887715866300945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144010696387850287821734593 108008022290887715866300945)
              ·
                refine ⟨81006016718165786899725709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108008022290887715866300945 81006016718165786899725709)
                ·
                  refine ⟨30377256269312170087397141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81006016718165786899725709 30377256269312170087397141)
                  ·
                    refine ⟨1423933887624007972846741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30377256269312170087397141 1423933887624007972846741)
                    ·
                      rfl

theorem cell23_8319304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_8319304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319304 prefixEnd_8319304 := by exact prefixLift 8319304
  have htrace : WordTrace (prefixWord ++ tailWord_8319304) baseStart_8319304 baseEnd_8319304 := by
    simpa [prefixWord, tailWord_8319304, baseEnd_8319304] using wordTrace_append hprefix tailTrace_8319304
  have hstable : (prefixWord ++ tailWord_8319304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319304).length < 2 ^ (prefixWord ++ tailWord_8319304).sum := by decide
  have hdescent : baseEnd_8319304 < baseStart_8319304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319338 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_8319338 : Nat := 118140960795 + 8319338 * 2 ^ 59
def prefixEnd_8319338 : Nat := 4983230072969 + 3 ^ 40 * 8319338 * 2
def baseEnd_8319338 : Nat := 1423939707071425595171689

theorem tailTrace_8319338 : CollatzResearch.WordTrace tailWord_8319338 prefixEnd_8319338 1423939707071425595171689 := by
  unfold tailWord_8319338
  simp only [CollatzResearch.WordTrace]
  refine ⟨75857796183616682664367667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202287456489644487104980445 75857796183616682664367667)
  ·
    refine ⟨113786694275425023996551501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75857796183616682664367667 113786694275425023996551501)
    ·
      refine ⟨42670010353284383998706813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113786694275425023996551501 42670010353284383998706813)
      ·
        refine ⟨16001253882481643999515055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42670010353284383998706813 16001253882481643999515055)
        ·
          refine ⟨24001880823722465999272583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001253882481643999515055 24001880823722465999272583)
          ·
            refine ⟨36002821235583698998908875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24001880823722465999272583 36002821235583698998908875)
            ·
              refine ⟨54004231853375548498363313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36002821235583698998908875 54004231853375548498363313)
              ·
                refine ⟨40503173890031661373772485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54004231853375548498363313 40503173890031661373772485)
                ·
                  refine ⟨7594345104380936507582341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40503173890031661373772485 7594345104380936507582341)
                  ·
                    refine ⟨1423939707071425595171689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7594345104380936507582341 1423939707071425595171689)
                    ·
                      rfl

theorem cell23_8319338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_8319338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319338 prefixEnd_8319338 := by exact prefixLift 8319338
  have htrace : WordTrace (prefixWord ++ tailWord_8319338) baseStart_8319338 baseEnd_8319338 := by
    simpa [prefixWord, tailWord_8319338, baseEnd_8319338] using wordTrace_append hprefix tailTrace_8319338
  have hstable : (prefixWord ++ tailWord_8319338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319338).length < 2 ^ (prefixWord ++ tailWord_8319338).sum := by decide
  have hdescent : baseEnd_8319338 < baseStart_8319338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319341 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_8319341 : Nat := 118140960795 + 8319341 * 2 ^ 59
def prefixEnd_8319341 : Nat := 4983230072969 + 3 ^ 40 * 8319341 * 2
def baseEnd_8319341 : Nat := 4271820661656240273777553

theorem tailTrace_8319341 : CollatzResearch.WordTrace tailWord_8319341 prefixEnd_8319341 4271820661656240273777553 := by
  unfold tailWord_8319341
  simp only [CollatzResearch.WordTrace]
  refine ⟨303431294153455862169829877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202287529435637241446553251 303431294153455862169829877)
  ·
    refine ⟨28446683826886487078421551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303431294153455862169829877 28446683826886487078421551)
    ·
      refine ⟨42670025740329730617632327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28446683826886487078421551 42670025740329730617632327)
      ·
        refine ⟨64005038610494595926448491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42670025740329730617632327 64005038610494595926448491)
        ·
          refine ⟨96007557915741893889672737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64005038610494595926448491 96007557915741893889672737)
          ·
            refine ⟨72005668436806420417254553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96007557915741893889672737 72005668436806420417254553)
            ·
              refine ⟨54004251327604815312940915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72005668436806420417254553 54004251327604815312940915)
              ·
                refine ⟨81006376991407222969411373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54004251327604815312940915 81006376991407222969411373)
                ·
                  refine ⟨30377391371777708613529265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81006376991407222969411373 30377391371777708613529265)
                  ·
                    refine ⟨22783043528833281460146949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30377391371777708613529265 22783043528833281460146949)
                    ·
                      refine ⟨4271820661656240273777553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22783043528833281460146949 4271820661656240273777553)
                      ·
                        rfl

theorem cell23_8319341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_8319341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319341 prefixEnd_8319341 := by exact prefixLift 8319341
  have htrace : WordTrace (prefixWord ++ tailWord_8319341) baseStart_8319341 baseEnd_8319341 := by
    simpa [prefixWord, tailWord_8319341, baseEnd_8319341] using wordTrace_append hprefix tailTrace_8319341
  have hstable : (prefixWord ++ tailWord_8319341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319341).length < 2 ^ (prefixWord ++ tailWord_8319341).sum := by decide
  have hdescent : baseEnd_8319341 < baseStart_8319341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319354 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_8319354 : Nat := 118140960795 + 8319354 * 2 ^ 59
def prefixEnd_8319354 : Nat := 4983230072969 + 3 ^ 40 * 8319354 * 2
def baseEnd_8319354 : Nat := 4271827336904748722914993

theorem tailTrace_8319354 : CollatzResearch.WordTrace tailWord_8319354 prefixEnd_8319354 4271827336904748722914993 := by
  unfold tailWord_8319354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75857942075602191347513279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202287845534939176926702077 75857942075602191347513279)
  ·
    refine ⟨113786913113403287021269919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75857942075602191347513279 113786913113403287021269919)
    ·
      refine ⟨170680369670104930531904879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113786913113403287021269919 170680369670104930531904879)
      ·
        refine ⟨256020554505157395797857319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170680369670104930531904879 256020554505157395797857319)
        ·
          refine ⟨384030831757736093696785979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256020554505157395797857319 384030831757736093696785979)
          ·
            refine ⟨576046247636604140545178969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384030831757736093696785979 576046247636604140545178969)
            ·
              refine ⟨432034685727453105408884227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576046247636604140545178969 432034685727453105408884227)
              ·
                refine ⟨648052028591179658113326341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432034685727453105408884227 648052028591179658113326341)
                ·
                  refine ⟨121509755360846185896248689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648052028591179658113326341 121509755360846185896248689)
                  ·
                    refine ⟨91132316520634639422186517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121509755360846185896248689 91132316520634639422186517)
                    ·
                      refine ⟨4271827336904748722914993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91132316520634639422186517 4271827336904748722914993)
                      ·
                        rfl

theorem cell23_8319354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_8319354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319354 prefixEnd_8319354 := by exact prefixLift 8319354
  have htrace : WordTrace (prefixWord ++ tailWord_8319354) baseStart_8319354 baseEnd_8319354 := by
    simpa [prefixWord, tailWord_8319354, baseEnd_8319354] using wordTrace_append hprefix tailTrace_8319354
  have hstable : (prefixWord ++ tailWord_8319354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319354).length < 2 ^ (prefixWord ++ tailWord_8319354).sum := by decide
  have hdescent : baseEnd_8319354 < baseStart_8319354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319413 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_8319413 : Nat := 118140960795 + 8319413 * 2 ^ 59
def prefixEnd_8319413 : Nat := 4983230072969 + 3 ^ 40 * 8319413 * 2
def baseEnd_8319413 : Nat := 4271857632263363992077223

theorem tailTrace_8319413 : CollatzResearch.WordTrace tailWord_8319413 prefixEnd_8319413 4271857632263363992077223 := by
  unfold tailWord_8319413
  simp only [CollatzResearch.WordTrace]
  refine ⟨303433920209195018466450893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202289280139463345644300595 303433920209195018466450893)
  ·
    refine ⟨113787720078448131924919085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303433920209195018466450893 113787720078448131924919085)
    ·
      refine ⟨42670395029418049471844657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113787720078448131924919085 42670395029418049471844657)
      ·
        refine ⟨32002796272063537103883493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42670395029418049471844657 32002796272063537103883493)
        ·
          refine ⟨6000524301011913206978155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32002796272063537103883493 6000524301011913206978155)
          ·
            refine ⟨9000786451517869810467233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000524301011913206978155 9000786451517869810467233)
            ·
              refine ⟨6750589838638402357850425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000786451517869810467233 6750589838638402357850425)
              ·
                refine ⟨5062942378978801768387819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750589838638402357850425 5062942378978801768387819)
                ·
                  refine ⟨7594413568468202652581729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062942378978801768387819 7594413568468202652581729)
                  ·
                    refine ⟨5695810176351151989436297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7594413568468202652581729 5695810176351151989436297)
                    ·
                      refine ⟨4271857632263363992077223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695810176351151989436297 4271857632263363992077223)
                      ·
                        rfl

theorem cell23_8319413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_8319413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319413 prefixEnd_8319413 := by exact prefixLift 8319413
  have htrace : WordTrace (prefixWord ++ tailWord_8319413) baseStart_8319413 baseEnd_8319413 := by
    simpa [prefixWord, tailWord_8319413, baseEnd_8319413] using wordTrace_append hprefix tailTrace_8319413
  have hstable : (prefixWord ++ tailWord_8319413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319413).length < 2 ^ (prefixWord ++ tailWord_8319413).sum := by decide
  have hdescent : baseEnd_8319413 < baseStart_8319413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319431 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_8319431 : Nat := 118140960795 + 8319431 * 2 ^ 59
def prefixEnd_8319431 : Nat := 4983230072969 + 3 ^ 40 * 8319431 * 2
def baseEnd_8319431 : Nat := 4271866874915144921652139

theorem tailTrace_8319431 : CollatzResearch.WordTrace tailWord_8319431 prefixEnd_8319431 4271866874915144921652139 := by
  unfold tailWord_8319431
  simp only [CollatzResearch.WordTrace]
  refine ⟨303434576723129807540606147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202289717815419871693737431 303434576723129807540606147)
  ·
    refine ⟨455151865084694711310909221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303434576723129807540606147 455151865084694711310909221)
    ·
      refine ⟨85340974703380258370795479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455151865084694711310909221 85340974703380258370795479)
      ·
        refine ⟨128011462055070387556193219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85340974703380258370795479 128011462055070387556193219)
        ·
          refine ⟨192017193082605581334289829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128011462055070387556193219 192017193082605581334289829)
          ·
            refine ⟨36003223702988546500179343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192017193082605581334289829 36003223702988546500179343)
            ·
              refine ⟨54004835554482819750269015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36003223702988546500179343 54004835554482819750269015)
              ·
                refine ⟨81007253331724229625403523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54004835554482819750269015 81007253331724229625403523)
                ·
                  refine ⟨121510879997586344438105285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81007253331724229625403523 121510879997586344438105285)
                  ·
                    refine ⟨22783289999547439582144741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121510879997586344438105285 22783289999547439582144741)
                    ·
                      refine ⟨4271866874915144921652139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22783289999547439582144741 4271866874915144921652139)
                      ·
                        rfl

theorem cell23_8319431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_8319431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319431 prefixEnd_8319431 := by exact prefixLift 8319431
  have htrace : WordTrace (prefixWord ++ tailWord_8319431) baseStart_8319431 baseEnd_8319431 := by
    simpa [prefixWord, tailWord_8319431, baseEnd_8319431] using wordTrace_append hprefix tailTrace_8319431
  have hstable : (prefixWord ++ tailWord_8319431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319431).length < 2 ^ (prefixWord ++ tailWord_8319431).sum := by decide
  have hdescent : baseEnd_8319431 < baseStart_8319431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319469 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_8319469 : Nat := 118140960795 + 8319469 * 2 ^ 59
def prefixEnd_8319469 : Nat := 4983230072969 + 3 ^ 40 * 8319469 * 2
def baseEnd_8319469 : Nat := 4271886387180015772976965

theorem tailTrace_8319469 : CollatzResearch.WordTrace tailWord_8319469 prefixEnd_8319469 4271886387180015772976965 := by
  unfold tailWord_8319469
  simp only [CollatzResearch.WordTrace]
  refine ⟨303435962696992140030489461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202290641797994760020326307 303435962696992140030489461)
  ·
    refine ⟨28447121502843013127858387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303435962696992140030489461 28447121502843013127858387)
    ·
      refine ⟨42670682254264519691787581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28447121502843013127858387 42670682254264519691787581)
      ·
        refine ⟨16001505845349194884420343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42670682254264519691787581 16001505845349194884420343)
        ·
          refine ⟨24002258768023792326630515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001505845349194884420343 24002258768023792326630515)
          ·
            refine ⟨36003388152035688489945773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24002258768023792326630515 36003388152035688489945773)
            ·
              refine ⟨13501270557013383183729665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36003388152035688489945773 13501270557013383183729665)
              ·
                refine ⟨10125952917760037387797249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13501270557013383183729665 10125952917760037387797249)
                ·
                  refine ⟨7594464688320028040847937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10125952917760037387797249 7594464688320028040847937)
                  ·
                    refine ⟨5695848516240021030635953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7594464688320028040847937 5695848516240021030635953)
                    ·
                      refine ⟨4271886387180015772976965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5695848516240021030635953 4271886387180015772976965)
                      ·
                        rfl

theorem cell23_8319469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_8319469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319469 prefixEnd_8319469 := by exact prefixLift 8319469
  have htrace : WordTrace (prefixWord ++ tailWord_8319469) baseStart_8319469 baseEnd_8319469 := by
    simpa [prefixWord, tailWord_8319469, baseEnd_8319469] using wordTrace_append hprefix tailTrace_8319469
  have hstable : (prefixWord ++ tailWord_8319469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319469).length < 2 ^ (prefixWord ++ tailWord_8319469).sum := by decide
  have hdescent : baseEnd_8319469 < baseStart_8319469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319471 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 4, 5]
def baseStart_8319471 : Nat := 118140960795 + 8319471 * 2 ^ 59
def prefixEnd_8319471 : Nat := 4983230072969 + 3 ^ 40 * 8319471 * 2
def baseEnd_8319471 : Nat := 1423962471380441588383985

theorem tailTrace_8319471 : CollatzResearch.WordTrace tailWord_8319471 prefixEnd_8319471 1423962471380441588383985 := by
  unfold tailWord_8319471
  simp only [CollatzResearch.WordTrace]
  refine ⟨303436035642984894372062267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202290690428656596248041511 303436035642984894372062267)
  ·
    refine ⟨455154053464477341558093401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303436035642984894372062267 455154053464477341558093401)
    ·
      refine ⟨341365540098358006168570051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455154053464477341558093401 341365540098358006168570051)
      ·
        refine ⟨512048310147537009252855077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341365540098358006168570051 512048310147537009252855077)
        ·
          refine ⟨96009058152663189234910327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512048310147537009252855077 96009058152663189234910327)
          ·
            refine ⟨144013587228994783852365491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96009058152663189234910327 144013587228994783852365491)
            ·
              refine ⟨216020380843492175778548237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144013587228994783852365491 216020380843492175778548237)
              ·
                refine ⟨81007642816309565916955589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216020380843492175778548237 81007642816309565916955589)
                ·
                  refine ⟨15188933028058043609429173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81007642816309565916955589 15188933028058043609429173)
                  ·
                    refine ⟨1423962471380441588383985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15188933028058043609429173 1423962471380441588383985)
                    ·
                      rfl

theorem cell23_8319471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_8319471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319471 prefixEnd_8319471 := by exact prefixLift 8319471
  have htrace : WordTrace (prefixWord ++ tailWord_8319471) baseStart_8319471 baseEnd_8319471 := by
    simpa [prefixWord, tailWord_8319471, baseEnd_8319471] using wordTrace_append hprefix tailTrace_8319471
  have hstable : (prefixWord ++ tailWord_8319471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319471).length < 2 ^ (prefixWord ++ tailWord_8319471).sum := by decide
  have hdescent : baseEnd_8319471 < baseStart_8319471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319481 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_8319481 : Nat := 118140960795 + 8319481 * 2 ^ 59
def prefixEnd_8319481 : Nat := 4983230072969 + 3 ^ 40 * 8319481 * 2
def baseEnd_8319481 : Nat := 4271892548947869726026909

theorem tailTrace_8319481 : CollatzResearch.WordTrace tailWord_8319481 prefixEnd_8319481 4271892548947869726026909 := by
  unfold tailWord_8319481
  simp only [CollatzResearch.WordTrace]
  refine ⟨303436400372948666079926297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202290933581965777386617531 303436400372948666079926297)
  ·
    refine ⟨227577300279711499559944723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303436400372948666079926297 227577300279711499559944723)
    ·
      refine ⟨341365950419567249339917085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227577300279711499559944723 341365950419567249339917085)
      ·
        refine ⟨128012231407337718502468907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341365950419567249339917085 128012231407337718502468907)
        ·
          refine ⟨192018347111006577753703361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128012231407337718502468907 192018347111006577753703361)
          ·
            refine ⟨144013760333254933315277521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192018347111006577753703361 144013760333254933315277521)
            ·
              refine ⟨108010320249941199986458141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144013760333254933315277521 108010320249941199986458141)
              ·
                refine ⟨40503870093727949994921803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108010320249941199986458141 40503870093727949994921803)
                ·
                  refine ⟨60755805140591924992382705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40503870093727949994921803 60755805140591924992382705)
                  ·
                    refine ⟨45566853855443943744287029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60755805140591924992382705 45566853855443943744287029)
                    ·
                      refine ⟨4271892548947869726026909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45566853855443943744287029 4271892548947869726026909)
                      ·
                        rfl

theorem cell23_8319481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_8319481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319481 prefixEnd_8319481 := by exact prefixLift 8319481
  have htrace : WordTrace (prefixWord ++ tailWord_8319481) baseStart_8319481 baseEnd_8319481 := by
    simpa [prefixWord, tailWord_8319481, baseEnd_8319481] using wordTrace_append hprefix tailTrace_8319481
  have hstable : (prefixWord ++ tailWord_8319481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319481).length < 2 ^ (prefixWord ++ tailWord_8319481).sum := by decide
  have hdescent : baseEnd_8319481 < baseStart_8319481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319491 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4]
def baseStart_8319491 : Nat := 118140960795 + 8319491 * 2 ^ 59
def prefixEnd_8319491 : Nat := 4983230072969 + 3 ^ 40 * 8319491 * 2
def baseEnd_8319491 : Nat := 4271897683754414686901863

theorem tailTrace_8319491 : CollatzResearch.WordTrace tailWord_8319491 prefixEnd_8319491 4271897683754414686901863 := by
  unfold tailWord_8319491
  simp only [CollatzResearch.WordTrace]
  refine ⟨303436765102912437787790327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202291176735274958525193551 303436765102912437787790327)
  ·
    refine ⟨455155147654368656681685491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303436765102912437787790327 455155147654368656681685491)
    ·
      refine ⟨682732721481552985022528237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455155147654368656681685491 682732721481552985022528237)
      ·
        refine ⟨256024770555582369383448089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682732721481552985022528237 256024770555582369383448089)
        ·
          refine ⟨192018577916686777037586067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256024770555582369383448089 192018577916686777037586067)
          ·
            refine ⟨288027866875030165556379101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192018577916686777037586067 288027866875030165556379101)
            ·
              refine ⟨108010450078136312083642163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288027866875030165556379101 108010450078136312083642163)
              ·
                refine ⟨162015675117204468125463245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108010450078136312083642163 162015675117204468125463245)
                ·
                  refine ⟨60755878168951675547048717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162015675117204468125463245 60755878168951675547048717)
                  ·
                    refine ⟨22783454313356878330143269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60755878168951675547048717 22783454313356878330143269)
                    ·
                      refine ⟨4271897683754414686901863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22783454313356878330143269 4271897683754414686901863)
                      ·
                        rfl

theorem cell23_8319491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_8319491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319491 prefixEnd_8319491 := by exact prefixLift 8319491
  have htrace : WordTrace (prefixWord ++ tailWord_8319491) baseStart_8319491 baseEnd_8319491 := by
    simpa [prefixWord, tailWord_8319491, baseEnd_8319491] using wordTrace_append hprefix tailTrace_8319491
  have hstable : (prefixWord ++ tailWord_8319491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319491).length < 2 ^ (prefixWord ++ tailWord_8319491).sum := by decide
  have hdescent : baseEnd_8319491 < baseStart_8319491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319586 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_8319586 : Nat := 118140960795 + 8319586 * 2 ^ 59
def prefixEnd_8319586 : Nat := 4983230072969 + 3 ^ 40 * 8319586 * 2
def baseEnd_8319586 : Nat := 1423982154805530605071309

theorem tailTrace_8319586 : CollatzResearch.WordTrace tailWord_8319586 prefixEnd_8319586 1423982154805530605071309 := by
  unfold tailWord_8319586
  simp only [CollatzResearch.WordTrace]
  refine ⟨75860057509392067253124653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202293486691712179341665741 75860057509392067253124653)
  ·
    refine ⟨28447521566022025219921745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75860057509392067253124653 28447521566022025219921745)
    ·
      refine ⟨21335641174516518914941309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28447521566022025219921745 21335641174516518914941309)
      ·
        refine ⟨8000865440443694593102991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21335641174516518914941309 8000865440443694593102991)
        ·
          refine ⟨12001298160665541889654487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8000865440443694593102991 12001298160665541889654487)
          ·
            refine ⟨18001947240998312834481731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001298160665541889654487 18001947240998312834481731)
            ·
              refine ⟨27002920861497469251722597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18001947240998312834481731 27002920861497469251722597)
              ·
                refine ⟨5063047661530775484697987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27002920861497469251722597 5063047661530775484697987)
                ·
                  refine ⟨7594571492296163227046981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063047661530775484697987 7594571492296163227046981)
                  ·
                    refine ⟨1423982154805530605071309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7594571492296163227046981 1423982154805530605071309)
                    ·
                      rfl

theorem cell23_8319586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_8319586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319586 prefixEnd_8319586 := by exact prefixLift 8319586
  have htrace : WordTrace (prefixWord ++ tailWord_8319586) baseStart_8319586 baseEnd_8319586 := by
    simpa [prefixWord, tailWord_8319586, baseEnd_8319586] using wordTrace_append hprefix tailTrace_8319586
  have hstable : (prefixWord ++ tailWord_8319586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319586).length < 2 ^ (prefixWord ++ tailWord_8319586).sum := by decide
  have hdescent : baseEnd_8319586 < baseStart_8319586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319626 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_8319626 : Nat := 118140960795 + 8319626 * 2 ^ 59
def prefixEnd_8319626 : Nat := 4983230072969 + 3 ^ 40 * 8319626 * 2
def baseEnd_8319626 : Nat := 4271967003642771658713743

theorem tailTrace_8319626 : CollatzResearch.WordTrace tailWord_8319626 prefixEnd_8319626 4271967003642771658713743 := by
  unfold tailWord_8319626
  simp only [CollatzResearch.WordTrace]
  refine ⟨75860422239355838960988683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202294459304948903895969821 75860422239355838960988683)
  ·
    refine ⟨113790633359033758441483025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75860422239355838960988683 113790633359033758441483025)
    ·
      refine ⟨85342975019275318831112269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113790633359033758441483025 85342975019275318831112269)
      ·
        refine ⟨32003615632228244561667101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85342975019275318831112269 32003615632228244561667101)
        ·
          refine ⟨12001355862085591710625163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32003615632228244561667101 12001355862085591710625163)
          ·
            refine ⟨18002033793128387565937745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001355862085591710625163 18002033793128387565937745)
            ·
              refine ⟨13501525344846290674453309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18002033793128387565937745 13501525344846290674453309)
              ·
                refine ⟨5063072004317359002919991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13501525344846290674453309 5063072004317359002919991)
                ·
                  refine ⟨7594608006476038504379987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063072004317359002919991 7594608006476038504379987)
                  ·
                    refine ⟨11391912009714057756569981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594608006476038504379987 11391912009714057756569981)
                    ·
                      refine ⟨4271967003642771658713743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11391912009714057756569981 4271967003642771658713743)
                      ·
                        rfl

theorem cell23_8319626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_8319626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319626 prefixEnd_8319626 := by exact prefixLift 8319626
  have htrace : WordTrace (prefixWord ++ tailWord_8319626) baseStart_8319626 baseEnd_8319626 := by
    simpa [prefixWord, tailWord_8319626, baseEnd_8319626] using wordTrace_append hprefix tailTrace_8319626
  have hstable : (prefixWord ++ tailWord_8319626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319626).length < 2 ^ (prefixWord ++ tailWord_8319626).sum := by decide
  have hdescent : baseEnd_8319626 < baseStart_8319626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319628 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_8319628 : Nat := 118140960795 + 8319628 * 2 ^ 59
def prefixEnd_8319628 : Nat := 4983230072969 + 3 ^ 40 * 8319628 * 2
def baseEnd_8319628 : Nat := 4271968030604080650888733

theorem tailTrace_8319628 : CollatzResearch.WordTrace tailWord_8319628 prefixEnd_8319628 4271968030604080650888733 := by
  unfold tailWord_8319628
  simp only [CollatzResearch.WordTrace]
  refine ⟨151720880951708055092763769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202294507935610740123685025 151720880951708055092763769)
  ·
    refine ⟨113790660713781041319572827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151720880951708055092763769 113790660713781041319572827)
    ·
      refine ⟨170685991070671561979359241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113790660713781041319572827 170685991070671561979359241)
      ·
        refine ⟨128014493303003671484519431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170685991070671561979359241 128014493303003671484519431)
        ·
          refine ⟨192021739954505507226779147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128014493303003671484519431 192021739954505507226779147)
          ·
            refine ⟨288032609931758260840168721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192021739954505507226779147 288032609931758260840168721)
            ·
              refine ⟨216024457448818695630126541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288032609931758260840168721 216024457448818695630126541)
              ·
                refine ⟨81009171543307010861297453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216024457448818695630126541 81009171543307010861297453)
                ·
                  refine ⟨30378439328740129072986545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81009171543307010861297453 30378439328740129072986545)
                  ·
                    refine ⟨22783829496555096804739909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30378439328740129072986545 22783829496555096804739909)
                    ·
                      refine ⟨4271968030604080650888733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22783829496555096804739909 4271968030604080650888733)
                      ·
                        rfl

theorem cell23_8319628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_8319628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319628 prefixEnd_8319628 := by exact prefixLift 8319628
  have htrace : WordTrace (prefixWord ++ tailWord_8319628) baseStart_8319628 baseEnd_8319628 := by
    simpa [prefixWord, tailWord_8319628, baseEnd_8319628] using wordTrace_append hprefix tailTrace_8319628
  have hstable : (prefixWord ++ tailWord_8319628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319628).length < 2 ^ (prefixWord ++ tailWord_8319628).sum := by decide
  have hdescent : baseEnd_8319628 < baseStart_8319628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319635 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 3]
def baseStart_8319635 : Nat := 118140960795 + 8319635 * 2 ^ 59
def prefixEnd_8319635 : Nat := 4983230072969 + 3 ^ 40 * 8319635 * 2
def baseEnd_8319635 : Nat := 4271971624968662123501201

theorem tailTrace_8319635 : CollatzResearch.WordTrace tailWord_8319635 prefixEnd_8319635 4271971624968662123501201 := by
  unfold tailWord_8319635
  simp only [CollatzResearch.WordTrace]
  refine ⟨303442017214390750381032359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202294678142927166920688239 303442017214390750381032359)
  ·
    refine ⟨455163025821586125571548539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303442017214390750381032359 455163025821586125571548539)
    ·
      refine ⟨682744538732379188357322809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455163025821586125571548539 682744538732379188357322809)
      ·
        refine ⟨512058404049284391267992107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682744538732379188357322809 512058404049284391267992107)
        ·
          refine ⟨768087606073926586901988161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512058404049284391267992107 768087606073926586901988161)
          ·
            refine ⟨576065704555444940176491121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768087606073926586901988161 576065704555444940176491121)
            ·
              refine ⟨432049278416583705132368341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576065704555444940176491121 432049278416583705132368341)
              ·
                refine ⟨10126154962888680589039883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 432049278416583705132368341 10126154962888680589039883)
                ·
                  refine ⟨15189232444333020883559825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126154962888680589039883 15189232444333020883559825)
                  ·
                    refine ⟨11391924333249765662669869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15189232444333020883559825 11391924333249765662669869)
                    ·
                      refine ⟨4271971624968662123501201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11391924333249765662669869 4271971624968662123501201)
                      ·
                        rfl

theorem cell23_8319635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_8319635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319635 prefixEnd_8319635 := by exact prefixLift 8319635
  have htrace : WordTrace (prefixWord ++ tailWord_8319635) baseStart_8319635 baseEnd_8319635 := by
    simpa [prefixWord, tailWord_8319635, baseEnd_8319635] using wordTrace_append hprefix tailTrace_8319635
  have hstable : (prefixWord ++ tailWord_8319635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319635).length < 2 ^ (prefixWord ++ tailWord_8319635).sum := by decide
  have hdescent : baseEnd_8319635 < baseStart_8319635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319662 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_8319662 : Nat := 118140960795 + 8319662 * 2 ^ 59
def prefixEnd_8319662 : Nat := 4983230072969 + 3 ^ 40 * 8319662 * 2
def baseEnd_8319662 : Nat := 4271985488946333517863577

theorem tailTrace_8319662 : CollatzResearch.WordTrace tailWord_8319662 prefixEnd_8319662 4271985488946333517863577 := by
  unfold tailWord_8319662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37930375248161616749033155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202295334656861955994843493 37930375248161616749033155)
  ·
    refine ⟨56895562872242425123549733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37930375248161616749033155 56895562872242425123549733)
    ·
      refine ⟨10667918038545454710665575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56895562872242425123549733 10667918038545454710665575)
      ·
        refine ⟨16001877057818182065998363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10667918038545454710665575 16001877057818182065998363)
        ·
          refine ⟨24002815586727273098997545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001877057818182065998363 24002815586727273098997545)
          ·
            refine ⟨18002111690045454824248159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24002815586727273098997545 18002111690045454824248159)
            ·
              refine ⟨27003167535068182236372239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002111690045454824248159 27003167535068182236372239)
              ·
                refine ⟨40504751302602273354558359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27003167535068182236372239 40504751302602273354558359)
                ·
                  refine ⟨60757126953903410031837539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40504751302602273354558359 60757126953903410031837539)
                  ·
                    refine ⟨91135690430855115047756309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60757126953903410031837539 91135690430855115047756309)
                    ·
                      refine ⟨4271985488946333517863577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91135690430855115047756309 4271985488946333517863577)
                      ·
                        rfl

theorem cell23_8319662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_8319662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319662 prefixEnd_8319662 := by exact prefixLift 8319662
  have htrace : WordTrace (prefixWord ++ tailWord_8319662) baseStart_8319662 baseEnd_8319662 := by
    simpa [prefixWord, tailWord_8319662, baseEnd_8319662] using wordTrace_append hprefix tailTrace_8319662
  have hstable : (prefixWord ++ tailWord_8319662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319662).length < 2 ^ (prefixWord ++ tailWord_8319662).sum := by decide
  have hdescent : baseEnd_8319662 < baseStart_8319662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319669 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_8319669 : Nat := 118140960795 + 8319669 * 2 ^ 59
def prefixEnd_8319669 : Nat := 4983230072969 + 3 ^ 40 * 8319669 * 2
def baseEnd_8319669 : Nat := 4271989083310914990476045

theorem tailTrace_8319669 : CollatzResearch.WordTrace tailWord_8319669 prefixEnd_8319669 4271989083310914990476045 := by
  unfold tailWord_8319669
  simp only [CollatzResearch.WordTrace]
  refine ⟨303443257296267574187770061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202295504864178382791846707 303443257296267574187770061)
  ·
    refine ⟨113791221486100340320413773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303443257296267574187770061 113791221486100340320413773)
    ·
      refine ⟨42671708057287627620155165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113791221486100340320413773 42671708057287627620155165)
      ·
        refine ⟨16001890521482860357558187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42671708057287627620155165 16001890521482860357558187)
        ·
          refine ⟨24002835782224290536337281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001890521482860357558187 24002835782224290536337281)
          ·
            refine ⟨18002126836668217902252961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24002835782224290536337281 18002126836668217902252961)
            ·
              refine ⟨13501595127501163426689721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18002126836668217902252961 13501595127501163426689721)
              ·
                refine ⟨10126196345625872570017291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13501595127501163426689721 10126196345625872570017291)
                ·
                  refine ⟨15189294518438808855025937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126196345625872570017291 15189294518438808855025937)
                  ·
                    refine ⟨11391970888829106641269453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15189294518438808855025937 11391970888829106641269453)
                    ·
                      refine ⟨4271989083310914990476045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11391970888829106641269453 4271989083310914990476045)
                      ·
                        rfl

theorem cell23_8319669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_8319669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319669 prefixEnd_8319669 := by exact prefixLift 8319669
  have htrace : WordTrace (prefixWord ++ tailWord_8319669) baseStart_8319669 baseEnd_8319669 := by
    simpa [prefixWord, tailWord_8319669, baseEnd_8319669] using wordTrace_append hprefix tailTrace_8319669
  have hstable : (prefixWord ++ tailWord_8319669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319669).length < 2 ^ (prefixWord ++ tailWord_8319669).sum := by decide
  have hdescent : baseEnd_8319669 < baseStart_8319669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319686 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_8319686 : Nat := 118140960795 + 8319686 * 2 ^ 59
def prefixEnd_8319686 : Nat := 4983230072969 + 3 ^ 40 * 8319686 * 2
def baseEnd_8319686 : Nat := 4271997812482041423963467

theorem tailTrace_8319686 : CollatzResearch.WordTrace tailWord_8319686 prefixEnd_8319686 4271997812482041423963467 := by
  unfold tailWord_8319686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482621166787687065348091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202295918224803990727425941 9482621166787687065348091)
  ·
    refine ⟨14223931750181530598022137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9482621166787687065348091 14223931750181530598022137)
    ·
      refine ⟨10667948812636147948516603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14223931750181530598022137 10667948812636147948516603)
      ·
        refine ⟨16001923218954221922774905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10667948812636147948516603 16001923218954221922774905)
        ·
          refine ⟨12001442414215666442081179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16001923218954221922774905 12001442414215666442081179)
          ·
            refine ⟨18002163621323499663121769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001442414215666442081179 18002163621323499663121769)
            ·
              refine ⟨13501622715992624747341327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18002163621323499663121769 13501622715992624747341327)
              ·
                refine ⟨20252434073988937121011991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13501622715992624747341327 20252434073988937121011991)
                ·
                  refine ⟨30378651110983405681517987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20252434073988937121011991 30378651110983405681517987)
                  ·
                    refine ⟨45567976666475108522276981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30378651110983405681517987 45567976666475108522276981)
                    ·
                      refine ⟨4271997812482041423963467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45567976666475108522276981 4271997812482041423963467)
                      ·
                        rfl

theorem cell23_8319686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_8319686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319686 prefixEnd_8319686 := by exact prefixLift 8319686
  have htrace : WordTrace (prefixWord ++ tailWord_8319686) baseStart_8319686 baseEnd_8319686 := by
    simpa [prefixWord, tailWord_8319686, baseEnd_8319686] using wordTrace_append hprefix tailTrace_8319686
  have hstable : (prefixWord ++ tailWord_8319686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319686).length < 2 ^ (prefixWord ++ tailWord_8319686).sum := by decide
  have hdescent : baseEnd_8319686 < baseStart_8319686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319700 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_8319700 : Nat := 118140960795 + 8319700 * 2 ^ 59
def prefixEnd_8319700 : Nat := 4983230072969 + 3 ^ 40 * 8319700 * 2
def baseEnd_8319700 : Nat := 4272005001211204369188403

theorem tailTrace_8319700 : CollatzResearch.WordTrace tailWord_8319700 prefixEnd_8319700 4272005001211204369188403 := by
  unfold tailWord_8319700
  simp only [CollatzResearch.WordTrace]
  refine ⟨151722193979577633241074277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202296258639436844321432369 151722193979577633241074277)
  ·
    refine ⟨28447911371170806232701427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151722193979577633241074277 28447911371170806232701427)
    ·
      refine ⟨42671867056756209349052141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28447911371170806232701427 42671867056756209349052141)
      ·
        refine ⟨16001950146283578505894553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42671867056756209349052141 16001950146283578505894553)
        ·
          refine ⟨12001462609712683879420915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16001950146283578505894553 12001462609712683879420915)
          ·
            refine ⟨18002193914569025819131373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001462609712683879420915 18002193914569025819131373)
            ·
              refine ⟨6750822717963384682174265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18002193914569025819131373 6750822717963384682174265)
              ·
                refine ⟨5063117038472538511630699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750822717963384682174265 5063117038472538511630699)
                ·
                  refine ⟨7594675557708807767446049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063117038472538511630699 7594675557708807767446049)
                  ·
                    refine ⟨5696006668281605825584537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7594675557708807767446049 5696006668281605825584537)
                    ·
                      refine ⟨4272005001211204369188403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696006668281605825584537 4272005001211204369188403)
                      ·
                        rfl

theorem cell23_8319700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_8319700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319700 prefixEnd_8319700 := by exact prefixLift 8319700
  have htrace : WordTrace (prefixWord ++ tailWord_8319700) baseStart_8319700 baseEnd_8319700 := by
    simpa [prefixWord, tailWord_8319700, baseEnd_8319700] using wordTrace_append hprefix tailTrace_8319700
  have hstable : (prefixWord ++ tailWord_8319700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319700).length < 2 ^ (prefixWord ++ tailWord_8319700).sum := by decide
  have hdescent : baseEnd_8319700 < baseStart_8319700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319716 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_8319716 : Nat := 118140960795 + 8319716 * 2 ^ 59
def prefixEnd_8319716 : Nat := 4983230072969 + 3 ^ 40 * 8319716 * 2
def baseEnd_8319716 : Nat := 4272013216901676306588329

theorem tailTrace_8319716 : CollatzResearch.WordTrace tailWord_8319716 prefixEnd_8319716 4272013216901676306588329 := by
  unfold tailWord_8319716
  simp only [CollatzResearch.WordTrace]
  refine ⟨151722485763548650607365501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202296647684731534143154001 151722485763548650607365501)
  ·
    refine ⟨56895932161330743977762063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151722485763548650607365501 56895932161330743977762063)
    ·
      refine ⟨85343898241996115966643095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56895932161330743977762063 85343898241996115966643095)
      ·
        refine ⟨128015847362994173949964643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85343898241996115966643095 128015847362994173949964643)
        ·
          refine ⟨192023771044491260924946965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128015847362994173949964643 192023771044491260924946965)
          ·
            refine ⟨9001114267710527855856889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192023771044491260924946965 9001114267710527855856889)
            ·
              refine ⟨6750835700782895891892667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9001114267710527855856889 6750835700782895891892667)
              ·
                refine ⟨10126253551174343837839001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750835700782895891892667 10126253551174343837839001)
                ·
                  refine ⟨7594690163380757878379251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10126253551174343837839001 7594690163380757878379251)
                  ·
                    refine ⟨11392035245071136817568877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594690163380757878379251 11392035245071136817568877)
                    ·
                      refine ⟨4272013216901676306588329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392035245071136817568877 4272013216901676306588329)
                      ·
                        rfl

theorem cell23_8319716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_8319716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319716 prefixEnd_8319716 := by exact prefixLift 8319716
  have htrace : WordTrace (prefixWord ++ tailWord_8319716) baseStart_8319716 baseEnd_8319716 := by
    simpa [prefixWord, tailWord_8319716, baseEnd_8319716] using wordTrace_append hprefix tailTrace_8319716
  have hstable : (prefixWord ++ tailWord_8319716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319716).length < 2 ^ (prefixWord ++ tailWord_8319716).sum := by decide
  have hdescent : baseEnd_8319716 < baseStart_8319716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319722 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_8319722 : Nat := 118140960795 + 8319722 * 2 ^ 59
def prefixEnd_8319722 : Nat := 4983230072969 + 3 ^ 40 * 8319722 * 2
def baseEnd_8319722 : Nat := 4272016297785603283113301

theorem tailTrace_8319722 : CollatzResearch.WordTrace tailWord_8319722 prefixEnd_8319722 4272016297785603283113301 := by
  unfold tailWord_8319722
  simp only [CollatzResearch.WordTrace]
  refine ⟨75861297591268891059862355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202296793576717042826299613 75861297591268891059862355)
  ·
    refine ⟨113791946386903336589793533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75861297591268891059862355 113791946386903336589793533)
    ·
      refine ⟨42671979895088751221172575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113791946386903336589793533 42671979895088751221172575)
      ·
        refine ⟨64007969842633126831758863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42671979895088751221172575 64007969842633126831758863)
        ·
          refine ⟨96011954763949690247638295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64007969842633126831758863 96011954763949690247638295)
          ·
            refine ⟨144017932145924535371457443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96011954763949690247638295 144017932145924535371457443)
            ·
              refine ⟨216026898218886803057186165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144017932145924535371457443 216026898218886803057186165)
              ·
                refine ⟨20252521708020637786611203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216026898218886803057186165 20252521708020637786611203)
                ·
                  refine ⟨30378782562030956679916805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20252521708020637786611203 30378782562030956679916805)
                  ·
                    refine ⟨5696021730380804377484401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30378782562030956679916805 5696021730380804377484401)
                    ·
                      refine ⟨4272016297785603283113301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696021730380804377484401 4272016297785603283113301)
                      ·
                        rfl

theorem cell23_8319722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_8319722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319722 prefixEnd_8319722 := by exact prefixLift 8319722
  have htrace : WordTrace (prefixWord ++ tailWord_8319722) baseStart_8319722 baseEnd_8319722 := by
    simpa [prefixWord, tailWord_8319722, baseEnd_8319722] using wordTrace_append hprefix tailTrace_8319722
  have hstable : (prefixWord ++ tailWord_8319722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319722).length < 2 ^ (prefixWord ++ tailWord_8319722).sum := by decide
  have hdescent : baseEnd_8319722 < baseStart_8319722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319725 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_8319725 : Nat := 118140960795 + 8319725 * 2 ^ 59
def prefixEnd_8319725 : Nat := 4983230072969 + 3 ^ 40 * 8319725 * 2
def baseEnd_8319725 : Nat := 4272017838227566771375787

theorem tailTrace_8319725 : CollatzResearch.WordTrace tailWord_8319725 prefixEnd_8319725 4272017838227566771375787 := by
  unfold tailWord_8319725
  simp only [CollatzResearch.WordTrace]
  refine ⟨303445299784064695751808629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202296866522709797167872419 303445299784064695751808629)
  ·
    refine ⟨28447996854756065226732059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303445299784064695751808629 28447996854756065226732059)
    ·
      refine ⟨42671995282134097840098089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28447996854756065226732059 42671995282134097840098089)
      ·
        refine ⟨32003996461600573380073567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42671995282134097840098089 32003996461600573380073567)
        ·
          refine ⟨48005994692400860070110351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32003996461600573380073567 48005994692400860070110351)
          ·
            refine ⟨72008992038601290105165527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48005994692400860070110351 72008992038601290105165527)
            ·
              refine ⟨108013488057901935157748291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72008992038601290105165527 108013488057901935157748291)
              ·
                refine ⟨162020232086852902736622437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108013488057901935157748291 162020232086852902736622437)
                ·
                  refine ⟨30378793516284919263116707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162020232086852902736622437 30378793516284919263116707)
                  ·
                    refine ⟨45568190274427378894675061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30378793516284919263116707 45568190274427378894675061)
                    ·
                      refine ⟨4272017838227566771375787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45568190274427378894675061 4272017838227566771375787)
                      ·
                        rfl

theorem cell23_8319725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_8319725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319725 prefixEnd_8319725 := by exact prefixLift 8319725
  have htrace : WordTrace (prefixWord ++ tailWord_8319725) baseStart_8319725 baseEnd_8319725 := by
    simpa [prefixWord, tailWord_8319725, baseEnd_8319725] using wordTrace_append hprefix tailTrace_8319725
  have hstable : (prefixWord ++ tailWord_8319725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319725).length < 2 ^ (prefixWord ++ tailWord_8319725).sum := by decide
  have hdescent : baseEnd_8319725 < baseStart_8319725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319726 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_8319726 : Nat := 118140960795 + 8319726 * 2 ^ 59
def prefixEnd_8319726 : Nat := 4983230072969 + 3 ^ 40 * 8319726 * 2
def baseEnd_8319726 : Nat := 4272018351708221267463283

theorem tailTrace_8319726 : CollatzResearch.WordTrace tailWord_8319726 prefixEnd_8319726 4272018351708221267463283 := by
  unfold tailWord_8319726
  simp only [CollatzResearch.WordTrace]
  refine ⟨37930667032132634115324379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202296890838040715281730021 37930667032132634115324379)
  ·
    refine ⟨56896000548198951172986569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37930667032132634115324379 56896000548198951172986569)
    ·
      refine ⟨42672000411149213379739927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56896000548198951172986569 42672000411149213379739927)
      ·
        refine ⟨64008000616723820069609891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42672000411149213379739927 64008000616723820069609891)
        ·
          refine ⟨96012000925085730104414837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64008000616723820069609891 96012000925085730104414837)
          ·
            refine ⟨9001125086726787197288891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96012000925085730104414837 9001125086726787197288891)
            ·
              refine ⟨13501687630090180795933337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001125086726787197288891 13501687630090180795933337)
              ·
                refine ⟨10126265722567635596950003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13501687630090180795933337 10126265722567635596950003)
                ·
                  refine ⟨15189398583851453395425005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126265722567635596950003 15189398583851453395425005)
                  ·
                    refine ⟨5696024468944295023284377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15189398583851453395425005 5696024468944295023284377)
                    ·
                      refine ⟨4272018351708221267463283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696024468944295023284377 4272018351708221267463283)
                      ·
                        rfl

theorem cell23_8319726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_8319726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319726 prefixEnd_8319726 := by exact prefixLift 8319726
  have htrace : WordTrace (prefixWord ++ tailWord_8319726) baseStart_8319726 baseEnd_8319726 := by
    simpa [prefixWord, tailWord_8319726, baseEnd_8319726] using wordTrace_append hprefix tailTrace_8319726
  have hstable : (prefixWord ++ tailWord_8319726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319726).length < 2 ^ (prefixWord ++ tailWord_8319726).sum := by decide
  have hdescent : baseEnd_8319726 < baseStart_8319726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319728 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 9]
def baseStart_8319728 : Nat := 118140960795 + 8319728 * 2 ^ 59
def prefixEnd_8319728 : Nat := 4983230072969 + 3 ^ 40 * 8319728 * 2
def baseEnd_8319728 : Nat := 474668819852170028848697

theorem tailTrace_8319728 : CollatzResearch.WordTrace tailWord_8319728 prefixEnd_8319728 474668819852170028848697 := by
  unfold tailWord_8319728
  simp only [CollatzResearch.WordTrace]
  refine ⟨151722704601526913632083919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202296939468702551509445225 151722704601526913632083919)
  ·
    refine ⟨227584056902290370448125879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151722704601526913632083919 227584056902290370448125879)
    ·
      refine ⟨341376085353435555672188819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227584056902290370448125879 341376085353435555672188819)
      ·
        refine ⟨512064128030153333508283229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341376085353435555672188819 512064128030153333508283229)
        ·
          refine ⟨192024048011307500065606211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512064128030153333508283229 192024048011307500065606211)
          ·
            refine ⟨288036072016961250098409317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192024048011307500065606211 288036072016961250098409317)
            ·
              refine ⟨54006763503180234393451747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288036072016961250098409317 54006763503180234393451747)
              ·
                refine ⟨81010145254770351590177621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54006763503180234393451747 81010145254770351590177621)
                ·
                  refine ⟨474668819852170028848697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81010145254770351590177621 474668819852170028848697)
                  ·
                    rfl

theorem cell23_8319728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_8319728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319728 prefixEnd_8319728 := by exact prefixLift 8319728
  have htrace : WordTrace (prefixWord ++ tailWord_8319728) baseStart_8319728 baseEnd_8319728 := by
    simpa [prefixWord, tailWord_8319728, baseEnd_8319728] using wordTrace_append hprefix tailTrace_8319728
  have hstable : (prefixWord ++ tailWord_8319728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319728).length < 2 ^ (prefixWord ++ tailWord_8319728).sum := by decide
  have hdescent : baseEnd_8319728 < baseStart_8319728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319742 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_8319742 : Nat := 118140960795 + 8319742 * 2 ^ 59
def prefixEnd_8319742 : Nat := 4983230072969 + 3 ^ 40 * 8319742 * 2
def baseEnd_8319742 : Nat := 4272026567398693204863209

theorem tailTrace_8319742 : CollatzResearch.WordTrace tailWord_8319742 prefixEnd_8319742 4272026567398693204863209 := by
  unfold tailWord_8319742
  simp only [CollatzResearch.WordTrace]
  refine ⟨37930739978125388456897185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202297279883335405103451653 37930739978125388456897185)
  ·
    refine ⟨28448054983594041342672889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37930739978125388456897185 28448054983594041342672889)
    ·
      refine ⟨21336041237695531007004667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28448054983594041342672889 21336041237695531007004667)
      ·
        refine ⟨32004061856543296510507001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21336041237695531007004667 32004061856543296510507001)
        ·
          refine ⟨24003046392407472382880251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32004061856543296510507001 24003046392407472382880251)
          ·
            refine ⟨36004569588611208574320377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24003046392407472382880251 36004569588611208574320377)
            ·
              refine ⟨27003427191458406430740283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36004569588611208574320377 27003427191458406430740283)
              ·
                refine ⟨40505140787187609646110425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27003427191458406430740283 40505140787187609646110425)
                ·
                  refine ⟨30378855590390707234582819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40505140787187609646110425 30378855590390707234582819)
                  ·
                    refine ⟨45568283385586060851874229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30378855590390707234582819 45568283385586060851874229)
                    ·
                      refine ⟨4272026567398693204863209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45568283385586060851874229 4272026567398693204863209)
                      ·
                        rfl

theorem cell23_8319742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_8319742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319742 prefixEnd_8319742 := by exact prefixLift 8319742
  have htrace : WordTrace (prefixWord ++ tailWord_8319742) baseStart_8319742 baseEnd_8319742 := by
    simpa [prefixWord, tailWord_8319742, baseEnd_8319742] using wordTrace_append hprefix tailTrace_8319742
  have hstable : (prefixWord ++ tailWord_8319742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319742).length < 2 ^ (prefixWord ++ tailWord_8319742).sum := by decide
  have hdescent : baseEnd_8319742 < baseStart_8319742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319755 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 3]
def baseStart_8319755 : Nat := 118140960795 + 8319755 * 2 ^ 59
def prefixEnd_8319755 : Nat := 4983230072969 + 3 ^ 40 * 8319755 * 2
def baseEnd_8319755 : Nat := 4272033242647201654000649

theorem tailTrace_8319755 : CollatzResearch.WordTrace tailWord_8319755 prefixEnd_8319755 4272033242647201654000649 := by
  unfold tailWord_8319755
  simp only [CollatzResearch.WordTrace]
  refine ⟨303446393973956010875400719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202297595982637340583600479 303446393973956010875400719)
  ·
    refine ⟨455169590960934016313101079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303446393973956010875400719 455169590960934016313101079)
    ·
      refine ⟨682754386441401024469651619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455169590960934016313101079 682754386441401024469651619)
      ·
        refine ⟨1024131579662101536704477429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682754386441401024469651619 1024131579662101536704477429)
        ·
          refine ⟨96012335593322019066044759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1024131579662101536704477429 96012335593322019066044759)
          ·
            refine ⟨144018503389983028599067139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96012335593322019066044759 144018503389983028599067139)
            ·
              refine ⟨216027755084974542898600709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144018503389983028599067139 216027755084974542898600709)
              ·
                refine ⟨40505204078432726793487633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216027755084974542898600709 40505204078432726793487633)
                ·
                  refine ⟨30378903058824545095115725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40505204078432726793487633 30378903058824545095115725)
                  ·
                    refine ⟨11392088647059204410668397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30378903058824545095115725 11392088647059204410668397)
                    ·
                      refine ⟨4272033242647201654000649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392088647059204410668397 4272033242647201654000649)
                      ·
                        rfl

theorem cell23_8319755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 3].length) (baseStart_8319755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319755 prefixEnd_8319755 := by exact prefixLift 8319755
  have htrace : WordTrace (prefixWord ++ tailWord_8319755) baseStart_8319755 baseEnd_8319755 := by
    simpa [prefixWord, tailWord_8319755, baseEnd_8319755] using wordTrace_append hprefix tailTrace_8319755
  have hstable : (prefixWord ++ tailWord_8319755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319755).length < 2 ^ (prefixWord ++ tailWord_8319755).sum := by decide
  have hdescent : baseEnd_8319755 < baseStart_8319755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319772 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_8319772 : Nat := 118140960795 + 8319772 * 2 ^ 59
def prefixEnd_8319772 : Nat := 4983230072969 + 3 ^ 40 * 8319772 * 2
def baseEnd_8319772 : Nat := 4272041971818328087488071

theorem tailTrace_8319772 : CollatzResearch.WordTrace tailWord_8319772 prefixEnd_8319772 4272041971818328087488071 := by
  unfold tailWord_8319772
  simp only [CollatzResearch.WordTrace]
  refine ⟨151723507007447211389384785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202298009343262948519179713 151723507007447211389384785)
  ·
    refine ⟨113792630255585408542038589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151723507007447211389384785 113792630255585408542038589)
    ·
      refine ⟨42672236345844528203264471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113792630255585408542038589 42672236345844528203264471)
      ·
        refine ⟨64008354518766792304896707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42672236345844528203264471 64008354518766792304896707)
        ·
          refine ⟨96012531778150188457345061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64008354518766792304896707 96012531778150188457345061)
          ·
            refine ⟨18002349708403160335752199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96012531778150188457345061 18002349708403160335752199)
            ·
              refine ⟨27003524562604740503628299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002349708403160335752199 27003524562604740503628299)
              ·
                refine ⟨40505286843907110755442449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27003524562604740503628299 40505286843907110755442449)
                ·
                  refine ⟨30378965132930333066581837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40505286843907110755442449 30378965132930333066581837)
                  ·
                    refine ⟨11392111924848874899968189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30378965132930333066581837 11392111924848874899968189)
                    ·
                      refine ⟨4272041971818328087488071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392111924848874899968189 4272041971818328087488071)
                      ·
                        rfl

theorem cell23_8319772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_8319772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319772 prefixEnd_8319772 := by exact prefixLift 8319772
  have htrace : WordTrace (prefixWord ++ tailWord_8319772) baseStart_8319772 baseEnd_8319772 := by
    simpa [prefixWord, tailWord_8319772, baseEnd_8319772] using wordTrace_append hprefix tailTrace_8319772
  have hstable : (prefixWord ++ tailWord_8319772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319772).length < 2 ^ (prefixWord ++ tailWord_8319772).sum := by decide
  have hdescent : baseEnd_8319772 < baseStart_8319772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319796 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 5]
def baseStart_8319796 : Nat := 118140960795 + 8319796 * 2 ^ 59
def prefixEnd_8319796 : Nat := 4983230072969 + 3 ^ 40 * 8319796 * 2
def baseEnd_8319796 : Nat := 474672699483781777065329

theorem tailTrace_8319796 : CollatzResearch.WordTrace tailWord_8319796 prefixEnd_8319796 474672699483781777065329 := by
  unfold tailWord_8319796
  simp only [CollatzResearch.WordTrace]
  refine ⟨151723944683403737438821621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202298592911204983251762161 151723944683403737438821621)
  ·
    refine ⟨14224119814069100384889527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151723944683403737438821621 14224119814069100384889527)
    ·
      refine ⟨21336179721103650577334291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14224119814069100384889527 21336179721103650577334291)
      ·
        refine ⟨32004269581655475866001437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21336179721103650577334291 32004269581655475866001437)
        ·
          refine ⟨12001601093120803449750539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32004269581655475866001437 12001601093120803449750539)
          ·
            refine ⟨18002401639681205174625809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001601093120803449750539 18002401639681205174625809)
            ·
              refine ⟨13501801229760903880969357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18002401639681205174625809 13501801229760903880969357)
              ·
                refine ⟨5063175461160338955363509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13501801229760903880969357 5063175461160338955363509)
                ·
                  refine ⟨474672699483781777065329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5063175461160338955363509 474672699483781777065329)
                  ·
                    rfl

theorem cell23_8319796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_8319796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319796 prefixEnd_8319796 := by exact prefixLift 8319796
  have htrace : WordTrace (prefixWord ++ tailWord_8319796) baseStart_8319796 baseEnd_8319796 := by
    simpa [prefixWord, tailWord_8319796, baseEnd_8319796] using wordTrace_append hprefix tailTrace_8319796
  have hstable : (prefixWord ++ tailWord_8319796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319796).length < 2 ^ (prefixWord ++ tailWord_8319796).sum := by decide
  have hdescent : baseEnd_8319796 < baseStart_8319796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319872 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 3, 5, 2]
def baseStart_8319872 : Nat := 118140960795 + 8319872 * 2 ^ 59
def prefixEnd_8319872 : Nat := 4983230072969 + 3 ^ 40 * 8319872 * 2
def baseEnd_8319872 : Nat := 4272093319883777696237611

theorem tailTrace_8319872 : CollatzResearch.WordTrace tailWord_8319872 prefixEnd_8319872 4272093319883777696237611 := by
  unfold tailWord_8319872
  simp only [CollatzResearch.WordTrace]
  refine ⟨151725330657266069928704935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202300440876354759904939913 151725330657266069928704935)
  ·
    refine ⟨227587995985899104893057403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151725330657266069928704935 227587995985899104893057403)
    ·
      refine ⟨341381993978848657339586105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227587995985899104893057403 341381993978848657339586105)
      ·
        refine ⟨256036495484136493004689579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341381993978848657339586105 256036495484136493004689579)
        ·
          refine ⟨384054743226204739507034369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256036495484136493004689579 384054743226204739507034369)
          ·
            refine ⟨288041057419653554630275777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384054743226204739507034369 288041057419653554630275777)
            ·
              refine ⟨216030793064740165972706833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288041057419653554630275777 216030793064740165972706833)
              ·
                refine ⟨162023094798555124479530125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216030793064740165972706833 162023094798555124479530125)
                ·
                  refine ⟨60758660549458171679823797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162023094798555124479530125 60758660549458171679823797)
                  ·
                    refine ⟨5696124426511703594983481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60758660549458171679823797 5696124426511703594983481)
                    ·
                      refine ⟨4272093319883777696237611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696124426511703594983481 4272093319883777696237611)
                      ·
                        rfl

theorem cell23_8319872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_8319872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319872 prefixEnd_8319872 := by exact prefixLift 8319872
  have htrace : WordTrace (prefixWord ++ tailWord_8319872) baseStart_8319872 baseEnd_8319872 := by
    simpa [prefixWord, tailWord_8319872, baseEnd_8319872] using wordTrace_append hprefix tailTrace_8319872
  have hstable : (prefixWord ++ tailWord_8319872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319872).length < 2 ^ (prefixWord ++ tailWord_8319872).sum := by decide
  have hdescent : baseEnd_8319872 < baseStart_8319872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319906 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_8319906 : Nat := 118140960795 + 8319906 * 2 ^ 59
def prefixEnd_8319906 : Nat := 4983230072969 + 3 ^ 40 * 8319906 * 2
def baseEnd_8319906 : Nat := 4272110778226030563212455

theorem tailTrace_8319906 : CollatzResearch.WordTrace tailWord_8319906 prefixEnd_8319906 4272110778226030563212455 := by
  unfold tailWord_8319906
  simp only [CollatzResearch.WordTrace]
  refine ⟨75862975349102240916036893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202301267597605975776098381 75862975349102240916036893)
  ·
    refine ⟨28448615755913340343513835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75862975349102240916036893 28448615755913340343513835)
    ·
      refine ⟨42672923633870010515270753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28448615755913340343513835 42672923633870010515270753)
      ·
        refine ⟨32004692725402507886453065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42672923633870010515270753 32004692725402507886453065)
        ·
          refine ⟨24003519544051880914839799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32004692725402507886453065 24003519544051880914839799)
          ·
            refine ⟨36005279316077821372259699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24003519544051880914839799 36005279316077821372259699)
            ·
              refine ⟨54007918974116732058389549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36005279316077821372259699 54007918974116732058389549)
              ·
                refine ⟨20252969615293774521896081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54007918974116732058389549 20252969615293774521896081)
                ·
                  refine ⟨15189727211470330891422061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20252969615293774521896081 15189727211470330891422061)
                  ·
                    refine ⟨5696147704301374084283273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15189727211470330891422061 5696147704301374084283273)
                    ·
                      refine ⟨4272110778226030563212455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696147704301374084283273 4272110778226030563212455)
                      ·
                        rfl

theorem cell23_8319906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_8319906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319906 prefixEnd_8319906 := by exact prefixLift 8319906
  have htrace : WordTrace (prefixWord ++ tailWord_8319906) baseStart_8319906 baseEnd_8319906 := by
    simpa [prefixWord, tailWord_8319906, baseEnd_8319906] using wordTrace_append hprefix tailTrace_8319906
  have hstable : (prefixWord ++ tailWord_8319906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319906).length < 2 ^ (prefixWord ++ tailWord_8319906).sum := by decide
  have hdescent : baseEnd_8319906 < baseStart_8319906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319919 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 7, 2, 2]
def baseStart_8319919 : Nat := 118140960795 + 8319919 * 2 ^ 59
def prefixEnd_8319919 : Nat := 4983230072969 + 3 ^ 40 * 8319919 * 2
def baseEnd_8319919 : Nat := 4272117453474539012349895

theorem tailTrace_8319919 : CollatzResearch.WordTrace tailWord_8319919 prefixEnd_8319919 4272117453474539012349895 := by
  unfold tailWord_8319919
  simp only [CollatzResearch.WordTrace]
  refine ⟨303452375545361866884370811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202301583696907911256247207 303452375545361866884370811)
  ·
    refine ⟨455178563318042800326556217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303452375545361866884370811 455178563318042800326556217)
    ·
      refine ⟨341383922488532100244917163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455178563318042800326556217 341383922488532100244917163)
      ·
        refine ⟨512075883732798150367375745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341383922488532100244917163 512075883732798150367375745)
        ·
          refine ⟨384056912799598612775531809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512075883732798150367375745 384056912799598612775531809)
          ·
            refine ⟨288042684599698959581648857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384056912799598612775531809 288042684599698959581648857)
            ·
              refine ⟨216032013449774219686236643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288042684599698959581648857 216032013449774219686236643)
              ·
                refine ⟨324048020174661329529354965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216032013449774219686236643 324048020174661329529354965)
                ·
                  refine ⟨7594875472843624910844257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 324048020174661329529354965 7594875472843624910844257)
                  ·
                    refine ⟨5696156604632718683133193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7594875472843624910844257 5696156604632718683133193)
                    ·
                      refine ⟨4272117453474539012349895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696156604632718683133193 4272117453474539012349895)
                      ·
                        rfl

theorem cell23_8319919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 2, 2].length) (baseStart_8319919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319919 prefixEnd_8319919 := by exact prefixLift 8319919
  have htrace : WordTrace (prefixWord ++ tailWord_8319919) baseStart_8319919 baseEnd_8319919 := by
    simpa [prefixWord, tailWord_8319919, baseEnd_8319919] using wordTrace_append hprefix tailTrace_8319919
  have hstable : (prefixWord ++ tailWord_8319919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319919).length < 2 ^ (prefixWord ++ tailWord_8319919).sum := by decide
  have hdescent : baseEnd_8319919 < baseStart_8319919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319929 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 2, 4]
def baseStart_8319929 : Nat := 118140960795 + 8319929 * 2 ^ 59
def prefixEnd_8319929 : Nat := 4983230072969 + 3 ^ 40 * 8319929 * 2
def baseEnd_8319929 : Nat := 1424040862760361324408283

theorem tailTrace_8319929 : CollatzResearch.WordTrace tailWord_8319929 prefixEnd_8319929 1424040862760361324408283 := by
  unfold tailWord_8319929
  simp only [CollatzResearch.WordTrace]
  refine ⟨303452740275325638592234841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202301826850217092394823227 303452740275325638592234841)
  ·
    refine ⟨227589555206494228944176131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303452740275325638592234841 227589555206494228944176131)
    ·
      refine ⟨341384332809741343416264197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227589555206494228944176131 341384332809741343416264197)
      ·
        refine ⟨64009562401826501890549537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341384332809741343416264197 64009562401826501890549537)
        ·
          refine ⟨48007171801369876417912153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64009562401826501890549537 48007171801369876417912153)
          ·
            refine ⟨36005378851027407313434115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48007171801369876417912153 36005378851027407313434115)
            ·
              refine ⟨54008068276541110970151173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36005378851027407313434115 54008068276541110970151173)
              ·
                refine ⟨10126512801851458306903345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54008068276541110970151173 10126512801851458306903345)
                ·
                  refine ⟨7594884601388593730177509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10126512801851458306903345 7594884601388593730177509)
                  ·
                    refine ⟨1424040862760361324408283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7594884601388593730177509 1424040862760361324408283)
                    ·
                      rfl

theorem cell23_8319929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_8319929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319929 prefixEnd_8319929 := by exact prefixLift 8319929
  have htrace : WordTrace (prefixWord ++ tailWord_8319929) baseStart_8319929 baseEnd_8319929 := by
    simpa [prefixWord, tailWord_8319929, baseEnd_8319929] using wordTrace_append hprefix tailTrace_8319929
  have hstable : (prefixWord ++ tailWord_8319929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319929).length < 2 ^ (prefixWord ++ tailWord_8319929).sum := by decide
  have hdescent : baseEnd_8319929 < baseStart_8319929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319935 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_8319935 : Nat := 118140960795 + 8319935 * 2 ^ 59
def prefixEnd_8319935 : Nat := 4983230072969 + 3 ^ 40 * 8319935 * 2
def baseEnd_8319935 : Nat := 4272125669165010949749821

theorem tailTrace_8319935 : CollatzResearch.WordTrace tailWord_8319935 prefixEnd_8319935 4272125669165010949749821 := by
  unfold tailWord_8319935
  simp only [CollatzResearch.WordTrace]
  refine ⟨303452959113303901616953259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202301972742202601077968839 303452959113303901616953259)
  ·
    refine ⟨455179438669955852425429889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303452959113303901616953259 455179438669955852425429889)
    ·
      refine ⟨341384579002466889319072417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455179438669955852425429889 341384579002466889319072417)
      ·
        refine ⟨256038434251850166989304313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341384579002466889319072417 256038434251850166989304313)
        ·
          refine ⟨192028825688887625241978235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256038434251850166989304313 192028825688887625241978235)
          ·
            refine ⟨288043238533331437862967353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192028825688887625241978235 288043238533331437862967353)
            ·
              refine ⟨216032428899998578397225515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288043238533331437862967353 216032428899998578397225515)
              ·
                refine ⟨324048643349997867595838273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216032428899998578397225515 324048643349997867595838273)
                ·
                  refine ⟨243036482512498400696878705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324048643349997867595838273 243036482512498400696878705)
                  ·
                    refine ⟨182277361884373800522659029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243036482512498400696878705 182277361884373800522659029)
                    ·
                      refine ⟨4272125669165010949749821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182277361884373800522659029 4272125669165010949749821)
                      ·
                        rfl

theorem cell23_8319935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_8319935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319935 prefixEnd_8319935 := by exact prefixLift 8319935
  have htrace : WordTrace (prefixWord ++ tailWord_8319935) baseStart_8319935 baseEnd_8319935 := by
    simpa [prefixWord, tailWord_8319935, baseEnd_8319935] using wordTrace_append hprefix tailTrace_8319935
  have hstable : (prefixWord ++ tailWord_8319935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319935).length < 2 ^ (prefixWord ++ tailWord_8319935).sum := by decide
  have hdescent : baseEnd_8319935 < baseStart_8319935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319969 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_8319969 : Nat := 118140960795 + 8319969 * 2 ^ 59
def prefixEnd_8319969 : Nat := 4983230072969 + 3 ^ 40 * 8319969 * 2
def baseEnd_8319969 : Nat := 4272143127507263816724665

theorem tailTrace_8319969 : CollatzResearch.WordTrace tailWord_8319969 prefixEnd_8319969 4272143127507263816724665 := by
  unfold tailWord_8319969
  simp only [CollatzResearch.WordTrace]
  refine ⟨303454199195180725423690961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202302799463453816949127307 303454199195180725423690961)
  ·
    refine ⟨227590649396385544067768221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303454199195180725423690961 227590649396385544067768221)
    ·
      refine ⟨85346493523644579025413083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227590649396385544067768221 85346493523644579025413083)
      ·
        refine ⟨128019740285466868538119625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85346493523644579025413083 128019740285466868538119625)
        ·
          refine ⟨96014805214100151403589719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128019740285466868538119625 96014805214100151403589719)
          ·
            refine ⟨144022207821150227105384579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96014805214100151403589719 144022207821150227105384579)
            ·
              refine ⟨216033311731725340658076869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144022207821150227105384579 216033311731725340658076869)
              ·
                refine ⟨40506245949698501373389413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216033311731725340658076869 40506245949698501373389413)
                ·
                  refine ⟨7594921115568469007510515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40506245949698501373389413 7594921115568469007510515)
                  ·
                    refine ⟨11392381673352703511265773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594921115568469007510515 11392381673352703511265773)
                    ·
                      refine ⟨4272143127507263816724665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392381673352703511265773 4272143127507263816724665)
                      ·
                        rfl

theorem cell23_8319969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_8319969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319969 prefixEnd_8319969 := by exact prefixLift 8319969
  have htrace : WordTrace (prefixWord ++ tailWord_8319969) baseStart_8319969 baseEnd_8319969 := by
    simpa [prefixWord, tailWord_8319969, baseEnd_8319969] using wordTrace_append hprefix tailTrace_8319969
  have hstable : (prefixWord ++ tailWord_8319969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319969).length < 2 ^ (prefixWord ++ tailWord_8319969).sum := by decide
  have hdescent : baseEnd_8319969 < baseStart_8319969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319970 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_8319970 : Nat := 118140960795 + 8319970 * 2 ^ 59
def prefixEnd_8319970 : Nat := 4983230072969 + 3 ^ 40 * 8319970 * 2
def baseEnd_8319970 : Nat := 4272143640987918312812161

theorem tailTrace_8319970 : CollatzResearch.WordTrace tailWord_8319970 prefixEnd_8319970 4272143640987918312812161 := by
  unfold tailWord_8319970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75863558917044275648619341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202302823778784735062984909 75863558917044275648619341)
  ·
    refine ⟨28448834593891603368232253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75863558917044275648619341 28448834593891603368232253)
    ·
      refine ⟨10668312972709351263087095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28448834593891603368232253 10668312972709351263087095)
      ·
        refine ⟨16002469459064026894630643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668312972709351263087095 16002469459064026894630643)
        ·
          refine ⟨24003704188596040341945965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16002469459064026894630643 24003704188596040341945965)
          ·
            refine ⟨9001389070723515128229737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24003704188596040341945965 9001389070723515128229737)
            ·
              refine ⟨6751041803042636346172303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9001389070723515128229737 6751041803042636346172303)
              ·
                refine ⟨10126562704563954519258455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751041803042636346172303 10126562704563954519258455)
                ·
                  refine ⟨15189844056845931778887683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126562704563954519258455 15189844056845931778887683)
                  ·
                    refine ⟨22784766085268897668331525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15189844056845931778887683 22784766085268897668331525)
                    ·
                      refine ⟨4272143640987918312812161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22784766085268897668331525 4272143640987918312812161)
                      ·
                        rfl

theorem cell23_8319970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_8319970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319970 prefixEnd_8319970 := by exact prefixLift 8319970
  have htrace : WordTrace (prefixWord ++ tailWord_8319970) baseStart_8319970 baseEnd_8319970 := by
    simpa [prefixWord, tailWord_8319970, baseEnd_8319970] using wordTrace_append hprefix tailTrace_8319970
  have hstable : (prefixWord ++ tailWord_8319970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319970).length < 2 ^ (prefixWord ++ tailWord_8319970).sum := by decide
  have hdescent : baseEnd_8319970 < baseStart_8319970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8319973 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_8319973 : Nat := 118140960795 + 8319973 * 2 ^ 59
def prefixEnd_8319973 : Nat := 4983230072969 + 3 ^ 40 * 8319973 * 2
def baseEnd_8319973 : Nat := 4272145181429881801074647

theorem tailTrace_8319973 : CollatzResearch.WordTrace tailWord_8319973 prefixEnd_8319973 4272145181429881801074647 := by
  unfold tailWord_8319973
  simp only [CollatzResearch.WordTrace]
  refine ⟨303454345087166234106836573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202302896724777489404557715 303454345087166234106836573)
  ·
    refine ⟨113795379407687337790063715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303454345087166234106836573 113795379407687337790063715)
    ·
      refine ⟨170693069111531006685095573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113795379407687337790063715 170693069111531006685095573)
      ·
        refine ⟨8001237614603015938363855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170693069111531006685095573 8001237614603015938363855)
        ·
          refine ⟨12001856421904523907545783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001237614603015938363855 12001856421904523907545783)
          ·
            refine ⟨18002784632856785861318675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001856421904523907545783 18002784632856785861318675)
            ·
              refine ⟨27004176949285178791978013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002784632856785861318675 27004176949285178791978013)
              ·
                refine ⟨10126566355981942046991755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27004176949285178791978013 10126566355981942046991755)
                ·
                  refine ⟨15189849533972913070487633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126566355981942046991755 15189849533972913070487633)
                  ·
                    refine ⟨11392387150479684802865725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15189849533972913070487633 11392387150479684802865725)
                    ·
                      refine ⟨4272145181429881801074647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392387150479684802865725 4272145181429881801074647)
                      ·
                        rfl

theorem cell23_8319973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_8319973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8319973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8319973 prefixEnd_8319973 := by exact prefixLift 8319973
  have htrace : WordTrace (prefixWord ++ tailWord_8319973) baseStart_8319973 baseEnd_8319973 := by
    simpa [prefixWord, tailWord_8319973, baseEnd_8319973] using wordTrace_append hprefix tailTrace_8319973
  have hstable : (prefixWord ++ tailWord_8319973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8319973).length < 2 ^ (prefixWord ++ tailWord_8319973).sum := by decide
  have hdescent : baseEnd_8319973 < baseStart_8319973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8319973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320026 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2]
def baseStart_8320026 : Nat := 118140960795 + 8320026 * 2 ^ 59
def prefixEnd_8320026 : Nat := 4983230072969 + 3 ^ 40 * 8320026 * 2
def baseEnd_8320026 : Nat := 4272172395904570093711903

theorem tailTrace_8320026 : CollatzResearch.WordTrace tailWord_8320026 prefixEnd_8320026 4272172395904570093711903 := by
  unfold tailWord_8320026
  simp only [CollatzResearch.WordTrace]
  refine ⟨75864069538993556039628983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202304185437316149439010621 75864069538993556039628983)
  ·
    refine ⟨113796104308490334059443475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75864069538993556039628983 113796104308490334059443475)
    ·
      refine ⟨170694156462735501089165213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113796104308490334059443475 170694156462735501089165213)
      ·
        refine ⟨64010308673525812908436955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170694156462735501089165213 64010308673525812908436955)
        ·
          refine ⟨96015463010288719362655433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64010308673525812908436955 96015463010288719362655433)
          ·
            refine ⟨72011597257716539521991575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96015463010288719362655433 72011597257716539521991575)
            ·
              refine ⟨108017395886574809282987363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72011597257716539521991575 108017395886574809282987363)
              ·
                refine ⟨162026093829862213924481045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108017395886574809282987363 162026093829862213924481045)
                ·
                  refine ⟨7594973148274791277710049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162026093829862213924481045 7594973148274791277710049)
                  ·
                    refine ⟨5696229861206093458282537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7594973148274791277710049 5696229861206093458282537)
                    ·
                      refine ⟨4272172395904570093711903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696229861206093458282537 4272172395904570093711903)
                      ·
                        rfl

theorem cell23_8320026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_8320026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320026 prefixEnd_8320026 := by exact prefixLift 8320026
  have htrace : WordTrace (prefixWord ++ tailWord_8320026) baseStart_8320026 baseEnd_8320026 := by
    simpa [prefixWord, tailWord_8320026, baseEnd_8320026] using wordTrace_append hprefix tailTrace_8320026
  have hstable : (prefixWord ++ tailWord_8320026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320026).length < 2 ^ (prefixWord ++ tailWord_8320026).sum := by decide
  have hdescent : baseEnd_8320026 < baseStart_8320026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320060 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_8320060 : Nat := 118140960795 + 8320060 * 2 ^ 59
def prefixEnd_8320060 : Nat := 4983230072969 + 3 ^ 40 * 8320060 * 2
def baseEnd_8320060 : Nat := 4272189854246822960686747

theorem tailTrace_8320060 : CollatzResearch.WordTrace tailWord_8320060 prefixEnd_8320060 4272189854246822960686747 := by
  unfold tailWord_8320060
  simp only [CollatzResearch.WordTrace]
  refine ⟨151728759118925523982626817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202305012158567365310169089 151728759118925523982626817)
  ·
    refine ⟨113796569339194142986970113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151728759118925523982626817 113796569339194142986970113)
    ·
      refine ⟨85347427004395607240227585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113796569339194142986970113 85347427004395607240227585)
      ·
        refine ⟨64010570253296705430170689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85347427004395607240227585 64010570253296705430170689)
        ·
          refine ⟨48007927689972529072628017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64010570253296705430170689 48007927689972529072628017)
          ·
            refine ⟨36005945767479396804471013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48007927689972529072628017 36005945767479396804471013)
            ·
              refine ⟨6751114831402386900838315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36005945767479396804471013 6751114831402386900838315)
              ·
                refine ⟨10126672247103580351257473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751114831402386900838315 10126672247103580351257473)
                ·
                  refine ⟨7595004185327685263443105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10126672247103580351257473 7595004185327685263443105)
                  ·
                    refine ⟨5696253138995763947582329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7595004185327685263443105 5696253138995763947582329)
                    ·
                      refine ⟨4272189854246822960686747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696253138995763947582329 4272189854246822960686747)
                      ·
                        rfl

theorem cell23_8320060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_8320060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320060 prefixEnd_8320060 := by exact prefixLift 8320060
  have htrace : WordTrace (prefixWord ++ tailWord_8320060) baseStart_8320060 baseEnd_8320060 := by
    simpa [prefixWord, tailWord_8320060, baseEnd_8320060] using wordTrace_append hprefix tailTrace_8320060
  have hstable : (prefixWord ++ tailWord_8320060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320060).length < 2 ^ (prefixWord ++ tailWord_8320060).sum := by decide
  have hdescent : baseEnd_8320060 < baseStart_8320060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320072 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_8320072 : Nat := 118140960795 + 8320072 * 2 ^ 59
def prefixEnd_8320072 : Nat := 4983230072969 + 3 ^ 40 * 8320072 * 2
def baseEnd_8320072 : Nat := 4272196016014676913736691

theorem tailTrace_8320072 : CollatzResearch.WordTrace tailWord_8320072 prefixEnd_8320072 4272196016014676913736691 := by
  unfold tailWord_8320072
  simp only [CollatzResearch.WordTrace]
  refine ⟨151728977956903787007345235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202305303942538382676460313 151728977956903787007345235)
  ·
    refine ⟨227593466935355680511017853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151728977956903787007345235 227593466935355680511017853)
    ·
      refine ⟨85347550100758380191631695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227593466935355680511017853 85347550100758380191631695)
      ·
        refine ⟨128021325151137570287447543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85347550100758380191631695 128021325151137570287447543)
        ·
          refine ⟨192031987726706355431171315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128021325151137570287447543 192031987726706355431171315)
          ·
            refine ⟨288047981590059533146756973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192031987726706355431171315 288047981590059533146756973)
            ·
              refine ⟨108017993096272324930033865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288047981590059533146756973 108017993096272324930033865)
              ·
                refine ⟨81013494822204243697525399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108017993096272324930033865 81013494822204243697525399)
                ·
                  refine ⟨121520242233306365546288099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81013494822204243697525399 121520242233306365546288099)
                  ·
                    refine ⟨182280363349959548319432149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121520242233306365546288099 182280363349959548319432149)
                    ·
                      refine ⟨4272196016014676913736691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182280363349959548319432149 4272196016014676913736691)
                      ·
                        rfl

theorem cell23_8320072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_8320072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320072 prefixEnd_8320072 := by exact prefixLift 8320072
  have htrace : WordTrace (prefixWord ++ tailWord_8320072) baseStart_8320072 baseEnd_8320072 := by
    simpa [prefixWord, tailWord_8320072, baseEnd_8320072] using wordTrace_append hprefix tailTrace_8320072
  have hstable : (prefixWord ++ tailWord_8320072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320072).length < 2 ^ (prefixWord ++ tailWord_8320072).sum := by decide
  have hdescent : baseEnd_8320072 < baseStart_8320072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320094 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_8320094 : Nat := 118140960795 + 8320094 * 2 ^ 59
def prefixEnd_8320094 : Nat := 4983230072969 + 3 ^ 40 * 8320094 * 2
def baseEnd_8320094 : Nat := 4272207312589075827661591

theorem tailTrace_8320094 : CollatzResearch.WordTrace tailWord_8320094 prefixEnd_8320094 4272207312589075827661591 := by
  unfold tailWord_8320094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37932344789965983971498917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202305838879818581181327557 37932344789965983971498917)
  ·
    refine ⟨7112314648118621994656047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37932344789965983971498917 7112314648118621994656047)
    ·
      refine ⟨10668471972177932991984071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7112314648118621994656047 10668471972177932991984071)
      ·
        refine ⟨16002707958266899487976107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668471972177932991984071 16002707958266899487976107)
        ·
          refine ⟨24004061937400349231964161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16002707958266899487976107 24004061937400349231964161)
          ·
            refine ⟨18003046453050261923973121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24004061937400349231964161 18003046453050261923973121)
            ·
              refine ⟨13502284839787696442979841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18003046453050261923973121 13502284839787696442979841)
              ·
                refine ⟨10126713629840772332234881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502284839787696442979841 10126713629840772332234881)
                ·
                  refine ⟨7595035222380579249176161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10126713629840772332234881 7595035222380579249176161)
                  ·
                    refine ⟨5696276416785434436882121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7595035222380579249176161 5696276416785434436882121)
                    ·
                      refine ⟨4272207312589075827661591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696276416785434436882121 4272207312589075827661591)
                      ·
                        rfl

theorem cell23_8320094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_8320094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320094 prefixEnd_8320094 := by exact prefixLift 8320094
  have htrace : WordTrace (prefixWord ++ tailWord_8320094) baseStart_8320094 baseEnd_8320094 := by
    simpa [prefixWord, tailWord_8320094, baseEnd_8320094] using wordTrace_append hprefix tailTrace_8320094
  have hstable : (prefixWord ++ tailWord_8320094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320094).length < 2 ^ (prefixWord ++ tailWord_8320094).sum := by decide
  have hdescent : baseEnd_8320094 < baseStart_8320094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320119 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_8320119 : Nat := 118140960795 + 8320119 * 2 ^ 59
def prefixEnd_8320119 : Nat := 4983230072969 + 3 ^ 40 * 8320119 * 2
def baseEnd_8320119 : Nat := 4272220149605438229848975

theorem tailTrace_8320119 : CollatzResearch.WordTrace tailWord_8320119 prefixEnd_8320119 4272220149605438229848975 := by
  unfold tailWord_8320119
  simp only [CollatzResearch.WordTrace]
  refine ⟨303459670144637301041651411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202306446763091534027767607 303459670144637301041651411)
  ·
    refine ⟨455189505216955951562477117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303459670144637301041651411 455189505216955951562477117)
    ·
      refine ⟨170696064456358481835928919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455189505216955951562477117 170696064456358481835928919)
      ·
        refine ⟨256044096684537722753893379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170696064456358481835928919 256044096684537722753893379)
        ·
          refine ⟨384066145026806584130840069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256044096684537722753893379 384066145026806584130840069)
          ·
            refine ⟨72012402192526234524532513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384066145026806584130840069 72012402192526234524532513)
            ·
              refine ⟨54009301644394675893399385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72012402192526234524532513 54009301644394675893399385)
              ·
                refine ⟨40506976233296006920049539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54009301644394675893399385 40506976233296006920049539)
                ·
                  refine ⟨60760464349944010380074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40506976233296006920049539 60760464349944010380074309)
                  ·
                    refine ⟨11392587065614501946263933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60760464349944010380074309 11392587065614501946263933)
                    ·
                      refine ⟨4272220149605438229848975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392587065614501946263933 4272220149605438229848975)
                      ·
                        rfl

theorem cell23_8320119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_8320119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320119 prefixEnd_8320119 := by exact prefixLift 8320119
  have htrace : WordTrace (prefixWord ++ tailWord_8320119) baseStart_8320119 baseEnd_8320119 := by
    simpa [prefixWord, tailWord_8320119, baseEnd_8320119] using wordTrace_append hprefix tailTrace_8320119
  have hstable : (prefixWord ++ tailWord_8320119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320119).length < 2 ^ (prefixWord ++ tailWord_8320119).sum := by decide
  have hdescent : baseEnd_8320119 < baseStart_8320119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320133 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_8320133 : Nat := 118140960795 + 8320133 * 2 ^ 59
def prefixEnd_8320133 : Nat := 4983230072969 + 3 ^ 40 * 8320133 * 2
def baseEnd_8320133 : Nat := 4272227338334601175073911

theorem tailTrace_8320133 : CollatzResearch.WordTrace tailWord_8320133 prefixEnd_8320133 4272227338334601175073911 := by
  unfold tailWord_8320133
  simp only [CollatzResearch.WordTrace]
  refine ⟨303460180766586581432661053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202306787177724387621774035 303460180766586581432661053)
  ·
    refine ⟨113797567787469968037247895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303460180766586581432661053 113797567787469968037247895)
    ·
      refine ⟨170696351681204952055871843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113797567787469968037247895 170696351681204952055871843)
      ·
        refine ⟨256044527521807428083807765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170696351681204952055871843 256044527521807428083807765)
        ·
          refine ⟨12002087227584723191428489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256044527521807428083807765 12002087227584723191428489)
          ·
            refine ⟨9001565420688542393571367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12002087227584723191428489 9001565420688542393571367)
            ·
              refine ⟨13502348131032813590357051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001565420688542393571367 13502348131032813590357051)
              ·
                refine ⟨20253522196549220385535577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13502348131032813590357051 20253522196549220385535577)
                ·
                  refine ⟨15190141647411915289151683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20253522196549220385535577 15190141647411915289151683)
                  ·
                    refine ⟨22785212471117872933727525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15190141647411915289151683 22785212471117872933727525)
                    ·
                      refine ⟨4272227338334601175073911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22785212471117872933727525 4272227338334601175073911)
                      ·
                        rfl

theorem cell23_8320133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_8320133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320133 prefixEnd_8320133 := by exact prefixLift 8320133
  have htrace : WordTrace (prefixWord ++ tailWord_8320133) baseStart_8320133 baseEnd_8320133 := by
    simpa [prefixWord, tailWord_8320133, baseEnd_8320133] using wordTrace_append hprefix tailTrace_8320133
  have hstable : (prefixWord ++ tailWord_8320133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320133).length < 2 ^ (prefixWord ++ tailWord_8320133).sum := by decide
  have hdescent : baseEnd_8320133 < baseStart_8320133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320156 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 6]
def baseStart_8320156 : Nat := 118140960795 + 8320156 * 2 ^ 59
def prefixEnd_8320156 : Nat := 4983230072969 + 3 ^ 40 * 8320156 * 2
def baseEnd_8320156 : Nat := 474693238709961620565145

theorem tailTrace_8320156 : CollatzResearch.WordTrace tailWord_8320156 prefixEnd_8320156 474693238709961620565145 := by
  unfold tailWord_8320156
  simp only [CollatzResearch.WordTrace]
  refine ⟨151730509822751628180374161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202307346430335504240498881 151730509822751628180374161)
  ·
    refine ⟨113797882367063721135280621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151730509822751628180374161 113797882367063721135280621)
    ·
      refine ⟨42674205887648895425730233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113797882367063721135280621 42674205887648895425730233)
      ·
        refine ⟨32005654415736671569297675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42674205887648895425730233 32005654415736671569297675)
        ·
          refine ⟨48008481623605007353946513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32005654415736671569297675 48008481623605007353946513)
          ·
            refine ⟨36006361217703755515459885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48008481623605007353946513 36006361217703755515459885)
            ·
              refine ⟨13502385456638908318297457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36006361217703755515459885 13502385456638908318297457)
              ·
                refine ⟨10126789092479181238723093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502385456638908318297457 10126789092479181238723093)
                ·
                  refine ⟨474693238709961620565145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10126789092479181238723093 474693238709961620565145)
                  ·
                    rfl

theorem cell23_8320156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_8320156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320156 prefixEnd_8320156 := by exact prefixLift 8320156
  have htrace : WordTrace (prefixWord ++ tailWord_8320156) baseStart_8320156 baseEnd_8320156 := by
    simpa [prefixWord, tailWord_8320156, baseEnd_8320156] using wordTrace_append hprefix tailTrace_8320156
  have hstable : (prefixWord ++ tailWord_8320156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320156).length < 2 ^ (prefixWord ++ tailWord_8320156).sum := by decide
  have hdescent : baseEnd_8320156 < baseStart_8320156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320176 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 4, 3, 2]
def baseStart_8320176 : Nat := 118140960795 + 8320176 * 2 ^ 59
def prefixEnd_8320176 : Nat := 4983230072969 + 3 ^ 40 * 8320176 * 2
def baseEnd_8320176 : Nat := 4272249418002744506836213

theorem tailTrace_8320176 : CollatzResearch.WordTrace tailWord_8320176 prefixEnd_8320176 4272249418002744506836213 := by
  unfold tailWord_8320176
  simp only [CollatzResearch.WordTrace]
  refine ⟨151730874552715399888238191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202307832736953866517650921 151730874552715399888238191)
  ·
    refine ⟨227596311829073099832357287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151730874552715399888238191 227596311829073099832357287)
    ·
      refine ⟨341394467743609649748535931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227596311829073099832357287 341394467743609649748535931)
      ·
        refine ⟨512091701615414474622803897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341394467743609649748535931 512091701615414474622803897)
        ·
          refine ⟨384068776211560855967102923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512091701615414474622803897 384068776211560855967102923)
          ·
            refine ⟨576103164317341283950654385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384068776211560855967102923 576103164317341283950654385)
            ·
              refine ⟨432077373238005962962990789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576103164317341283950654385 432077373238005962962990789)
              ·
                refine ⟨81014507482126118055560773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432077373238005962962990789 81014507482126118055560773)
                ·
                  refine ⟨15190220152898647135417645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81014507482126118055560773 15190220152898647135417645)
                  ·
                    refine ⟨5696332557336992675781617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15190220152898647135417645 5696332557336992675781617)
                    ·
                      refine ⟨4272249418002744506836213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696332557336992675781617 4272249418002744506836213)
                      ·
                        rfl

theorem cell23_8320176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 3, 2].length) (baseStart_8320176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320176 prefixEnd_8320176 := by exact prefixLift 8320176
  have htrace : WordTrace (prefixWord ++ tailWord_8320176) baseStart_8320176 baseEnd_8320176 := by
    simpa [prefixWord, tailWord_8320176, baseEnd_8320176] using wordTrace_append hprefix tailTrace_8320176
  have hstable : (prefixWord ++ tailWord_8320176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320176).length < 2 ^ (prefixWord ++ tailWord_8320176).sum := by decide
  have hdescent : baseEnd_8320176 < baseStart_8320176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320199 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 1, 6]
def baseStart_8320199 : Nat := 118140960795 + 8320199 * 2 ^ 59
def prefixEnd_8320199 : Nat := 4983230072969 + 3 ^ 40 * 8320199 * 2
def baseEnd_8320199 : Nat := 1424087076019265972282869

theorem tailTrace_8320199 : CollatzResearch.WordTrace tailWord_8320199 prefixEnd_8320199 1424087076019265972282869 := by
  unfold tailWord_8320199
  simp only [CollatzResearch.WordTrace]
  refine ⟨303462587984347474704563651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202308391989564983136375767 303462587984347474704563651)
  ·
    refine ⟨455193881976521212056845477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303462587984347474704563651 455193881976521212056845477)
    ·
      refine ⟨85348852870597727260658527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455193881976521212056845477 85348852870597727260658527)
      ·
        refine ⟨128023279305896590890987791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85348852870597727260658527 128023279305896590890987791)
        ·
          refine ⟨192034918958844886336481687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128023279305896590890987791 192034918958844886336481687)
          ·
            refine ⟨288052378438267329504722531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192034918958844886336481687 288052378438267329504722531)
            ·
              refine ⟨432078567657400994257083797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288052378438267329504722531 432078567657400994257083797)
              ·
                refine ⟨20253682858940671605800803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432078567657400994257083797 20253682858940671605800803)
                ·
                  refine ⟨30380524288411007408701205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20253682858940671605800803 30380524288411007408701205)
                  ·
                    refine ⟨1424087076019265972282869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30380524288411007408701205 1424087076019265972282869)
                    ·
                      rfl

theorem cell23_8320199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_8320199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320199 prefixEnd_8320199 := by exact prefixLift 8320199
  have htrace : WordTrace (prefixWord ++ tailWord_8320199) baseStart_8320199 baseEnd_8320199 := by
    simpa [prefixWord, tailWord_8320199, baseEnd_8320199] using wordTrace_append hprefix tailTrace_8320199
  have hstable : (prefixWord ++ tailWord_8320199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320199).length < 2 ^ (prefixWord ++ tailWord_8320199).sum := by decide
  have hdescent : baseEnd_8320199 < baseStart_8320199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320200 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_8320200 : Nat := 118140960795 + 8320200 * 2 ^ 59
def prefixEnd_8320200 : Nat := 4983230072969 + 3 ^ 40 * 8320200 * 2
def baseEnd_8320200 : Nat := 4272261741538452412936103

theorem tailTrace_8320200 : CollatzResearch.WordTrace tailWord_8320200 prefixEnd_8320200 4272261741538452412936103 := by
  unfold tailWord_8320200
  simp only [CollatzResearch.WordTrace]
  refine ⟨151731312228671925937675027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202308416304895901250233369 151731312228671925937675027)
  ·
    refine ⟨227596968343007888906512541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151731312228671925937675027 227596968343007888906512541)
    ·
      refine ⟨85348863128627958339942203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227596968343007888906512541 85348863128627958339942203)
      ·
        refine ⟨128023294692941937509913305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85348863128627958339942203 128023294692941937509913305)
        ·
          refine ⟨96017471019706453132434979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128023294692941937509913305 96017471019706453132434979)
          ·
            refine ⟨144026206529559679698652469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96017471019706453132434979 144026206529559679698652469)
            ·
              refine ⟨13502456862146219971748669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144026206529559679698652469 13502456862146219971748669)
              ·
                refine ⟨5063421323304832489405751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13502456862146219971748669 5063421323304832489405751)
                ·
                  refine ⟨7595131984957248734108627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063421323304832489405751 7595131984957248734108627)
                  ·
                    refine ⟨11392697977435873101162941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7595131984957248734108627 11392697977435873101162941)
                    ·
                      refine ⟨4272261741538452412936103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392697977435873101162941 4272261741538452412936103)
                      ·
                        rfl

theorem cell23_8320200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_8320200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320200 prefixEnd_8320200 := by exact prefixLift 8320200
  have htrace : WordTrace (prefixWord ++ tailWord_8320200) baseStart_8320200 baseEnd_8320200 := by
    simpa [prefixWord, tailWord_8320200, baseEnd_8320200] using wordTrace_append hprefix tailTrace_8320200
  have hstable : (prefixWord ++ tailWord_8320200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320200).length < 2 ^ (prefixWord ++ tailWord_8320200).sum := by decide
  have hdescent : baseEnd_8320200 < baseStart_8320200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320243 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 3]
def baseStart_8320243 : Nat := 118140960795 + 8320243 * 2 ^ 59
def prefixEnd_8320243 : Nat := 4983230072969 + 3 ^ 40 * 8320243 * 2
def baseEnd_8320243 : Nat := 4272283821206595744698405

theorem tailTrace_8320243 : CollatzResearch.WordTrace tailWord_8320243 prefixEnd_8320243 4272283821206595744698405 := by
  unfold tailWord_8320243
  simp only [CollatzResearch.WordTrace]
  refine ⟨303464192796188070219165383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202309461864125380146110255 303464192796188070219165383)
  ·
    refine ⟨455196289194282105328748075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303464192796188070219165383 455196289194282105328748075)
    ·
      refine ⟨682794433791423157993122113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455196289194282105328748075 682794433791423157993122113)
      ·
        refine ⟨512095825343567368494841585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682794433791423157993122113 512095825343567368494841585)
        ·
          refine ⟨384071869007675526371131189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512095825343567368494841585 384071869007675526371131189)
          ·
            refine ⟨36006737719469580597293549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384071869007675526371131189 36006737719469580597293549)
            ·
              refine ⟨13502526644801092723985081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36006737719469580597293549 13502526644801092723985081)
              ·
                refine ⟨10126894983600819542988811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502526644801092723985081 10126894983600819542988811)
                ·
                  refine ⟨15190342475401229314483217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126894983600819542988811 15190342475401229314483217)
                  ·
                    refine ⟨11392756856550921985862413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15190342475401229314483217 11392756856550921985862413)
                    ·
                      refine ⟨4272283821206595744698405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392756856550921985862413 4272283821206595744698405)
                      ·
                        rfl

theorem cell23_8320243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_8320243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320243 prefixEnd_8320243 := by exact prefixLift 8320243
  have htrace : WordTrace (prefixWord ++ tailWord_8320243) baseStart_8320243 baseEnd_8320243 := by
    simpa [prefixWord, tailWord_8320243, baseEnd_8320243] using wordTrace_append hprefix tailTrace_8320243
  have hstable : (prefixWord ++ tailWord_8320243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320243).length < 2 ^ (prefixWord ++ tailWord_8320243).sum := by decide
  have hdescent : baseEnd_8320243 < baseStart_8320243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320290 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_8320290 : Nat := 118140960795 + 8320290 * 2 ^ 59
def prefixEnd_8320290 : Nat := 4983230072969 + 3 ^ 40 * 8320290 * 2
def baseEnd_8320290 : Nat := 4272307954797357060810689

theorem tailTrace_8320290 : CollatzResearch.WordTrace tailWord_8320290 prefixEnd_8320290 4272307954797357060810689 := by
  unfold tailWord_8320290
  simp only [CollatzResearch.WordTrace]
  refine ⟨75866476756754449311531581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202310604684678531497417549 75866476756754449311531581)
  ·
    refine ⟨28449928783782918491824343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75866476756754449311531581 28449928783782918491824343)
    ·
      refine ⟨42674893175674377737736515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449928783782918491824343 42674893175674377737736515)
      ·
        refine ⟨64012339763511566606604773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42674893175674377737736515 64012339763511566606604773)
        ·
          refine ⟨12002313705658418738738395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64012339763511566606604773 12002313705658418738738395)
          ·
            refine ⟨18003470558487628108107593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12002313705658418738738395 18003470558487628108107593)
            ·
              refine ⟨13502602918865721081080695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18003470558487628108107593 13502602918865721081080695)
              ·
                refine ⟨20253904378298581621621043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13502602918865721081080695 20253904378298581621621043)
                ·
                  refine ⟨30380856567447872432431565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20253904378298581621621043 30380856567447872432431565)
                  ·
                    refine ⟨11392821212792952162161837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30380856567447872432431565 11392821212792952162161837)
                    ·
                      refine ⟨4272307954797357060810689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392821212792952162161837 4272307954797357060810689)
                      ·
                        rfl

theorem cell23_8320290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_8320290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320290 prefixEnd_8320290 := by exact prefixLift 8320290
  have htrace : WordTrace (prefixWord ++ tailWord_8320290) baseStart_8320290 baseEnd_8320290 := by
    simpa [prefixWord, tailWord_8320290, baseEnd_8320290] using wordTrace_append hprefix tailTrace_8320290
  have hstable : (prefixWord ++ tailWord_8320290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320290).length < 2 ^ (prefixWord ++ tailWord_8320290).sum := by decide
  have hdescent : baseEnd_8320290 < baseStart_8320290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320299 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_8320299 : Nat := 118140960795 + 8320299 * 2 ^ 59
def prefixEnd_8320299 : Nat := 4983230072969 + 3 ^ 40 * 8320299 * 2
def baseEnd_8320299 : Nat := 4272312576123247525598147

theorem tailTrace_8320299 : CollatzResearch.WordTrace tailWord_8320299 prefixEnd_8320299 4272312576123247525598147 := by
  unfold tailWord_8320299
  simp only [CollatzResearch.WordTrace]
  refine ⟨303466235283985191783203951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202310823522656794522135967 303466235283985191783203951)
  ·
    refine ⟨455199352925977787674805927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303466235283985191783203951 455199352925977787674805927)
    ·
      refine ⟨682799029388966681512208891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455199352925977787674805927 682799029388966681512208891)
      ·
        refine ⟨1024198544083450022268313337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682799029388966681512208891 1024198544083450022268313337)
        ·
          refine ⟨768148908062587516701235003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024198544083450022268313337 768148908062587516701235003)
          ·
            refine ⟨1152223362093881275051852505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768148908062587516701235003 1152223362093881275051852505)
            ·
              refine ⟨864167521570410956288889379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152223362093881275051852505 864167521570410956288889379)
              ·
                refine ⟨1296251282355616434433334069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864167521570410956288889379 1296251282355616434433334069)
                ·
                  refine ⟨121523557720839040728125069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1296251282355616434433334069 121523557720839040728125069)
                  ·
                    refine ⟨45571334145314640273046901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121523557720839040728125069 45571334145314640273046901)
                    ·
                      refine ⟨4272312576123247525598147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45571334145314640273046901 4272312576123247525598147)
                      ·
                        rfl

theorem cell23_8320299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_8320299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320299 prefixEnd_8320299 := by exact prefixLift 8320299
  have htrace : WordTrace (prefixWord ++ tailWord_8320299) baseStart_8320299 baseEnd_8320299 := by
    simpa [prefixWord, tailWord_8320299, baseEnd_8320299] using wordTrace_append hprefix tailTrace_8320299
  have hstable : (prefixWord ++ tailWord_8320299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320299).length < 2 ^ (prefixWord ++ tailWord_8320299).sum := by decide
  have hdescent : baseEnd_8320299 < baseStart_8320299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320324 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_8320324 : Nat := 118140960795 + 8320324 * 2 ^ 59
def prefixEnd_8320324 : Nat := 4983230072969 + 3 ^ 40 * 8320324 * 2
def baseEnd_8320324 : Nat := 4272325413139609927785533

theorem tailTrace_8320324 : CollatzResearch.WordTrace tailWord_8320324 prefixEnd_8320324 4272325413139609927785533 := by
  unfold tailWord_8320324
  simp only [CollatzResearch.WordTrace]
  refine ⟨151733573554447310526432013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202311431405929747368576017 151733573554447310526432013)
  ·
    refine ⟨56900090082917741447412005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151733573554447310526432013 56900090082917741447412005)
    ·
      refine ⟨10668766890547076521389751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56900090082917741447412005 10668766890547076521389751)
      ·
        refine ⟨16003150335820614782084627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668766890547076521389751 16003150335820614782084627)
        ·
          refine ⟨24004725503730922173126941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16003150335820614782084627 24004725503730922173126941)
          ·
            refine ⟨9001772063899095814922603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24004725503730922173126941 9001772063899095814922603)
            ·
              refine ⟨13502658095848643722383905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001772063899095814922603 13502658095848643722383905)
              ·
                refine ⟨10126993571886482791787929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502658095848643722383905 10126993571886482791787929)
                ·
                  refine ⟨7595245178914862093840947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10126993571886482791787929 7595245178914862093840947)
                  ·
                    refine ⟨11392867768372293140761421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7595245178914862093840947 11392867768372293140761421)
                    ·
                      refine ⟨4272325413139609927785533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11392867768372293140761421 4272325413139609927785533)
                      ·
                        rfl

theorem cell23_8320324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_8320324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320324 prefixEnd_8320324 := by exact prefixLift 8320324
  have htrace : WordTrace (prefixWord ++ tailWord_8320324) baseStart_8320324 baseEnd_8320324 := by
    simpa [prefixWord, tailWord_8320324, baseEnd_8320324] using wordTrace_append hprefix tailTrace_8320324
  have hstable : (prefixWord ++ tailWord_8320324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320324).length < 2 ^ (prefixWord ++ tailWord_8320324).sum := by decide
  have hdescent : baseEnd_8320324 < baseStart_8320324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320336 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 7]
def baseStart_8320336 : Nat := 118140960795 + 8320336 * 2 ^ 59
def prefixEnd_8320336 : Nat := 4983230072969 + 3 ^ 40 * 8320336 * 2
def baseEnd_8320336 : Nat := 474703508323051542315053

theorem tailTrace_8320336 : CollatzResearch.WordTrace tailWord_8320336 prefixEnd_8320336 474703508323051542315053 := by
  unfold tailWord_8320336
  simp only [CollatzResearch.WordTrace]
  refine ⟨151733792392425573551150431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202311723189900764734867241 151733792392425573551150431)
  ·
    refine ⟨227600688588638360326725647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151733792392425573551150431 227600688588638360326725647)
    ·
      refine ⟨341401032882957540490088471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227600688588638360326725647 341401032882957540490088471)
      ·
        refine ⟨512101549324436310735132707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341401032882957540490088471 512101549324436310735132707)
        ·
          refine ⟨768152323986654466102699061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512101549324436310735132707 768152323986654466102699061)
          ·
            refine ⟨72014280373748856197128037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 768152323986654466102699061 72014280373748856197128037)
            ·
              refine ⟨13502677570077910536961507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72014280373748856197128037 13502677570077910536961507)
              ·
                refine ⟨20254016355116865805442261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13502677570077910536961507 20254016355116865805442261)
                ·
                  refine ⟨474703508323051542315053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20254016355116865805442261 474703508323051542315053)
                  ·
                    rfl

theorem cell23_8320336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_8320336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320336 prefixEnd_8320336 := by exact prefixLift 8320336
  have htrace : WordTrace (prefixWord ++ tailWord_8320336) baseStart_8320336 baseEnd_8320336 := by
    simpa [prefixWord, tailWord_8320336, baseEnd_8320336] using wordTrace_append hprefix tailTrace_8320336
  have hstable : (prefixWord ++ tailWord_8320336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320336).length < 2 ^ (prefixWord ++ tailWord_8320336).sum := by decide
  have hdescent : baseEnd_8320336 < baseStart_8320336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320393 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_8320393 : Nat := 118140960795 + 8320393 * 2 ^ 59
def prefixEnd_8320393 : Nat := 4983230072969 + 3 ^ 40 * 8320393 * 2
def baseEnd_8320393 : Nat := 4272360843304770157822715

theorem tailTrace_8320393 : CollatzResearch.WordTrace tailWord_8320393 prefixEnd_8320393 4272360843304770157822715 := by
  unfold tailWord_8320393
  simp only [CollatzResearch.WordTrace]
  refine ⟨303469663745644645837125833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202313109163763097224750555 303469663745644645837125833)
  ·
    refine ⟨227602247809233484377844375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303469663745644645837125833 227602247809233484377844375)
    ·
      refine ⟨341403371713850226566766563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227602247809233484377844375 341403371713850226566766563)
      ·
        refine ⟨512105057570775339850149845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341403371713850226566766563 512105057570775339850149845)
        ·
          refine ⟨12002462286815047027737887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 512105057570775339850149845 12002462286815047027737887)
          ·
            refine ⟨18003693430222570541606831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12002462286815047027737887 18003693430222570541606831)
            ·
              refine ⟨27005540145333855812410247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18003693430222570541606831 27005540145333855812410247)
              ·
                refine ⟨40508310218000783718615371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27005540145333855812410247 40508310218000783718615371)
                ·
                  refine ⟨60762465327001175577923057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40508310218000783718615371 60762465327001175577923057)
                  ·
                    refine ⟨45571848995250881683442293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60762465327001175577923057 45571848995250881683442293)
                    ·
                      refine ⟨4272360843304770157822715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45571848995250881683442293 4272360843304770157822715)
                      ·
                        rfl

theorem cell23_8320393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_8320393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320393 prefixEnd_8320393 := by exact prefixLift 8320393
  have htrace : WordTrace (prefixWord ++ tailWord_8320393) baseStart_8320393 baseEnd_8320393 := by
    simpa [prefixWord, tailWord_8320393, baseEnd_8320393] using wordTrace_append hprefix tailTrace_8320393
  have hstable : (prefixWord ++ tailWord_8320393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320393).length < 2 ^ (prefixWord ++ tailWord_8320393).sum := by decide
  have hdescent : baseEnd_8320393 < baseStart_8320393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320398 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_8320398 : Nat := 118140960795 + 8320398 * 2 ^ 59
def prefixEnd_8320398 : Nat := 4983230072969 + 3 ^ 40 * 8320398 * 2
def baseEnd_8320398 : Nat := 4272363410708042638260193

theorem tailTrace_8320398 : CollatzResearch.WordTrace tailWord_8320398 prefixEnd_8320398 4272363410708042638260193 := by
  unfold tailWord_8320398
  simp only [CollatzResearch.WordTrace]
  refine ⟨37933730763828316461382231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202313230740417687794038565 37933730763828316461382231)
  ·
    refine ⟨56900596145742474692073347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37933730763828316461382231 56900596145742474692073347)
    ·
      refine ⟨85350894218613712038110021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56900596145742474692073347 85350894218613712038110021)
      ·
        refine ⟨16003292665990071007145629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85350894218613712038110021 16003292665990071007145629)
        ·
          refine ⟨6001234749746276627679611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16003292665990071007145629 6001234749746276627679611)
          ·
            refine ⟨9001852124619414941519417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001234749746276627679611 9001852124619414941519417)
            ·
              refine ⟨6751389093464561206139563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9001852124619414941519417 6751389093464561206139563)
              ·
                refine ⟨10127083640196841809209345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751389093464561206139563 10127083640196841809209345)
                ·
                  refine ⟨7595312730147631356907009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127083640196841809209345 7595312730147631356907009)
                  ·
                    refine ⟨5696484547610723517680257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7595312730147631356907009 5696484547610723517680257)
                    ·
                      refine ⟨4272363410708042638260193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696484547610723517680257 4272363410708042638260193)
                      ·
                        rfl

theorem cell23_8320398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_8320398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320398 prefixEnd_8320398 := by exact prefixLift 8320398
  have htrace : WordTrace (prefixWord ++ tailWord_8320398) baseStart_8320398 baseEnd_8320398 := by
    simpa [prefixWord, tailWord_8320398, baseEnd_8320398] using wordTrace_append hprefix tailTrace_8320398
  have hstable : (prefixWord ++ tailWord_8320398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320398).length < 2 ^ (prefixWord ++ tailWord_8320398).sum := by decide
  have hdescent : baseEnd_8320398 < baseStart_8320398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320473 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_8320473 : Nat := 118140960795 + 8320473 * 2 ^ 59
def prefixEnd_8320473 : Nat := 4983230072969 + 3 ^ 40 * 8320473 * 2
def baseEnd_8320473 : Nat := 1424133973919043281607449

theorem tailTrace_8320473 : CollatzResearch.WordTrace tailWord_8320473 prefixEnd_8320473 1424133973919043281607449 := by
  unfold tailWord_8320473
  simp only [CollatzResearch.WordTrace]
  refine ⟨303472581585354819500038073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202315054390236546333358715 303472581585354819500038073)
  ·
    refine ⟨227604436189016114625028555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303472581585354819500038073 227604436189016114625028555)
    ·
      refine ⟨341406654283524171937542833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227604436189016114625028555 341406654283524171937542833)
      ·
        refine ⟨256054990712643128953157125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341406654283524171937542833 256054990712643128953157125)
        ·
          refine ⟨48010310758620586678716961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256054990712643128953157125 48010310758620586678716961)
          ·
            refine ⟨36007733068965440009037721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48010310758620586678716961 36007733068965440009037721)
            ·
              refine ⟨27005799801724080006778291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36007733068965440009037721 27005799801724080006778291)
              ·
                refine ⟨40508699702586120010167437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27005799801724080006778291 40508699702586120010167437)
                ·
                  refine ⟨15190762388469795003812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40508699702586120010167437 15190762388469795003812789)
                  ·
                    refine ⟨1424133973919043281607449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15190762388469795003812789 1424133973919043281607449)
                    ·
                      rfl

theorem cell23_8320473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_8320473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320473 prefixEnd_8320473 := by exact prefixLift 8320473
  have htrace : WordTrace (prefixWord ++ tailWord_8320473) baseStart_8320473 baseEnd_8320473 := by
    simpa [prefixWord, tailWord_8320473, baseEnd_8320473] using wordTrace_append hprefix tailTrace_8320473
  have hstable : (prefixWord ++ tailWord_8320473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320473).length < 2 ^ (prefixWord ++ tailWord_8320473).sum := by decide
  have hdescent : baseEnd_8320473 < baseStart_8320473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320480 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 2, 3, 2]
def baseStart_8320480 : Nat := 118140960795 + 8320480 * 2 ^ 59
def prefixEnd_8320480 : Nat := 4983230072969 + 3 ^ 40 * 8320480 * 2
def baseEnd_8320480 : Nat := 4272405516121711317434815

theorem tailTrace_8320480 : CollatzResearch.WordTrace tailWord_8320480 prefixEnd_8320480 4272405516121711317434815 := by
  unfold tailWord_8320480
  simp only [CollatzResearch.WordTrace]
  refine ⟨151736418448164729847771447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202315224597552973130361929 151736418448164729847771447)
  ·
    refine ⟨227604627672247094771657171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151736418448164729847771447 227604627672247094771657171)
    ·
      refine ⟨341406941508370642157485757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227604627672247094771657171 341406941508370642157485757)
      ·
        refine ⟨128027603065638990809057159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341406941508370642157485757 128027603065638990809057159)
        ·
          refine ⟨192041404598458486213585739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128027603065638990809057159 192041404598458486213585739)
          ·
            refine ⟨288062106897687729320378609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192041404598458486213585739 288062106897687729320378609)
            ·
              refine ⟨216046580173265796990283957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288062106897687729320378609 216046580173265796990283957)
              ·
                refine ⟨20254366891243668467839121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216046580173265796990283957 20254366891243668467839121)
                ·
                  refine ⟨15190775168432751350879341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20254366891243668467839121 15190775168432751350879341)
                  ·
                    refine ⟨5696540688162281756579753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15190775168432751350879341 5696540688162281756579753)
                    ·
                      refine ⟨4272405516121711317434815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696540688162281756579753 4272405516121711317434815)
                      ·
                        rfl

theorem cell23_8320480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_8320480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320480 prefixEnd_8320480 := by exact prefixLift 8320480
  have htrace : WordTrace (prefixWord ++ tailWord_8320480) baseStart_8320480 baseEnd_8320480 := by
    simpa [prefixWord, tailWord_8320480, baseEnd_8320480] using wordTrace_append hprefix tailTrace_8320480
  have hstable : (prefixWord ++ tailWord_8320480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320480).length < 2 ^ (prefixWord ++ tailWord_8320480).sum := by decide
  have hdescent : baseEnd_8320480 < baseStart_8320480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320520 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 2, 4]
def baseStart_8320520 : Nat := 118140960795 + 8320520 * 2 ^ 59
def prefixEnd_8320520 : Nat := 4983230072969 + 3 ^ 40 * 8320520 * 2
def baseEnd_8320520 : Nat := 1424142018449297053644877

theorem tailTrace_8320520 : CollatzResearch.WordTrace tailWord_8320520 prefixEnd_8320520 1424142018449297053644877 := by
  unfold tailWord_8320520
  simp only [CollatzResearch.WordTrace]
  refine ⟨151737147908092273263499507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202316197210789697684666009 151737147908092273263499507)
  ·
    refine ⟨227605721862138409895249261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151737147908092273263499507 227605721862138409895249261)
    ·
      refine ⟨85352145698301903710718473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227605721862138409895249261 85352145698301903710718473)
      ·
        refine ⟨64014109273726427783038855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85352145698301903710718473 64014109273726427783038855)
        ·
          refine ⟨96021163910589641674558283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64014109273726427783038855 96021163910589641674558283)
          ·
            refine ⟨144031745865884462511837425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96021163910589641674558283 144031745865884462511837425)
            ·
              refine ⟨108023809399413346883878069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144031745865884462511837425 108023809399413346883878069)
              ·
                refine ⟨10127232131195001270363569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108023809399413346883878069 10127232131195001270363569)
                ·
                  refine ⟨7595424098396250952772677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127232131195001270363569 7595424098396250952772677)
                  ·
                    refine ⟨1424142018449297053644877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7595424098396250952772677 1424142018449297053644877)
                    ·
                      rfl

theorem cell23_8320520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_8320520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320520 prefixEnd_8320520 := by exact prefixLift 8320520
  have htrace : WordTrace (prefixWord ++ tailWord_8320520) baseStart_8320520 baseEnd_8320520 := by
    simpa [prefixWord, tailWord_8320520, baseEnd_8320520] using wordTrace_append hprefix tailTrace_8320520
  have hstable : (prefixWord ++ tailWord_8320520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320520).length < 2 ^ (prefixWord ++ tailWord_8320520).sum := by decide
  have hdescent : baseEnd_8320520 < baseStart_8320520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320533 : List Nat := [1, 3, 2, 1, 3, 3, 1, 9]
def baseStart_8320533 : Nat := 118140960795 + 8320533 * 2 ^ 59
def prefixEnd_8320533 : Nat := 4983230072969 + 3 ^ 40 * 8320533 * 2
def baseEnd_8320533 : Nat := 158238249281348133706373

theorem tailTrace_8320533 : CollatzResearch.WordTrace tailWord_8320533 prefixEnd_8320533 158238249281348133706373 := by
  unfold tailWord_8320533
  simp only [CollatzResearch.WordTrace]
  refine ⟨303474769965137449747222253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202316513310091633164814835 303474769965137449747222253)
  ·
    refine ⟨113803038736926543655208345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303474769965137449747222253 113803038736926543655208345)
    ·
      refine ⟨85352279052694907741406259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113803038736926543655208345 85352279052694907741406259)
      ·
        refine ⟨128028418579042361612109389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85352279052694907741406259 128028418579042361612109389)
        ·
          refine ⟨48010656967140885604541021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128028418579042361612109389 48010656967140885604541021)
          ·
            refine ⟨18003996362677832101702883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48010656967140885604541021 18003996362677832101702883)
            ·
              refine ⟨27005994544016748152554325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18003996362677832101702883 27005994544016748152554325)
              ·
                refine ⟨158238249281348133706373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27005994544016748152554325 158238249281348133706373)
                ·
                  rfl

theorem cell23_8320533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 9].length) (baseStart_8320533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320533 prefixEnd_8320533 := by exact prefixLift 8320533
  have htrace : WordTrace (prefixWord ++ tailWord_8320533) baseStart_8320533 baseEnd_8320533 := by
    simpa [prefixWord, tailWord_8320533, baseEnd_8320533] using wordTrace_append hprefix tailTrace_8320533
  have hstable : (prefixWord ++ tailWord_8320533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320533).length < 2 ^ (prefixWord ++ tailWord_8320533).sum := by decide
  have hdescent : baseEnd_8320533 < baseStart_8320533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320598 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_8320598 : Nat := 118140960795 + 8320598 * 2 ^ 59
def prefixEnd_8320598 : Nat := 4983230072969 + 3 ^ 40 * 8320598 * 2
def baseEnd_8320598 : Nat := 4272466106838941855759273

theorem tailTrace_8320598 : CollatzResearch.WordTrace tailWord_8320598 prefixEnd_8320598 4272466106838941855759273 := by
  unfold tailWord_8320598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18967321294368872865521153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202318093806601310565558965 18967321294368872865521153)
  ·
    refine ⟨14225490970776654649140865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18967321294368872865521153 14225490970776654649140865)
    ·
      refine ⟨10669118228082490986855649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14225490970776654649140865 10669118228082490986855649)
      ·
        refine ⟨8001838671061868240141737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10669118228082490986855649 8001838671061868240141737)
        ·
          refine ⟨6001379003296401180106303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8001838671061868240141737 6001379003296401180106303)
          ·
            refine ⟨9002068504944601770159455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001379003296401180106303 9002068504944601770159455)
            ·
              refine ⟨13503102757416902655239183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9002068504944601770159455 13503102757416902655239183)
              ·
                refine ⟨20254654136125353982858775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13503102757416902655239183 20254654136125353982858775)
                ·
                  refine ⟨30381981204188030974288163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20254654136125353982858775 30381981204188030974288163)
                  ·
                    refine ⟨45572971806282046461432245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30381981204188030974288163 45572971806282046461432245)
                    ·
                      refine ⟨4272466106838941855759273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45572971806282046461432245 4272466106838941855759273)
                      ·
                        rfl

theorem cell23_8320598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_8320598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320598 prefixEnd_8320598 := by exact prefixLift 8320598
  have htrace : WordTrace (prefixWord ++ tailWord_8320598) baseStart_8320598 baseEnd_8320598 := by
    simpa [prefixWord, tailWord_8320598, baseEnd_8320598] using wordTrace_append hprefix tailTrace_8320598
  have hstable : (prefixWord ++ tailWord_8320598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320598).length < 2 ^ (prefixWord ++ tailWord_8320598).sum := by decide
  have hdescent : baseEnd_8320598 < baseStart_8320598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320617 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 4, 2, 2]
def baseStart_8320617 : Nat := 118140960795 + 8320617 * 2 ^ 59
def prefixEnd_8320617 : Nat := 4983230072969 + 3 ^ 40 * 8320617 * 2
def baseEnd_8320617 : Nat := 4272475862971377281421685

theorem tailTrace_8320617 : CollatzResearch.WordTrace tailWord_8320617 prefixEnd_8320617 4272475862971377281421685 := by
  unfold tailWord_8320617
  simp only [CollatzResearch.WordTrace]
  refine ⟨303477833696833132093280105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202318555797888754728853403 303477833696833132093280105)
  ·
    refine ⟨227608375272624849069960079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303477833696833132093280105 227608375272624849069960079)
    ·
      refine ⟨341412562908937273604940119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227608375272624849069960079 341412562908937273604940119)
      ·
        refine ⟨512118844363405910407410179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341412562908937273604940119 512118844363405910407410179)
        ·
          refine ⟨768178266545108865611115269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512118844363405910407410179 768178266545108865611115269)
          ·
            refine ⟨144033424977207912302084113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 768178266545108865611115269 144033424977207912302084113)
            ·
              refine ⟨108025068732905934226563085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144033424977207912302084113 108025068732905934226563085)
              ·
                refine ⟨40509400774839725334961157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108025068732905934226563085 40509400774839725334961157)
                ·
                  refine ⟨7595512645282448500305217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40509400774839725334961157 7595512645282448500305217)
                  ·
                    refine ⟨5696634483961836375228913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7595512645282448500305217 5696634483961836375228913)
                    ·
                      refine ⟨4272475862971377281421685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696634483961836375228913 4272475862971377281421685)
                      ·
                        rfl

theorem cell23_8320617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 2, 2].length) (baseStart_8320617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320617 prefixEnd_8320617 := by exact prefixLift 8320617
  have htrace : WordTrace (prefixWord ++ tailWord_8320617) baseStart_8320617 baseEnd_8320617 := by
    simpa [prefixWord, tailWord_8320617, baseEnd_8320617] using wordTrace_append hprefix tailTrace_8320617
  have hstable : (prefixWord ++ tailWord_8320617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320617).length < 2 ^ (prefixWord ++ tailWord_8320617).sum := by decide
  have hdescent : baseEnd_8320617 < baseStart_8320617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320623 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 7]
def baseStart_8320623 : Nat := 118140960795 + 8320623 * 2 ^ 59
def prefixEnd_8320623 : Nat := 4983230072969 + 3 ^ 40 * 8320623 * 2
def baseEnd_8320623 : Nat := 474719882650589361994073

theorem tailTrace_8320623 : CollatzResearch.WordTrace tailWord_8320623 prefixEnd_8320623 474719882650589361994073 := by
  unfold tailWord_8320623
  simp only [CollatzResearch.WordTrace]
  refine ⟨303478052534811395117998523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202318701689874263411999015 303478052534811395117998523)
  ·
    refine ⟨455217078802217092676997785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303478052534811395117998523 455217078802217092676997785)
    ·
      refine ⟨341412809101662819507748339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455217078802217092676997785 341412809101662819507748339)
      ·
        refine ⟨512119213652494229261622509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341412809101662819507748339 512119213652494229261622509)
        ·
          refine ⟨192044705119685335973108441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512119213652494229261622509 192044705119685335973108441)
          ·
            refine ⟨144033528839764001979831331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192044705119685335973108441 144033528839764001979831331)
            ·
              refine ⟨216050293259646002969746997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144033528839764001979831331 216050293259646002969746997)
              ·
                refine ⟨20254714993091812778413781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216050293259646002969746997 20254714993091812778413781)
                ·
                  refine ⟨474719882650589361994073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20254714993091812778413781 474719882650589361994073)
                  ·
                    rfl

theorem cell23_8320623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 7].length) (baseStart_8320623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320623 prefixEnd_8320623 := by exact prefixLift 8320623
  have htrace : WordTrace (prefixWord ++ tailWord_8320623) baseStart_8320623 baseEnd_8320623 := by
    simpa [prefixWord, tailWord_8320623, baseEnd_8320623] using wordTrace_append hprefix tailTrace_8320623
  have hstable : (prefixWord ++ tailWord_8320623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320623).length < 2 ^ (prefixWord ++ tailWord_8320623).sum := by decide
  have hdescent : baseEnd_8320623 < baseStart_8320623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320668 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_8320668 : Nat := 118140960795 + 8320668 * 2 ^ 59
def prefixEnd_8320668 : Nat := 4983230072969 + 3 ^ 40 * 8320668 * 2
def baseEnd_8320668 : Nat := 4272502050484756581883951

theorem tailTrace_8320668 : CollatzResearch.WordTrace tailWord_8320668 prefixEnd_8320668 4272502050484756581883951 := by
  unfold tailWord_8320668
  simp only [CollatzResearch.WordTrace]
  refine ⟨151739846909824183901693329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202319795879765578535591105 151739846909824183901693329)
  ·
    refine ⟨113804885182368137926269997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151739846909824183901693329 113804885182368137926269997)
    ·
      refine ⟨42676831943388051722351249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113804885182368137926269997 42676831943388051722351249)
      ·
        refine ⟨32007623957541038791763437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42676831943388051722351249 32007623957541038791763437)
        ·
          refine ⟨12002858984077889546911289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32007623957541038791763437 12002858984077889546911289)
          ·
            refine ⟨9002144238058417160183467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12002858984077889546911289 9002144238058417160183467)
            ·
              refine ⟨13503216357087625740275201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9002144238058417160183467 13503216357087625740275201)
              ·
                refine ⟨10127412267815719305206401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13503216357087625740275201 10127412267815719305206401)
                ·
                  refine ⟨7595559200861789478904801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127412267815719305206401 7595559200861789478904801)
                  ·
                    refine ⟨5696669400646342109178601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7595559200861789478904801 5696669400646342109178601)
                    ·
                      refine ⟨4272502050484756581883951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696669400646342109178601 4272502050484756581883951)
                      ·
                        rfl

theorem cell23_8320668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_8320668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320668 prefixEnd_8320668 := by exact prefixLift 8320668
  have htrace : WordTrace (prefixWord ++ tailWord_8320668) baseStart_8320668 baseEnd_8320668 := by
    simpa [prefixWord, tailWord_8320668, baseEnd_8320668] using wordTrace_append hprefix tailTrace_8320668
  have hstable : (prefixWord ++ tailWord_8320668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320668).length < 2 ^ (prefixWord ++ tailWord_8320668).sum := by decide
  have hdescent : baseEnd_8320668 < baseStart_8320668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320674 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_8320674 : Nat := 118140960795 + 8320674 * 2 ^ 59
def prefixEnd_8320674 : Nat := 4983230072969 + 3 ^ 40 * 8320674 * 2
def baseEnd_8320674 : Nat := 474722792374298173156547

theorem tailTrace_8320674 : CollatzResearch.WordTrace tailWord_8320674 prefixEnd_8320674 474722792374298173156547 := by
  unfold tailWord_8320674
  simp only [CollatzResearch.WordTrace]
  refine ⟨75869978164406657707026269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202319941771751087218736717 75869978164406657707026269)
  ·
    refine ⟨28451241811652496640134851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75869978164406657707026269 28451241811652496640134851)
    ·
      refine ⟨42676862717478744960202277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28451241811652496640134851 42676862717478744960202277)
      ·
        refine ⟨8001911759527264680037927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42676862717478744960202277 8001911759527264680037927)
        ·
          refine ⟨12002867639290897020056891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001911759527264680037927 12002867639290897020056891)
          ·
            refine ⟨18004301458936345530085337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12002867639290897020056891 18004301458936345530085337)
            ·
              refine ⟨13503226094202259147564003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18004301458936345530085337 13503226094202259147564003)
              ·
                refine ⟨20254839141303388721346005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13503226094202259147564003 20254839141303388721346005)
                ·
                  refine ⟨474722792374298173156547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20254839141303388721346005 474722792374298173156547)
                  ·
                    rfl

theorem cell23_8320674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_8320674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320674 prefixEnd_8320674 := by exact prefixLift 8320674
  have htrace : WordTrace (prefixWord ++ tailWord_8320674) baseStart_8320674 baseEnd_8320674 := by
    simpa [prefixWord, tailWord_8320674, baseEnd_8320674] using wordTrace_append hprefix tailTrace_8320674
  have hstable : (prefixWord ++ tailWord_8320674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320674).length < 2 ^ (prefixWord ++ tailWord_8320674).sum := by decide
  have hdescent : baseEnd_8320674 < baseStart_8320674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320690 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_8320690 : Nat := 118140960795 + 8320690 * 2 ^ 59
def prefixEnd_8320690 : Nat := 4983230072969 + 3 ^ 40 * 8320690 * 2
def baseEnd_8320690 : Nat := 4272513347059155495808849

theorem tailTrace_8320690 : CollatzResearch.WordTrace tailWord_8320690 prefixEnd_8320690 4272513347059155495808849 := by
  unfold tailWord_8320690
  simp only [CollatzResearch.WordTrace]
  refine ⟨75870124056392166390171881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202320330817045777040458349 75870124056392166390171881)
  ·
    refine ⟨56902593042294124792628911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75870124056392166390171881 56902593042294124792628911)
    ·
      refine ⟨85353889563441187188943367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56902593042294124792628911 85353889563441187188943367)
      ·
        refine ⟨128030834345161780783415051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85353889563441187188943367 128030834345161780783415051)
        ·
          refine ⟨192046251517742671175122577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128030834345161780783415051 192046251517742671175122577)
          ·
            refine ⟨144034688638307003381341933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192046251517742671175122577 144034688638307003381341933)
            ·
              refine ⟨54013008239365126268003225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144034688638307003381341933 54013008239365126268003225)
              ·
                refine ⟨40509756179523844701002419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54013008239365126268003225 40509756179523844701002419)
                ·
                  refine ⟨60764634269285767051503629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40509756179523844701002419 60764634269285767051503629)
                  ·
                    refine ⟨22786737850982162644313861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60764634269285767051503629 22786737850982162644313861)
                    ·
                      refine ⟨4272513347059155495808849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22786737850982162644313861 4272513347059155495808849)
                      ·
                        rfl

theorem cell23_8320690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_8320690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320690 prefixEnd_8320690 := by exact prefixLift 8320690
  have htrace : WordTrace (prefixWord ++ tailWord_8320690) baseStart_8320690 baseEnd_8320690 := by
    simpa [prefixWord, tailWord_8320690, baseEnd_8320690] using wordTrace_append hprefix tailTrace_8320690
  have hstable : (prefixWord ++ tailWord_8320690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320690).length < 2 ^ (prefixWord ++ tailWord_8320690).sum := by decide
  have hdescent : baseEnd_8320690 < baseStart_8320690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320724 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_8320724 : Nat := 118140960795 + 8320724 * 2 ^ 59
def prefixEnd_8320724 : Nat := 4983230072969 + 3 ^ 40 * 8320724 * 2
def baseEnd_8320724 : Nat := 4272530805401408362783693

theorem tailTrace_8320724 : CollatzResearch.WordTrace tailWord_8320724 prefixEnd_8320724 4272530805401408362783693 := by
  unfold tailWord_8320724
  simp only [CollatzResearch.WordTrace]
  refine ⟨151740868153722744683712613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202321157538296992911616817 151740868153722744683712613)
  ·
    refine ⟨28451412778823014628196115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151740868153722744683712613 28451412778823014628196115)
    ·
      refine ⟨42677119168234521942294173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28451412778823014628196115 42677119168234521942294173)
      ·
        refine ⟨16003919688087945728360315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42677119168234521942294173 16003919688087945728360315)
        ·
          refine ⟨24005879532131918592540473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16003919688087945728360315 24005879532131918592540473)
          ·
            refine ⟨18004409649098938944405355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24005879532131918592540473 18004409649098938944405355)
            ·
              refine ⟨27006614473648408416608033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18004409649098938944405355 27006614473648408416608033)
              ·
                refine ⟨20254960855236306312456025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27006614473648408416608033 20254960855236306312456025)
                ·
                  refine ⟨15191220641427229734342019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20254960855236306312456025 15191220641427229734342019)
                  ·
                    refine ⟨22786830962140844601513029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15191220641427229734342019 22786830962140844601513029)
                    ·
                      refine ⟨4272530805401408362783693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22786830962140844601513029 4272530805401408362783693)
                      ·
                        rfl

theorem cell23_8320724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_8320724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320724 prefixEnd_8320724 := by exact prefixLift 8320724
  have htrace : WordTrace (prefixWord ++ tailWord_8320724) baseStart_8320724 baseEnd_8320724 := by
    simpa [prefixWord, tailWord_8320724, baseEnd_8320724] using wordTrace_append hprefix tailTrace_8320724
  have hstable : (prefixWord ++ tailWord_8320724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320724).length < 2 ^ (prefixWord ++ tailWord_8320724).sum := by decide
  have hdescent : baseEnd_8320724 < baseStart_8320724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320727 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_8320727 : Nat := 118140960795 + 8320727 * 2 ^ 59
def prefixEnd_8320727 : Nat := 4983230072969 + 3 ^ 40 * 8320727 * 2
def baseEnd_8320727 : Nat := 4272532345843371851046179

theorem tailTrace_8320727 : CollatzResearch.WordTrace tailWord_8320727 prefixEnd_8320727 4272532345843371851046179 := by
  unfold tailWord_8320727
  simp only [CollatzResearch.WordTrace]
  refine ⟨303481845726434620879784435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202321230484289747253189623 303481845726434620879784435)
  ·
    refine ⟨455222768589651931319676653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303481845726434620879784435 455222768589651931319676653)
    ·
      refine ⟨170708538221119474244878745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455222768589651931319676653 170708538221119474244878745)
      ·
        refine ⟨128031403665839605683659059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170708538221119474244878745 128031403665839605683659059)
        ·
          refine ⟨192047105498759408525488589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128031403665839605683659059 192047105498759408525488589)
          ·
            refine ⟨72017664562034778197058221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192047105498759408525488589 72017664562034778197058221)
            ·
              refine ⟨27006624210763041823896833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72017664562034778197058221 27006624210763041823896833)
              ·
                refine ⟨20254968158072281367922625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27006624210763041823896833 20254968158072281367922625)
                ·
                  refine ⟨15191226118554211025941969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20254968158072281367922625 15191226118554211025941969)
                  ·
                    refine ⟨11393419588915658269456477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15191226118554211025941969 11393419588915658269456477)
                    ·
                      refine ⟨4272532345843371851046179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11393419588915658269456477 4272532345843371851046179)
                      ·
                        rfl

theorem cell23_8320727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_8320727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320727 prefixEnd_8320727 := by exact prefixLift 8320727
  have htrace : WordTrace (prefixWord ++ tailWord_8320727) baseStart_8320727 baseEnd_8320727 := by
    simpa [prefixWord, tailWord_8320727, baseEnd_8320727] using wordTrace_append hprefix tailTrace_8320727
  have hstable : (prefixWord ++ tailWord_8320727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320727).length < 2 ^ (prefixWord ++ tailWord_8320727).sum := by decide
  have hdescent : baseEnd_8320727 < baseStart_8320727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320730 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_8320730 : Nat := 118140960795 + 8320730 * 2 ^ 59
def prefixEnd_8320730 : Nat := 4983230072969 + 3 ^ 40 * 8320730 * 2
def baseEnd_8320730 : Nat := 474725987365037259923185

theorem tailTrace_8320730 : CollatzResearch.WordTrace tailWord_8320730 prefixEnd_8320730 474725987365037259923185 := by
  unfold tailWord_8320730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75870488786355938098035911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202321303430282501594762429 75870488786355938098035911)
  ·
    refine ⟨113805733179533907147053867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75870488786355938098035911 113805733179533907147053867)
    ·
      refine ⟨170708599769300860720580801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113805733179533907147053867 170708599769300860720580801)
      ·
        refine ⟨128031449826975645540435601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170708599769300860720580801 128031449826975645540435601)
        ·
          refine ⟨96023587370231734155326701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128031449826975645540435601 96023587370231734155326701)
          ·
            refine ⟨36008845263836900308247513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96023587370231734155326701 36008845263836900308247513)
            ·
              refine ⟨27006633947877675231185635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36008845263836900308247513 27006633947877675231185635)
              ·
                refine ⟨40509950921816512846778453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27006633947877675231185635 40509950921816512846778453)
                ·
                  refine ⟨474725987365037259923185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40509950921816512846778453 474725987365037259923185)
                  ·
                    rfl

theorem cell23_8320730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_8320730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320730 prefixEnd_8320730 := by exact prefixLift 8320730
  have htrace : WordTrace (prefixWord ++ tailWord_8320730) baseStart_8320730 baseEnd_8320730 := by
    simpa [prefixWord, tailWord_8320730, baseEnd_8320730] using wordTrace_append hprefix tailTrace_8320730
  have hstable : (prefixWord ++ tailWord_8320730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320730).length < 2 ^ (prefixWord ++ tailWord_8320730).sum := by decide
  have hdescent : baseEnd_8320730 < baseStart_8320730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320747 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 6]
def baseStart_8320747 : Nat := 118140960795 + 8320747 * 2 ^ 59
def prefixEnd_8320747 : Nat := 4983230072969 + 3 ^ 40 * 8320747 * 2
def baseEnd_8320747 : Nat := 474726957272940196977343

theorem tailTrace_8320747 : CollatzResearch.WordTrace tailWord_8320747 prefixEnd_8320747 474726957272940196977343 := by
  unfold tailWord_8320747
  simp only [CollatzResearch.WordTrace]
  refine ⟨303482575186362164295512495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202321716790908109530341663 303482575186362164295512495)
  ·
    refine ⟨455223862779543246443268743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303482575186362164295512495 455223862779543246443268743)
    ·
      refine ⟨682835794169314869664903115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455223862779543246443268743 682835794169314869664903115)
      ·
        refine ⟨1024253691253972304497354673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682835794169314869664903115 1024253691253972304497354673)
        ·
          refine ⟨768190268440479228373016005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024253691253972304497354673 768190268440479228373016005)
          ·
            refine ⟨144035675332589855319940501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 768190268440479228373016005 144035675332589855319940501)
            ·
              refine ⟨6751672281215149468122211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144035675332589855319940501 6751672281215149468122211)
              ·
                refine ⟨10127508421822724202183317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751672281215149468122211 10127508421822724202183317)
                ·
                  refine ⟨474726957272940196977343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10127508421822724202183317 474726957272940196977343)
                  ·
                    rfl

theorem cell23_8320747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 6].length) (baseStart_8320747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320747 prefixEnd_8320747 := by exact prefixLift 8320747
  have htrace : WordTrace (prefixWord ++ tailWord_8320747) baseStart_8320747 baseEnd_8320747 := by
    simpa [prefixWord, tailWord_8320747, baseEnd_8320747] using wordTrace_append hprefix tailTrace_8320747
  have hstable : (prefixWord ++ tailWord_8320747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320747).length < 2 ^ (prefixWord ++ tailWord_8320747).sum := by decide
  have hdescent : baseEnd_8320747 < baseStart_8320747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320767 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 1, 5, 2]
def baseStart_8320767 : Nat := 118140960795 + 8320767 * 2 ^ 59
def prefixEnd_8320767 : Nat := 4983230072969 + 3 ^ 40 * 8320767 * 2
def baseEnd_8320767 : Nat := 4272552885069551694545995

theorem tailTrace_8320767 : CollatzResearch.WordTrace tailWord_8320767 prefixEnd_8320767 4272552885069551694545995 := by
  unfold tailWord_8320767
  simp only [CollatzResearch.WordTrace]
  refine ⟨303483304646289707711240555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202322203097526471807493703 303483304646289707711240555)
  ·
    refine ⟨455224956969434561566860833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303483304646289707711240555 455224956969434561566860833)
    ·
      refine ⟨341418717727075921175145625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455224956969434561566860833 341418717727075921175145625)
      ·
        refine ⟨256064038295306940881359219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341418717727075921175145625 256064038295306940881359219)
        ·
          refine ⟨384096057442960411322038829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256064038295306940881359219 384096057442960411322038829)
          ·
            refine ⟨144036021541110154245764561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384096057442960411322038829 144036021541110154245764561)
            ·
              refine ⟨108027016155832615684323421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144036021541110154245764561 108027016155832615684323421)
              ·
                refine ⟨40510131058437230881621283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108027016155832615684323421 40510131058437230881621283)
                ·
                  refine ⟨60765196587655846322431925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40510131058437230881621283 60765196587655846322431925)
                  ·
                    refine ⟨5696737180092735592727993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60765196587655846322431925 5696737180092735592727993)
                    ·
                      refine ⟨4272552885069551694545995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5696737180092735592727993 4272552885069551694545995)
                      ·
                        rfl

theorem cell23_8320767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_8320767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320767 prefixEnd_8320767 := by exact prefixLift 8320767
  have htrace : WordTrace (prefixWord ++ tailWord_8320767) baseStart_8320767 baseEnd_8320767 := by
    simpa [prefixWord, tailWord_8320767, baseEnd_8320767] using wordTrace_append hprefix tailTrace_8320767
  have hstable : (prefixWord ++ tailWord_8320767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320767).length < 2 ^ (prefixWord ++ tailWord_8320767).sum := by decide
  have hdescent : baseEnd_8320767 < baseStart_8320767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320825 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 1, 1, 3]
def baseStart_8320825 : Nat := 118140960795 + 8320825 * 2 ^ 59
def prefixEnd_8320825 : Nat := 4983230072969 + 3 ^ 40 * 8320825 * 2
def baseEnd_8320825 : Nat := 4272582666947512467620729

theorem tailTrace_8320825 : CollatzResearch.WordTrace tailWord_8320825 prefixEnd_8320825 4272582666947512467620729 := by
  unfold tailWord_8320825
  simp only [CollatzResearch.WordTrace]
  refine ⟨303485420080079583616851929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202323613386719722411234619 303485420080079583616851929)
  ·
    refine ⟨227614065060059687712638947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303485420080079583616851929 227614065060059687712638947)
    ·
      refine ⟨341421097590089531568958421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227614065060059687712638947 341421097590089531568958421)
      ·
        refine ⟨8002056974767723396147463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 341421097590089531568958421 8002056974767723396147463)
        ·
          refine ⟨12003085462151585094221195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002056974767723396147463 12003085462151585094221195)
          ·
            refine ⟨18004628193227377641331793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12003085462151585094221195 18004628193227377641331793)
            ·
              refine ⟨13503471144920533230998845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18004628193227377641331793 13503471144920533230998845)
              ·
                refine ⟨5063801679345199961624567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13503471144920533230998845 5063801679345199961624567)
                ·
                  refine ⟨7595702519017799942436851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063801679345199961624567 7595702519017799942436851)
                  ·
                    refine ⟨11393553778526699913655277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7595702519017799942436851 11393553778526699913655277)
                    ·
                      refine ⟨4272582666947512467620729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11393553778526699913655277 4272582666947512467620729)
                      ·
                        rfl

theorem cell23_8320825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_8320825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320825 prefixEnd_8320825 := by exact prefixLift 8320825
  have htrace : WordTrace (prefixWord ++ tailWord_8320825) baseStart_8320825 baseEnd_8320825 := by
    simpa [prefixWord, tailWord_8320825, baseEnd_8320825] using wordTrace_append hprefix tailTrace_8320825
  have hstable : (prefixWord ++ tailWord_8320825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320825).length < 2 ^ (prefixWord ++ tailWord_8320825).sum := by decide
  have hdescent : baseEnd_8320825 < baseStart_8320825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320864 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_8320864 : Nat := 118140960795 + 8320864 * 2 ^ 59
def prefixEnd_8320864 : Nat := 4983230072969 + 3 ^ 40 * 8320864 * 2
def baseEnd_8320864 : Nat := 4272602692693037815033049

theorem tailTrace_8320864 : CollatzResearch.WordTrace tailWord_8320864 prefixEnd_8320864 4272602692693037815033049 := by
  unfold tailWord_8320864
  simp only [CollatzResearch.WordTrace]
  refine ⟨151743421263469146638760823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202324561684625528851681097 151743421263469146638760823)
  ·
    refine ⟨227615131895203719958141235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151743421263469146638760823 227615131895203719958141235)
    ·
      refine ⟨341422697842805579937211853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227615131895203719958141235 341422697842805579937211853)
      ·
        refine ⟨128033511691052092476454445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341422697842805579937211853 128033511691052092476454445)
        ·
          refine ⟨48012566884144534678670417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128033511691052092476454445 48012566884144534678670417)
          ·
            refine ⟨36009425163108401009002813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48012566884144534678670417 36009425163108401009002813)
            ·
              refine ⟨13503534436165650378376055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36009425163108401009002813 13503534436165650378376055)
              ·
                refine ⟨20255301654248475567564083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13503534436165650378376055 20255301654248475567564083)
                ·
                  refine ⟨30382952481372713351346125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20255301654248475567564083 30382952481372713351346125)
                  ·
                    refine ⟨11393607180514767506754797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30382952481372713351346125 11393607180514767506754797)
                    ·
                      refine ⟨4272602692693037815033049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11393607180514767506754797 4272602692693037815033049)
                      ·
                        rfl

theorem cell23_8320864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_8320864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320864 prefixEnd_8320864 := by exact prefixLift 8320864
  have htrace : WordTrace (prefixWord ++ tailWord_8320864) baseStart_8320864 baseEnd_8320864 := by
    simpa [prefixWord, tailWord_8320864, baseEnd_8320864] using wordTrace_append hprefix tailTrace_8320864
  have hstable : (prefixWord ++ tailWord_8320864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320864).length < 2 ^ (prefixWord ++ tailWord_8320864).sum := by decide
  have hdescent : baseEnd_8320864 < baseStart_8320864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320877 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_8320877 : Nat := 118140960795 + 8320877 * 2 ^ 59
def prefixEnd_8320877 : Nat := 4983230072969 + 3 ^ 40 * 8320877 * 2
def baseEnd_8320877 : Nat := 4272609367941546264170489

theorem tailTrace_8320877 : CollatzResearch.WordTrace tailWord_8320877 prefixEnd_8320877 4272609367941546264170489 := by
  unfold tailWord_8320877
  simp only [CollatzResearch.WordTrace]
  refine ⟨303487316675891196497744885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202324877783927464331829923 303487316675891196497744885)
  ·
    refine ⟨28451935938364799671663583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303487316675891196497744885 28451935938364799671663583)
    ·
      refine ⟨42677903907547199507495375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28451935938364799671663583 42677903907547199507495375)
      ·
        refine ⟨64016855861320799261243063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42677903907547199507495375 64016855861320799261243063)
        ·
          refine ⟨96025283791981198891864595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64016855861320799261243063 96025283791981198891864595)
          ·
            refine ⟨144037925687971798337796893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96025283791981198891864595 144037925687971798337796893)
            ·
              refine ⟨54014222132989424376673835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144037925687971798337796893 54014222132989424376673835)
              ·
                refine ⟨81021333199484136565010753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54014222132989424376673835 81021333199484136565010753)
                ·
                  refine ⟨60765999899613102423758065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81021333199484136565010753 60765999899613102423758065)
                  ·
                    refine ⟨45574499924709826817818549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60765999899613102423758065 45574499924709826817818549)
                    ·
                      refine ⟨4272609367941546264170489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45574499924709826817818549 4272609367941546264170489)
                      ·
                        rfl

theorem cell23_8320877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_8320877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320877 prefixEnd_8320877 := by exact prefixLift 8320877
  have htrace : WordTrace (prefixWord ++ tailWord_8320877) baseStart_8320877 baseEnd_8320877 := by
    simpa [prefixWord, tailWord_8320877, baseEnd_8320877] using wordTrace_append hprefix tailTrace_8320877
  have hstable : (prefixWord ++ tailWord_8320877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320877).length < 2 ^ (prefixWord ++ tailWord_8320877).sum := by decide
  have hdescent : baseEnd_8320877 < baseStart_8320877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320907 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 3]
def baseStart_8320907 : Nat := 118140960795 + 8320907 * 2 ^ 59
def prefixEnd_8320907 : Nat := 4983230072969 + 3 ^ 40 * 8320907 * 2
def baseEnd_8320907 : Nat := 4272624772361181146795351

theorem tailTrace_8320907 : CollatzResearch.WordTrace tailWord_8320907 prefixEnd_8320907 4272624772361181146795351 := by
  unfold tailWord_8320907
  simp only [CollatzResearch.WordTrace]
  refine ⟨303488410865782511621336975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202325607243855007747557983 303488410865782511621336975)
  ·
    refine ⟨455232616298673767432005463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303488410865782511621336975 455232616298673767432005463)
    ·
      refine ⟨682848924448010651148008195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455232616298673767432005463 682848924448010651148008195)
      ·
        refine ⟨1024273386672015976722012293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682848924448010651148008195 1024273386672015976722012293)
        ·
          refine ⟨192051260001002995635377305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1024273386672015976722012293 192051260001002995635377305)
          ·
            refine ⟨144038445000752246726532979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192051260001002995635377305 144038445000752246726532979)
            ·
              refine ⟨216057667501128370089799469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144038445000752246726532979 216057667501128370089799469)
              ·
                refine ⟨81021625312923138783674801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216057667501128370089799469 81021625312923138783674801)
                ·
                  refine ⟨60766218984692354087756101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81021625312923138783674801 60766218984692354087756101)
                  ·
                    refine ⟨11393666059629816391454269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60766218984692354087756101 11393666059629816391454269)
                    ·
                      refine ⟨4272624772361181146795351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11393666059629816391454269 4272624772361181146795351)
                      ·
                        rfl

theorem cell23_8320907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 3].length) (baseStart_8320907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320907 prefixEnd_8320907 := by exact prefixLift 8320907
  have htrace : WordTrace (prefixWord ++ tailWord_8320907) baseStart_8320907 baseEnd_8320907 := by
    simpa [prefixWord, tailWord_8320907, baseEnd_8320907] using wordTrace_append hprefix tailTrace_8320907
  have hstable : (prefixWord ++ tailWord_8320907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320907).length < 2 ^ (prefixWord ++ tailWord_8320907).sum := by decide
  have hdescent : baseEnd_8320907 < baseStart_8320907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320917 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_8320917 : Nat := 118140960795 + 8320917 * 2 ^ 59
def prefixEnd_8320917 : Nat := 4983230072969 + 3 ^ 40 * 8320917 * 2
def baseEnd_8320917 : Nat := 4272629907167726107670305

theorem tailTrace_8320917 : CollatzResearch.WordTrace tailWord_8320917 prefixEnd_8320917 4272629907167726107670305 := by
  unfold tailWord_8320917
  simp only [CollatzResearch.WordTrace]
  refine ⟨303488775595746283329201005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202325850397164188886134003 303488775595746283329201005)
  ·
    refine ⟨113808290848404856248450377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303488775595746283329201005 113808290848404856248450377)
    ·
      refine ⟨85356218136303642186337783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113808290848404856248450377 85356218136303642186337783)
      ·
        refine ⟨128034327204455463279506675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85356218136303642186337783 128034327204455463279506675)
        ·
          refine ⟨192051490806683194919260013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128034327204455463279506675 192051490806683194919260013)
          ·
            refine ⟨72019309052506198094722505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192051490806683194919260013 72019309052506198094722505)
            ·
              refine ⟨54014481789379648571041879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72019309052506198094722505 54014481789379648571041879)
              ·
                refine ⟨81021722684069472856562819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54014481789379648571041879 81021722684069472856562819)
                ·
                  refine ⟨121532584026104209284844229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81021722684069472856562819 121532584026104209284844229)
                  ·
                    refine ⟨22787359504894539240908293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121532584026104209284844229 22787359504894539240908293)
                    ·
                      refine ⟨4272629907167726107670305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22787359504894539240908293 4272629907167726107670305)
                      ·
                        rfl

theorem cell23_8320917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_8320917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320917 prefixEnd_8320917 := by exact prefixLift 8320917
  have htrace : WordTrace (prefixWord ++ tailWord_8320917) baseStart_8320917 baseEnd_8320917 := by
    simpa [prefixWord, tailWord_8320917, baseEnd_8320917] using wordTrace_append hprefix tailTrace_8320917
  have hstable : (prefixWord ++ tailWord_8320917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320917).length < 2 ^ (prefixWord ++ tailWord_8320917).sum := by decide
  have hdescent : baseEnd_8320917 < baseStart_8320917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320924 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8320924 : Nat := 118140960795 + 8320924 * 2 ^ 59
def prefixEnd_8320924 : Nat := 4983230072969 + 3 ^ 40 * 8320924 * 2
def baseEnd_8320924 : Nat := 4272633501532307580282773

theorem tailTrace_8320924 : CollatzResearch.WordTrace tailWord_8320924 prefixEnd_8320924 4272633501532307580282773 := by
  unfold tailWord_8320924
  simp only [CollatzResearch.WordTrace]
  refine ⟨151744515453360461762352913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202326020604480615683137217 151744515453360461762352913)
  ·
    refine ⟨113808386590020346321764685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151744515453360461762352913 113808386590020346321764685)
    ·
      refine ⟨42678144971257629870661757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113808386590020346321764685 42678144971257629870661757)
      ·
        refine ⟨16004304364221611201498159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42678144971257629870661757 16004304364221611201498159)
        ·
          refine ⟨24006456546332416802247239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16004304364221611201498159 24006456546332416802247239)
          ·
            refine ⟨36009684819498625203370859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24006456546332416802247239 36009684819498625203370859)
            ·
              refine ⟨54014527229247937805056289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36009684819498625203370859 54014527229247937805056289)
              ·
                refine ⟨40510895421935953353792217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54014527229247937805056289 40510895421935953353792217)
                ·
                  refine ⟨30383171566451965015344163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40510895421935953353792217 30383171566451965015344163)
                  ·
                    refine ⟨45574757349677947523016245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30383171566451965015344163 45574757349677947523016245)
                    ·
                      refine ⟨4272633501532307580282773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45574757349677947523016245 4272633501532307580282773)
                      ·
                        rfl

theorem cell23_8320924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8320924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320924 prefixEnd_8320924 := by exact prefixLift 8320924
  have htrace : WordTrace (prefixWord ++ tailWord_8320924) baseStart_8320924 baseEnd_8320924 := by
    simpa [prefixWord, tailWord_8320924, baseEnd_8320924] using wordTrace_append hprefix tailTrace_8320924
  have hstable : (prefixWord ++ tailWord_8320924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320924).length < 2 ^ (prefixWord ++ tailWord_8320924).sum := by decide
  have hdescent : baseEnd_8320924 < baseStart_8320924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320937 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_8320937 : Nat := 118140960795 + 8320937 * 2 ^ 59
def prefixEnd_8320937 : Nat := 4983230072969 + 3 ^ 40 * 8320937 * 2
def baseEnd_8320937 : Nat := 4272640176780816029420213

theorem tailTrace_8320937 : CollatzResearch.WordTrace tailWord_8320937 prefixEnd_8320937 4272640176780816029420213 := by
  unfold tailWord_8320937
  simp only [CollatzResearch.WordTrace]
  refine ⟨303489505055673826744929065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202326336703782551163286043 303489505055673826744929065)
  ·
    refine ⟨227617128791755370058696799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303489505055673826744929065 227617128791755370058696799)
    ·
      refine ⟨341425693187633055088045199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227617128791755370058696799 341425693187633055088045199)
      ·
        refine ⟨512138539781449582632067799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341425693187633055088045199 512138539781449582632067799)
        ·
          refine ⟨768207809672174373948101699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512138539781449582632067799 768207809672174373948101699)
          ·
            refine ⟨1152311714508261560922152549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768207809672174373948101699 1152311714508261560922152549)
            ·
              refine ⟨216058446470299042672903603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1152311714508261560922152549 216058446470299042672903603)
              ·
                refine ⟨324087669705448564009355405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216058446470299042672903603 324087669705448564009355405)
                ·
                  refine ⟨121532876139543211503508277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324087669705448564009355405 121532876139543211503508277)
                  ·
                    refine ⟨11393707138082176078453901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121532876139543211503508277 11393707138082176078453901)
                    ·
                      refine ⟨4272640176780816029420213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11393707138082176078453901 4272640176780816029420213)
                      ·
                        rfl

theorem cell23_8320937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_8320937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320937 prefixEnd_8320937 := by exact prefixLift 8320937
  have htrace : WordTrace (prefixWord ++ tailWord_8320937) baseStart_8320937 baseEnd_8320937 := by
    simpa [prefixWord, tailWord_8320937, baseEnd_8320937] using wordTrace_append hprefix tailTrace_8320937
  have hstable : (prefixWord ++ tailWord_8320937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320937).length < 2 ^ (prefixWord ++ tailWord_8320937).sum := by decide
  have hdescent : baseEnd_8320937 < baseStart_8320937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8320991 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 2, 5]
def baseStart_8320991 : Nat := 118140960795 + 8320991 * 2 ^ 59
def prefixEnd_8320991 : Nat := 4983230072969 + 3 ^ 40 * 8320991 * 2
def baseEnd_8320991 : Nat := 1424222634912052939381655

theorem tailTrace_8320991 : CollatzResearch.WordTrace tailWord_8320991 prefixEnd_8320991 1424222634912052939381655 := by
  unfold tailWord_8320991
  simp only [CollatzResearch.WordTrace]
  refine ⟨303491474597478193967394827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202327649731652129311596551 303491474597478193967394827)
  ·
    refine ⟨455237211896217290951092241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303491474597478193967394827 455237211896217290951092241)
    ·
      refine ⟨341427908922162968213319181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455237211896217290951092241 341427908922162968213319181)
      ·
        refine ⟨128035465845811113079994693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341427908922162968213319181 128035465845811113079994693)
        ·
          refine ⟨24006649846089583702499005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128035465845811113079994693 24006649846089583702499005)
          ·
            refine ⟨9002493692283593888437127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24006649846089583702499005 9002493692283593888437127)
            ·
              refine ⟨13503740538425390832655691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9002493692283593888437127 13503740538425390832655691)
              ·
                refine ⟨20255610807638086248983537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13503740538425390832655691 20255610807638086248983537)
                ·
                  refine ⟨15191708105728564686737653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20255610807638086248983537 15191708105728564686737653)
                  ·
                    refine ⟨1424222634912052939381655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15191708105728564686737653 1424222634912052939381655)
                    ·
                      rfl

theorem cell23_8320991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_8320991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8320991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8320991 prefixEnd_8320991 := by exact prefixLift 8320991
  have htrace : WordTrace (prefixWord ++ tailWord_8320991) baseStart_8320991 baseEnd_8320991 := by
    simpa [prefixWord, tailWord_8320991, baseEnd_8320991] using wordTrace_append hprefix tailTrace_8320991
  have hstable : (prefixWord ++ tailWord_8320991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8320991).length < 2 ^ (prefixWord ++ tailWord_8320991).sum := by decide
  have hdescent : baseEnd_8320991 < baseStart_8320991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8320991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321007 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_8321007 : Nat := 118140960795 + 8321007 * 2 ^ 59
def prefixEnd_8321007 : Nat := 4983230072969 + 3 ^ 40 * 8321007 * 2
def baseEnd_8321007 : Nat := 4272676120426630755544891

theorem tailTrace_8321007 : CollatzResearch.WordTrace tailWord_8321007 prefixEnd_8321007 4272676120426630755544891 := by
  unfold tailWord_8321007
  simp only [CollatzResearch.WordTrace]
  refine ⟨303492058165420228699977275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202328038776946819133318183 303492058165420228699977275)
  ·
    refine ⟨455238087248130343049965913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303492058165420228699977275 455238087248130343049965913)
    ·
      refine ⟨341428565436097757287474435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455238087248130343049965913 341428565436097757287474435)
      ·
        refine ⟨512142848154146635931211653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341428565436097757287474435 512142848154146635931211653)
        ·
          refine ⟨96026784028902494237102185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512142848154146635931211653 96026784028902494237102185)
          ·
            refine ⟨72020088021676870677826639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96026784028902494237102185 72020088021676870677826639)
            ·
              refine ⟨108030132032515306016739959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72020088021676870677826639 108030132032515306016739959)
              ·
                refine ⟨162045198048772959025109939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108030132032515306016739959 162045198048772959025109939)
                ·
                  refine ⟨243067797073159438537664909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162045198048772959025109939 243067797073159438537664909)
                  ·
                    refine ⟨91150423902434789451624341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243067797073159438537664909 91150423902434789451624341)
                    ·
                      refine ⟨4272676120426630755544891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91150423902434789451624341 4272676120426630755544891)
                      ·
                        rfl

theorem cell23_8321007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_8321007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321007 prefixEnd_8321007 := by exact prefixLift 8321007
  have htrace : WordTrace (prefixWord ++ tailWord_8321007) baseStart_8321007 baseEnd_8321007 := by
    simpa [prefixWord, tailWord_8321007, baseEnd_8321007] using wordTrace_append hprefix tailTrace_8321007
  have hstable : (prefixWord ++ tailWord_8321007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321007).length < 2 ^ (prefixWord ++ tailWord_8321007).sum := by decide
  have hdescent : baseEnd_8321007 < baseStart_8321007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321172 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_8321172 : Nat := 118140960795 + 8321172 * 2 ^ 59
def prefixEnd_8321172 : Nat := 4983230072969 + 3 ^ 40 * 8321172 * 2
def baseEnd_8321172 : Nat := 4272760844734622609981633

theorem tailTrace_8321172 : CollatzResearch.WordTrace tailWord_8321172 prefixEnd_8321172 4272760844734622609981633 := by
  unfold tailWord_8321172
  simp only [CollatzResearch.WordTrace]
  refine ⟨151749038104911230939866885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202332050806548307919822513 151749038104911230939866885)
  ·
    refine ⟨28452944644670855801225041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151749038104911230939866885 28452944644670855801225041)
    ·
      refine ⟨21339708483503141850918781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28452944644670855801225041 21339708483503141850918781)
      ·
        refine ⟨8002390681313678194094543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21339708483503141850918781 8002390681313678194094543)
        ·
          refine ⟨12003586021970517291141815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002390681313678194094543 12003586021970517291141815)
          ·
            refine ⟨18005379032955775936712723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12003586021970517291141815 18005379032955775936712723)
            ·
              refine ⟨27008068549433663905069085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18005379032955775936712723 27008068549433663905069085)
              ·
                refine ⟨10128025706037623964400907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27008068549433663905069085 10128025706037623964400907)
                ·
                  refine ⟨15192038559056435946601361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10128025706037623964400907 15192038559056435946601361)
                  ·
                    refine ⟨11394028919292326959951021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15192038559056435946601361 11394028919292326959951021)
                    ·
                      refine ⟨4272760844734622609981633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394028919292326959951021 4272760844734622609981633)
                      ·
                        rfl

theorem cell23_8321172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_8321172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321172 prefixEnd_8321172 := by exact prefixLift 8321172
  have htrace : WordTrace (prefixWord ++ tailWord_8321172) baseStart_8321172 baseEnd_8321172 := by
    simpa [prefixWord, tailWord_8321172, baseEnd_8321172] using wordTrace_append hprefix tailTrace_8321172
  have hstable : (prefixWord ++ tailWord_8321172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321172).length < 2 ^ (prefixWord ++ tailWord_8321172).sum := by decide
  have hdescent : baseEnd_8321172 < baseStart_8321172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321185 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_8321185 : Nat := 118140960795 + 8321185 * 2 ^ 59
def prefixEnd_8321185 : Nat := 4983230072969 + 3 ^ 40 * 8321185 * 2
def baseEnd_8321185 : Nat := 4272767519983131059119073

theorem tailTrace_8321185 : CollatzResearch.WordTrace tailWord_8321185 prefixEnd_8321185 4272767519983131059119073 := by
  unfold tailWord_8321185
  simp only [CollatzResearch.WordTrace]
  refine ⟨303498550358775365099957009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202332366905850243399971339 303498550358775365099957009)
  ·
    refine ⟨227623912769081523824967757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303498550358775365099957009 227623912769081523824967757)
    ·
      refine ⟨85358967288405571434362909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227623912769081523824967757 85358967288405571434362909)
      ·
        refine ⟨32009612733152089287886091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85358967288405571434362909 32009612733152089287886091)
        ·
          refine ⟨48014419099728133931829137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32009612733152089287886091 48014419099728133931829137)
          ·
            refine ⟨36010814324796100448871853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48014419099728133931829137 36010814324796100448871853)
            ·
              refine ⟨13504055371798537668326945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36010814324796100448871853 13504055371798537668326945)
              ·
                refine ⟨10128041528848903251245209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13504055371798537668326945 10128041528848903251245209)
                ·
                  refine ⟨7596031146636677438433907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128041528848903251245209 7596031146636677438433907)
                  ·
                    refine ⟨11394046719955016157650861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596031146636677438433907 11394046719955016157650861)
                    ·
                      refine ⟨4272767519983131059119073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394046719955016157650861 4272767519983131059119073)
                      ·
                        rfl

theorem cell23_8321185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_8321185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321185 prefixEnd_8321185 := by exact prefixLift 8321185
  have htrace : WordTrace (prefixWord ++ tailWord_8321185) baseStart_8321185 baseEnd_8321185 := by
    simpa [prefixWord, tailWord_8321185, baseEnd_8321185] using wordTrace_append hprefix tailTrace_8321185
  have hstable : (prefixWord ++ tailWord_8321185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321185).length < 2 ^ (prefixWord ++ tailWord_8321185).sum := by decide
  have hdescent : baseEnd_8321185 < baseStart_8321185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321212 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_8321212 : Nat := 118140960795 + 8321212 * 2 ^ 59
def prefixEnd_8321212 : Nat := 4983230072969 + 3 ^ 40 * 8321212 * 2
def baseEnd_8321212 : Nat := 4272781383960802453481449

theorem tailTrace_8321212 : CollatzResearch.WordTrace tailWord_8321212 prefixEnd_8321212 4272781383960802453481449 := by
  unfold tailWord_8321212
  simp only [CollatzResearch.WordTrace]
  refine ⟨151749767564838774355594945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202333023419785032474126593 151749767564838774355594945)
  ·
    refine ⟨113812325673629080766696209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151749767564838774355594945 113812325673629080766696209)
    ·
      refine ⟨85359244255221810575022157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113812325673629080766696209 85359244255221810575022157)
      ·
        refine ⟨32009716595708178965633309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85359244255221810575022157 32009716595708178965633309)
        ·
          refine ⟨12003643723390567112112491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32009716595708178965633309 12003643723390567112112491)
          ·
            refine ⟨18005465585085850668168737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12003643723390567112112491 18005465585085850668168737)
            ·
              refine ⟨13504099188814388001126553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18005465585085850668168737 13504099188814388001126553)
              ·
                refine ⟨10128074391610791000844915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13504099188814388001126553 10128074391610791000844915)
                ·
                  refine ⟨15192111587416186501267373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10128074391610791000844915 15192111587416186501267373)
                  ·
                    refine ⟨5697041845281069937975265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15192111587416186501267373 5697041845281069937975265)
                    ·
                      refine ⟨4272781383960802453481449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697041845281069937975265 4272781383960802453481449)
                      ·
                        rfl

theorem cell23_8321212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_8321212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321212 prefixEnd_8321212 := by exact prefixLift 8321212
  have htrace : WordTrace (prefixWord ++ tailWord_8321212) baseStart_8321212 baseEnd_8321212 := by
    simpa [prefixWord, tailWord_8321212, baseEnd_8321212] using wordTrace_append hprefix tailTrace_8321212
  have hstable : (prefixWord ++ tailWord_8321212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321212).length < 2 ^ (prefixWord ++ tailWord_8321212).sum := by decide
  have hdescent : baseEnd_8321212 < baseStart_8321212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321241 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_8321241 : Nat := 118140960795 + 8321241 * 2 ^ 59
def prefixEnd_8321241 : Nat := 4983230072969 + 3 ^ 40 * 8321241 * 2
def baseEnd_8321241 : Nat := 4272796274899782840018815

theorem tailTrace_8321241 : CollatzResearch.WordTrace tailWord_8321241 prefixEnd_8321241 4272796274899782840018815 := by
  unfold tailWord_8321241
  simp only [CollatzResearch.WordTrace]
  refine ⟨303500592846572486663995577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202333728564381657775997051 303500592846572486663995577)
  ·
    refine ⟨227625444634929364997996683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303500592846572486663995577 227625444634929364997996683)
    ·
      refine ⟨341438166952394047496995025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227625444634929364997996683 341438166952394047496995025)
      ·
        refine ⟨256078625214295535622746269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341438166952394047496995025 256078625214295535622746269)
        ·
          refine ⟨96029484455360825858529851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256078625214295535622746269 96029484455360825858529851)
          ·
            refine ⟨144044226683041238787794777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96029484455360825858529851 144044226683041238787794777)
            ·
              refine ⟨108033170012280929090846083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144044226683041238787794777 108033170012280929090846083)
              ·
                refine ⟨162049755018421393636269125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108033170012280929090846083 162049755018421393636269125)
                ·
                  refine ⟨30384329065954011306800461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162049755018421393636269125 30384329065954011306800461)
                  ·
                    refine ⟨11394123399732754240050173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30384329065954011306800461 11394123399732754240050173)
                    ·
                      refine ⟨4272796274899782840018815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394123399732754240050173 4272796274899782840018815)
                      ·
                        rfl

theorem cell23_8321241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_8321241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321241 prefixEnd_8321241 := by exact prefixLift 8321241
  have htrace : WordTrace (prefixWord ++ tailWord_8321241) baseStart_8321241 baseEnd_8321241 := by
    simpa [prefixWord, tailWord_8321241, baseEnd_8321241] using wordTrace_append hprefix tailTrace_8321241
  have hstable : (prefixWord ++ tailWord_8321241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321241).length < 2 ^ (prefixWord ++ tailWord_8321241).sum := by decide
  have hdescent : baseEnd_8321241 < baseStart_8321241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321308 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_8321308 : Nat := 118140960795 + 8321308 * 2 ^ 59
def prefixEnd_8321308 : Nat := 4983230072969 + 3 ^ 40 * 8321308 * 2
def baseEnd_8321308 : Nat := 1424276892701211359293669

theorem tailTrace_8321308 : CollatzResearch.WordTrace tailWord_8321308 prefixEnd_8321308 1424276892701211359293669 := by
  unfold tailWord_8321308
  simp only [CollatzResearch.WordTrace]
  refine ⟨151751518268664878553342289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202335357691553171404456385 151751518268664878553342289)
  ·
    refine ⟨113813638701498658915006717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151751518268664878553342289 113813638701498658915006717)
    ·
      refine ⟨42680114513061997093127519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113813638701498658915006717 42680114513061997093127519)
      ·
        refine ⟨64020171769592995639691279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42680114513061997093127519 64020171769592995639691279)
        ·
          refine ⟨96030257654389493459536919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64020171769592995639691279 96030257654389493459536919)
          ·
            refine ⟨144045386481584240189305379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96030257654389493459536919 144045386481584240189305379)
            ·
              refine ⟨216068079722376360283958069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144045386481584240189305379 216068079722376360283958069)
              ·
                refine ⟨20256382473972783776621069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216068079722376360283958069 20256382473972783776621069)
                ·
                  refine ⟨7596143427739793916232901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20256382473972783776621069 7596143427739793916232901)
                  ·
                    refine ⟨1424276892701211359293669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596143427739793916232901 1424276892701211359293669)
                    ·
                      rfl

theorem cell23_8321308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_8321308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321308 prefixEnd_8321308 := by exact prefixLift 8321308
  have htrace : WordTrace (prefixWord ++ tailWord_8321308) baseStart_8321308 baseEnd_8321308 := by
    simpa [prefixWord, tailWord_8321308, baseEnd_8321308] using wordTrace_append hprefix tailTrace_8321308
  have hstable : (prefixWord ++ tailWord_8321308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321308).length < 2 ^ (prefixWord ++ tailWord_8321308).sum := by decide
  have hdescent : baseEnd_8321308 < baseStart_8321308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321332 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_8321332 : Nat := 118140960795 + 8321332 * 2 ^ 59
def prefixEnd_8321332 : Nat := 4983230072969 + 3 ^ 40 * 8321332 * 2
def baseEnd_8321332 : Nat := 4272843001639341983980897

theorem tailTrace_8321332 : CollatzResearch.WordTrace tailWord_8321332 prefixEnd_8321332 4272843001639341983980897 := by
  unfold tailWord_8321332
  simp only [CollatzResearch.WordTrace]
  refine ⟨151751955944621404602779125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202335941259495206137038833 151751955944621404602779125)
  ·
    refine ⟨14226745869808256681510543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151751955944621404602779125 14226745869808256681510543)
    ·
      refine ⟨21340118804712385022265815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14226745869808256681510543 21340118804712385022265815)
      ·
        refine ⟨32010178207068577533398723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21340118804712385022265815 32010178207068577533398723)
        ·
          refine ⟨48015267310602866300098085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32010178207068577533398723 48015267310602866300098085)
          ·
            refine ⟨9002862620738037431268391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48015267310602866300098085 9002862620738037431268391)
            ·
              refine ⟨13504293931107056146902587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9002862620738037431268391 13504293931107056146902587)
              ·
                refine ⟨20256440896660584220353881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13504293931107056146902587 20256440896660584220353881)
                ·
                  refine ⟨15192330672495438165265411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20256440896660584220353881 15192330672495438165265411)
                  ·
                    refine ⟨22788496008743157247898117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15192330672495438165265411 22788496008743157247898117)
                    ·
                      refine ⟨4272843001639341983980897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22788496008743157247898117 4272843001639341983980897)
                      ·
                        rfl

theorem cell23_8321332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_8321332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321332 prefixEnd_8321332 := by exact prefixLift 8321332
  have htrace : WordTrace (prefixWord ++ tailWord_8321332) baseStart_8321332 baseEnd_8321332 := by
    simpa [prefixWord, tailWord_8321332, baseEnd_8321332] using wordTrace_append hprefix tailTrace_8321332
  have hstable : (prefixWord ++ tailWord_8321332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321332).length < 2 ^ (prefixWord ++ tailWord_8321332).sum := by decide
  have hdescent : baseEnd_8321332 < baseStart_8321332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321342 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_8321342 : Nat := 118140960795 + 8321342 * 2 ^ 59
def prefixEnd_8321342 : Nat := 4983230072969 + 3 ^ 40 * 8321342 * 2
def baseEnd_8321342 : Nat := 1424282712148628981618617

theorem tailTrace_8321342 : CollatzResearch.WordTrace tailWord_8321342 prefixEnd_8321342 1424282712148628981618617 := by
  unfold tailWord_8321342
  simp only [CollatzResearch.WordTrace]
  refine ⟨37938034577400822614177785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202336184412804387275614853 37938034577400822614177785)
  ·
    refine ⟨28453525933050616960633339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37938034577400822614177785 28453525933050616960633339)
    ·
      refine ⟨42680288899575925440950009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28453525933050616960633339 42680288899575925440950009)
      ·
        refine ⟨32010216674681944080712507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42680288899575925440950009 32010216674681944080712507)
        ·
          refine ⟨48015325012022916121068761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32010216674681944080712507 48015325012022916121068761)
          ·
            refine ⟨36011493759017187090801571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48015325012022916121068761 36011493759017187090801571)
            ·
              refine ⟨54017240638525780636202357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36011493759017187090801571 54017240638525780636202357)
              ·
                refine ⟨5064116309861791934643971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54017240638525780636202357 5064116309861791934643971)
                ·
                  refine ⟨7596174464792687901965957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064116309861791934643971 7596174464792687901965957)
                  ·
                    refine ⟨1424282712148628981618617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596174464792687901965957 1424282712148628981618617)
                    ·
                      rfl

theorem cell23_8321342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_8321342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321342 prefixEnd_8321342 := by exact prefixLift 8321342
  have htrace : WordTrace (prefixWord ++ tailWord_8321342) baseStart_8321342 baseEnd_8321342 := by
    simpa [prefixWord, tailWord_8321342, baseEnd_8321342] using wordTrace_append hprefix tailTrace_8321342
  have hstable : (prefixWord ++ tailWord_8321342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321342).length < 2 ^ (prefixWord ++ tailWord_8321342).sum := by decide
  have hdescent : baseEnd_8321342 < baseStart_8321342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321405 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_8321405 : Nat := 118140960795 + 8321405 * 2 ^ 59
def prefixEnd_8321405 : Nat := 4983230072969 + 3 ^ 40 * 8321405 * 2
def baseEnd_8321405 : Nat := 4272880485727120198368061

theorem tailTrace_8321405 : CollatzResearch.WordTrace tailWord_8321405 prefixEnd_8321405 4272880485727120198368061 := by
  unfold tailWord_8321405
  simp only [CollatzResearch.WordTrace]
  refine ⟨303506574417978342672965669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202337716278652228448643779 303506574417978342672965669)
  ·
    refine ⟨56907482703370939251181063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303506574417978342672965669 56907482703370939251181063)
    ·
      refine ⟨85361224055056408876771595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56907482703370939251181063 85361224055056408876771595)
      ·
        refine ⟨128041836082584613315157393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85361224055056408876771595 128041836082584613315157393)
        ·
          refine ⟨96031377061938459986368045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128041836082584613315157393 96031377061938459986368045)
          ·
            refine ⟨36011766398226922494888017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96031377061938459986368045 36011766398226922494888017)
            ·
              refine ⟨27008824798670191871166013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36011766398226922494888017 27008824798670191871166013)
              ·
                refine ⟨10128309299501321951687255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27008824798670191871166013 10128309299501321951687255)
                ·
                  refine ⟨15192463949251982927530883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10128309299501321951687255 15192463949251982927530883)
                  ·
                    refine ⟨22788695923877974391296325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15192463949251982927530883 22788695923877974391296325)
                    ·
                      refine ⟨4272880485727120198368061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22788695923877974391296325 4272880485727120198368061)
                      ·
                        rfl

theorem cell23_8321405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_8321405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321405 prefixEnd_8321405 := by exact prefixLift 8321405
  have htrace : WordTrace (prefixWord ++ tailWord_8321405) baseStart_8321405 baseEnd_8321405 := by
    simpa [prefixWord, tailWord_8321405, baseEnd_8321405] using wordTrace_append hprefix tailTrace_8321405
  have hstable : (prefixWord ++ tailWord_8321405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321405).length < 2 ^ (prefixWord ++ tailWord_8321405).sum := by decide
  have hdescent : baseEnd_8321405 < baseStart_8321405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321408 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_8321408 : Nat := 118140960795 + 8321408 * 2 ^ 59
def prefixEnd_8321408 : Nat := 4983230072969 + 3 ^ 40 * 8321408 * 2
def baseEnd_8321408 : Nat := 4272882026169083686630547

theorem tailTrace_8321408 : CollatzResearch.WordTrace tailWord_8321408 prefixEnd_8321408 4272882026169083686630547 := by
  unfold tailWord_8321408
  simp only [CollatzResearch.WordTrace]
  refine ⟨151753341918483737092662439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202337789224644982790216585 151753341918483737092662439)
  ·
    refine ⟨227630012877725605638993659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151753341918483737092662439 227630012877725605638993659)
    ·
      refine ⟨341445019316588408458490489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227630012877725605638993659 341445019316588408458490489)
      ·
        refine ⟨256083764487441306343867867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341445019316588408458490489 256083764487441306343867867)
        ·
          refine ⟨384125646731161959515801801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256083764487441306343867867 384125646731161959515801801)
          ·
            refine ⟨288094235048371469636851351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384125646731161959515801801 288094235048371469636851351)
            ·
              refine ⟨432141352572557204455277027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288094235048371469636851351 432141352572557204455277027)
              ·
                refine ⟨648212028858835806682915541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432141352572557204455277027 648212028858835806682915541)
                ·
                  refine ⟨15192469426378964219130833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 648212028858835806682915541 15192469426378964219130833)
                  ·
                    refine ⟨11394352069784223164348125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15192469426378964219130833 11394352069784223164348125)
                    ·
                      refine ⟨4272882026169083686630547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394352069784223164348125 4272882026169083686630547)
                      ·
                        rfl

theorem cell23_8321408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_8321408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321408 prefixEnd_8321408 := by exact prefixLift 8321408
  have htrace : WordTrace (prefixWord ++ tailWord_8321408) baseStart_8321408 baseEnd_8321408 := by
    simpa [prefixWord, tailWord_8321408, baseEnd_8321408] using wordTrace_append hprefix tailTrace_8321408
  have hstable : (prefixWord ++ tailWord_8321408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321408).length < 2 ^ (prefixWord ++ tailWord_8321408).sum := by decide
  have hdescent : baseEnd_8321408 < baseStart_8321408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321415 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 2, 4]
def baseStart_8321415 : Nat := 118140960795 + 8321415 * 2 ^ 59
def prefixEnd_8321415 : Nat := 4983230072969 + 3 ^ 40 * 8321415 * 2
def baseEnd_8321415 : Nat := 1424295206844555053081005

theorem tailTrace_8321415 : CollatzResearch.WordTrace tailWord_8321415 prefixEnd_8321415 1424295206844555053081005 := by
  unfold tailWord_8321415
  simp only [CollatzResearch.WordTrace]
  refine ⟨303506939147942114380829699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202337959431961409587219799 303506939147942114380829699)
  ·
    refine ⟨455260408721913171571244549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303506939147942114380829699 455260408721913171571244549)
    ·
      refine ⟨85361326635358719669608353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455260408721913171571244549 85361326635358719669608353)
      ·
        refine ⟨64020994976519039752206265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85361326635358719669608353 64020994976519039752206265)
        ·
          refine ⟨48015746232389279814154699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64020994976519039752206265 48015746232389279814154699)
          ·
            refine ⟨72023619348583919721232049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48015746232389279814154699 72023619348583919721232049)
            ·
              refine ⟨54017714511437939790924037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72023619348583919721232049 54017714511437939790924037)
              ·
                refine ⟨10128321470894613710798257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54017714511437939790924037 10128321470894613710798257)
                ·
                  refine ⟨7596241103170960283098693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128321470894613710798257 7596241103170960283098693)
                  ·
                    refine ⟨1424295206844555053081005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596241103170960283098693 1424295206844555053081005)
                    ·
                      rfl

theorem cell23_8321415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_8321415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321415 prefixEnd_8321415 := by exact prefixLift 8321415
  have htrace : WordTrace (prefixWord ++ tailWord_8321415) baseStart_8321415 baseEnd_8321415 := by
    simpa [prefixWord, tailWord_8321415, baseEnd_8321415] using wordTrace_append hprefix tailTrace_8321415
  have hstable : (prefixWord ++ tailWord_8321415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321415).length < 2 ^ (prefixWord ++ tailWord_8321415).sum := by decide
  have hdescent : baseEnd_8321415 < baseStart_8321415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321432 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 2, 4]
def baseStart_8321432 : Nat := 118140960795 + 8321432 * 2 ^ 59
def prefixEnd_8321432 : Nat := 4983230072969 + 3 ^ 40 * 8321432 * 2
def baseEnd_8321432 : Nat := 1424298116568263864243479

theorem tailTrace_8321432 : CollatzResearch.WordTrace tailWord_8321432 prefixEnd_8321432 1424298116568263864243479 := by
  unfold tailWord_8321432
  simp only [CollatzResearch.WordTrace]
  refine ⟨151753779594440263142099275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202338372792587017522799033 151753779594440263142099275)
  ·
    refine ⟨227630669391660394713148913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151753779594440263142099275 227630669391660394713148913)
    ·
      refine ⟨170723002043745296034861685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227630669391660394713148913 170723002043745296034861685)
      ·
        refine ⟨16005281441601121503268283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170723002043745296034861685 16005281441601121503268283)
        ·
          refine ⟨24007922162401682254902425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16005281441601121503268283 24007922162401682254902425)
          ·
            refine ⟨18005941621801261691176819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24007922162401682254902425 18005941621801261691176819)
            ·
              refine ⟨27008912432701892536765229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18005941621801261691176819 27008912432701892536765229)
              ·
                refine ⟨10128342162263209701286961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27008912432701892536765229 10128342162263209701286961)
                ·
                  refine ⟨7596256621697407275965221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128342162263209701286961 7596256621697407275965221)
                  ·
                    refine ⟨1424298116568263864243479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596256621697407275965221 1424298116568263864243479)
                    ·
                      rfl

theorem cell23_8321432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_8321432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321432 prefixEnd_8321432 := by exact prefixLift 8321432
  have htrace : WordTrace (prefixWord ++ tailWord_8321432) baseStart_8321432 baseEnd_8321432 := by
    simpa [prefixWord, tailWord_8321432, baseEnd_8321432] using wordTrace_append hprefix tailTrace_8321432
  have hstable : (prefixWord ++ tailWord_8321432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321432).length < 2 ^ (prefixWord ++ tailWord_8321432).sum := by decide
  have hdescent : baseEnd_8321432 < baseStart_8321432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321512 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_8321512 : Nat := 118140960795 + 8321512 * 2 ^ 59
def prefixEnd_8321512 : Nat := 4983230072969 + 3 ^ 40 * 8321512 * 2
def baseEnd_8321512 : Nat := 4272935428157151279730069

theorem tailTrace_8321512 : CollatzResearch.WordTrace tailWord_8321512 prefixEnd_8321512 4272935428157151279730069 := by
  unfold tailWord_8321512
  simp only [CollatzResearch.WordTrace]
  refine ⟨151755238514295349973555395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202340318019060466631407193 151755238514295349973555395)
  ·
    refine ⟨227632857771443024960333093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151755238514295349973555395 227632857771443024960333093)
    ·
      refine ⟨42681160832145567180062455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227632857771443024960333093 42681160832145567180062455)
      ·
        refine ⟨64021741248218350770093683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42681160832145567180062455 64021741248218350770093683)
        ·
          refine ⟨96032611872327526155140525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64021741248218350770093683 96032611872327526155140525)
          ·
            refine ⟨36012229452122822308177697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96032611872327526155140525 36012229452122822308177697)
            ·
              refine ⟨27009172089092116731133273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36012229452122822308177697 27009172089092116731133273)
              ·
                refine ⟨20256879066819087548349955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27009172089092116731133273 20256879066819087548349955)
                ·
                  refine ⟨30385318600228631322524933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20256879066819087548349955 30385318600228631322524933)
                  ·
                    refine ⟨5697247237542868372973425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30385318600228631322524933 5697247237542868372973425)
                    ·
                      refine ⟨4272935428157151279730069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697247237542868372973425 4272935428157151279730069)
                      ·
                        rfl

theorem cell23_8321512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_8321512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321512 prefixEnd_8321512 := by exact prefixLift 8321512
  have htrace : WordTrace (prefixWord ++ tailWord_8321512) baseStart_8321512 baseEnd_8321512 := by
    simpa [prefixWord, tailWord_8321512, baseEnd_8321512] using wordTrace_append hprefix tailTrace_8321512
  have hstable : (prefixWord ++ tailWord_8321512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321512).length < 2 ^ (prefixWord ++ tailWord_8321512).sum := by decide
  have hdescent : baseEnd_8321512 < baseStart_8321512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321529 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 2, 2, 2]
def baseStart_8321529 : Nat := 118140960795 + 8321529 * 2 ^ 59
def prefixEnd_8321529 : Nat := 4983230072969 + 3 ^ 40 * 8321529 * 2
def baseEnd_8321529 : Nat := 4272944157328277713217491

theorem tailTrace_8321529 : CollatzResearch.WordTrace tailWord_8321529 prefixEnd_8321529 4272944157328277713217491 := by
  unfold tailWord_8321529
  simp only [CollatzResearch.WordTrace]
  refine ⟨303511097069529111850479641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202340731379686074566986427 303511097069529111850479641)
  ·
    refine ⟨227633322802146833887859731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303511097069529111850479641 227633322802146833887859731)
    ·
      refine ⟨341449984203220250831789597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227633322802146833887859731 341449984203220250831789597)
      ·
        refine ⟨128043744076207594061921099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341449984203220250831789597 128043744076207594061921099)
        ·
          refine ⟨192065616114311391092881649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128043744076207594061921099 192065616114311391092881649)
          ·
            refine ⟨144049212085733543319661237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192065616114311391092881649 144049212085733543319661237)
            ·
              refine ⟨13504613633037519686218241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144049212085733543319661237 13504613633037519686218241)
              ·
                refine ⟨10128460224778139764663681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13504613633037519686218241 10128460224778139764663681)
                ·
                  refine ⟨7596345168583604823497761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128460224778139764663681 7596345168583604823497761)
                  ·
                    refine ⟨5697258876437703617623321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7596345168583604823497761 5697258876437703617623321)
                    ·
                      refine ⟨4272944157328277713217491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697258876437703617623321 4272944157328277713217491)
                      ·
                        rfl

theorem cell23_8321529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_8321529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321529 prefixEnd_8321529 := by exact prefixLift 8321529
  have htrace : WordTrace (prefixWord ++ tailWord_8321529) baseStart_8321529 baseEnd_8321529 := by
    simpa [prefixWord, tailWord_8321529, baseEnd_8321529] using wordTrace_append hprefix tailTrace_8321529
  have hstable : (prefixWord ++ tailWord_8321529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321529).length < 2 ^ (prefixWord ++ tailWord_8321529).sum := by decide
  have hdescent : baseEnd_8321529 < baseStart_8321529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321535 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 5]
def baseStart_8321535 : Nat := 118140960795 + 8321535 * 2 ^ 59
def prefixEnd_8321535 : Nat := 4983230072969 + 3 ^ 40 * 8321535 * 2
def baseEnd_8321535 : Nat := 474771915356911632193607

theorem tailTrace_8321535 : CollatzResearch.WordTrace tailWord_8321535 prefixEnd_8321535 474771915356911632193607 := by
  unfold tailWord_8321535
  simp only [CollatzResearch.WordTrace]
  refine ⟨303511315907507374875198059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202340877271671583250132039 303511315907507374875198059)
  ·
    refine ⟨455266973861261062312797089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303511315907507374875198059 455266973861261062312797089)
    ·
      refine ⟨341450230395945796734597817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455266973861261062312797089 341450230395945796734597817)
      ·
        refine ⟨256087672796959347550948363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341450230395945796734597817 256087672796959347550948363)
        ·
          refine ⟨384131509195439021326422545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256087672796959347550948363 384131509195439021326422545)
          ·
            refine ⟨288098631896579265994816909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384131509195439021326422545 288098631896579265994816909)
            ·
              refine ⟨108036986961217224748056341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288098631896579265994816909 108036986961217224748056341)
              ·
                refine ⟨5064233763807057410065141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108036986961217224748056341 5064233763807057410065141)
                ·
                  refine ⟨474771915356911632193607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5064233763807057410065141 474771915356911632193607)
                  ·
                    rfl

theorem cell23_8321535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 5].length) (baseStart_8321535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321535 prefixEnd_8321535 := by exact prefixLift 8321535
  have htrace : WordTrace (prefixWord ++ tailWord_8321535) baseStart_8321535 baseEnd_8321535 := by
    simpa [prefixWord, tailWord_8321535, baseEnd_8321535] using wordTrace_append hprefix tailTrace_8321535
  have hstable : (prefixWord ++ tailWord_8321535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321535).length < 2 ^ (prefixWord ++ tailWord_8321535).sum := by decide
  have hdescent : baseEnd_8321535 < baseStart_8321535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321546 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_8321546 : Nat := 118140960795 + 8321546 * 2 ^ 59
def prefixEnd_8321546 : Nat := 4983230072969 + 3 ^ 40 * 8321546 * 2
def baseEnd_8321546 : Nat := 4272952886499404146704913

theorem tailTrace_8321546 : CollatzResearch.WordTrace tailWord_8321546 prefixEnd_8321546 4272952886499404146704913 := by
  unfold tailWord_8321546
  simp only [CollatzResearch.WordTrace]
  refine ⟨75877929277616880938462123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202341144740311682502565661 75877929277616880938462123)
  ·
    refine ⟨113816893916425321407693185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75877929277616880938462123 113816893916425321407693185)
    ·
      refine ⟨85362670437318991055769889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113816893916425321407693185 85362670437318991055769889)
      ·
        refine ⟨64022002827989243291827417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85362670437318991055769889 64022002827989243291827417)
        ·
          refine ⟨48016502120991932468870563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64022002827989243291827417 48016502120991932468870563)
          ·
            refine ⟨72024753181487898703305845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48016502120991932468870563 72024753181487898703305845)
            ·
              refine ⟨6752320610764490503434923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72024753181487898703305845 6752320610764490503434923)
              ·
                refine ⟨10128480916146735755152385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6752320610764490503434923 10128480916146735755152385)
                ·
                  refine ⟨7596360687110051816364289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128480916146735755152385 7596360687110051816364289)
                  ·
                    refine ⟨5697270515332538862273217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7596360687110051816364289 5697270515332538862273217)
                    ·
                      refine ⟨4272952886499404146704913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697270515332538862273217 4272952886499404146704913)
                      ·
                        rfl

theorem cell23_8321546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_8321546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321546 prefixEnd_8321546 := by exact prefixLift 8321546
  have htrace : WordTrace (prefixWord ++ tailWord_8321546) baseStart_8321546 baseEnd_8321546 := by
    simpa [prefixWord, tailWord_8321546, baseEnd_8321546] using wordTrace_append hprefix tailTrace_8321546
  have hstable : (prefixWord ++ tailWord_8321546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321546).length < 2 ^ (prefixWord ++ tailWord_8321546).sum := by decide
  have hdescent : baseEnd_8321546 < baseStart_8321546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321565 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_8321565 : Nat := 118140960795 + 8321565 * 2 ^ 59
def prefixEnd_8321565 : Nat := 4983230072969 + 3 ^ 40 * 8321565 * 2
def baseEnd_8321565 : Nat := 1424320880877279857455775

theorem tailTrace_8321565 : CollatzResearch.WordTrace tailWord_8321565 prefixEnd_8321565 1424320880877279857455775 := by
  unfold tailWord_8321565
  simp only [CollatzResearch.WordTrace]
  refine ⟨303512410097398689998790149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202341606731599126665860099 303512410097398689998790149)
  ·
    refine ⟨56908576893262254374773153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303512410097398689998790149 56908576893262254374773153)
    ·
      refine ⟨42681432669946690781079865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56908576893262254374773153 42681432669946690781079865)
      ·
        refine ⟨32011074502460018085809899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42681432669946690781079865 32011074502460018085809899)
        ·
          refine ⟨48016611753690027128714849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32011074502460018085809899 48016611753690027128714849)
          ·
            refine ⟨36012458815267520346536137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48016611753690027128714849 36012458815267520346536137)
            ·
              refine ⟨27009344111450640259902103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36012458815267520346536137 27009344111450640259902103)
              ·
                refine ⟨40514016167175960389853155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27009344111450640259902103 40514016167175960389853155)
                ·
                  refine ⟨60771024250763940584779733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40514016167175960389853155 60771024250763940584779733)
                  ·
                    refine ⟨1424320880877279857455775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60771024250763940584779733 1424320880877279857455775)
                    ·
                      rfl

theorem cell23_8321565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_8321565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321565 prefixEnd_8321565 := by exact prefixLift 8321565
  have htrace : WordTrace (prefixWord ++ tailWord_8321565) baseStart_8321565 baseEnd_8321565 := by
    simpa [prefixWord, tailWord_8321565, baseEnd_8321565] using wordTrace_append hprefix tailTrace_8321565
  have hstable : (prefixWord ++ tailWord_8321565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321565).length < 2 ^ (prefixWord ++ tailWord_8321565).sum := by decide
  have hdescent : baseEnd_8321565 < baseStart_8321565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321585 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_8321585 : Nat := 118140960795 + 8321585 * 2 ^ 59
def prefixEnd_8321585 : Nat := 4983230072969 + 3 ^ 40 * 8321585 * 2
def baseEnd_8321585 : Nat := 4272972912244929494117233

theorem tailTrace_8321585 : CollatzResearch.WordTrace tailWord_8321585 prefixEnd_8321585 4272972912244929494117233 := by
  unfold tailWord_8321585
  simp only [CollatzResearch.WordTrace]
  refine ⟨303513139557326233414518209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202342093038217488943012139 303513139557326233414518209)
  ·
    refine ⟨227634854667994675060888657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303513139557326233414518209 227634854667994675060888657)
    ·
      refine ⟨170726141000996006295666493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227634854667994675060888657 170726141000996006295666493)
      ·
        refine ⟨64022302875373502360874935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170726141000996006295666493 64022302875373502360874935)
        ·
          refine ⟨96033454313060253541312403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64022302875373502360874935 96033454313060253541312403)
          ·
            refine ⟨144050181469590380311968605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96033454313060253541312403 144050181469590380311968605)
            ·
              refine ⟨54018818051096392616988227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144050181469590380311968605 54018818051096392616988227)
              ·
                refine ⟨81028227076644588925482341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54018818051096392616988227 81028227076644588925482341)
                ·
                  refine ⟨15192792576870860423527939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81028227076644588925482341 15192792576870860423527939)
                  ·
                    refine ⟨22789188865306290635291909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15192792576870860423527939 22789188865306290635291909)
                    ·
                      refine ⟨4272972912244929494117233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22789188865306290635291909 4272972912244929494117233)
                      ·
                        rfl

theorem cell23_8321585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_8321585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321585 prefixEnd_8321585 := by exact prefixLift 8321585
  have htrace : WordTrace (prefixWord ++ tailWord_8321585) baseStart_8321585 baseEnd_8321585 := by
    simpa [prefixWord, tailWord_8321585, baseEnd_8321585] using wordTrace_append hprefix tailTrace_8321585
  have hstable : (prefixWord ++ tailWord_8321585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321585).length < 2 ^ (prefixWord ++ tailWord_8321585).sum := by decide
  have hdescent : baseEnd_8321585 < baseStart_8321585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321642 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_8321642 : Nat := 118140960795 + 8321642 * 2 ^ 59
def prefixEnd_8321642 : Nat := 4983230072969 + 3 ^ 40 * 8321642 * 2
def baseEnd_8321642 : Nat := 474778020071359530122719

theorem tailTrace_8321642 : CollatzResearch.WordTrace tailWord_8321642 prefixEnd_8321642 474778020071359530122719 := by
  unfold tailWord_8321642
  simp only [CollatzResearch.WordTrace]
  refine ⟨75878804629529933037335795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202343479012079821432895453 75878804629529933037335795)
  ·
    refine ⟨113818206944294899556003693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75878804629529933037335795 113818206944294899556003693)
    ·
      refine ⟨42681827604110587333501385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113818206944294899556003693 42681827604110587333501385)
      ·
        refine ⟨32011370703082940500126039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42681827604110587333501385 32011370703082940500126039)
        ·
          refine ⟨48017056054624410750189059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32011370703082940500126039 48017056054624410750189059)
          ·
            refine ⟨72025584081936616125283589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48017056054624410750189059 72025584081936616125283589)
            ·
              refine ⟨13504797015363115523490673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72025584081936616125283589 13504797015363115523490673)
              ·
                refine ⟨10128597761522336642618005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13504797015363115523490673 10128597761522336642618005)
                ·
                  refine ⟨474778020071359530122719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10128597761522336642618005 474778020071359530122719)
                  ·
                    rfl

theorem cell23_8321642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_8321642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321642 prefixEnd_8321642 := by exact prefixLift 8321642
  have htrace : WordTrace (prefixWord ++ tailWord_8321642) baseStart_8321642 baseEnd_8321642 := by
    simpa [prefixWord, tailWord_8321642, baseEnd_8321642] using wordTrace_append hprefix tailTrace_8321642
  have hstable : (prefixWord ++ tailWord_8321642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321642).length < 2 ^ (prefixWord ++ tailWord_8321642).sum := by decide
  have hdescent : baseEnd_8321642 < baseStart_8321642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321646 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_8321646 : Nat := 118140960795 + 8321646 * 2 ^ 59
def prefixEnd_8321646 : Nat := 4983230072969 + 3 ^ 40 * 8321646 * 2
def baseEnd_8321646 : Nat := 1424334744854951251818151

theorem tailTrace_8321646 : CollatzResearch.WordTrace tailWord_8321646 prefixEnd_8321646 1424334744854951251818151 := by
  unfold tailWord_8321646
  simp only [CollatzResearch.WordTrace]
  refine ⟨37939420551263155104061099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202343576273403493888325861 37939420551263155104061099)
  ·
    refine ⟨56909130826894732656091649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37939420551263155104061099 56909130826894732656091649)
    ·
      refine ⟨42681848120171049492068737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56909130826894732656091649 42681848120171049492068737)
      ·
        refine ⟨32011386090128287119051553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42681848120171049492068737 32011386090128287119051553)
        ·
          refine ⟨24008539567596215339288665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32011386090128287119051553 24008539567596215339288665)
          ·
            refine ⟨18006404675697161504466499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24008539567596215339288665 18006404675697161504466499)
            ·
              refine ⟨27009607013545742256699749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18006404675697161504466499 27009607013545742256699749)
              ·
                refine ⟨5064301315039826673131203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27009607013545742256699749 5064301315039826673131203)
                ·
                  refine ⟨7596451972559740009696805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064301315039826673131203 7596451972559740009696805)
                  ·
                    refine ⟨1424334744854951251818151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596451972559740009696805 1424334744854951251818151)
                    ·
                      rfl

theorem cell23_8321646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_8321646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321646 prefixEnd_8321646 := by exact prefixLift 8321646
  have htrace : WordTrace (prefixWord ++ tailWord_8321646) baseStart_8321646 baseEnd_8321646 := by
    simpa [prefixWord, tailWord_8321646, baseEnd_8321646] using wordTrace_append hprefix tailTrace_8321646
  have hstable : (prefixWord ++ tailWord_8321646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321646).length < 2 ^ (prefixWord ++ tailWord_8321646).sum := by decide
  have hdescent : baseEnd_8321646 < baseStart_8321646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321655 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 3, 5]
def baseStart_8321655 : Nat := 118140960795 + 8321655 * 2 ^ 59
def prefixEnd_8321655 : Nat := 4983230072969 + 3 ^ 40 * 8321655 * 2
def baseEnd_8321655 : Nat := 1424336285296914740080637

theorem tailTrace_8321655 : CollatzResearch.WordTrace tailWord_8321655 prefixEnd_8321655 1424336285296914740080637 := by
  unfold tailWord_8321655
  simp only [CollatzResearch.WordTrace]
  refine ⟨303515692667072635369566419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202343795111381756913044279 303515692667072635369566419)
  ·
    refine ⟨455273539000608953054349629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303515692667072635369566419 455273539000608953054349629)
    ·
      refine ⟨170727577125228357395381111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455273539000608953054349629 170727577125228357395381111)
      ·
        refine ⟨256091365687842536093071667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170727577125228357395381111 256091365687842536093071667)
        ·
          refine ⟨384137048531763804139607501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256091365687842536093071667 384137048531763804139607501)
          ·
            refine ⟨144051393199411426552352813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384137048531763804139607501 144051393199411426552352813)
            ·
              refine ⟨54019272449779284957132305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144051393199411426552352813 54019272449779284957132305)
              ·
                refine ⟨40514454337334463717849229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54019272449779284957132305 40514454337334463717849229)
                ·
                  refine ⟨15192920376500423894193461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40514454337334463717849229 15192920376500423894193461)
                  ·
                    refine ⟨1424336285296914740080637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15192920376500423894193461 1424336285296914740080637)
                    ·
                      rfl

theorem cell23_8321655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_8321655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321655 prefixEnd_8321655 := by exact prefixLift 8321655
  have htrace : WordTrace (prefixWord ++ tailWord_8321655) baseStart_8321655 baseEnd_8321655 := by
    simpa [prefixWord, tailWord_8321655, baseEnd_8321655] using wordTrace_append hprefix tailTrace_8321655
  have hstable : (prefixWord ++ tailWord_8321655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321655).length < 2 ^ (prefixWord ++ tailWord_8321655).sum := by decide
  have hdescent : baseEnd_8321655 < baseStart_8321655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321665 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_8321665 : Nat := 118140960795 + 8321665 * 2 ^ 59
def prefixEnd_8321665 : Nat := 4983230072969 + 3 ^ 40 * 8321665 * 2
def baseEnd_8321665 : Nat := 4273013990697289181116865

theorem tailTrace_8321665 : CollatzResearch.WordTrace tailWord_8321665 prefixEnd_8321665 4273013990697289181116865 := by
  unfold tailWord_8321665
  simp only [CollatzResearch.WordTrace]
  refine ⟨303516057397036407077430449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202344038264690938051620299 303516057397036407077430449)
  ·
    refine ⟨227637043047777305308072837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303516057397036407077430449 227637043047777305308072837)
    ·
      refine ⟨42681945571458244745263657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227637043047777305308072837 42681945571458244745263657)
      ·
        refine ⟨32011459178593683558947743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42681945571458244745263657 32011459178593683558947743)
        ·
          refine ⟨48017188767890525338421615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32011459178593683558947743 48017188767890525338421615)
          ·
            refine ⟨72025783151835788007632423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48017188767890525338421615 72025783151835788007632423)
            ·
              refine ⟨108038674727753682011448635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72025783151835788007632423 108038674727753682011448635)
              ·
                refine ⟨162058012091630523017172953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108038674727753682011448635 162058012091630523017172953)
                ·
                  refine ⟨121543509068722892262879715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162058012091630523017172953 121543509068722892262879715)
                  ·
                    refine ⟨182315263603084338394319573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121543509068722892262879715 182315263603084338394319573)
                    ·
                      refine ⟨4273013990697289181116865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182315263603084338394319573 4273013990697289181116865)
                      ·
                        rfl

theorem cell23_8321665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_8321665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321665 prefixEnd_8321665 := by exact prefixLift 8321665
  have htrace : WordTrace (prefixWord ++ tailWord_8321665) baseStart_8321665 baseEnd_8321665 := by
    simpa [prefixWord, tailWord_8321665, baseEnd_8321665] using wordTrace_append hprefix tailTrace_8321665
  have hstable : (prefixWord ++ tailWord_8321665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321665).length < 2 ^ (prefixWord ++ tailWord_8321665).sum := by decide
  have hdescent : baseEnd_8321665 < baseStart_8321665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321669 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_8321669 : Nat := 118140960795 + 8321669 * 2 ^ 59
def prefixEnd_8321669 : Nat := 4983230072969 + 3 ^ 40 * 8321669 * 2
def baseEnd_8321669 : Nat := 4273016044619907165466847

theorem tailTrace_8321669 : CollatzResearch.WordTrace tailWord_8321669 prefixEnd_8321669 4273016044619907165466847 := by
  unfold tailWord_8321669
  simp only [CollatzResearch.WordTrace]
  refine ⟨303516203289021915760576061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202344135526014610507050707 303516203289021915760576061)
  ·
    refine ⟨113818576233383218410216023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303516203289021915760576061 113818576233383218410216023)
    ·
      refine ⟨170727864350074827615324035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113818576233383218410216023 170727864350074827615324035)
      ·
        refine ⟨256091796525112241422986053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170727864350074827615324035 256091796525112241422986053)
        ·
          refine ⟨48017211848458545266809885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256091796525112241422986053 48017211848458545266809885)
          ·
            refine ⟨18006454443171954475053707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48017211848458545266809885 18006454443171954475053707)
            ·
              refine ⟨27009681664757931712580561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18006454443171954475053707 27009681664757931712580561)
              ·
                refine ⟨20257261248568448784435421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27009681664757931712580561 20257261248568448784435421)
                ·
                  refine ⟨7596472968213168294163283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20257261248568448784435421 7596472968213168294163283)
                  ·
                    refine ⟨11394709452319752441244925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596472968213168294163283 11394709452319752441244925)
                    ·
                      refine ⟨4273016044619907165466847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394709452319752441244925 4273016044619907165466847)
                      ·
                        rfl

theorem cell23_8321669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_8321669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321669 prefixEnd_8321669 := by exact prefixLift 8321669
  have htrace : WordTrace (prefixWord ++ tailWord_8321669) baseStart_8321669 baseEnd_8321669 := by
    simpa [prefixWord, tailWord_8321669, baseEnd_8321669] using wordTrace_append hprefix tailTrace_8321669
  have hstable : (prefixWord ++ tailWord_8321669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321669).length < 2 ^ (prefixWord ++ tailWord_8321669).sum := by decide
  have hdescent : baseEnd_8321669 < baseStart_8321669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321703 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_8321703 : Nat := 118140960795 + 8321703 * 2 ^ 59
def prefixEnd_8321703 : Nat := 4983230072969 + 3 ^ 40 * 8321703 * 2
def baseEnd_8321703 : Nat := 4273033502962160032441691

theorem tailTrace_8321703 : CollatzResearch.WordTrace tailWord_8321703 prefixEnd_8321703 4273033502962160032441691 := by
  unfold tailWord_8321703
  simp only [CollatzResearch.WordTrace]
  refine ⟨303517443370898739567313763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202344962247265826378209175 303517443370898739567313763)
  ·
    refine ⟨455276165056348109350970645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303517443370898739567313763 455276165056348109350970645)
    ·
      refine ⟨21341070237016317625826749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 455276165056348109350970645 21341070237016317625826749)
      ·
        refine ⟨8002901338881119109685031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21341070237016317625826749 8002901338881119109685031)
        ·
          refine ⟨12004352008321678664527547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002901338881119109685031 12004352008321678664527547)
          ·
            refine ⟨18006528012482517996791321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004352008321678664527547 18006528012482517996791321)
            ·
              refine ⟨13504896009361888497593491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18006528012482517996791321 13504896009361888497593491)
              ·
                refine ⟨20257344014042832746390237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13504896009361888497593491 20257344014042832746390237)
                ·
                  refine ⟨7596504005266062279896339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20257344014042832746390237 7596504005266062279896339)
                  ·
                    refine ⟨11394756007899093419844509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596504005266062279896339 11394756007899093419844509)
                    ·
                      refine ⟨4273033502962160032441691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394756007899093419844509 4273033502962160032441691)
                      ·
                        rfl

theorem cell23_8321703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_8321703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321703 prefixEnd_8321703 := by exact prefixLift 8321703
  have htrace : WordTrace (prefixWord ++ tailWord_8321703) baseStart_8321703 baseEnd_8321703 := by
    simpa [prefixWord, tailWord_8321703, baseEnd_8321703] using wordTrace_append hprefix tailTrace_8321703
  have hstable : (prefixWord ++ tailWord_8321703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321703).length < 2 ^ (prefixWord ++ tailWord_8321703).sum := by decide
  have hdescent : baseEnd_8321703 < baseStart_8321703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321705 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_8321705 : Nat := 118140960795 + 8321705 * 2 ^ 59
def prefixEnd_8321705 : Nat := 4983230072969 + 3 ^ 40 * 8321705 * 2
def baseEnd_8321705 : Nat := 4273034529923469024616681

theorem tailTrace_8321705 : CollatzResearch.WordTrace tailWord_8321705 prefixEnd_8321705 4273034529923469024616681 := by
  unfold tailWord_8321705
  simp only [CollatzResearch.WordTrace]
  refine ⟨303517516316891493908886569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202345010877927662605924379 303517516316891493908886569)
  ·
    refine ⟨227638137237668620431664927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303517516316891493908886569 227638137237668620431664927)
    ·
      refine ⟨341457205856502930647497391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227638137237668620431664927 341457205856502930647497391)
      ·
        refine ⟨512185808784754395971246087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341457205856502930647497391 512185808784754395971246087)
        ·
          refine ⟨768278713177131593956869131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512185808784754395971246087 768278713177131593956869131)
          ·
            refine ⟨1152418069765697390935303697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768278713177131593956869131 1152418069765697390935303697)
            ·
              refine ⟨864313552324273043201477773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152418069765697390935303697 864313552324273043201477773)
              ·
                refine ⟨324117582121602391200554165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864313552324273043201477773 324117582121602391200554165)
                ·
                  refine ⟨30386023323900224175051953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324117582121602391200554165 30386023323900224175051953)
                  ·
                    refine ⟨22789517492925168131288965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30386023323900224175051953 22789517492925168131288965)
                    ·
                      refine ⟨4273034529923469024616681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22789517492925168131288965 4273034529923469024616681)
                      ·
                        rfl

theorem cell23_8321705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_8321705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321705 prefixEnd_8321705 := by exact prefixLift 8321705
  have htrace : WordTrace (prefixWord ++ tailWord_8321705) baseStart_8321705 baseEnd_8321705 := by
    simpa [prefixWord, tailWord_8321705, baseEnd_8321705] using wordTrace_append hprefix tailTrace_8321705
  have hstable : (prefixWord ++ tailWord_8321705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321705).length < 2 ^ (prefixWord ++ tailWord_8321705).sum := by decide
  have hdescent : baseEnd_8321705 < baseStart_8321705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321719 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 1, 6]
def baseStart_8321719 : Nat := 118140960795 + 8321719 * 2 ^ 59
def prefixEnd_8321719 : Nat := 4983230072969 + 3 ^ 40 * 8321719 * 2
def baseEnd_8321719 : Nat := 1424347239550877323280539

theorem tailTrace_8321719 : CollatzResearch.WordTrace tailWord_8321719 prefixEnd_8321719 1424347239550877323280539 := by
  unfold tailWord_8321719
  simp only [CollatzResearch.WordTrace]
  refine ⟨303518026938840774299896211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202345351292560516199930807 303518026938840774299896211)
  ·
    refine ⟨455277040408261161449844317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303518026938840774299896211 455277040408261161449844317)
    ·
      refine ⟨170728890153097935543691619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455277040408261161449844317 170728890153097935543691619)
      ·
        refine ⟨256093335229646903315537429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170728890153097935543691619 256093335229646903315537429)
        ·
          refine ⟨12004375088889698592915817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256093335229646903315537429 12004375088889698592915817)
          ·
            refine ⟨9003281316667273944686863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12004375088889698592915817 9003281316667273944686863)
            ·
              refine ⟨13504921975000910917030295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9003281316667273944686863 13504921975000910917030295)
              ·
                refine ⟨20257382962501366375545443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13504921975000910917030295 20257382962501366375545443)
                ·
                  refine ⟨30386074443752049563318165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20257382962501366375545443 30386074443752049563318165)
                  ·
                    refine ⟨1424347239550877323280539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30386074443752049563318165 1424347239550877323280539)
                    ·
                      rfl

theorem cell23_8321719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_8321719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321719 prefixEnd_8321719 := by exact prefixLift 8321719
  have htrace : WordTrace (prefixWord ++ tailWord_8321719) baseStart_8321719 baseEnd_8321719 := by
    simpa [prefixWord, tailWord_8321719, baseEnd_8321719] using wordTrace_append hprefix tailTrace_8321719
  have hstable : (prefixWord ++ tailWord_8321719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321719).length < 2 ^ (prefixWord ++ tailWord_8321719).sum := by decide
  have hdescent : baseEnd_8321719 < baseStart_8321719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321726 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_8321726 : Nat := 118140960795 + 8321726 * 2 ^ 59
def prefixEnd_8321726 : Nat := 4983230072969 + 3 ^ 40 * 8321726 * 2
def baseEnd_8321726 : Nat := 4273045313017213442454085

theorem tailTrace_8321726 : CollatzResearch.WordTrace tailWord_8321726 prefixEnd_8321726 4273045313017213442454085 := by
  unfold tailWord_8321726
  simp only [CollatzResearch.WordTrace]
  refine ⟨37939785281226926811925129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202345521499876942996934021 37939785281226926811925129)
  ·
    refine ⟨28454838960920195108943847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37939785281226926811925129 28454838960920195108943847)
    ·
      refine ⟨42682258441380292663415771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28454838960920195108943847 42682258441380292663415771)
      ·
        refine ⟨64023387662070438995123657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42682258441380292663415771 64023387662070438995123657)
        ·
          refine ⟨48017540746552829246342743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64023387662070438995123657 48017540746552829246342743)
          ·
            refine ⟨72026311119829243869514115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48017540746552829246342743 72026311119829243869514115)
            ·
              refine ⟨108039466679743865804271173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72026311119829243869514115 108039466679743865804271173)
              ·
                refine ⟨20257400002451974838300845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108039466679743865804271173 20257400002451974838300845)
                ·
                  refine ⟨7596525000919490564362817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20257400002451974838300845 7596525000919490564362817)
                  ·
                    refine ⟨5697393750689617923272113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7596525000919490564362817 5697393750689617923272113)
                    ·
                      refine ⟨4273045313017213442454085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697393750689617923272113 4273045313017213442454085)
                      ·
                        rfl

theorem cell23_8321726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_8321726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321726 prefixEnd_8321726 := by exact prefixLift 8321726
  have htrace : WordTrace (prefixWord ++ tailWord_8321726) baseStart_8321726 baseEnd_8321726 := by
    simpa [prefixWord, tailWord_8321726, baseEnd_8321726] using wordTrace_append hprefix tailTrace_8321726
  have hstable : (prefixWord ++ tailWord_8321726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321726).length < 2 ^ (prefixWord ++ tailWord_8321726).sum := by decide
  have hdescent : baseEnd_8321726 < baseStart_8321726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321732 : List Nat := [2, 3, 3, 1, 1, 3, 1, 9]
def baseStart_8321732 : Nat := 118140960795 + 8321732 * 2 ^ 59
def prefixEnd_8321732 : Nat := 4983230072969 + 3 ^ 40 * 8321732 * 2
def baseEnd_8321732 : Nat := 158261051625968163665891

theorem tailTrace_8321732 : CollatzResearch.WordTrace tailWord_8321732 prefixEnd_8321732 158261051625968163665891 := by
  unfold tailWord_8321732
  simp only [CollatzResearch.WordTrace]
  refine ⟨151759250543896838760059725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202345667391862451680079633 151759250543896838760059725)
  ·
    refine ⟨56909718953961314535022397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151759250543896838760059725 56909718953961314535022397)
    ·
      refine ⟨21341144607735492950633399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56909718953961314535022397 21341144607735492950633399)
      ·
        refine ⟨32011716911603239425950099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21341144607735492950633399 32011716911603239425950099)
        ·
          refine ⟨48017575367404859138925149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32011716911603239425950099 48017575367404859138925149)
          ·
            refine ⟨18006590762776822177096931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48017575367404859138925149 18006590762776822177096931)
            ·
              refine ⟨27009886144165233265645397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18006590762776822177096931 27009886144165233265645397)
              ·
                refine ⟨158261051625968163665891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27009886144165233265645397 158261051625968163665891)
                ·
                  rfl

theorem cell23_8321732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 9].length) (baseStart_8321732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321732 prefixEnd_8321732 := by exact prefixLift 8321732
  have htrace : WordTrace (prefixWord ++ tailWord_8321732) baseStart_8321732 baseEnd_8321732 := by
    simpa [prefixWord, tailWord_8321732, baseEnd_8321732] using wordTrace_append hprefix tailTrace_8321732
  have hstable : (prefixWord ++ tailWord_8321732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321732).length < 2 ^ (prefixWord ++ tailWord_8321732).sum := by decide
  have hdescent : baseEnd_8321732 < baseStart_8321732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321749 : List Nat := [1, 3, 2, 5, 1, 2, 9]
def baseStart_8321749 : Nat := 118140960795 + 8321749 * 2 ^ 59
def prefixEnd_8321749 : Nat := 4983230072969 + 3 ^ 40 * 8321749 * 2
def baseEnd_8321749 : Nat := 52753791642867492005759

theorem tailTrace_8321749 : CollatzResearch.WordTrace tailWord_8321749 prefixEnd_8321749 52753791642867492005759 := by
  unfold tailWord_8321749
  simp only [CollatzResearch.WordTrace]
  refine ⟨303519121128732089423488301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202346080752488059615658867 303519121128732089423488301)
  ·
    refine ⟨113819670423274533533808113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303519121128732089423488301 113819670423274533533808113)
    ·
      refine ⟨85364752817455900150356085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113819670423274533533808113 85364752817455900150356085)
      ·
        refine ⟨8002945576636490639095883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85364752817455900150356085 8002945576636490639095883)
        ·
          refine ⟨12004418364954735958643825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002945576636490639095883 12004418364954735958643825)
          ·
            refine ⟨9003313773716051968982869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12004418364954735958643825 9003313773716051968982869)
            ·
              refine ⟨52753791642867492005759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9003313773716051968982869 52753791642867492005759)
              ·
                rfl

theorem cell23_8321749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 9].length) (baseStart_8321749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321749 prefixEnd_8321749 := by exact prefixLift 8321749
  have htrace : WordTrace (prefixWord ++ tailWord_8321749) baseStart_8321749 baseEnd_8321749 := by
    simpa [prefixWord, tailWord_8321749, baseEnd_8321749] using wordTrace_append hprefix tailTrace_8321749
  have hstable : (prefixWord ++ tailWord_8321749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321749).length < 2 ^ (prefixWord ++ tailWord_8321749).sum := by decide
  have hdescent : baseEnd_8321749 < baseStart_8321749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321759 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 3]
def baseStart_8321759 : Nat := 118140960795 + 8321759 * 2 ^ 59
def prefixEnd_8321759 : Nat := 4983230072969 + 3 ^ 40 * 8321759 * 2
def baseEnd_8321759 : Nat := 4273062257878811813341433

theorem tailTrace_8321759 : CollatzResearch.WordTrace tailWord_8321759 prefixEnd_8321759 4273062257878811813341433 := by
  unfold tailWord_8321759
  simp only [CollatzResearch.WordTrace]
  refine ⟨303519485858695861131352331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202346323905797240754234887 303519485858695861131352331)
  ·
    refine ⟨455279228788043791697028497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303519485858695861131352331 455279228788043791697028497)
    ·
      refine ⟨341459421591032843772771373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455279228788043791697028497 341459421591032843772771373)
      ·
        refine ⟨128047283096637316414789265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341459421591032843772771373 128047283096637316414789265)
        ·
          refine ⟨96035462322477987311091949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128047283096637316414789265 96035462322477987311091949)
          ·
            refine ⟨36013298370929245241659481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96035462322477987311091949 36013298370929245241659481)
            ·
              refine ⟨27009973778196933931244611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36013298370929245241659481 27009973778196933931244611)
              ·
                refine ⟨40514960667295400896866917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27009973778196933931244611 40514960667295400896866917)
                ·
                  refine ⟨7596555125117887668162547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40514960667295400896866917 7596555125117887668162547)
                  ·
                    refine ⟨11394832687676831502243821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596555125117887668162547 11394832687676831502243821)
                    ·
                      refine ⟨4273062257878811813341433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394832687676831502243821 4273062257878811813341433)
                      ·
                        rfl

theorem cell23_8321759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_8321759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321759 prefixEnd_8321759 := by exact prefixLift 8321759
  have htrace : WordTrace (prefixWord ++ tailWord_8321759) baseStart_8321759 baseEnd_8321759 := by
    simpa [prefixWord, tailWord_8321759, baseEnd_8321759] using wordTrace_append hprefix tailTrace_8321759
  have hstable : (prefixWord ++ tailWord_8321759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321759).length < 2 ^ (prefixWord ++ tailWord_8321759).sum := by decide
  have hdescent : baseEnd_8321759 < baseStart_8321759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321786 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2]
def baseStart_8321786 : Nat := 118140960795 + 8321786 * 2 ^ 59
def prefixEnd_8321786 : Nat := 4983230072969 + 3 ^ 40 * 8321786 * 2
def baseEnd_8321786 : Nat := 4273076121856483207703809

theorem tailTrace_8321786 : CollatzResearch.WordTrace tailWord_8321786 prefixEnd_8321786 4273076121856483207703809 := by
  unfold tailWord_8321786
  simp only [CollatzResearch.WordTrace]
  refine ⟨75880117657399511185646303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202346980419732029828390141 75880117657399511185646303)
  ·
    refine ⟨113820176486099266778469455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75880117657399511185646303 113820176486099266778469455)
    ·
      refine ⟨170730264729148900167704183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113820176486099266778469455 170730264729148900167704183)
      ·
        refine ⟨256095397093723350251556275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170730264729148900167704183 256095397093723350251556275)
        ·
          refine ⟨384143095640585025377334413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256095397093723350251556275 384143095640585025377334413)
          ·
            refine ⟨144053660865219384516500405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384143095640585025377334413 144053660865219384516500405)
            ·
              refine ⟨13505030706114317298421913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144053660865219384516500405 13505030706114317298421913)
              ·
                refine ⟨10128773029585737973816435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13505030706114317298421913 10128773029585737973816435)
                ·
                  refine ⟨15193159544378606960724653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10128773029585737973816435 15193159544378606960724653)
                  ·
                    refine ⟨5697434829141977610271745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15193159544378606960724653 5697434829141977610271745)
                    ·
                      refine ⟨4273076121856483207703809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697434829141977610271745 4273076121856483207703809)
                      ·
                        rfl

theorem cell23_8321786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_8321786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321786 prefixEnd_8321786 := by exact prefixLift 8321786
  have htrace : WordTrace (prefixWord ++ tailWord_8321786) baseStart_8321786 baseEnd_8321786 := by
    simpa [prefixWord, tailWord_8321786, baseEnd_8321786] using wordTrace_append hprefix tailTrace_8321786
  have hstable : (prefixWord ++ tailWord_8321786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321786).length < 2 ^ (prefixWord ++ tailWord_8321786).sum := by decide
  have hdescent : baseEnd_8321786 < baseStart_8321786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321802 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_8321802 : Nat := 118140960795 + 8321802 * 2 ^ 59
def prefixEnd_8321802 : Nat := 4983230072969 + 3 ^ 40 * 8321802 * 2
def baseEnd_8321802 : Nat := 4273084337546955145103735

theorem tailTrace_8321802 : CollatzResearch.WordTrace tailWord_8321802 prefixEnd_8321802 4273084337546955145103735 := by
  unfold tailWord_8321802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75880263549385019868791915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202347369465026719650111773 75880263549385019868791915)
  ·
    refine ⟨113820395324077529803187873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75880263549385019868791915 113820395324077529803187873)
    ·
      refine ⟨85365296493058147352390905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113820395324077529803187873 85365296493058147352390905)
      ·
        refine ⟨64023972369793610514293179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85365296493058147352390905 64023972369793610514293179)
        ·
          refine ⟨96035958554690415771439769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64023972369793610514293179 96035958554690415771439769)
          ·
            refine ⟨72026968916017811828579827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96035958554690415771439769 72026968916017811828579827)
            ·
              refine ⟨108040453374026717742869741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72026968916017811828579827 108040453374026717742869741)
              ·
                refine ⟨40515170015260019153576153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108040453374026717742869741 40515170015260019153576153)
                ·
                  refine ⟨30386377511445014365182115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40515170015260019153576153 30386377511445014365182115)
                  ·
                    refine ⟨45579566267167521547773173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30386377511445014365182115 45579566267167521547773173)
                    ·
                      refine ⟨4273084337546955145103735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45579566267167521547773173 4273084337546955145103735)
                      ·
                        rfl

theorem cell23_8321802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_8321802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321802 prefixEnd_8321802 := by exact prefixLift 8321802
  have htrace : WordTrace (prefixWord ++ tailWord_8321802) baseStart_8321802 baseEnd_8321802 := by
    simpa [prefixWord, tailWord_8321802, baseEnd_8321802] using wordTrace_append hprefix tailTrace_8321802
  have hstable : (prefixWord ++ tailWord_8321802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321802).length < 2 ^ (prefixWord ++ tailWord_8321802).sum := by decide
  have hdescent : baseEnd_8321802 < baseStart_8321802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321810 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_8321810 : Nat := 118140960795 + 8321810 * 2 ^ 59
def prefixEnd_8321810 : Nat := 4983230072969 + 3 ^ 40 * 8321810 * 2
def baseEnd_8321810 : Nat := 4273088445392191113803699

theorem tailTrace_8321810 : CollatzResearch.WordTrace tailWord_8321810 prefixEnd_8321810 4273088445392191113803699 := by
  unfold tailWord_8321810
  simp only [CollatzResearch.WordTrace]
  refine ⟨75880336495377774210364721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202347563987674064560972589 75880336495377774210364721)
  ·
    refine ⟨56910252371533330657773541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75880336495377774210364721 56910252371533330657773541)
    ·
      refine ⟨10670672319662499498332539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56910252371533330657773541 10670672319662499498332539)
      ·
        refine ⟨16006008479493749247498809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10670672319662499498332539 16006008479493749247498809)
        ·
          refine ⟨12004506359620311935624107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16006008479493749247498809 12004506359620311935624107)
          ·
            refine ⟨18006759539430467903436161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004506359620311935624107 18006759539430467903436161)
            ·
              refine ⟨13505069654572850927577121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18006759539430467903436161 13505069654572850927577121)
              ·
                refine ⟨10128802240929638195682841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13505069654572850927577121 10128802240929638195682841)
                ·
                  refine ⟨7596601680697228646762131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128802240929638195682841 7596601680697228646762131)
                  ·
                    refine ⟨11394902521045842970143197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596601680697228646762131 11394902521045842970143197)
                    ·
                      refine ⟨4273088445392191113803699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11394902521045842970143197 4273088445392191113803699)
                      ·
                        rfl

theorem cell23_8321810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_8321810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321810 prefixEnd_8321810 := by exact prefixLift 8321810
  have htrace : WordTrace (prefixWord ++ tailWord_8321810) baseStart_8321810 baseEnd_8321810 := by
    simpa [prefixWord, tailWord_8321810, baseEnd_8321810] using wordTrace_append hprefix tailTrace_8321810
  have hstable : (prefixWord ++ tailWord_8321810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321810).length < 2 ^ (prefixWord ++ tailWord_8321810).sum := by decide
  have hdescent : baseEnd_8321810 < baseStart_8321810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321889 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_8321889 : Nat := 118140960795 + 8321889 * 2 ^ 59
def prefixEnd_8321889 : Nat := 4983230072969 + 3 ^ 40 * 8321889 * 2
def baseEnd_8321889 : Nat := 4273129010363896304715835

theorem tailTrace_8321889 : CollatzResearch.WordTrace tailWord_8321889 prefixEnd_8321889 4273129010363896304715835 := by
  unfold tailWord_8321889
  simp only [CollatzResearch.WordTrace]
  refine ⟨303524227348224893333584721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202349484898816595555723147 303524227348224893333584721)
  ·
    refine ⟨227643170511168670000188541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303524227348224893333584721 227643170511168670000188541)
    ·
      refine ⟨85366188941688251250070703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227643170511168670000188541 85366188941688251250070703)
      ·
        refine ⟨128049283412532376875106055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85366188941688251250070703 128049283412532376875106055)
        ·
          refine ⟨192073925118798565312659083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128049283412532376875106055 192073925118798565312659083)
          ·
            refine ⟨288110887678197847968988625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192073925118798565312659083 288110887678197847968988625)
            ·
              refine ⟨216083165758648385976741469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288110887678197847968988625 216083165758648385976741469)
              ·
                refine ⟨81031187159493144741278051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216083165758648385976741469 81031187159493144741278051)
                ·
                  refine ⟨121546780739239717111917077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81031187159493144741278051 121546780739239717111917077)
                  ·
                    refine ⟨5697505347151861739621113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121546780739239717111917077 5697505347151861739621113)
                    ·
                      refine ⟨4273129010363896304715835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697505347151861739621113 4273129010363896304715835)
                      ·
                        rfl

theorem cell23_8321889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_8321889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321889 prefixEnd_8321889 := by exact prefixLift 8321889
  have htrace : WordTrace (prefixWord ++ tailWord_8321889) baseStart_8321889 baseEnd_8321889 := by
    simpa [prefixWord, tailWord_8321889, baseEnd_8321889] using wordTrace_append hprefix tailTrace_8321889
  have hstable : (prefixWord ++ tailWord_8321889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321889).length < 2 ^ (prefixWord ++ tailWord_8321889).sum := by decide
  have hdescent : baseEnd_8321889 < baseStart_8321889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321899 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 3, 4]
def baseStart_8321899 : Nat := 118140960795 + 8321899 * 2 ^ 59
def prefixEnd_8321899 : Nat := 4983230072969 + 3 ^ 40 * 8321899 * 2
def baseEnd_8321899 : Nat := 1424378048390147088530263

theorem tailTrace_8321899 : CollatzResearch.WordTrace tailWord_8321899 prefixEnd_8321899 1424378048390147088530263 := by
  unfold tailWord_8321899
  simp only [CollatzResearch.WordTrace]
  refine ⟨303524592078188665041448751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202349728052125776694299167 303524592078188665041448751)
  ·
    refine ⟨455286888117282997562173127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303524592078188665041448751 455286888117282997562173127)
    ·
      refine ⟨682930332175924496343259691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455286888117282997562173127 682930332175924496343259691)
      ·
        refine ⟨1024395498263886744514889537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682930332175924496343259691 1024395498263886744514889537)
        ·
          refine ⟨768296623697915058386167153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024395498263886744514889537 768296623697915058386167153)
          ·
            refine ⟨576222467773436293789625365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768296623697915058386167153 576222467773436293789625365)
            ·
              refine ⟨27010428176879826271388689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 576222467773436293789625365 27010428176879826271388689)
              ·
                refine ⟨20257821132659869703541517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27010428176879826271388689 20257821132659869703541517)
                ·
                  refine ⟨7596682924747451138828069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20257821132659869703541517 7596682924747451138828069)
                  ·
                    refine ⟨1424378048390147088530263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596682924747451138828069 1424378048390147088530263)
                    ·
                      rfl

theorem cell23_8321899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 4].length) (baseStart_8321899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321899 prefixEnd_8321899 := by exact prefixLift 8321899
  have htrace : WordTrace (prefixWord ++ tailWord_8321899) baseStart_8321899 baseEnd_8321899 := by
    simpa [prefixWord, tailWord_8321899, baseEnd_8321899] using wordTrace_append hprefix tailTrace_8321899
  have hstable : (prefixWord ++ tailWord_8321899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321899).length < 2 ^ (prefixWord ++ tailWord_8321899).sum := by decide
  have hdescent : baseEnd_8321899 < baseStart_8321899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321932 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_8321932 : Nat := 118140960795 + 8321932 * 2 ^ 59
def prefixEnd_8321932 : Nat := 4983230072969 + 3 ^ 40 * 8321932 * 2
def baseEnd_8321932 : Nat := 4273151090032039636478137

theorem tailTrace_8321932 : CollatzResearch.WordTrace tailWord_8321932 prefixEnd_8321932 4273151090032039636478137 := by
  unfold tailWord_8321932
  simp only [CollatzResearch.WordTrace]
  refine ⟨151762897843534555838700025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202350530458046074451600033 151762897843534555838700025)
  ·
    refine ⟨113822173382650916879025019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151762897843534555838700025 113822173382650916879025019)
    ·
      refine ⟨170733260073976375318537529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113822173382650916879025019 170733260073976375318537529)
      ·
        refine ⟨128049945055482281488903147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170733260073976375318537529 128049945055482281488903147)
        ·
          refine ⟨192074917583223422233354721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128049945055482281488903147 192074917583223422233354721)
          ·
            refine ⟨144056188187417566675016041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192074917583223422233354721 144056188187417566675016041)
            ·
              refine ⟨108042141140563175006262031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144056188187417566675016041 108042141140563175006262031)
              ·
                refine ⟨162063211710844762509393047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108042141140563175006262031 162063211710844762509393047)
                ·
                  refine ⟨243094817566267143764089571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162063211710844762509393047 243094817566267143764089571)
                  ·
                    refine ⟨364642226349400715646134357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243094817566267143764089571 364642226349400715646134357)
                    ·
                      refine ⟨4273151090032039636478137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 364642226349400715646134357 4273151090032039636478137)
                      ·
                        rfl

theorem cell23_8321932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_8321932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321932 prefixEnd_8321932 := by exact prefixLift 8321932
  have htrace : WordTrace (prefixWord ++ tailWord_8321932) baseStart_8321932 baseEnd_8321932 := by
    simpa [prefixWord, tailWord_8321932, baseEnd_8321932] using wordTrace_append hprefix tailTrace_8321932
  have hstable : (prefixWord ++ tailWord_8321932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321932).length < 2 ^ (prefixWord ++ tailWord_8321932).sum := by decide
  have hdescent : baseEnd_8321932 < baseStart_8321932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321946 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_8321946 : Nat := 118140960795 + 8321946 * 2 ^ 59
def prefixEnd_8321946 : Nat := 4983230072969 + 3 ^ 40 * 8321946 * 2
def baseEnd_8321946 : Nat := 474795364306800286855897

theorem tailTrace_8321946 : CollatzResearch.WordTrace tailWord_8321946 prefixEnd_8321946 474795364306800286855897 := by
  unfold tailWord_8321946
  simp only [CollatzResearch.WordTrace]
  refine ⟨75881576577254598017102423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202350870872678928045606461 75881576577254598017102423)
  ·
    refine ⟨113822364865881897025653635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75881576577254598017102423 113822364865881897025653635)
    ·
      refine ⟨170733547298822845538480453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113822364865881897025653635 170733547298822845538480453)
      ·
        refine ⟨32012540118529283538465085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170733547298822845538480453 32012540118529283538465085)
        ·
          refine ⟨12004702544448481326924407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32012540118529283538465085 12004702544448481326924407)
          ·
            refine ⟨18007053816672721990386611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004702544448481326924407 18007053816672721990386611)
            ·
              refine ⟨27010580725009082985579917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18007053816672721990386611 27010580725009082985579917)
              ·
                refine ⟨10128967771878406119592469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27010580725009082985579917 10128967771878406119592469)
                ·
                  refine ⟨474795364306800286855897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10128967771878406119592469 474795364306800286855897)
                  ·
                    rfl

theorem cell23_8321946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_8321946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321946 prefixEnd_8321946 := by exact prefixLift 8321946
  have htrace : WordTrace (prefixWord ++ tailWord_8321946) baseStart_8321946 baseEnd_8321946 := by
    simpa [prefixWord, tailWord_8321946, baseEnd_8321946] using wordTrace_append hprefix tailTrace_8321946
  have hstable : (prefixWord ++ tailWord_8321946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321946).length < 2 ^ (prefixWord ++ tailWord_8321946).sum := by decide
  have hdescent : baseEnd_8321946 < baseStart_8321946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321956 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_8321956 : Nat := 118140960795 + 8321956 * 2 ^ 59
def prefixEnd_8321956 : Nat := 4983230072969 + 3 ^ 40 * 8321956 * 2
def baseEnd_8321956 : Nat := 4273163413567747542578027

theorem tailTrace_8321956 : CollatzResearch.WordTrace tailWord_8321956 prefixEnd_8321956 4273163413567747542578027 := by
  unfold tailWord_8321956
  simp only [CollatzResearch.WordTrace]
  refine ⟨151763335519491081888136861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202351114025988109184182481 151763335519491081888136861)
  ·
    refine ⟨56911250819809155708051323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151763335519491081888136861 56911250819809155708051323)
    ·
      refine ⟨85366876229713733562076985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56911250819809155708051323 85366876229713733562076985)
      ·
        refine ⟨64025157172285300171557739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85366876229713733562076985 64025157172285300171557739)
        ·
          refine ⟨96037735758427950257336609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64025157172285300171557739 96037735758427950257336609)
          ·
            refine ⟨72028301818820962693002457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96037735758427950257336609 72028301818820962693002457)
            ·
              refine ⟨54021226364115722019751843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72028301818820962693002457 54021226364115722019751843)
              ·
                refine ⟨81031839546173583029627765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54021226364115722019751843 81031839546173583029627765)
                ·
                  refine ⟨7596734957453773409027603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81031839546173583029627765 7596734957453773409027603)
                  ·
                    refine ⟨11395102436180660113541405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596734957453773409027603 11395102436180660113541405)
                    ·
                      refine ⟨4273163413567747542578027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11395102436180660113541405 4273163413567747542578027)
                      ·
                        rfl

theorem cell23_8321956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_8321956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321956 prefixEnd_8321956 := by exact prefixLift 8321956
  have htrace : WordTrace (prefixWord ++ tailWord_8321956) baseStart_8321956 baseEnd_8321956 := by
    simpa [prefixWord, tailWord_8321956, baseEnd_8321956] using wordTrace_append hprefix tailTrace_8321956
  have hstable : (prefixWord ++ tailWord_8321956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321956).length < 2 ^ (prefixWord ++ tailWord_8321956).sum := by decide
  have hdescent : baseEnd_8321956 < baseStart_8321956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8321989 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_8321989 : Nat := 118140960795 + 8321989 * 2 ^ 59
def prefixEnd_8321989 : Nat := 4983230072969 + 3 ^ 40 * 8321989 * 2
def baseEnd_8321989 : Nat := 1424393452809781971155125

theorem tailTrace_8321989 : CollatzResearch.WordTrace tailWord_8321989 prefixEnd_8321989 1424393452809781971155125 := by
  unfold tailWord_8321989
  simp only [CollatzResearch.WordTrace]
  refine ⟨303527874647862610412225021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202351916431908406941483347 303527874647862610412225021)
  ·
    refine ⟨113822952992948478904584383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303527874647862610412225021 113822952992948478904584383)
    ·
      refine ⟨170734429489422718356876575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113822952992948478904584383 170734429489422718356876575)
      ·
        refine ⟨256101644234134077535314863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170734429489422718356876575 256101644234134077535314863)
        ·
          refine ⟨384152466351201116302972295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256101644234134077535314863 384152466351201116302972295)
          ·
            refine ⟨576228699526801674454458443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384152466351201116302972295 576228699526801674454458443)
            ·
              refine ⟨864343049290202511681687665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576228699526801674454458443 864343049290202511681687665)
              ·
                refine ⟨648257286967651883761265749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864343049290202511681687665 648257286967651883761265749)
                ·
                  refine ⟨7596765081652170512827333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 648257286967651883761265749 7596765081652170512827333)
                  ·
                    refine ⟨1424393452809781971155125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596765081652170512827333 1424393452809781971155125)
                    ·
                      rfl

theorem cell23_8321989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_8321989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8321989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8321989 prefixEnd_8321989 := by exact prefixLift 8321989
  have htrace : WordTrace (prefixWord ++ tailWord_8321989) baseStart_8321989 baseEnd_8321989 := by
    simpa [prefixWord, tailWord_8321989, baseEnd_8321989] using wordTrace_append hprefix tailTrace_8321989
  have hstable : (prefixWord ++ tailWord_8321989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8321989).length < 2 ^ (prefixWord ++ tailWord_8321989).sum := by decide
  have hdescent : baseEnd_8321989 < baseStart_8321989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8321989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322026 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_8322026 : Nat := 118140960795 + 8322026 * 2 ^ 59
def prefixEnd_8322026 : Nat := 4983230072969 + 3 ^ 40 * 8322026 * 2
def baseEnd_8322026 : Nat := 4273199357213562268702705

theorem tailTrace_8322026 : CollatzResearch.WordTrace tailWord_8322026 prefixEnd_8322026 4273199357213562268702705 := by
  unfold tailWord_8322026
  simp only [CollatzResearch.WordTrace]
  refine ⟨75882306037182141432830483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202352816099152377154214621 75882306037182141432830483)
  ·
    refine ⟨113823459055773212149245725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75882306037182141432830483 113823459055773212149245725)
    ·
      refine ⟨42683797145914954555967147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113823459055773212149245725 42683797145914954555967147)
      ·
        refine ⟨64025695718872431833950721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42683797145914954555967147 64025695718872431833950721)
        ·
          refine ⟨48019271789154323875463041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64025695718872431833950721 48019271789154323875463041)
          ·
            refine ⟨36014453841865742906597281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48019271789154323875463041 36014453841865742906597281)
            ·
              refine ⟨27010840381399307179947961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36014453841865742906597281 27010840381399307179947961)
              ·
                refine ⟨20258130286049480384960971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27010840381399307179947961 20258130286049480384960971)
                ·
                  refine ⟨30387195429074220577441457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20258130286049480384960971 30387195429074220577441457)
                  ·
                    refine ⟨22790396571805665433081093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30387195429074220577441457 22790396571805665433081093)
                    ·
                      refine ⟨4273199357213562268702705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22790396571805665433081093 4273199357213562268702705)
                      ·
                        rfl

theorem cell23_8322026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_8322026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322026 prefixEnd_8322026 := by exact prefixLift 8322026
  have htrace : WordTrace (prefixWord ++ tailWord_8322026) baseStart_8322026 baseEnd_8322026 := by
    simpa [prefixWord, tailWord_8322026, baseEnd_8322026] using wordTrace_append hprefix tailTrace_8322026
  have hstable : (prefixWord ++ tailWord_8322026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322026).length < 2 ^ (prefixWord ++ tailWord_8322026).sum := by decide
  have hdescent : baseEnd_8322026 < baseStart_8322026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322033 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_8322033 : Nat := 118140960795 + 8322033 * 2 ^ 59
def prefixEnd_8322033 : Nat := 4983230072969 + 3 ^ 40 * 8322033 * 2
def baseEnd_8322033 : Nat := 4273202951578143741315173

theorem tailTrace_8322033 : CollatzResearch.WordTrace tailWord_8322033 prefixEnd_8322033 4273202951578143741315173 := by
  unfold tailWord_8322033
  simp only [CollatzResearch.WordTrace]
  refine ⟨303529479459703205926826753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202352986306468803951217835 303529479459703205926826753)
  ·
    refine ⟨227647109594777404445120065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303529479459703205926826753 227647109594777404445120065)
    ·
      refine ⟨170735332196083053333840049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227647109594777404445120065 170735332196083053333840049)
      ·
        refine ⟨128051499147062290000380037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170735332196083053333840049 128051499147062290000380037)
        ·
          refine ⟨24009656090074179375071257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128051499147062290000380037 24009656090074179375071257)
          ·
            refine ⟨18007242067555634531303443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24009656090074179375071257 18007242067555634531303443)
            ·
              refine ⟨27010863101333451796955165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18007242067555634531303443 27010863101333451796955165)
              ·
                refine ⟨10129073663000044423858187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27010863101333451796955165 10129073663000044423858187)
                ·
                  refine ⟨15193610494500066635787281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10129073663000044423858187 15193610494500066635787281)
                  ·
                    refine ⟨11395207870875049976840461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15193610494500066635787281 11395207870875049976840461)
                    ·
                      refine ⟨4273202951578143741315173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11395207870875049976840461 4273202951578143741315173)
                      ·
                        rfl

theorem cell23_8322033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_8322033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322033 prefixEnd_8322033 := by exact prefixLift 8322033
  have htrace : WordTrace (prefixWord ++ tailWord_8322033) baseStart_8322033 baseEnd_8322033 := by
    simpa [prefixWord, tailWord_8322033, baseEnd_8322033] using wordTrace_append hprefix tailTrace_8322033
  have hstable : (prefixWord ++ tailWord_8322033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322033).length < 2 ^ (prefixWord ++ tailWord_8322033).sum := by decide
  have hdescent : baseEnd_8322033 < baseStart_8322033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322050 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_8322050 : Nat := 118140960795 + 8322050 * 2 ^ 59
def prefixEnd_8322050 : Nat := 4983230072969 + 3 ^ 40 * 8322050 * 2
def baseEnd_8322050 : Nat := 4273211680749270174802595

theorem tailTrace_8322050 : CollatzResearch.WordTrace tailWord_8322050 prefixEnd_8322050 4273211680749270174802595 := by
  unfold tailWord_8322050
  simp only [CollatzResearch.WordTrace]
  refine ⟨75882524875160404457548901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202353399667094411886797069 75882524875160404457548901)
  ·
    refine ⟨14227973414092575835790419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75882524875160404457548901 14227973414092575835790419)
    ·
      refine ⟨21341960121138863753685629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14227973414092575835790419 21341960121138863753685629)
      ·
        refine ⟨8003235045427073907632111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21341960121138863753685629 8003235045427073907632111)
        ·
          refine ⟨12004852568140610861448167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003235045427073907632111 12004852568140610861448167)
          ·
            refine ⟨18007278852210916292172251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004852568140610861448167 18007278852210916292172251)
            ·
              refine ⟨27010918278316374438258377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18007278852210916292172251 27010918278316374438258377)
              ·
                refine ⟨20258188708737280828693783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27010918278316374438258377 20258188708737280828693783)
                ·
                  refine ⟨30387283063105921243040675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20258188708737280828693783 30387283063105921243040675)
                  ·
                    refine ⟨45580924594658881864561013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30387283063105921243040675 45580924594658881864561013)
                    ·
                      refine ⟨4273211680749270174802595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45580924594658881864561013 4273211680749270174802595)
                      ·
                        rfl

theorem cell23_8322050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_8322050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322050 prefixEnd_8322050 := by exact prefixLift 8322050
  have htrace : WordTrace (prefixWord ++ tailWord_8322050) baseStart_8322050 baseEnd_8322050 := by
    simpa [prefixWord, tailWord_8322050, baseEnd_8322050] using wordTrace_append hprefix tailTrace_8322050
  have hstable : (prefixWord ++ tailWord_8322050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322050).length < 2 ^ (prefixWord ++ tailWord_8322050).sum := by decide
  have hdescent : baseEnd_8322050 < baseStart_8322050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322073 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 1, 3, 2]
def baseStart_8322073 : Nat := 118140960795 + 8322073 * 2 ^ 59
def prefixEnd_8322073 : Nat := 4983230072969 + 3 ^ 40 * 8322073 * 2
def baseEnd_8322073 : Nat := 4273223490804323584814989

theorem tailTrace_8322073 : CollatzResearch.WordTrace tailWord_8322073 prefixEnd_8322073 4273223490804323584814989 := by
  unfold tailWord_8322073
  simp only [CollatzResearch.WordTrace]
  refine ⟨303530938379558292758282873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202353958919705528505521915 303530938379558292758282873)
  ·
    refine ⟨227648203784668719568712155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303530938379558292758282873 227648203784668719568712155)
    ·
      refine ⟨341472305677003079353068233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227648203784668719568712155 341472305677003079353068233)
      ·
        refine ⟨256104229257752309514801175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341472305677003079353068233 256104229257752309514801175)
        ·
          refine ⟨384156343886628464272201763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256104229257752309514801175 384156343886628464272201763)
          ·
            refine ⟨576234515829942696408302645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384156343886628464272201763 576234515829942696408302645)
            ·
              refine ⟨54021985859057127788278373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 576234515829942696408302645 54021985859057127788278373)
              ·
                refine ⟨10129122348573211460302195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54021985859057127788278373 10129122348573211460302195)
                ·
                  refine ⟨15193683522859817190453293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10129122348573211460302195 15193683522859817190453293)
                  ·
                    refine ⟨5697631321072431446419985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15193683522859817190453293 5697631321072431446419985)
                    ·
                      refine ⟨4273223490804323584814989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697631321072431446419985 4273223490804323584814989)
                      ·
                        rfl

theorem cell23_8322073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_8322073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322073 prefixEnd_8322073 := by exact prefixLift 8322073
  have htrace : WordTrace (prefixWord ++ tailWord_8322073) baseStart_8322073 baseEnd_8322073 := by
    simpa [prefixWord, tailWord_8322073, baseEnd_8322073] using wordTrace_append hprefix tailTrace_8322073
  have hstable : (prefixWord ++ tailWord_8322073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322073).length < 2 ^ (prefixWord ++ tailWord_8322073).sum := by decide
  have hdescent : baseEnd_8322073 < baseStart_8322073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322120 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_8322120 : Nat := 118140960795 + 8322120 * 2 ^ 59
def prefixEnd_8322120 : Nat := 4983230072969 + 3 ^ 40 * 8322120 * 2
def baseEnd_8322120 : Nat := 4273247624395084900927273

theorem tailTrace_8322120 : CollatzResearch.WordTrace tailWord_8322120 prefixEnd_8322120 4273247624395084900927273 := by
  unfold tailWord_8322120
  simp only [CollatzResearch.WordTrace]
  refine ⟨151766326305194009892621907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202355101740258679856829209 151766326305194009892621907)
  ·
    refine ⟨227649489457791014838932861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151766326305194009892621907 227649489457791014838932861)
    ·
      refine ⟨85368558546671630564599823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227649489457791014838932861 85368558546671630564599823)
      ·
        refine ⟨128052837820007445846899735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85368558546671630564599823 128052837820007445846899735)
        ·
          refine ⟨192079256730011168770349603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128052837820007445846899735 192079256730011168770349603)
          ·
            refine ⟨288118885095016753155524405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192079256730011168770349603 288118885095016753155524405)
            ·
              refine ⟨27011145477657820608330413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288118885095016753155524405 27011145477657820608330413)
              ·
                refine ⟨10129179554121682728123905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27011145477657820608330413 10129179554121682728123905)
                ·
                  refine ⟨7596884665591262046092929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10129179554121682728123905 7596884665591262046092929)
                  ·
                    refine ⟨5697663499193446534569697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7596884665591262046092929 5697663499193446534569697)
                    ·
                      refine ⟨4273247624395084900927273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5697663499193446534569697 4273247624395084900927273)
                      ·
                        rfl

theorem cell23_8322120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_8322120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322120 prefixEnd_8322120 := by exact prefixLift 8322120
  have htrace : WordTrace (prefixWord ++ tailWord_8322120) baseStart_8322120 baseEnd_8322120 := by
    simpa [prefixWord, tailWord_8322120, baseEnd_8322120] using wordTrace_append hprefix tailTrace_8322120
  have hstable : (prefixWord ++ tailWord_8322120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322120).length < 2 ^ (prefixWord ++ tailWord_8322120).sum := by decide
  have hdescent : baseEnd_8322120 < baseStart_8322120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322156 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_8322156 : Nat := 118140960795 + 8322156 * 2 ^ 59
def prefixEnd_8322156 : Nat := 4983230072969 + 3 ^ 40 * 8322156 * 2
def baseEnd_8322156 : Nat := 1424422036566215586692369

theorem tailTrace_8322156 : CollatzResearch.WordTrace tailWord_8322156 prefixEnd_8322156 1424422036566215586692369 := by
  unfold tailWord_8322156
  simp only [CollatzResearch.WordTrace]
  refine ⟨151766982819128798966777161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202355977092171731955702881 151766982819128798966777161)
  ·
    refine ⟨113825237114346599225082871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151766982819128798966777161 113825237114346599225082871)
    ·
      refine ⟨170737855671519898837624307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113825237114346599225082871 170737855671519898837624307)
      ·
        refine ⟨256106783507279848256436461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170737855671519898837624307 256106783507279848256436461)
        ·
          refine ⟨96040043815229943096163673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256106783507279848256436461 96040043815229943096163673)
          ·
            refine ⟨72030032861422457322122755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96040043815229943096163673 72030032861422457322122755)
            ·
              refine ⟨108045049292133685983184133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72030032861422457322122755 108045049292133685983184133)
              ·
                refine ⟨20258446742275066121847025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108045049292133685983184133 20258446742275066121847025)
                ·
                  refine ⟨15193835056706299591385269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20258446742275066121847025 15193835056706299591385269)
                  ·
                    refine ⟨1424422036566215586692369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15193835056706299591385269 1424422036566215586692369)
                    ·
                      rfl

theorem cell23_8322156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_8322156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322156 prefixEnd_8322156 := by exact prefixLift 8322156
  have htrace : WordTrace (prefixWord ++ tailWord_8322156) baseStart_8322156 baseEnd_8322156 := by
    simpa [prefixWord, tailWord_8322156, baseEnd_8322156] using wordTrace_append hprefix tailTrace_8322156
  have hstable : (prefixWord ++ tailWord_8322156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322156).length < 2 ^ (prefixWord ++ tailWord_8322156).sum := by decide
  have hdescent : baseEnd_8322156 < baseStart_8322156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322176 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_8322176 : Nat := 118140960795 + 8322176 * 2 ^ 59
def prefixEnd_8322176 : Nat := 4983230072969 + 3 ^ 40 * 8322176 * 2
def baseEnd_8322176 : Nat := 4273276379311736681827015

theorem tailTrace_8322176 : CollatzResearch.WordTrace tailWord_8322176 prefixEnd_8322176 4273276379311736681827015 := by
  unfold tailWord_8322176
  simp only [CollatzResearch.WordTrace]
  refine ⟨151767347549092570674641191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202356463398790094232854921 151767347549092570674641191)
  ·
    refine ⟨227651021323638856011961787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151767347549092570674641191 227651021323638856011961787)
    ·
      refine ⟨341476531985458284017942681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227651021323638856011961787 341476531985458284017942681)
      ·
        refine ⟨256107398989093713013457011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341476531985458284017942681 256107398989093713013457011)
        ·
          refine ⟨384161098483640569520185517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256107398989093713013457011 384161098483640569520185517)
          ·
            refine ⟨144060411931365213570069569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384161098483640569520185517 144060411931365213570069569)
            ·
              refine ⟨108045308948523910177552177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144060411931365213570069569 108045308948523910177552177)
              ·
                refine ⟨81033981711392932633164133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108045308948523910177552177 81033981711392932633164133)
                ·
                  refine ⟨15193871570886174868718275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81033981711392932633164133 15193871570886174868718275)
                  ·
                    refine ⟨22790807356329262303077413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15193871570886174868718275 22790807356329262303077413)
                    ·
                      refine ⟨4273276379311736681827015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22790807356329262303077413 4273276379311736681827015)
                      ·
                        rfl

theorem cell23_8322176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_8322176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322176 prefixEnd_8322176 := by exact prefixLift 8322176
  have htrace : WordTrace (prefixWord ++ tailWord_8322176) baseStart_8322176 baseEnd_8322176 := by
    simpa [prefixWord, tailWord_8322176, baseEnd_8322176] using wordTrace_append hprefix tailTrace_8322176
  have hstable : (prefixWord ++ tailWord_8322176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322176).length < 2 ^ (prefixWord ++ tailWord_8322176).sum := by decide
  have hdescent : baseEnd_8322176 < baseStart_8322176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322190 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_8322190 : Nat := 118140960795 + 8322190 * 2 ^ 59
def prefixEnd_8322190 : Nat := 4983230072969 + 3 ^ 40 * 8322190 * 2
def baseEnd_8322190 : Nat := 1424427856013633209017317

theorem tailTrace_8322190 : CollatzResearch.WordTrace tailWord_8322190 prefixEnd_8322190 1424427856013633209017317 := by
  unfold tailWord_8322190
  simp only [CollatzResearch.WordTrace]
  refine ⟨37941900715016802717536503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202356803813422947826861349 37941900715016802717536503)
  ·
    refine ⟨56912851072525204076304755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37941900715016802717536503 56912851072525204076304755)
    ·
      refine ⟨85369276608787806114457133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56912851072525204076304755 85369276608787806114457133)
      ·
        refine ⟨32013478728295427292921425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85369276608787806114457133 32013478728295427292921425)
        ·
          refine ⟨24010109046221570469691069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32013478728295427292921425 24010109046221570469691069)
          ·
            refine ⟨9003790892333088926134151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24010109046221570469691069 9003790892333088926134151)
            ·
              refine ⟨13505686338499633389201227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9003790892333088926134151 13505686338499633389201227)
              ·
                refine ⟨20258529507749450083801841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13505686338499633389201227 20258529507749450083801841)
                ·
                  refine ⟨15193897130812087562851381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20258529507749450083801841 15193897130812087562851381)
                  ·
                    refine ⟨1424427856013633209017317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15193897130812087562851381 1424427856013633209017317)
                    ·
                      rfl

theorem cell23_8322190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_8322190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322190 prefixEnd_8322190 := by exact prefixLift 8322190
  have htrace : WordTrace (prefixWord ++ tailWord_8322190) baseStart_8322190 baseEnd_8322190 := by
    simpa [prefixWord, tailWord_8322190, baseEnd_8322190] using wordTrace_append hprefix tailTrace_8322190
  have hstable : (prefixWord ++ tailWord_8322190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322190).length < 2 ^ (prefixWord ++ tailWord_8322190).sum := by decide
  have hdescent : baseEnd_8322190 < baseStart_8322190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322243 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 3]
def baseStart_8322243 : Nat := 118140960795 + 8322243 * 2 ^ 59
def prefixEnd_8322243 : Nat := 4983230072969 + 3 ^ 40 * 8322243 * 2
def baseEnd_8322243 : Nat := 4273310782515587919689207

theorem tailTrace_8322243 : CollatzResearch.WordTrace tailWord_8322243 prefixEnd_8322243 4273310782515587919689207 := by
  unfold tailWord_8322243
  simp only [CollatzResearch.WordTrace]
  refine ⟨303537138788942411791971383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202358092525961607861314255 303537138788942411791971383)
  ·
    refine ⟨455305708183413617687957075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303537138788942411791971383 455305708183413617687957075)
    ·
      refine ⟨682958562275120426531935613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455305708183413617687957075 682958562275120426531935613)
      ·
        refine ⟨256109460853170159949475855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682958562275120426531935613 256109460853170159949475855)
        ·
          refine ⟨384164191279755239924213783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256109460853170159949475855 384164191279755239924213783)
          ·
            refine ⟨576246286919632859886320675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384164191279755239924213783 576246286919632859886320675)
            ·
              refine ⟨864369430379449289829481013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576246286919632859886320675 864369430379449289829481013)
              ·
                refine ⟨81034634098073370921513845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 864369430379449289829481013 81034634098073370921513845)
                ·
                  refine ⟨7596996946694378523891923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81034634098073370921513845 7596996946694378523891923)
                  ·
                    refine ⟨11395495420041567785837885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596996946694378523891923 11395495420041567785837885)
                    ·
                      refine ⟨4273310782515587919689207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11395495420041567785837885 4273310782515587919689207)
                      ·
                        rfl

theorem cell23_8322243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_8322243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322243 prefixEnd_8322243 := by exact prefixLift 8322243
  have htrace : WordTrace (prefixWord ++ tailWord_8322243) baseStart_8322243 baseEnd_8322243 := by
    simpa [prefixWord, tailWord_8322243, baseEnd_8322243] using wordTrace_append hprefix tailTrace_8322243
  have hstable : (prefixWord ++ tailWord_8322243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322243).length < 2 ^ (prefixWord ++ tailWord_8322243).sum := by decide
  have hdescent : baseEnd_8322243 < baseStart_8322243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322254 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_8322254 : Nat := 118140960795 + 8322254 * 2 ^ 59
def prefixEnd_8322254 : Nat := 4983230072969 + 3 ^ 40 * 8322254 * 2
def baseEnd_8322254 : Nat := 1424438810267595792217219

theorem tailTrace_8322254 : CollatzResearch.WordTrace tailWord_8322254 prefixEnd_8322254 1424438810267595792217219 := by
  unfold tailWord_8322254
  simp only [CollatzResearch.WordTrace]
  refine ⟨37942192498987820083827727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202358359994601707113747877 37942192498987820083827727)
  ·
    refine ⟨56913288748481730125741591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37942192498987820083827727 56913288748481730125741591)
    ·
      refine ⟨85369933122722595188612387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56913288748481730125741591 85369933122722595188612387)
      ·
        refine ⟨128054899684083892782918581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85369933122722595188612387 128054899684083892782918581)
        ·
          refine ⟨12005146845382864948398617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128054899684083892782918581 12005146845382864948398617)
          ·
            refine ⟨9003860134037148711298963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12005146845382864948398617 9003860134037148711298963)
            ·
              refine ⟨13505790201055723066948445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9003860134037148711298963 13505790201055723066948445)
              ·
                refine ⟨5064671325395896150105667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13505790201055723066948445 5064671325395896150105667)
                ·
                  refine ⟨7597006988093844225158501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064671325395896150105667 7597006988093844225158501)
                  ·
                    refine ⟨1424438810267595792217219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597006988093844225158501 1424438810267595792217219)
                    ·
                      rfl

theorem cell23_8322254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_8322254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322254 prefixEnd_8322254 := by exact prefixLift 8322254
  have htrace : WordTrace (prefixWord ++ tailWord_8322254) baseStart_8322254 baseEnd_8322254 := by
    simpa [prefixWord, tailWord_8322254, baseEnd_8322254] using wordTrace_append hprefix tailTrace_8322254
  have hstable : (prefixWord ++ tailWord_8322254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322254).length < 2 ^ (prefixWord ++ tailWord_8322254).sum := by decide
  have hdescent : baseEnd_8322254 < baseStart_8322254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322263 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 1, 5]
def baseStart_8322263 : Nat := 118140960795 + 8322263 * 2 ^ 59
def prefixEnd_8322263 : Nat := 4983230072969 + 3 ^ 40 * 8322263 * 2
def baseEnd_8322263 : Nat := 1424440350709559280479705

theorem tailTrace_8322263 : CollatzResearch.WordTrace tailWord_8322263 prefixEnd_8322263 1424440350709559280479705 := by
  unfold tailWord_8322263
  simp only [CollatzResearch.WordTrace]
  refine ⟨303537868248869955207699443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202358578832579970138466295 303537868248869955207699443)
  ·
    refine ⟨455306802373304932811549165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303537868248869955207699443 455306802373304932811549165)
    ·
      refine ⟨170740050889989349804330937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455306802373304932811549165 170740050889989349804330937)
      ·
        refine ⟨128055038167492012353248203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170740050889989349804330937 128055038167492012353248203)
        ·
          refine ⟨192082557251238018529872305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128055038167492012353248203 192082557251238018529872305)
          ·
            refine ⟨144061917938428513897404229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192082557251238018529872305 144061917938428513897404229)
            ·
              refine ⟨27011609613455346355763293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144061917938428513897404229 27011609613455346355763293)
              ·
                refine ⟨10129353605045754883411235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27011609613455346355763293 10129353605045754883411235)
                ·
                  refine ⟨15194030407568632325116853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10129353605045754883411235 15194030407568632325116853)
                  ·
                    refine ⟨1424440350709559280479705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15194030407568632325116853 1424440350709559280479705)
                    ·
                      rfl

theorem cell23_8322263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_8322263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322263 prefixEnd_8322263 := by exact prefixLift 8322263
  have htrace : WordTrace (prefixWord ++ tailWord_8322263) baseStart_8322263 baseEnd_8322263 := by
    simpa [prefixWord, tailWord_8322263, baseEnd_8322263] using wordTrace_append hprefix tailTrace_8322263
  have hstable : (prefixWord ++ tailWord_8322263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322263).length < 2 ^ (prefixWord ++ tailWord_8322263).sum := by decide
  have hdescent : baseEnd_8322263 < baseStart_8322263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322300 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_8322300 : Nat := 118140960795 + 8322300 * 2 ^ 59
def prefixEnd_8322300 : Nat := 4983230072969 + 3 ^ 40 * 8322300 * 2
def baseEnd_8322300 : Nat := 4273340050912894196676445

theorem tailTrace_8322300 : CollatzResearch.WordTrace tailWord_8322300 prefixEnd_8322300 4273340050912894196676445 := by
  unfold tailWord_8322300
  simp only [CollatzResearch.WordTrace]
  refine ⟨151769608874867955263398177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202359478499823940351197569 151769608874867955263398177)
  ·
    refine ⟨113827206656150966447548633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151769608874867955263398177 113827206656150966447548633)
    ·
      refine ⟨85370404992113224835661475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113827206656150966447548633 85370404992113224835661475)
      ·
        refine ⟨128055607488169837253492213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85370404992113224835661475 128055607488169837253492213)
        ·
          refine ⟨12005213202015922242514895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128055607488169837253492213 12005213202015922242514895)
          ·
            refine ⟨18007819803023883363772343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12005213202015922242514895 18007819803023883363772343)
            ·
              refine ⟨27011729704535825045658515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18007819803023883363772343 27011729704535825045658515)
              ·
                refine ⟨40517594556803737568487773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27011729704535825045658515 40517594556803737568487773)
                ·
                  refine ⟨15194097958801401588182915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40517594556803737568487773 15194097958801401588182915)
                  ·
                    refine ⟨22791146938202102382274373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15194097958801401588182915 22791146938202102382274373)
                    ·
                      refine ⟨4273340050912894196676445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22791146938202102382274373 4273340050912894196676445)
                      ·
                        rfl

theorem cell23_8322300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_8322300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322300 prefixEnd_8322300 := by exact prefixLift 8322300
  have htrace : WordTrace (prefixWord ++ tailWord_8322300) baseStart_8322300 baseEnd_8322300 := by
    simpa [prefixWord, tailWord_8322300, baseEnd_8322300] using wordTrace_append hprefix tailTrace_8322300
  have hstable : (prefixWord ++ tailWord_8322300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322300).length < 2 ^ (prefixWord ++ tailWord_8322300).sum := by decide
  have hdescent : baseEnd_8322300 < baseStart_8322300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322313 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_8322313 : Nat := 118140960795 + 8322313 * 2 ^ 59
def prefixEnd_8322313 : Nat := 4983230072969 + 3 ^ 40 * 8322313 * 2
def baseEnd_8322313 : Nat := 4273346726161402645813885

theorem tailTrace_8322313 : CollatzResearch.WordTrace tailWord_8322313 prefixEnd_8322313 4273346726161402645813885 := by
  unfold tailWord_8322313
  simp only [CollatzResearch.WordTrace]
  refine ⟨303539691898688813747019593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202359794599125875831346395 303539691898688813747019593)
  ·
    refine ⟨227654768924016610310264695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303539691898688813747019593 227654768924016610310264695)
    ·
      refine ⟨341482153386024915465397043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227654768924016610310264695 341482153386024915465397043)
      ·
        refine ⟨512223230079037373198095565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341482153386024915465397043 512223230079037373198095565)
        ·
          refine ⟨192083711279639014949285837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512223230079037373198095565 192083711279639014949285837)
          ·
            refine ⟨72031391729864630605982189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192083711279639014949285837 72031391729864630605982189)
            ·
              refine ⟨27011771898699236477243321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72031391729864630605982189 27011771898699236477243321)
              ·
                refine ⟨20258828924024427357932491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27011771898699236477243321 20258828924024427357932491)
                ·
                  refine ⟨30388243386036641036898737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20258828924024427357932491 30388243386036641036898737)
                  ·
                    refine ⟨22791182539527480777674053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30388243386036641036898737 22791182539527480777674053)
                    ·
                      refine ⟨4273346726161402645813885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22791182539527480777674053 4273346726161402645813885)
                      ·
                        rfl

theorem cell23_8322313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_8322313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322313 prefixEnd_8322313 := by exact prefixLift 8322313
  have htrace : WordTrace (prefixWord ++ tailWord_8322313) baseStart_8322313 baseEnd_8322313 := by
    simpa [prefixWord, tailWord_8322313, baseEnd_8322313] using wordTrace_append hprefix tailTrace_8322313
  have hstable : (prefixWord ++ tailWord_8322313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322313).length < 2 ^ (prefixWord ++ tailWord_8322313).sum := by decide
  have hdescent : baseEnd_8322313 < baseStart_8322313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322393 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_8322393 : Nat := 118140960795 + 8322393 * 2 ^ 59
def prefixEnd_8322393 : Nat := 4983230072969 + 3 ^ 40 * 8322393 * 2
def baseEnd_8322393 : Nat := 4273387804613762332813517

theorem tailTrace_8322393 : CollatzResearch.WordTrace tailWord_8322393 prefixEnd_8322393 4273387804613762332813517 := by
  unfold tailWord_8322393
  simp only [CollatzResearch.WordTrace]
  refine ⟨303542609738398987409931833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202361739825599324939954555 303542609738398987409931833)
  ·
    refine ⟨227656957303799240557448875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303542609738398987409931833 227656957303799240557448875)
    ·
      refine ⟨341485435955698860836173313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227656957303799240557448875 341485435955698860836173313)
      ·
        refine ⟨256114076966774145627129985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341485435955698860836173313 256114076966774145627129985)
        ·
          refine ⟨192085557725080609220347489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256114076966774145627129985 192085557725080609220347489)
          ·
            refine ⟨144064168293810456915260617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192085557725080609220347489 144064168293810456915260617)
            ·
              refine ⟨108048126220357842686445463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144064168293810456915260617 108048126220357842686445463)
              ·
                refine ⟨162072189330536764029668195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108048126220357842686445463 162072189330536764029668195)
                ·
                  refine ⟨243108283995805146044502293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162072189330536764029668195 243108283995805146044502293)
                  ·
                    refine ⟨11395700812303366220836045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243108283995805146044502293 11395700812303366220836045)
                    ·
                      refine ⟨4273387804613762332813517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11395700812303366220836045 4273387804613762332813517)
                      ·
                        rfl

theorem cell23_8322393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_8322393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322393 prefixEnd_8322393 := by exact prefixLift 8322393
  have htrace : WordTrace (prefixWord ++ tailWord_8322393) baseStart_8322393 baseEnd_8322393 := by
    simpa [prefixWord, tailWord_8322393, baseEnd_8322393] using wordTrace_append hprefix tailTrace_8322393
  have hstable : (prefixWord ++ tailWord_8322393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322393).length < 2 ^ (prefixWord ++ tailWord_8322393).sum := by decide
  have hdescent : baseEnd_8322393 < baseStart_8322393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8322453 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_8322453 : Nat := 118140960795 + 8322453 * 2 ^ 59
def prefixEnd_8322453 : Nat := 4983230072969 + 3 ^ 40 * 8322453 * 2
def baseEnd_8322453 : Nat := 4273418613453032098063241

theorem tailTrace_8322453 : CollatzResearch.WordTrace tailWord_8322453 prefixEnd_8322453 4273418613453032098063241 := by
  unfold tailWord_8322453
  simp only [CollatzResearch.WordTrace]
  refine ⟨303544798118181617657116013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202363198745454411771410675 303544798118181617657116013)
  ·
    refine ⟨113829299294318106621418505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303544798118181617657116013 113829299294318106621418505)
    ·
      refine ⟨85371974470738579966063879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113829299294318106621418505 85371974470738579966063879)
      ·
        refine ⟨128057961706107869949095819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85371974470738579966063879 128057961706107869949095819)
        ·
          refine ⟨192086942559161804923643729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128057961706107869949095819 192086942559161804923643729)
          ·
            refine ⟨144065206919371353692732797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192086942559161804923643729 144065206919371353692732797)
            ·
              refine ⟨54024452594764257634774799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144065206919371353692732797 54024452594764257634774799)
              ·
                refine ⟨81036678892146386452162199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54024452594764257634774799 81036678892146386452162199)
                ·
                  refine ⟨121555018338219579678243299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81036678892146386452162199 121555018338219579678243299)
                  ·
                    refine ⟨182332527507329369517364949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121555018338219579678243299 182332527507329369517364949)
                    ·
                      refine ⟨4273418613453032098063241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182332527507329369517364949 4273418613453032098063241)
                      ·
                        rfl

theorem cell23_8322453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_8322453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8322453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8322453 prefixEnd_8322453 := by exact prefixLift 8322453
  have htrace : WordTrace (prefixWord ++ tailWord_8322453) baseStart_8322453 baseEnd_8322453 := by
    simpa [prefixWord, tailWord_8322453, baseEnd_8322453] using wordTrace_append hprefix tailTrace_8322453
  have hstable : (prefixWord ++ tailWord_8322453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8322453).length < 2 ^ (prefixWord ++ tailWord_8322453).sum := by decide
  have hdescent : baseEnd_8322453 < baseStart_8322453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8322453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
