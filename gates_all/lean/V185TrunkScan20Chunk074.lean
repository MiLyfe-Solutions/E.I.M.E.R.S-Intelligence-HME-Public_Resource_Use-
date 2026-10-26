import V185TrunkScan20Chunk073

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_451081 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 2]
def baseStart_451081 : Nat := 118140960795 + 451081 * 2 ^ 59
def prefixEnd_451081 : Nat := 4983230072969 + 3 ^ 40 * 451081 * 2
def baseEnd_451081 : Nat := 205885659654093224189353

theorem tailTrace_451081 : CollatzResearch.WordTrace tailWord_451081 prefixEnd_451081 205885659654093224189353 := by
  unfold tailWord_451081
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452275678818050346561097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10968183785878700231040731 16452275678818050346561097)
  ·
    refine ⟨12339206759113537759920823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16452275678818050346561097 12339206759113537759920823)
    ·
      refine ⟨18508810138670306639881235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339206759113537759920823 18508810138670306639881235)
      ·
        refine ⟨27763215208005459959821853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18508810138670306639881235 27763215208005459959821853)
        ·
          refine ⟨10411205703002047484933195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27763215208005459959821853 10411205703002047484933195)
          ·
            refine ⟨15616808554503071227399793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411205703002047484933195 15616808554503071227399793)
            ·
              refine ⟨11712606415877303420549845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15616808554503071227399793 11712606415877303420549845)
              ·
                refine ⟨274514212872124298919137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11712606415877303420549845 274514212872124298919137)
                ·
                  refine ⟨205885659654093224189353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274514212872124298919137 205885659654093224189353)
                  ·
                    rfl

theorem cell20_451081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_451081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451081 prefixEnd_451081 := by exact prefixLift 451081
  have htrace : WordTrace (prefixWord ++ tailWord_451081) baseStart_451081 baseEnd_451081 := by
    simpa [prefixWord, tailWord_451081, baseEnd_451081] using wordTrace_append hprefix tailTrace_451081
  have hstable : (prefixWord ++ tailWord_451081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451081).length < 2 ^ (prefixWord ++ tailWord_451081).sum := by decide
  have hdescent : baseEnd_451081 < baseStart_451081 := by decide
  rcases family_descends (prefixWord ++ tailWord_451081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451109 : List Nat := [1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_451109 : Nat := 118140960795 + 451109 * 2 ^ 59
def prefixEnd_451109 : Nat := 4983230072969 + 3 ^ 40 * 451109 * 2
def baseEnd_451109 : Nat := 68632813205683190418635

theorem tailTrace_451109 : CollatzResearch.WordTrace tailWord_451109 prefixEnd_451109 68632813205683190418635 := by
  unfold tailWord_451109
  simp only [CollatzResearch.WordTrace]
  refine ⟨16453296922716611128580381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10968864615144407419053587 16453296922716611128580381)
  ·
    refine ⟨6169986346018729173217643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16453296922716611128580381 6169986346018729173217643)
    ·
      refine ⟨9254979519028093759826465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169986346018729173217643 9254979519028093759826465)
      ·
        refine ⟨6941234639271070319869849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9254979519028093759826465 6941234639271070319869849)
        ·
          refine ⟨5205925979453302739902387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6941234639271070319869849 5205925979453302739902387)
          ·
            refine ⟨7808888969179954109853581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205925979453302739902387 7808888969179954109853581)
            ·
              refine ⟨2928333363442482791195093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808888969179954109853581 2928333363442482791195093)
              ·
                refine ⟨68632813205683190418635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2928333363442482791195093 68632813205683190418635)
                ·
                  rfl

theorem cell20_451109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_451109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451109 prefixEnd_451109 := by exact prefixLift 451109
  have htrace : WordTrace (prefixWord ++ tailWord_451109) baseStart_451109 baseEnd_451109 := by
    simpa [prefixWord, tailWord_451109, baseEnd_451109] using wordTrace_append hprefix tailTrace_451109
  have hstable : (prefixWord ++ tailWord_451109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451109).length < 2 ^ (prefixWord ++ tailWord_451109).sum := by decide
  have hdescent : baseEnd_451109 < baseStart_451109 := by decide
  rcases family_descends (prefixWord ++ tailWord_451109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451153 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 2]
def baseStart_451153 : Nat := 118140960795 + 451153 * 2 ^ 59
def prefixEnd_451153 : Nat := 4983230072969 + 3 ^ 40 * 451153 * 2
def baseEnd_451153 : Nat := 205918522415980973789059

theorem tailTrace_451153 : CollatzResearch.WordTrace tailWord_451153 prefixEnd_451153 205918522415980973789059 := by
  unfold tailWord_451153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16454901734557206643182113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10969934489704804428788075 16454901734557206643182113)
  ·
    refine ⟨12341176300917904982386585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16454901734557206643182113 12341176300917904982386585)
    ·
      refine ⟨9255882225688428736789939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12341176300917904982386585 9255882225688428736789939)
      ·
        refine ⟨13883823338532643105184909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255882225688428736789939 13883823338532643105184909)
        ·
          refine ⟨5206433751949741164444341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13883823338532643105184909 5206433751949741164444341)
          ·
            refine ⟨488103164245288234166657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5206433751949741164444341 488103164245288234166657)
            ·
              refine ⟨366077373183966175624993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488103164245288234166657 366077373183966175624993)
              ·
                refine ⟨274558029887974631718745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366077373183966175624993 274558029887974631718745)
                ·
                  refine ⟨205918522415980973789059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274558029887974631718745 205918522415980973789059)
                  ·
                    rfl

theorem cell20_451153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_451153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451153 prefixEnd_451153 := by exact prefixLift 451153
  have htrace : WordTrace (prefixWord ++ tailWord_451153) baseStart_451153 baseEnd_451153 := by
    simpa [prefixWord, tailWord_451153, baseEnd_451153] using wordTrace_append hprefix tailTrace_451153
  have hstable : (prefixWord ++ tailWord_451153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451153).length < 2 ^ (prefixWord ++ tailWord_451153).sum := by decide
  have hdescent : baseEnd_451153 < baseStart_451153 := by decide
  rcases family_descends (prefixWord ++ tailWord_451153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451171 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_451171 : Nat := 118140960795 + 451171 * 2 ^ 59
def prefixEnd_451171 : Nat := 4983230072969 + 3 ^ 40 * 451171 * 2
def baseEnd_451171 : Nat := 205926738106452911188985

theorem tailTrace_451171 : CollatzResearch.WordTrace tailWord_451171 prefixEnd_451171 205926738106452911188985 := by
  unfold tailWord_451171
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455558248491995717337367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10970372165661330478224911 16455558248491995717337367)
  ·
    refine ⟨24683337372737993576006051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16455558248491995717337367 24683337372737993576006051)
    ·
      refine ⟨37025006059106990364009077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24683337372737993576006051 37025006059106990364009077)
      ·
        refine ⟨3471094318041280346625851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37025006059106990364009077 3471094318041280346625851)
        ·
          refine ⟨5206641477061920519938777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471094318041280346625851 5206641477061920519938777)
          ·
            refine ⟨3904981107796440389954083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5206641477061920519938777 3904981107796440389954083)
            ·
              refine ⟨5857471661694660584931125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904981107796440389954083 5857471661694660584931125)
              ·
                refine ⟨549137968283874429837293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5857471661694660584931125 549137968283874429837293)
                ·
                  refine ⟨205926738106452911188985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549137968283874429837293 205926738106452911188985)
                  ·
                    rfl

theorem cell20_451171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_451171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451171 prefixEnd_451171 := by exact prefixLift 451171
  have htrace : WordTrace (prefixWord ++ tailWord_451171) baseStart_451171 baseEnd_451171 := by
    simpa [prefixWord, tailWord_451171, baseEnd_451171] using wordTrace_append hprefix tailTrace_451171
  have hstable : (prefixWord ++ tailWord_451171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451171).length < 2 ^ (prefixWord ++ tailWord_451171).sum := by decide
  have hdescent : baseEnd_451171 < baseStart_451171 := by decide
  rcases family_descends (prefixWord ++ tailWord_451171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451181 : List Nat := [1, 5, 1, 1, 3, 2, 3, 4]
def baseStart_451181 : Nat := 118140960795 + 451181 * 2 ^ 59
def prefixEnd_451181 : Nat := 4983230072969 + 3 ^ 40 * 451181 * 2
def baseEnd_451181 : Nat := 68643767459645773618537

theorem tailTrace_451181 : CollatzResearch.WordTrace tailWord_451181 prefixEnd_451181 68643767459645773618537 := by
  unfold tailWord_451181
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455922978455767425201397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10970615318970511616800931 16455922978455767425201397)
  ·
    refine ⟨1542742779230228196112631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16455922978455767425201397 1542742779230228196112631)
    ·
      refine ⟨2314114168845342294168947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542742779230228196112631 2314114168845342294168947)
      ·
        refine ⟨3471171253268013441253421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314114168845342294168947 3471171253268013441253421)
        ·
          refine ⟨1301689219975505040470033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3471171253268013441253421 1301689219975505040470033)
          ·
            refine ⟨976266914981628780352525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301689219975505040470033 976266914981628780352525)
            ·
              refine ⟨366100093118110792632197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 976266914981628780352525 366100093118110792632197)
              ·
                refine ⟨68643767459645773618537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366100093118110792632197 68643767459645773618537)
                ·
                  rfl

theorem cell20_451181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_451181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451181 prefixEnd_451181 := by exact prefixLift 451181
  have htrace : WordTrace (prefixWord ++ tailWord_451181) baseStart_451181 baseEnd_451181 := by
    simpa [prefixWord, tailWord_451181, baseEnd_451181] using wordTrace_append hprefix tailTrace_451181
  have hstable : (prefixWord ++ tailWord_451181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451181).length < 2 ^ (prefixWord ++ tailWord_451181).sum := by decide
  have hdescent : baseEnd_451181 < baseStart_451181 := by decide
  rcases family_descends (prefixWord ++ tailWord_451181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451192 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_451192 : Nat := 118140960795 + 451192 * 2 ^ 59
def prefixEnd_451192 : Nat := 4983230072969 + 3 ^ 40 * 451192 * 2
def baseEnd_451192 : Nat := 205936323078670171488899

theorem tailTrace_451192 : CollatzResearch.WordTrace tailWord_451192 prefixEnd_451192 205936323078670171488899 := by
  unfold tailWord_451192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8228162090707958151925915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10970882787610610869234553 8228162090707958151925915)
  ·
    refine ⟨12342243136061937227888873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8228162090707958151925915 12342243136061937227888873)
    ·
      refine ⟨9256682352046452920916655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12342243136061937227888873 9256682352046452920916655)
      ·
        refine ⟨13885023528069679381374983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256682352046452920916655 13885023528069679381374983)
        ·
          refine ⟨20827535292104519072062475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13885023528069679381374983 20827535292104519072062475)
          ·
            refine ⟨31241302938156778608093713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20827535292104519072062475 31241302938156778608093713)
            ·
              refine ⟨23430977203617583956070285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31241302938156778608093713 23430977203617583956070285)
              ·
                refine ⟨8786616451356593983526357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23430977203617583956070285 8786616451356593983526357)
                ·
                  refine ⟨205936323078670171488899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8786616451356593983526357 205936323078670171488899)
                  ·
                    rfl

theorem cell20_451192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_451192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451192 prefixEnd_451192 := by exact prefixLift 451192
  have htrace : WordTrace (prefixWord ++ tailWord_451192) baseStart_451192 baseEnd_451192 := by
    simpa [prefixWord, tailWord_451192, baseEnd_451192] using wordTrace_append hprefix tailTrace_451192
  have hstable : (prefixWord ++ tailWord_451192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451192).length < 2 ^ (prefixWord ++ tailWord_451192).sum := by decide
  have hdescent : baseEnd_451192 < baseStart_451192 := by decide
  rcases family_descends (prefixWord ++ tailWord_451192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451223 : List Nat := [1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_451223 : Nat := 118140960795 + 451223 * 2 ^ 59
def prefixEnd_451223 : Nat := 4983230072969 + 3 ^ 40 * 451223 * 2
def baseEnd_451223 : Nat := 68650157441123947151813

theorem tailTrace_451223 : CollatzResearch.WordTrace tailWord_451223 prefixEnd_451223 68650157441123947151813 := by
  unfold tailWord_451223
  simp only [CollatzResearch.WordTrace]
  refine ⟨16457454844303608598230323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10971636562869072398820215 16457454844303608598230323)
  ·
    refine ⟨24686182266455412897345485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16457454844303608598230323 24686182266455412897345485)
    ·
      refine ⟨9257318349920779836504557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24686182266455412897345485 9257318349920779836504557)
      ·
        refine ⟨3471494381220292438689209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9257318349920779836504557 3471494381220292438689209)
        ·
          refine ⟨2603620785915219329016907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3471494381220292438689209 2603620785915219329016907)
          ·
            refine ⟨3905431178872828993525361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603620785915219329016907 3905431178872828993525361)
            ·
              refine ⟨2929073384154621745144021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905431178872828993525361 2929073384154621745144021)
              ·
                refine ⟨68650157441123947151813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2929073384154621745144021 68650157441123947151813)
                ·
                  rfl

theorem cell20_451223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_451223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451223 prefixEnd_451223 := by exact prefixLift 451223
  have htrace : WordTrace (prefixWord ++ tailWord_451223) baseStart_451223 baseEnd_451223 := by
    simpa [prefixWord, tailWord_451223, baseEnd_451223] using wordTrace_append hprefix tailTrace_451223
  have hstable : (prefixWord ++ tailWord_451223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451223).length < 2 ^ (prefixWord ++ tailWord_451223).sum := by decide
  have hdescent : baseEnd_451223 < baseStart_451223 := by decide
  rcases family_descends (prefixWord ++ tailWord_451223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451246 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_451246 : Nat := 118140960795 + 451246 * 2 ^ 59
def prefixEnd_451246 : Nat := 4983230072969 + 3 ^ 40 * 451246 * 2
def baseEnd_451246 : Nat := 205960970150085983688679

theorem tailTrace_451246 : CollatzResearch.WordTrace tailWord_451246 prefixEnd_451246 205960970150085983688679 := by
  unfold tailWord_451246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057286715402535440789699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10972195815480189017545061 2057286715402535440789699)
  ·
    refine ⟨3085930073103803161184549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2057286715402535440789699 3085930073103803161184549)
    ·
      refine ⟨578611888706963092722103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3085930073103803161184549 578611888706963092722103)
      ·
        refine ⟨867917833060444639083155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578611888706963092722103 867917833060444639083155)
        ·
          refine ⟨1301876749590666958624733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867917833060444639083155 1301876749590666958624733)
          ·
            refine ⟨488203781096500109484275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1301876749590666958624733 488203781096500109484275)
            ·
              refine ⟨732305671644750164226413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488203781096500109484275 732305671644750164226413)
              ·
                refine ⟨274614626866781311584905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732305671644750164226413 274614626866781311584905)
                ·
                  refine ⟨205960970150085983688679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274614626866781311584905 205960970150085983688679)
                  ·
                    rfl

theorem cell20_451246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_451246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451246 prefixEnd_451246 := by exact prefixLift 451246
  have htrace : WordTrace (prefixWord ++ tailWord_451246) baseStart_451246 baseEnd_451246 := by
    simpa [prefixWord, tailWord_451246, baseEnd_451246] using wordTrace_append hprefix tailTrace_451246
  have hstable : (prefixWord ++ tailWord_451246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451246).length < 2 ^ (prefixWord ++ tailWord_451246).sum := by decide
  have hdescent : baseEnd_451246 < baseStart_451246 := by decide
  rcases family_descends (prefixWord ++ tailWord_451246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451261 : List Nat := [1, 4, 1, 2, 1, 3, 8]
def baseStart_451261 : Nat := 118140960795 + 451261 * 2 ^ 59
def prefixEnd_451261 : Nat := 4983230072969 + 3 ^ 40 * 451261 * 2
def baseEnd_451261 : Nat := 22885312950979177576513

theorem tailTrace_451261 : CollatzResearch.WordTrace tailWord_451261 prefixEnd_451261 22885312950979177576513 := by
  unfold tailWord_451261
  simp only [CollatzResearch.WordTrace]
  refine ⟨16458840818165941088113637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10972560545443960725409091 16458840818165941088113637)
  ·
    refine ⟨3086032653406113954021307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16458840818165941088113637 3086032653406113954021307)
    ·
      refine ⟨4629048980109170931031961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3086032653406113954021307 4629048980109170931031961)
      ·
        refine ⟨3471786735081878198273971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4629048980109170931031961 3471786735081878198273971)
        ·
          refine ⟨5207680102622817297410957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471786735081878198273971 5207680102622817297410957)
          ·
            refine ⟨1952880038483556486529109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5207680102622817297410957 1952880038483556486529109)
            ·
              refine ⟨22885312950979177576513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1952880038483556486529109 22885312950979177576513)
              ·
                rfl

theorem cell20_451261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_451261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451261 prefixEnd_451261 := by exact prefixLift 451261
  have htrace : WordTrace (prefixWord ++ tailWord_451261) baseStart_451261 baseEnd_451261 := by
    simpa [prefixWord, tailWord_451261, baseEnd_451261] using wordTrace_append hprefix tailTrace_451261
  have hstable : (prefixWord ++ tailWord_451261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451261).length < 2 ^ (prefixWord ++ tailWord_451261).sum := by decide
  have hdescent : baseEnd_451261 < baseStart_451261 := by decide
  rcases family_descends (prefixWord ++ tailWord_451261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451277 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 3]
def baseStart_451277 : Nat := 118140960795 + 451277 * 2 ^ 59
def prefixEnd_451277 : Nat := 4983230072969 + 3 ^ 40 * 451277 * 2
def baseEnd_451277 : Nat := 205975119394787653655219

theorem tailTrace_451277 : CollatzResearch.WordTrace tailWord_451277 prefixEnd_451277 205975119394787653655219 := by
  unfold tailWord_451277
  simp only [CollatzResearch.WordTrace]
  refine ⟨16459424386107975820696085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10972949590738650547130723 16459424386107975820696085)
  ·
    refine ⟨771535518098811366595129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16459424386107975820696085 771535518098811366595129)
    ·
      refine ⟨578651638574108524946347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 771535518098811366595129 578651638574108524946347)
      ·
        refine ⟨867977457861162787419521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578651638574108524946347 867977457861162787419521)
        ·
          refine ⟨650983093395872090564641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867977457861162787419521 650983093395872090564641)
          ·
            refine ⟨488237320046904067923481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650983093395872090564641 488237320046904067923481)
            ·
              refine ⟨366177990035178050942611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488237320046904067923481 366177990035178050942611)
              ·
                refine ⟨549266985052767076413917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366177990035178050942611 549266985052767076413917)
                ·
                  refine ⟨205975119394787653655219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549266985052767076413917 205975119394787653655219)
                  ·
                    rfl

theorem cell20_451277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_451277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451277 prefixEnd_451277 := by exact prefixLift 451277
  have htrace : WordTrace (prefixWord ++ tailWord_451277) baseStart_451277 baseEnd_451277 := by
    simpa [prefixWord, tailWord_451277, baseEnd_451277] using wordTrace_append hprefix tailTrace_451277
  have hstable : (prefixWord ++ tailWord_451277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451277).length < 2 ^ (prefixWord ++ tailWord_451277).sum := by decide
  have hdescent : baseEnd_451277 < baseStart_451277 := by decide
  rcases family_descends (prefixWord ++ tailWord_451277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451278 : List Nat := [4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_451278 : Nat := 118140960795 + 451278 * 2 ^ 59
def prefixEnd_451278 : Nat := 4983230072969 + 3 ^ 40 * 451278 * 2
def baseEnd_451278 : Nat := 68658525274012031540627

theorem tailTrace_451278 : CollatzResearch.WordTrace tailWord_451278 prefixEnd_451278 68658525274012031540627 := by
  unfold tailWord_451278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057432607388044123935311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10972973906069568660988325 2057432607388044123935311)
  ·
    refine ⟨3086148911082066185902967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2057432607388044123935311 3086148911082066185902967)
    ·
      refine ⟨4629223366623099278854451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3086148911082066185902967 4629223366623099278854451)
      ·
        refine ⟨6943835049934648918281677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629223366623099278854451 6943835049934648918281677)
        ·
          refine ⟨2603938143725493344355629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6943835049934648918281677 2603938143725493344355629)
          ·
            refine ⟨976476803897060004133361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2603938143725493344355629 976476803897060004133361)
            ·
              refine ⟨732357602922795003100021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976476803897060004133361 732357602922795003100021)
              ·
                refine ⟨68658525274012031540627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 732357602922795003100021 68658525274012031540627)
                ·
                  rfl

theorem cell20_451278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_451278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451278 prefixEnd_451278 := by exact prefixLift 451278
  have htrace : WordTrace (prefixWord ++ tailWord_451278) baseStart_451278 baseEnd_451278 := by
    simpa [prefixWord, tailWord_451278, baseEnd_451278] using wordTrace_append hprefix tailTrace_451278
  have hstable : (prefixWord ++ tailWord_451278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451278).length < 2 ^ (prefixWord ++ tailWord_451278).sum := by decide
  have hdescent : baseEnd_451278 < baseStart_451278 := by decide
  rcases family_descends (prefixWord ++ tailWord_451278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451337 : List Nat := [1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_451337 : Nat := 118140960795 + 451337 * 2 ^ 59
def prefixEnd_451337 : Nat := 4983230072969 + 3 ^ 40 * 451337 * 2
def baseEnd_451337 : Nat := 68667501676564703884991

theorem tailTrace_451337 : CollatzResearch.WordTrace tailWord_451337 prefixEnd_451337 68667501676564703884991 := by
  unfold tailWord_451337
  simp only [CollatzResearch.WordTrace]
  refine ⟨16461612765890606067880265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10974408510593737378586843 16461612765890606067880265)
  ·
    refine ⟨12346209574417954550910199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16461612765890606067880265 12346209574417954550910199)
    ·
      refine ⟨18519314361626931826365299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346209574417954550910199 18519314361626931826365299)
      ·
        refine ⟨27778971542440397739547949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18519314361626931826365299 27778971542440397739547949)
        ·
          refine ⟨10417114328415149152330481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27778971542440397739547949 10417114328415149152330481)
          ·
            refine ⟨7812835746311361864247861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10417114328415149152330481 7812835746311361864247861)
            ·
              refine ⟨732453351216690174773237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7812835746311361864247861 732453351216690174773237)
              ·
                refine ⟨68667501676564703884991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 732453351216690174773237 68667501676564703884991)
                ·
                  rfl

theorem cell20_451337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_451337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451337 prefixEnd_451337 := by exact prefixLift 451337
  have htrace : WordTrace (prefixWord ++ tailWord_451337) baseStart_451337 baseEnd_451337 := by
    simpa [prefixWord, tailWord_451337, baseEnd_451337] using wordTrace_append hprefix tailTrace_451337
  have hstable : (prefixWord ++ tailWord_451337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451337).length < 2 ^ (prefixWord ++ tailWord_451337).sum := by decide
  have hdescent : baseEnd_451337 < baseStart_451337 := by decide
  rcases family_descends (prefixWord ++ tailWord_451337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451354 : List Nat := [3, 1, 1, 3, 2, 1, 5, 4]
def baseStart_451354 : Nat := 118140960795 + 451354 * 2 ^ 59
def prefixEnd_451354 : Nat := 4983230072969 + 3 ^ 40 * 451354 * 2
def baseEnd_451354 : Nat := 68670088097639202696079

theorem tailTrace_451354 : CollatzResearch.WordTrace tailWord_451354 prefixEnd_451354 68670088097639202696079 := by
  unfold tailWord_451354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115558201707254492812279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10974821871219345314166077 4115558201707254492812279)
  ·
    refine ⟨6173337302560881739218419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4115558201707254492812279 6173337302560881739218419)
    ·
      refine ⟨9260005953841322608827629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6173337302560881739218419 9260005953841322608827629)
      ·
        refine ⟨3472502232690495978310361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9260005953841322608827629 3472502232690495978310361)
        ·
          refine ⟨2604376674517871983732771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472502232690495978310361 2604376674517871983732771)
          ·
            refine ⟨3906565011776807975599157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604376674517871983732771 3906565011776807975599157)
            ·
              refine ⟨366240469854075747712421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3906565011776807975599157 366240469854075747712421)
              ·
                refine ⟨68670088097639202696079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366240469854075747712421 68670088097639202696079)
                ·
                  rfl

theorem cell20_451354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_451354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451354 prefixEnd_451354 := by exact prefixLift 451354
  have htrace : WordTrace (prefixWord ++ tailWord_451354) baseStart_451354 baseEnd_451354 := by
    simpa [prefixWord, tailWord_451354, baseEnd_451354] using wordTrace_append hprefix tailTrace_451354
  have hstable : (prefixWord ++ tailWord_451354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451354).length < 2 ^ (prefixWord ++ tailWord_451354).sum := by decide
  have hdescent : baseEnd_451354 < baseStart_451354 := by decide
  rcases family_descends (prefixWord ++ tailWord_451354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451368 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_451368 : Nat := 118140960795 + 451368 * 2 ^ 59
def prefixEnd_451368 : Nat := 4983230072969 + 3 ^ 40 * 451368 * 2
def baseEnd_451368 : Nat := 206016654274395781621513

theorem tailTrace_451368 : CollatzResearch.WordTrace tailWord_451368 prefixEnd_451368 206016654274395781621513 := by
  unfold tailWord_451368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231371714389149181129379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10975162285852198908172505 8231371714389149181129379)
  ·
    refine ⟨12347057571583723771694069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8231371714389149181129379 12347057571583723771694069)
    ·
      refine ⟨1157536647335974103596319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12347057571583723771694069 1157536647335974103596319)
      ·
        refine ⟨1736304971003961155394479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157536647335974103596319 1736304971003961155394479)
        ·
          refine ⟨2604457456505941733091719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736304971003961155394479 2604457456505941733091719)
          ·
            refine ⟨3906686184758912599637579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604457456505941733091719 3906686184758912599637579)
            ·
              refine ⟨5860029277138368899456369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906686184758912599637579 5860029277138368899456369)
              ·
                refine ⟨4395021957853776674592277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860029277138368899456369 4395021957853776674592277)
                ·
                  refine ⟨206016654274395781621513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4395021957853776674592277 206016654274395781621513)
                  ·
                    rfl

theorem cell20_451368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_451368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451368 prefixEnd_451368 := by exact prefixLift 451368
  have htrace : WordTrace (prefixWord ++ tailWord_451368) baseStart_451368 baseEnd_451368 := by
    simpa [prefixWord, tailWord_451368, baseEnd_451368] using wordTrace_append hprefix tailTrace_451368
  have hstable : (prefixWord ++ tailWord_451368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451368).length < 2 ^ (prefixWord ++ tailWord_451368).sum := by decide
  have hdescent : baseEnd_451368 < baseStart_451368 := by decide
  rcases family_descends (prefixWord ++ tailWord_451368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451405 : List Nat := [1, 6, 1, 2, 3, 1, 2, 4]
def baseStart_451405 : Nat := 118140960795 + 451405 * 2 ^ 59
def prefixEnd_451405 : Nat := 4983230072969 + 3 ^ 40 * 451405 * 2
def baseEnd_451405 : Nat := 68677847360862699129343

theorem tailTrace_451405 : CollatzResearch.WordTrace tailWord_451405 prefixEnd_451405 68677847360862699129343 := by
  unfold tailWord_451405
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464092929644253681355669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976061953096169120903779 16464092929644253681355669)
  ·
    refine ⟨771754356077074391313547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16464092929644253681355669 771754356077074391313547)
    ·
      refine ⟨1157631534115611586970321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771754356077074391313547 1157631534115611586970321)
      ·
        refine ⟨868223650586708690227741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157631534115611586970321 868223650586708690227741)
        ·
          refine ⟨325583868970015758835403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 868223650586708690227741 325583868970015758835403)
          ·
            refine ⟨488375803455023638253105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325583868970015758835403 488375803455023638253105)
            ·
              refine ⟨366281852591267728689829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488375803455023638253105 366281852591267728689829)
              ·
                refine ⟨68677847360862699129343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366281852591267728689829 68677847360862699129343)
                ·
                  rfl

theorem cell20_451405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].length) (baseStart_451405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451405 prefixEnd_451405 := by exact prefixLift 451405
  have htrace : WordTrace (prefixWord ++ tailWord_451405) baseStart_451405 baseEnd_451405 := by
    simpa [prefixWord, tailWord_451405, baseEnd_451405] using wordTrace_append hprefix tailTrace_451405
  have hstable : (prefixWord ++ tailWord_451405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451405).length < 2 ^ (prefixWord ++ tailWord_451405).sum := by decide
  have hdescent : baseEnd_451405 < baseStart_451405 := by decide
  rcases family_descends (prefixWord ++ tailWord_451405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451409 : List Nat := [1, 2, 2, 1, 6, 2, 2, 4]
def baseStart_451409 : Nat := 118140960795 + 451409 * 2 ^ 59
def prefixEnd_451409 : Nat := 4983230072969 + 3 ^ 40 * 451409 * 2
def baseEnd_451409 : Nat := 68678455930527287084893

theorem tailTrace_451409 : CollatzResearch.WordTrace tailWord_451409 prefixEnd_451409 68678455930527287084893 := by
  unfold tailWord_451409
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464238821629762364501281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976159214419841576334187 16464238821629762364501281)
  ·
    refine ⟨12348179116222321773375961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16464238821629762364501281 12348179116222321773375961)
    ·
      refine ⟨9261134337166741330031971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12348179116222321773375961 9261134337166741330031971)
      ·
        refine ⟨13891701505750111995047957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9261134337166741330031971 13891701505750111995047957)
        ·
          refine ⟨651173508082036499767873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13891701505750111995047957 651173508082036499767873)
          ·
            refine ⟨488380131061527374825905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651173508082036499767873 488380131061527374825905)
            ·
              refine ⟨366285098296145531119429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488380131061527374825905 366285098296145531119429)
              ·
                refine ⟨68678455930527287084893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366285098296145531119429 68678455930527287084893)
                ·
                  rfl

theorem cell20_451409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_451409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451409 prefixEnd_451409 := by exact prefixLift 451409
  have htrace : WordTrace (prefixWord ++ tailWord_451409) baseStart_451409 baseEnd_451409 := by
    simpa [prefixWord, tailWord_451409, baseEnd_451409] using wordTrace_append hprefix tailTrace_451409
  have hstable : (prefixWord ++ tailWord_451409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451409).length < 2 ^ (prefixWord ++ tailWord_451409).sum := by decide
  have hdescent : baseEnd_451409 < baseStart_451409 := by decide
  rcases family_descends (prefixWord ++ tailWord_451409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451413 : List Nat := [1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_451413 : Nat := 118140960795 + 451413 * 2 ^ 59
def prefixEnd_451413 : Nat := 4983230072969 + 3 ^ 40 * 451413 * 2
def baseEnd_451413 : Nat := 68679064500191875040443

theorem tailTrace_451413 : CollatzResearch.WordTrace tailWord_451413 prefixEnd_451413 68679064500191875040443 := by
  unfold tailWord_451413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464384713615271047646893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976256475743514031764595 16464384713615271047646893)
  ·
    refine ⟨6174144267605726642867585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16464384713615271047646893 6174144267605726642867585)
    ·
      refine ⟨4630608200704294982150689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6174144267605726642867585 4630608200704294982150689)
      ·
        refine ⟨3472956150528221236613017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4630608200704294982150689 3472956150528221236613017)
        ·
          refine ⟨2604717112896165927459763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472956150528221236613017 2604717112896165927459763)
          ·
            refine ⟨3907075669344248891189645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604717112896165927459763 3907075669344248891189645)
            ·
              refine ⟨1465153376004093334196117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3907075669344248891189645 1465153376004093334196117)
              ·
                refine ⟨68679064500191875040443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1465153376004093334196117 68679064500191875040443)
                ·
                  rfl

theorem cell20_451413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_451413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451413 prefixEnd_451413 := by exact prefixLift 451413
  have htrace : WordTrace (prefixWord ++ tailWord_451413) baseStart_451413 baseEnd_451413 := by
    simpa [prefixWord, tailWord_451413, baseEnd_451413] using wordTrace_append hprefix tailTrace_451413
  have hstable : (prefixWord ++ tailWord_451413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451413).length < 2 ^ (prefixWord ++ tailWord_451413).sum := by decide
  have hdescent : baseEnd_451413 < baseStart_451413 := by decide
  rcases family_descends (prefixWord ++ tailWord_451413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451437 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_451437 : Nat := 118140960795 + 451437 * 2 ^ 59
def prefixEnd_451437 : Nat := 4983230072969 + 3 ^ 40 * 451437 * 2
def baseEnd_451437 : Nat := 206048147754538208321231

theorem tailTrace_451437 : CollatzResearch.WordTrace tailWord_451437 prefixEnd_451437 206048147754538208321231 := by
  unfold tailWord_451437
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465260065528323146520565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976840043685548764347043 16465260065528323146520565)
  ·
    refine ⟨1543618131143280294986303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16465260065528323146520565 1543618131143280294986303)
    ·
      refine ⟨2315427196714920442479455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1543618131143280294986303 2315427196714920442479455)
      ·
        refine ⟨3473140795072380663719183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315427196714920442479455 3473140795072380663719183)
        ·
          refine ⟨5209711192608570995578775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473140795072380663719183 5209711192608570995578775)
          ·
            refine ⟨7814566788912856493368163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209711192608570995578775 7814566788912856493368163)
            ·
              refine ⟨11721850183369284740052245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814566788912856493368163 11721850183369284740052245)
              ·
                refine ⟨549461727345435222189949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11721850183369284740052245 549461727345435222189949)
                ·
                  refine ⟨206048147754538208321231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549461727345435222189949 206048147754538208321231)
                  ·
                    rfl

theorem cell20_451437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_451437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451437 prefixEnd_451437 := by exact prefixLift 451437
  have htrace : WordTrace (prefixWord ++ tailWord_451437) baseStart_451437 baseEnd_451437 := by
    simpa [prefixWord, tailWord_451437, baseEnd_451437] using wordTrace_append hprefix tailTrace_451437
  have hstable : (prefixWord ++ tailWord_451437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451437).length < 2 ^ (prefixWord ++ tailWord_451437).sum := by decide
  have hdescent : baseEnd_451437 < baseStart_451437 := by decide
  rcases family_descends (prefixWord ++ tailWord_451437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451489 : List Nat := [1, 2, 3, 4, 1, 9]
def baseStart_451489 : Nat := 118140960795 + 451489 * 2 ^ 59
def prefixEnd_451489 : Nat := 4983230072969 + 3 ^ 40 * 451489 * 2
def baseEnd_451489 : Nat := 7632291924868782910655

theorem tailTrace_451489 : CollatzResearch.WordTrace tailWord_451489 prefixEnd_451489 7632291924868782910655 := by
  unfold tailWord_451489
  simp only [CollatzResearch.WordTrace]
  refine ⟨16467156661339936027413521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10978104440893290684942347 16467156661339936027413521)
  ·
    refine ⟨12350367496004952020560141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16467156661339936027413521 12350367496004952020560141)
    ·
      refine ⟨4631387811001857007710053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12350367496004952020560141 4631387811001857007710053)
      ·
        refine ⟨868385214562848188945635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4631387811001857007710053 868385214562848188945635)
        ·
          refine ⟨1302577821844272283418453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868385214562848188945635 1302577821844272283418453)
          ·
            refine ⟨7632291924868782910655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1302577821844272283418453 7632291924868782910655)
            ·
              rfl

theorem cell20_451489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 9].length) (baseStart_451489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451489 prefixEnd_451489 := by exact prefixLift 451489
  have htrace : WordTrace (prefixWord ++ tailWord_451489) baseStart_451489 baseEnd_451489 := by
    simpa [prefixWord, tailWord_451489, baseEnd_451489] using wordTrace_append hprefix tailTrace_451489
  have hstable : (prefixWord ++ tailWord_451489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451489).length < 2 ^ (prefixWord ++ tailWord_451489).sum := by decide
  have hdescent : baseEnd_451489 < baseStart_451489 := by decide
  rcases family_descends (prefixWord ++ tailWord_451489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451513 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_451513 : Nat := 118140960795 + 451513 * 2 ^ 59
def prefixEnd_451513 : Nat := 4983230072969 + 3 ^ 40 * 451513 * 2
def baseEnd_451513 : Nat := 206082836225419721787587

theorem tailTrace_451513 : CollatzResearch.WordTrace tailWord_451513 prefixEnd_451513 206082836225419721787587 := by
  unfold tailWord_451513
  simp only [CollatzResearch.WordTrace]
  refine ⟨16468032013252988126287193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10978688008835325417524795 16468032013252988126287193)
  ·
    refine ⟨12351024009939741094715395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16468032013252988126287193 12351024009939741094715395)
    ·
      refine ⟨18526536014909611642073093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351024009939741094715395 18526536014909611642073093)
      ·
        refine ⟨3473725502795552182888705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18526536014909611642073093 3473725502795552182888705)
        ·
          refine ⟨2605294127096664137166529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473725502795552182888705 2605294127096664137166529)
          ·
            refine ⟨1953970595322498102874897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605294127096664137166529 1953970595322498102874897)
            ·
              refine ⟨1465477946491873577156173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1953970595322498102874897 1465477946491873577156173)
              ·
                refine ⟨549554229934452591433565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1465477946491873577156173 549554229934452591433565)
                ·
                  refine ⟨206082836225419721787587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549554229934452591433565 206082836225419721787587)
                  ·
                    rfl

theorem cell20_451513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_451513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451513 prefixEnd_451513 := by exact prefixLift 451513
  have htrace : WordTrace (prefixWord ++ tailWord_451513) baseStart_451513 baseEnd_451513 := by
    simpa [prefixWord, tailWord_451513, baseEnd_451513] using wordTrace_append hprefix tailTrace_451513
  have hstable : (prefixWord ++ tailWord_451513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451513).length < 2 ^ (prefixWord ++ tailWord_451513).sum := by decide
  have hdescent : baseEnd_451513 < baseStart_451513 := by decide
  rcases family_descends (prefixWord ++ tailWord_451513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451520 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_451520 : Nat := 118140960795 + 451520 * 2 ^ 59
def prefixEnd_451520 : Nat := 4983230072969 + 3 ^ 40 * 451520 * 2
def baseEnd_451520 : Nat := 206086031216158808554225

theorem tailTrace_451520 : CollatzResearch.WordTrace tailWord_451520 prefixEnd_451520 206086031216158808554225 := by
  unfold tailWord_451520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234143662113814160896007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10978858216151752214528009 8234143662113814160896007)
  ·
    refine ⟨12351215493170721241344011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8234143662113814160896007 12351215493170721241344011)
    ·
      refine ⟨18526823239756081862016017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351215493170721241344011 18526823239756081862016017)
      ·
        refine ⟨13895117429817061396512013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18526823239756081862016017 13895117429817061396512013)
        ·
          refine ⟨5210669036181398023692005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13895117429817061396512013 5210669036181398023692005)
          ·
            refine ⟨977000444284012129442251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5210669036181398023692005 977000444284012129442251)
            ·
              refine ⟨1465500666426018194163377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977000444284012129442251 1465500666426018194163377)
              ·
                refine ⟨1099125499819513645622533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465500666426018194163377 1099125499819513645622533)
                ·
                  refine ⟨206086031216158808554225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099125499819513645622533 206086031216158808554225)
                  ·
                    rfl

theorem cell20_451520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_451520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451520 prefixEnd_451520 := by exact prefixLift 451520
  have htrace : WordTrace (prefixWord ++ tailWord_451520) baseStart_451520 baseEnd_451520 := by
    simpa [prefixWord, tailWord_451520, baseEnd_451520] using wordTrace_append hprefix tailTrace_451520
  have hstable : (prefixWord ++ tailWord_451520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451520).length < 2 ^ (prefixWord ++ tailWord_451520).sum := by decide
  have hdescent : baseEnd_451520 < baseStart_451520 := by decide
  rcases family_descends (prefixWord ++ tailWord_451520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451537 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 2]
def baseStart_451537 : Nat := 118140960795 + 451537 * 2 ^ 59
def prefixEnd_451537 : Nat := 4983230072969 + 3 ^ 40 * 451537 * 2
def baseEnd_451537 : Nat := 206093790479382304987489

theorem tailTrace_451537 : CollatzResearch.WordTrace tailWord_451537 prefixEnd_451537 206093790479382304987489 := by
  unfold tailWord_451537
  simp only [CollatzResearch.WordTrace]
  refine ⟨16468907365166040225160865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10979271576777360150107243 16468907365166040225160865)
  ·
    refine ⟨12351680523874530168870649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16468907365166040225160865 12351680523874530168870649)
    ·
      refine ⟨9263760392905897626652987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12351680523874530168870649 9263760392905897626652987)
      ·
        refine ⟨13895640589358846439979481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263760392905897626652987 13895640589358846439979481)
        ·
          refine ⟨10421730442019134829984611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13895640589358846439979481 10421730442019134829984611)
          ·
            refine ⟨15632595663028702244976917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421730442019134829984611 15632595663028702244976917)
            ·
              refine ⟨732777921704470417733293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15632595663028702244976917 732777921704470417733293)
              ·
                refine ⟨274791720639176406649985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732777921704470417733293 274791720639176406649985)
                ·
                  refine ⟨206093790479382304987489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274791720639176406649985 206093790479382304987489)
                  ·
                    rfl

theorem cell20_451537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_451537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451537 prefixEnd_451537 := by exact prefixLift 451537
  have htrace : WordTrace (prefixWord ++ tailWord_451537) baseStart_451537 baseEnd_451537 := by
    simpa [prefixWord, tailWord_451537, baseEnd_451537] using wordTrace_append hprefix tailTrace_451537
  have hstable : (prefixWord ++ tailWord_451537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451537).length < 2 ^ (prefixWord ++ tailWord_451537).sum := by decide
  have hdescent : baseEnd_451537 < baseStart_451537 := by decide
  rcases family_descends (prefixWord ++ tailWord_451537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451551 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_451551 : Nat := 118140960795 + 451551 * 2 ^ 59
def prefixEnd_451551 : Nat := 4983230072969 + 3 ^ 40 * 451551 * 2
def baseEnd_451551 : Nat := 206100180460860478520765

theorem tailTrace_451551 : CollatzResearch.WordTrace tailWord_451551 prefixEnd_451551 206100180460860478520765 := by
  unfold tailWord_451551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469417987115320616170507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10979611991410213744113671 16469417987115320616170507)
  ·
    refine ⟨24704126980672980924255761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16469417987115320616170507 24704126980672980924255761)
    ·
      refine ⟨18528095235504735693191821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24704126980672980924255761 18528095235504735693191821)
      ·
        refine ⟨6948035713314275884946933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18528095235504735693191821 6948035713314275884946933)
        ·
          refine ⟨651378348123213364213775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6948035713314275884946933 651378348123213364213775)
          ·
            refine ⟨977067522184820046320663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651378348123213364213775 977067522184820046320663)
            ·
              refine ⟨1465601283277230069480995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977067522184820046320663 1465601283277230069480995)
              ·
                refine ⟨2198401924915845104221493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465601283277230069480995 2198401924915845104221493)
                ·
                  refine ⟨206100180460860478520765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2198401924915845104221493 206100180460860478520765)
                  ·
                    rfl

theorem cell20_451551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_451551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451551 prefixEnd_451551 := by exact prefixLift 451551
  have htrace : WordTrace (prefixWord ++ tailWord_451551) baseStart_451551 baseEnd_451551 := by
    simpa [prefixWord, tailWord_451551, baseEnd_451551] using wordTrace_append hprefix tailTrace_451551
  have hstable : (prefixWord ++ tailWord_451551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451551).length < 2 ^ (prefixWord ++ tailWord_451551).sum := by decide
  have hdescent : baseEnd_451551 < baseStart_451551 := by decide
  rcases family_descends (prefixWord ++ tailWord_451551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451554 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_451554 : Nat := 118140960795 + 451554 * 2 ^ 59
def prefixEnd_451554 : Nat := 4983230072969 + 3 ^ 40 * 451554 * 2
def baseEnd_451554 : Nat := 206101549742605801420753

theorem tailTrace_451554 : CollatzResearch.WordTrace tailWord_451554 prefixEnd_451554 206101549742605801420753 := by
  unfold tailWord_451554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117381851526113032132429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10979684937402968085686477 4117381851526113032132429)
  ·
    refine ⟨1544018194322292387049661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4117381851526113032132429 1544018194322292387049661)
    ·
      refine ⟨579006822870859645143623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1544018194322292387049661 579006822870859645143623)
      ·
        refine ⟨868510234306289467715435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579006822870859645143623 868510234306289467715435)
        ·
          refine ⟨1302765351459434201573153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868510234306289467715435 1302765351459434201573153)
          ·
            refine ⟨977074013594575651179865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302765351459434201573153 977074013594575651179865)
            ·
              refine ⟨732805510195931738384899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977074013594575651179865 732805510195931738384899)
              ·
                refine ⟨1099208265293897607577349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732805510195931738384899 1099208265293897607577349)
                ·
                  refine ⟨206101549742605801420753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099208265293897607577349 206101549742605801420753)
                  ·
                    rfl

theorem cell20_451554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_451554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451554 prefixEnd_451554 := by exact prefixLift 451554
  have htrace : WordTrace (prefixWord ++ tailWord_451554) baseStart_451554 baseEnd_451554 := by
    simpa [prefixWord, tailWord_451554, baseEnd_451554] using wordTrace_append hprefix tailTrace_451554
  have hstable : (prefixWord ++ tailWord_451554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451554).length < 2 ^ (prefixWord ++ tailWord_451554).sum := by decide
  have hdescent : baseEnd_451554 < baseStart_451554 := by decide
  rcases family_descends (prefixWord ++ tailWord_451554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451592 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 2]
def baseStart_451592 : Nat := 118140960795 + 451592 * 2 ^ 59
def prefixEnd_451592 : Nat := 4983230072969 + 3 ^ 40 * 451592 * 2
def baseEnd_451592 : Nat := 206118893978046558153931

theorem tailTrace_451592 : CollatzResearch.WordTrace tailWord_451592 prefixEnd_451592 206118893978046558153931 := by
  unfold tailWord_451592
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235456689983392309206515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10980608919977856412275353 8235456689983392309206515)
  ·
    refine ⟨12353185034975088463809773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8235456689983392309206515 12353185034975088463809773)
    ·
      refine ⟨4632444388115658173928665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12353185034975088463809773 4632444388115658173928665)
      ·
        refine ⟨3474333291086743630446499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4632444388115658173928665 3474333291086743630446499)
        ·
          refine ⟨5211499936630115445669749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474333291086743630446499 5211499936630115445669749)
          ·
            refine ⟨488578119059073323031539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5211499936630115445669749 488578119059073323031539)
            ·
              refine ⟨732867178588609984547309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488578119059073323031539 732867178588609984547309)
              ·
                refine ⟨274825191970728744205241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732867178588609984547309 274825191970728744205241)
                ·
                  refine ⟨206118893978046558153931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274825191970728744205241 206118893978046558153931)
                  ·
                    rfl

theorem cell20_451592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_451592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451592 prefixEnd_451592 := by exact prefixLift 451592
  have htrace : WordTrace (prefixWord ++ tailWord_451592) baseStart_451592 baseEnd_451592 := by
    simpa [prefixWord, tailWord_451592, baseEnd_451592] using wordTrace_append hprefix tailTrace_451592
  have hstable : (prefixWord ++ tailWord_451592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451592).length < 2 ^ (prefixWord ++ tailWord_451592).sum := by decide
  have hdescent : baseEnd_451592 < baseStart_451592 := by decide
  rcases family_descends (prefixWord ++ tailWord_451592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451610 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_451610 : Nat := 118140960795 + 451610 * 2 ^ 59
def prefixEnd_451610 : Nat := 4983230072969 + 3 ^ 40 * 451610 * 2
def baseEnd_451610 : Nat := 206127109668518495553857

theorem tailTrace_451610 : CollatzResearch.WordTrace tailWord_451610 prefixEnd_451610 206127109668518495553857 := by
  unfold tailWord_451610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117892473475393423142071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10981046595934382461712189 4117892473475393423142071)
  ·
    refine ⟨6176838710213090134713107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117892473475393423142071 6176838710213090134713107)
    ·
      refine ⟨9265258065319635202069661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6176838710213090134713107 9265258065319635202069661)
      ·
        refine ⟨3474471774494863200776123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9265258065319635202069661 3474471774494863200776123)
        ·
          refine ⟨5211707661742294801164185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474471774494863200776123 5211707661742294801164185)
          ·
            refine ⟨3908780746306721100873139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5211707661742294801164185 3908780746306721100873139)
            ·
              refine ⟨5863171119460081651309709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908780746306721100873139 5863171119460081651309709)
              ·
                refine ⟨2198689169797530619241141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5863171119460081651309709 2198689169797530619241141)
                ·
                  refine ⟨206127109668518495553857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2198689169797530619241141 206127109668518495553857)
                  ·
                    rfl

theorem cell20_451610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_451610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451610 prefixEnd_451610 := by exact prefixLift 451610
  have htrace : WordTrace (prefixWord ++ tailWord_451610) baseStart_451610 baseEnd_451610 := by
    simpa [prefixWord, tailWord_451610, baseEnd_451610] using wordTrace_append hprefix tailTrace_451610
  have hstable : (prefixWord ++ tailWord_451610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451610).length < 2 ^ (prefixWord ++ tailWord_451610).sum := by decide
  have hdescent : baseEnd_451610 < baseStart_451610 := by decide
  rcases family_descends (prefixWord ++ tailWord_451610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451620 : List Nat := [2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_451620 : Nat := 118140960795 + 451620 * 2 ^ 59
def prefixEnd_451620 : Nat := 4983230072969 + 3 ^ 40 * 451620 * 2
def baseEnd_451620 : Nat := 68710557980334301740161

theorem tailTrace_451620 : CollatzResearch.WordTrace tailWord_451620 prefixEnd_451620 68710557980334301740161 := by
  unfold tailWord_451620
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235967311932672700216157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10981289749243563600288209 8235967311932672700216157)
  ·
    refine ⟨3088487741974752262581059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8235967311932672700216157 3088487741974752262581059)
    ·
      refine ⟨4632731612962128393871589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088487741974752262581059 4632731612962128393871589)
      ·
        refine ⟨868637177430399073850923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4632731612962128393871589 868637177430399073850923)
        ·
          refine ⟨1302955766145598610776385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868637177430399073850923 1302955766145598610776385)
          ·
            refine ⟨977216824609198958082289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302955766145598610776385 977216824609198958082289)
            ·
              refine ⟨732912618456899218561717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977216824609198958082289 732912618456899218561717)
              ·
                refine ⟨68710557980334301740161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 732912618456899218561717 68710557980334301740161)
                ·
                  rfl

theorem cell20_451620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_451620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451620 prefixEnd_451620 := by exact prefixLift 451620
  have htrace : WordTrace (prefixWord ++ tailWord_451620) baseStart_451620 baseEnd_451620 := by
    simpa [prefixWord, tailWord_451620, baseEnd_451620] using wordTrace_append hprefix tailTrace_451620
  have hstable : (prefixWord ++ tailWord_451620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451620).length < 2 ^ (prefixWord ++ tailWord_451620).sum := by decide
  have hdescent : baseEnd_451620 < baseStart_451620 := by decide
  rcases family_descends (prefixWord ++ tailWord_451620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451623 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 3]
def baseStart_451623 : Nat := 118140960795 + 451623 * 2 ^ 59
def prefixEnd_451623 : Nat := 4983230072969 + 3 ^ 40 * 451623 * 2
def baseEnd_451623 : Nat := 206133043222748228120471

theorem tailTrace_451623 : CollatzResearch.WordTrace tailWord_451623 prefixEnd_451623 206133043222748228120471 := by
  unfold tailWord_451623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472044042854476912791523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10981362695236317941861015 16472044042854476912791523)
  ·
    refine ⟨24708066064281715369187285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16472044042854476912791523 24708066064281715369187285)
    ·
      refine ⟨579095298381602703965327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24708066064281715369187285 579095298381602703965327)
      ·
        refine ⟨868642947572404055947991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579095298381602703965327 868642947572404055947991)
        ·
          refine ⟨1302964421358606083921987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868642947572404055947991 1302964421358606083921987)
          ·
            refine ⟨1954446632037909125882981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302964421358606083921987 1954446632037909125882981)
            ·
              refine ⟨366458743507107961103059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1954446632037909125882981 366458743507107961103059)
              ·
                refine ⟨549688115260661941654589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366458743507107961103059 549688115260661941654589)
                ·
                  refine ⟨206133043222748228120471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549688115260661941654589 206133043222748228120471)
                  ·
                    rfl

theorem cell20_451623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_451623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451623 prefixEnd_451623 := by exact prefixLift 451623
  have htrace : WordTrace (prefixWord ++ tailWord_451623) baseStart_451623 baseEnd_451623 := by
    simpa [prefixWord, tailWord_451623, baseEnd_451623] using wordTrace_append hprefix tailTrace_451623
  have hstable : (prefixWord ++ tailWord_451623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451623).length < 2 ^ (prefixWord ++ tailWord_451623).sum := by decide
  have hdescent : baseEnd_451623 < baseStart_451623 := by decide
  rcases family_descends (prefixWord ++ tailWord_451623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451641 : List Nat := [1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_451641 : Nat := 118140960795 + 451641 * 2 ^ 59
def prefixEnd_451641 : Nat := 4983230072969 + 3 ^ 40 * 451641 * 2
def baseEnd_451641 : Nat := 68713752971073388506799

theorem tailTrace_451641 : CollatzResearch.WordTrace tailWord_451641 prefixEnd_451641 68713752971073388506799 := by
  unfold tailWord_451641
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472700556789265986946777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10981800371192843991297851 16472700556789265986946777)
  ·
    refine ⟨12354525417591949490210083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16472700556789265986946777 12354525417591949490210083)
    ·
      refine ⟨18531788126387924235315125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12354525417591949490210083 18531788126387924235315125)
      ·
        refine ⟨1737355136848867897060793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18531788126387924235315125 1737355136848867897060793)
        ·
          refine ⟨1303016352636650922795595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737355136848867897060793 1303016352636650922795595)
          ·
            refine ⟨1954524528954976384193393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303016352636650922795595 1954524528954976384193393)
            ·
              refine ⟨1465893396716232288145045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954524528954976384193393 1465893396716232288145045)
              ·
                refine ⟨68713752971073388506799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1465893396716232288145045 68713752971073388506799)
                ·
                  rfl

theorem cell20_451641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_451641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451641 prefixEnd_451641 := by exact prefixLift 451641
  have htrace : WordTrace (prefixWord ++ tailWord_451641) baseStart_451641 baseEnd_451641 := by
    simpa [prefixWord, tailWord_451641, baseEnd_451641] using wordTrace_append hprefix tailTrace_451641
  have hstable : (prefixWord ++ tailWord_451641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451641).length < 2 ^ (prefixWord ++ tailWord_451641).sum := by decide
  have hdescent : baseEnd_451641 < baseStart_451641 := by decide
  rcases family_descends (prefixWord ++ tailWord_451641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451668 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 2]
def baseStart_451668 : Nat := 118140960795 + 451668 * 2 ^ 59
def prefixEnd_451668 : Nat := 4983230072969 + 3 ^ 40 * 451668 * 2
def baseEnd_451668 : Nat := 206153582448928071620287

theorem tailTrace_451668 : CollatzResearch.WordTrace tailWord_451668 prefixEnd_451668 206153582448928071620287 := by
  unfold tailWord_451668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236842663845724799089829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10982456885127633065453105 8236842663845724799089829)
  ·
    refine ⟨1544407999471073399829343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8236842663845724799089829 1544407999471073399829343)
    ·
      refine ⟨2316611999206610099744015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1544407999471073399829343 2316611999206610099744015)
      ·
        refine ⟨3474917998809915149616023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316611999206610099744015 3474917998809915149616023)
        ·
          refine ⟨5212376998214872724424035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474917998809915149616023 5212376998214872724424035)
          ·
            refine ⟨7818565497322309086636053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212376998214872724424035 7818565497322309086636053)
            ·
              refine ⟨366495257686983238436065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7818565497322309086636053 366495257686983238436065)
              ·
                refine ⟨274871443265237428827049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366495257686983238436065 274871443265237428827049)
                ·
                  refine ⟨206153582448928071620287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274871443265237428827049 206153582448928071620287)
                  ·
                    rfl

theorem cell20_451668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_451668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451668 prefixEnd_451668 := by exact prefixLift 451668
  have htrace : WordTrace (prefixWord ++ tailWord_451668) baseStart_451668 baseEnd_451668 := by
    simpa [prefixWord, tailWord_451668, baseEnd_451668] using wordTrace_append hprefix tailTrace_451668
  have hstable : (prefixWord ++ tailWord_451668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451668).length < 2 ^ (prefixWord ++ tailWord_451668).sum := by decide
  have hdescent : baseEnd_451668 < baseStart_451668 := by decide
  rcases family_descends (prefixWord ++ tailWord_451668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451682 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_451682 : Nat := 118140960795 + 451682 * 2 ^ 59
def prefixEnd_451682 : Nat := 4983230072969 + 3 ^ 40 * 451682 * 2
def baseEnd_451682 : Nat := 206159972430406245153563

theorem tailTrace_451682 : CollatzResearch.WordTrace tailWord_451682 prefixEnd_451682 206159972430406245153563 := by
  unfold tailWord_451682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118548987410182497297325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10982797299760486659459533 4118548987410182497297325)
  ·
    refine ⟨1544455870278818436486497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4118548987410182497297325 1544455870278818436486497)
    ·
      refine ⟨1158341902709113827364873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1544455870278818436486497 1158341902709113827364873)
      ·
        refine ⟨868756427031835370523655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1158341902709113827364873 868756427031835370523655)
        ·
          refine ⟨1303134640547753055785483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868756427031835370523655 1303134640547753055785483)
          ·
            refine ⟨1954701960821629583678225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303134640547753055785483 1954701960821629583678225)
            ·
              refine ⟨1466026470616222187758669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954701960821629583678225 1466026470616222187758669)
              ·
                refine ⟨549759926481083320409501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1466026470616222187758669 549759926481083320409501)
                ·
                  refine ⟨206159972430406245153563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549759926481083320409501 206159972430406245153563)
                  ·
                    rfl

theorem cell20_451682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_451682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451682 prefixEnd_451682 := by exact prefixLift 451682
  have htrace : WordTrace (prefixWord ++ tailWord_451682) baseStart_451682 baseEnd_451682 := by
    simpa [prefixWord, tailWord_451682, baseEnd_451682] using wordTrace_append hprefix tailTrace_451682
  have hstable : (prefixWord ++ tailWord_451682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451682).length < 2 ^ (prefixWord ++ tailWord_451682).sum := by decide
  have hdescent : baseEnd_451682 < baseStart_451682 := by decide
  rcases family_descends (prefixWord ++ tailWord_451682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451717 : List Nat := [1, 3, 1, 1, 6, 1, 7]
def baseStart_451717 : Nat := 118140960795 + 451717 * 2 ^ 59
def prefixEnd_451717 : Nat := 4983230072969 + 3 ^ 40 * 451717 * 2
def baseEnd_451717 : Nat := 22908438598233519887417

theorem tailTrace_451717 : CollatzResearch.WordTrace tailWord_451717 prefixEnd_451717 22908438598233519887417 := by
  unfold tailWord_451717
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475472504513930966713405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10983648336342620644475603 16475472504513930966713405)
  ·
    refine ⟨6178302189192724112517527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16475472504513930966713405 6178302189192724112517527)
    ·
      refine ⟨9267453283789086168776291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6178302189192724112517527 9267453283789086168776291)
      ·
        refine ⟨13901179925683629253164437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9267453283789086168776291 13901179925683629253164437)
        ·
          refine ⟨651617809016420121242083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13901179925683629253164437 651617809016420121242083)
          ·
            refine ⟨977426713524630181863125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651617809016420121242083 977426713524630181863125)
            ·
              refine ⟨22908438598233519887417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 977426713524630181863125 22908438598233519887417)
              ·
                rfl

theorem cell20_451717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_451717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451717 prefixEnd_451717 := by exact prefixLift 451717
  have htrace : WordTrace (prefixWord ++ tailWord_451717) baseStart_451717 baseEnd_451717 := by
    simpa [prefixWord, tailWord_451717, baseEnd_451717] using wordTrace_append hprefix tailTrace_451717
  have hstable : (prefixWord ++ tailWord_451717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451717).length < 2 ^ (prefixWord ++ tailWord_451717).sum := by decide
  have hdescent : baseEnd_451717 < baseStart_451717 := by decide
  rcases family_descends (prefixWord ++ tailWord_451717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451731 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_451731 : Nat := 118140960795 + 451731 * 2 ^ 59
def prefixEnd_451731 : Nat := 4983230072969 + 3 ^ 40 * 451731 * 2
def baseEnd_451731 : Nat := 206182337365579852520029

theorem tailTrace_451731 : CollatzResearch.WordTrace tailWord_451731 prefixEnd_451731 206182337365579852520029 := by
  unfold tailWord_451731
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475983126463211357723047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10983988750975474238482031 16475983126463211357723047)
  ·
    refine ⟨24713974689694817036584571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16475983126463211357723047 24713974689694817036584571)
    ·
      refine ⟨37070962034542225554876857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713974689694817036584571 37070962034542225554876857)
      ·
        refine ⟨27803221525906669166157643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37070962034542225554876857 27803221525906669166157643)
        ·
          refine ⟨41704832288860003749236465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27803221525906669166157643 41704832288860003749236465)
          ·
            refine ⟨31278624216645002811927349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41704832288860003749236465 31278624216645002811927349)
            ·
              refine ⟨2932371020310469013618189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31278624216645002811927349 2932371020310469013618189)
              ·
                refine ⟨1099639132616425880106821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932371020310469013618189 1099639132616425880106821)
                ·
                  refine ⟨206182337365579852520029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099639132616425880106821 206182337365579852520029)
                  ·
                    rfl

theorem cell20_451731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_451731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451731 prefixEnd_451731 := by exact prefixLift 451731
  have htrace : WordTrace (prefixWord ++ tailWord_451731) baseStart_451731 baseEnd_451731 := by
    simpa [prefixWord, tailWord_451731, baseEnd_451731] using wordTrace_append hprefix tailTrace_451731
  have hstable : (prefixWord ++ tailWord_451731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451731).length < 2 ^ (prefixWord ++ tailWord_451731).sum := by decide
  have hdescent : baseEnd_451731 < baseStart_451731 := by decide
  rcases family_descends (prefixWord ++ tailWord_451731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451748 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_451748 : Nat := 118140960795 + 451748 * 2 ^ 59
def prefixEnd_451748 : Nat := 4983230072969 + 3 ^ 40 * 451748 * 2
def baseEnd_451748 : Nat := 206190096628803348953293

theorem tailTrace_451748 : CollatzResearch.WordTrace tailWord_451748 prefixEnd_451748 206190096628803348953293 := by
  unfold tailWord_451748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8238301583700811630545949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10984402111601082174061265 8238301583700811630545949)
  ·
    refine ⟨3089363093887804361454731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8238301583700811630545949 3089363093887804361454731)
    ·
      refine ⟨4634044640831706542182097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089363093887804361454731 4634044640831706542182097)
      ·
        refine ⟨3475533480623779906636573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4634044640831706542182097 3475533480623779906636573)
        ·
          refine ⟨1303325055233917464988715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3475533480623779906636573 1303325055233917464988715)
          ·
            refine ⟨1954987582850876197483073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303325055233917464988715 1954987582850876197483073)
            ·
              refine ⟨1466240687138157148112305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954987582850876197483073 1466240687138157148112305)
              ·
                refine ⟨1099680515353617861084229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466240687138157148112305 1099680515353617861084229)
                ·
                  refine ⟨206190096628803348953293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099680515353617861084229 206190096628803348953293)
                  ·
                    rfl

theorem cell20_451748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_451748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451748 prefixEnd_451748 := by exact prefixLift 451748
  have htrace : WordTrace (prefixWord ++ tailWord_451748) baseStart_451748 baseEnd_451748 := by
    simpa [prefixWord, tailWord_451748, baseEnd_451748] using wordTrace_append hprefix tailTrace_451748
  have hstable : (prefixWord ++ tailWord_451748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451748).length < 2 ^ (prefixWord ++ tailWord_451748).sum := by decide
  have hdescent : baseEnd_451748 < baseStart_451748 := by decide
  rcases family_descends (prefixWord ++ tailWord_451748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451751 : List Nat := [1, 1, 6, 2, 1, 3, 2, 4]
def baseStart_451751 : Nat := 118140960795 + 451751 * 2 ^ 59
def prefixEnd_451751 : Nat := 4983230072969 + 3 ^ 40 * 451751 * 2
def baseEnd_451751 : Nat := 68730488636849557284427

theorem tailTrace_451751 : CollatzResearch.WordTrace tailWord_451751 prefixEnd_451751 68730488636849557284427 := by
  unfold tailWord_451751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16476712586390754773451107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10984475057593836515634071 16476712586390754773451107)
  ·
    refine ⟨24715068879586132160176661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16476712586390754773451107 24715068879586132160176661)
    ·
      refine ⟨1158518853730599945008281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24715068879586132160176661 1158518853730599945008281)
      ·
        refine ⟨868889140297949958756211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1158518853730599945008281 868889140297949958756211)
        ·
          refine ⟨1303333710446924938134317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868889140297949958756211 1303333710446924938134317)
          ·
            refine ⟨488750141417596851800369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1303333710446924938134317 488750141417596851800369)
            ·
              refine ⟨366562606063197638850277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488750141417596851800369 366562606063197638850277)
              ·
                refine ⟨68730488636849557284427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366562606063197638850277 68730488636849557284427)
                ·
                  rfl

theorem cell20_451751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_451751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451751 prefixEnd_451751 := by exact prefixLift 451751
  have htrace : WordTrace (prefixWord ++ tailWord_451751) baseStart_451751 baseEnd_451751 := by
    simpa [prefixWord, tailWord_451751, baseEnd_451751] using wordTrace_append hprefix tailTrace_451751
  have hstable : (prefixWord ++ tailWord_451751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451751).length < 2 ^ (prefixWord ++ tailWord_451751).sum := by decide
  have hdescent : baseEnd_451751 < baseStart_451751 := by decide
  rcases family_descends (prefixWord ++ tailWord_451751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451762 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_451762 : Nat := 118140960795 + 451762 * 2 ^ 59
def prefixEnd_451762 : Nat := 4983230072969 + 3 ^ 40 * 451762 * 2
def baseEnd_451762 : Nat := 206196486610281522486569

theorem tailTrace_451762 : CollatzResearch.WordTrace tailWord_451762 prefixEnd_451762 206196486610281522486569 := by
  unfold tailWord_451762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119278447337725913025385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10984742526233935768067693 4119278447337725913025385)
  ·
    refine ⟨3089458835503294434769039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4119278447337725913025385 3089458835503294434769039)
    ·
      refine ⟨4634188253254941652153559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089458835503294434769039 4634188253254941652153559)
      ·
        refine ⟨6951282379882412478230339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634188253254941652153559 6951282379882412478230339)
        ·
          refine ⟨10426923569823618717345509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951282379882412478230339 10426923569823618717345509)
          ·
            refine ⟨1955048169341928509502283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10426923569823618717345509 1955048169341928509502283)
            ·
              refine ⟨2932572254012892764253425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955048169341928509502283 2932572254012892764253425)
              ·
                refine ⟨2199429190509669573190069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2932572254012892764253425 2199429190509669573190069)
                ·
                  refine ⟨206196486610281522486569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2199429190509669573190069 206196486610281522486569)
                  ·
                    rfl

theorem cell20_451762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_451762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451762 prefixEnd_451762 := by exact prefixLift 451762
  have htrace : WordTrace (prefixWord ++ tailWord_451762) baseStart_451762 baseEnd_451762 := by
    simpa [prefixWord, tailWord_451762, baseEnd_451762] using wordTrace_append hprefix tailTrace_451762
  have hstable : (prefixWord ++ tailWord_451762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451762).length < 2 ^ (prefixWord ++ tailWord_451762).sum := by decide
  have hdescent : baseEnd_451762 < baseStart_451762 := by decide
  rcases family_descends (prefixWord ++ tailWord_451762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451778 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_451778 : Nat := 118140960795 + 451778 * 2 ^ 59
def prefixEnd_451778 : Nat := 4983230072969 + 3 ^ 40 * 451778 * 2
def baseEnd_451778 : Nat := 206203789446256577953171

theorem tailTrace_451778 : CollatzResearch.WordTrace tailWord_451778 prefixEnd_451778 206203789446256577953171 := by
  unfold tailWord_451778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119424339323234596170997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10985131571528625589789325 4119424339323234596170997)
  ·
    refine ⟨386196031811553243391031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4119424339323234596170997 386196031811553243391031)
    ·
      refine ⟨579294047717329865086547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386196031811553243391031 579294047717329865086547)
      ·
        refine ⟨868941071575994797629821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579294047717329865086547 868941071575994797629821)
        ·
          refine ⟨325852901840998049111183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 868941071575994797629821 325852901840998049111183)
          ·
            refine ⟨488779352761497073666775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325852901840998049111183 488779352761497073666775)
            ·
              refine ⟨733169029142245610500163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488779352761497073666775 733169029142245610500163)
              ·
                refine ⟨1099753543713368415750245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733169029142245610500163 1099753543713368415750245)
                ·
                  refine ⟨206203789446256577953171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099753543713368415750245 206203789446256577953171)
                  ·
                    rfl

theorem cell20_451778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_451778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451778 prefixEnd_451778 := by exact prefixLift 451778
  have htrace : WordTrace (prefixWord ++ tailWord_451778) baseStart_451778 baseEnd_451778 := by
    simpa [prefixWord, tailWord_451778, baseEnd_451778] using wordTrace_append hprefix tailTrace_451778
  have hstable : (prefixWord ++ tailWord_451778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451778).length < 2 ^ (prefixWord ++ tailWord_451778).sum := by decide
  have hdescent : baseEnd_451778 < baseStart_451778 := by decide
  rcases family_descends (prefixWord ++ tailWord_451778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451786 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_451786 : Nat := 118140960795 + 451786 * 2 ^ 59
def prefixEnd_451786 : Nat := 4983230072969 + 3 ^ 40 * 451786 * 2
def baseEnd_451786 : Nat := 206207440864244105686471

theorem tailTrace_451786 : CollatzResearch.WordTrace tailWord_451786 prefixEnd_451786 206207440864244105686471 := by
  unfold tailWord_451786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119497285315988937743803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10985326094175970500650141 4119497285315988937743803)
  ·
    refine ⟨6179245927973983406615705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4119497285315988937743803 6179245927973983406615705)
    ·
      refine ⟨4634434445980487554961779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6179245927973983406615705 4634434445980487554961779)
      ·
        refine ⟨6951651668970731332442669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634434445980487554961779 6951651668970731332442669)
        ·
          refine ⟨2606869375864024249666001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6951651668970731332442669 2606869375864024249666001)
          ·
            refine ⟨1955152031898018187249501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2606869375864024249666001 1955152031898018187249501)
            ·
              refine ⟨733182011961756820218563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1955152031898018187249501 733182011961756820218563)
              ·
                refine ⟨1099773017942635230327845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733182011961756820218563 1099773017942635230327845)
                ·
                  refine ⟨206207440864244105686471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099773017942635230327845 206207440864244105686471)
                  ·
                    rfl

theorem cell20_451786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_451786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451786 prefixEnd_451786 := by exact prefixLift 451786
  have htrace : WordTrace (prefixWord ++ tailWord_451786) baseStart_451786 baseEnd_451786 := by
    simpa [prefixWord, tailWord_451786, baseEnd_451786] using wordTrace_append hprefix tailTrace_451786
  have hstable : (prefixWord ++ tailWord_451786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451786).length < 2 ^ (prefixWord ++ tailWord_451786).sum := by decide
  have hdescent : baseEnd_451786 < baseStart_451786 := by decide
  rcases family_descends (prefixWord ++ tailWord_451786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451807 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_451807 : Nat := 118140960795 + 451807 * 2 ^ 59
def prefixEnd_451807 : Nat := 4983230072969 + 3 ^ 40 * 451807 * 2
def baseEnd_451807 : Nat := 206217025836461365986385

theorem tailTrace_451807 : CollatzResearch.WordTrace tailWord_451807 prefixEnd_451807 206217025836461365986385 := by
  unfold tailWord_451807
  simp only [CollatzResearch.WordTrace]
  refine ⟨16478755074187876337489675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10985836716125250891659783 16478755074187876337489675)
  ·
    refine ⟨24718132611281814506234513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16478755074187876337489675 24718132611281814506234513)
    ·
      refine ⟨18538599458461360879675885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24718132611281814506234513 18538599458461360879675885)
      ·
        refine ⟨6951974796923010329878457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18538599458461360879675885 6951974796923010329878457)
        ·
          refine ⟨5213981097692257747408843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6951974796923010329878457 5213981097692257747408843)
          ·
            refine ⟨7820971646538386621113265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213981097692257747408843 7820971646538386621113265)
            ·
              refine ⟨5865728734903789965834949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7820971646538386621113265 5865728734903789965834949)
              ·
                refine ⟨1099824137794460618594053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5865728734903789965834949 1099824137794460618594053)
                ·
                  refine ⟨206217025836461365986385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099824137794460618594053 206217025836461365986385)
                  ·
                    rfl

theorem cell20_451807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_451807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451807 prefixEnd_451807 := by exact prefixLift 451807
  have htrace : WordTrace (prefixWord ++ tailWord_451807) baseStart_451807 baseEnd_451807 := by
    simpa [prefixWord, tailWord_451807, baseEnd_451807] using wordTrace_append hprefix tailTrace_451807
  have hstable : (prefixWord ++ tailWord_451807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451807).length < 2 ^ (prefixWord ++ tailWord_451807).sum := by decide
  have hdescent : baseEnd_451807 < baseStart_451807 := by decide
  rcases family_descends (prefixWord ++ tailWord_451807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451841 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 2]
def baseStart_451841 : Nat := 118140960795 + 451841 * 2 ^ 59
def prefixEnd_451841 : Nat := 4983230072969 + 3 ^ 40 * 451841 * 2
def baseEnd_451841 : Nat := 206232544362908358852913

theorem tailTrace_451841 : CollatzResearch.WordTrace tailWord_451841 prefixEnd_451841 206232544362908358852913 := by
  unfold tailWord_451841
  simp only [CollatzResearch.WordTrace]
  refine ⟨16479995156064700144227377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10986663437376466762818251 16479995156064700144227377)
  ·
    refine ⟨12359996367048525108170533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16479995156064700144227377 12359996367048525108170533)
    ·
      refine ⟨2317499318821598457781975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12359996367048525108170533 2317499318821598457781975)
      ·
        refine ⟨3476248978232397686672963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317499318821598457781975 3476248978232397686672963)
        ·
          refine ⟨5214373467348596530009445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476248978232397686672963 5214373467348596530009445)
          ·
            refine ⟨977695025127861849376771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5214373467348596530009445 977695025127861849376771)
            ·
              refine ⟨1466542537691792774065157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977695025127861849376771 1466542537691792774065157)
              ·
                refine ⟨274976725817211145137217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1466542537691792774065157 274976725817211145137217)
                ·
                  refine ⟨206232544362908358852913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274976725817211145137217 206232544362908358852913)
                  ·
                    rfl

theorem cell20_451841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_451841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451841 prefixEnd_451841 := by exact prefixLift 451841
  have htrace : WordTrace (prefixWord ++ tailWord_451841) baseStart_451841 baseEnd_451841 := by
    simpa [prefixWord, tailWord_451841, baseEnd_451841] using wordTrace_append hprefix tailTrace_451841
  have hstable : (prefixWord ++ tailWord_451841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451841).length < 2 ^ (prefixWord ++ tailWord_451841).sum := by decide
  have hdescent : baseEnd_451841 < baseStart_451841 := by decide
  rcases family_descends (prefixWord ++ tailWord_451841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451845 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_451845 : Nat := 118140960795 + 451845 * 2 ^ 59
def prefixEnd_451845 : Nat := 4983230072969 + 3 ^ 40 * 451845 * 2
def baseEnd_451845 : Nat := 206234370071902122719563

theorem tailTrace_451845 : CollatzResearch.WordTrace tailWord_451845 prefixEnd_451845 206234370071902122719563 := by
  unfold tailWord_451845
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480141048050208827372989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10986760698700139218248659 16480141048050208827372989)
  ·
    refine ⟨6180052893018828310264871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16480141048050208827372989 6180052893018828310264871)
    ·
      refine ⟨9270079339528242465397307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180052893018828310264871 9270079339528242465397307)
      ·
        refine ⟨13905119009292363698095961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270079339528242465397307 13905119009292363698095961)
        ·
          refine ⟨10428839256969272773571971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13905119009292363698095961 10428839256969272773571971)
          ·
            refine ⟨15643258885453909160357957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10428839256969272773571971 15643258885453909160357957)
            ·
              refine ⟨2933111041022607967567117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15643258885453909160357957 2933111041022607967567117)
              ·
                refine ⟨1099916640383477987837669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2933111041022607967567117 1099916640383477987837669)
                ·
                  refine ⟨206234370071902122719563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099916640383477987837669 206234370071902122719563)
                  ·
                    rfl

theorem cell20_451845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_451845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451845 prefixEnd_451845 := by exact prefixLift 451845
  have htrace : WordTrace (prefixWord ++ tailWord_451845) baseStart_451845 baseEnd_451845 := by
    simpa [prefixWord, tailWord_451845, baseEnd_451845] using wordTrace_append hprefix tailTrace_451845
  have hstable : (prefixWord ++ tailWord_451845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451845).length < 2 ^ (prefixWord ++ tailWord_451845).sum := by decide
  have hdescent : baseEnd_451845 < baseStart_451845 := by decide
  rcases family_descends (prefixWord ++ tailWord_451845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451848 : List Nat := [2, 1, 3, 2, 4, 2, 1, 5]
def baseStart_451848 : Nat := 118140960795 + 451848 * 2 ^ 59
def prefixEnd_451848 : Nat := 4983230072969 + 3 ^ 40 * 451848 * 2
def baseEnd_451848 : Nat := 68745246451215815206517

theorem tailTrace_451848 : CollatzResearch.WordTrace tailWord_451848 prefixEnd_451848 68745246451215815206517 := by
  unfold tailWord_451848
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240125233519670169866099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10986833644692893559821465 8240125233519670169866099)
  ·
    refine ⟨12360187850279505254799149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8240125233519670169866099 12360187850279505254799149)
    ·
      refine ⟨4635070443854814470549681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12360187850279505254799149 4635070443854814470549681)
      ·
        refine ⟨3476302832891110852912261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635070443854814470549681 3476302832891110852912261)
        ·
          refine ⟨651806781167083284921049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3476302832891110852912261 651806781167083284921049)
          ·
            refine ⟨488855085875312463690787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651806781167083284921049 488855085875312463690787)
            ·
              refine ⟨733282628812968695536181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488855085875312463690787 733282628812968695536181)
              ·
                refine ⟨68745246451215815206517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733282628812968695536181 68745246451215815206517)
                ·
                  rfl

theorem cell20_451848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_451848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451848 prefixEnd_451848 := by exact prefixLift 451848
  have htrace : WordTrace (prefixWord ++ tailWord_451848) baseStart_451848 baseEnd_451848 := by
    simpa [prefixWord, tailWord_451848, baseEnd_451848] using wordTrace_append hprefix tailTrace_451848
  have hstable : (prefixWord ++ tailWord_451848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451848).length < 2 ^ (prefixWord ++ tailWord_451848).sum := by decide
  have hdescent : baseEnd_451848 < baseStart_451848 := by decide
  rcases family_descends (prefixWord ++ tailWord_451848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451858 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_451858 : Nat := 118140960795 + 451858 * 2 ^ 59
def prefixEnd_451858 : Nat := 4983230072969 + 3 ^ 40 * 451858 * 2
def baseEnd_451858 : Nat := 206240303626131855286177

theorem tailTrace_451858 : CollatzResearch.WordTrace tailWord_451858 prefixEnd_451858 206240303626131855286177 := by
  unfold tailWord_451858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4120153799250778011899057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10987076798002074698397485 4120153799250778011899057)
  ·
    refine ⟨3090115349438083508924293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4120153799250778011899057 3090115349438083508924293)
    ·
      refine ⟨579396628019640657923305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3090115349438083508924293 579396628019640657923305)
      ·
        refine ⟨434547471014730493442479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579396628019640657923305 434547471014730493442479)
        ·
          refine ⟨651821206522095740163719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434547471014730493442479 651821206522095740163719)
          ·
            refine ⟨977731809783143610245579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651821206522095740163719 977731809783143610245579)
            ·
              refine ⟨1466597714674715415368369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977731809783143610245579 1466597714674715415368369)
              ·
                refine ⟨1099948286006036561526277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466597714674715415368369 1099948286006036561526277)
                ·
                  refine ⟨206240303626131855286177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099948286006036561526277 206240303626131855286177)
                  ·
                    rfl

theorem cell20_451858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_451858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451858 prefixEnd_451858 := by exact prefixLift 451858
  have htrace : WordTrace (prefixWord ++ tailWord_451858) baseStart_451858 baseEnd_451858 := by
    simpa [prefixWord, tailWord_451858, baseEnd_451858] using wordTrace_append hprefix tailTrace_451858
  have hstable : (prefixWord ++ tailWord_451858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451858).length < 2 ^ (prefixWord ++ tailWord_451858).sum := by decide
  have hdescent : baseEnd_451858 < baseStart_451858 := by decide
  rcases family_descends (prefixWord ++ tailWord_451858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451859 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_451859 : Nat := 118140960795 + 451859 * 2 ^ 59
def prefixEnd_451859 : Nat := 4983230072969 + 3 ^ 40 * 451859 * 2
def baseEnd_451859 : Nat := 206240760053380296252839

theorem tailTrace_451859 : CollatzResearch.WordTrace tailWord_451859 prefixEnd_451859 206240760053380296252839 := by
  unfold tailWord_451859
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480651669999489218382631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10987101113332992812255087 16480651669999489218382631)
  ·
    refine ⟨24720977504999233827573947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16480651669999489218382631 24720977504999233827573947)
    ·
      refine ⟨37081466257498850741360921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24720977504999233827573947 37081466257498850741360921)
      ·
        refine ⟨27811099693124138056020691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37081466257498850741360921 27811099693124138056020691)
        ·
          refine ⟨41716649539686207084031037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27811099693124138056020691 41716649539686207084031037)
          ·
            refine ⟨15643743577382327656511639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41716649539686207084031037 15643743577382327656511639)
            ·
              refine ⟨23465615366073491484767459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15643743577382327656511639 23465615366073491484767459)
              ·
                refine ⟨35198423049110237227151189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23465615366073491484767459 35198423049110237227151189)
                ·
                  refine ⟨206240760053380296252839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35198423049110237227151189 206240760053380296252839)
                  ·
                    rfl

theorem cell20_451859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_451859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451859 prefixEnd_451859 := by exact prefixLift 451859
  have htrace : WordTrace (prefixWord ++ tailWord_451859) baseStart_451859 baseEnd_451859 := by
    simpa [prefixWord, tailWord_451859, baseEnd_451859] using wordTrace_append hprefix tailTrace_451859
  have hstable : (prefixWord ++ tailWord_451859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451859).length < 2 ^ (prefixWord ++ tailWord_451859).sum := by decide
  have hdescent : baseEnd_451859 < baseStart_451859 := by decide
  rcases family_descends (prefixWord ++ tailWord_451859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451876 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_451876 : Nat := 118140960795 + 451876 * 2 ^ 59
def prefixEnd_451876 : Nat := 4983230072969 + 3 ^ 40 * 451876 * 2
def baseEnd_451876 : Nat := 206248519316603792686103

theorem tailTrace_451876 : CollatzResearch.WordTrace tailWord_451876 prefixEnd_451876 206248519316603792686103 := by
  unfold tailWord_451876
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240635855468950560875741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10987514473958600747834321 8240635855468950560875741)
  ·
    refine ⟨3090238445800856460328403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8240635855468950560875741 3090238445800856460328403)
    ·
      refine ⟨4635357668701284690492605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3090238445800856460328403 4635357668701284690492605)
      ·
        refine ⟨1738259125762981758934727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4635357668701284690492605 1738259125762981758934727)
        ·
          refine ⟨2607388688644472638402091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738259125762981758934727 2607388688644472638402091)
          ·
            refine ⟨3911083032966708957603137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607388688644472638402091 3911083032966708957603137)
            ·
              refine ⟨2933312274725031718202353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3911083032966708957603137 2933312274725031718202353)
              ·
                refine ⟨2199984206043773788651765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933312274725031718202353 2199984206043773788651765)
                ·
                  refine ⟨206248519316603792686103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2199984206043773788651765 206248519316603792686103)
                  ·
                    rfl

theorem cell20_451876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_451876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451876 prefixEnd_451876 := by exact prefixLift 451876
  have htrace : WordTrace (prefixWord ++ tailWord_451876) baseStart_451876 baseEnd_451876 := by
    simpa [prefixWord, tailWord_451876, baseEnd_451876] using wordTrace_append hprefix tailTrace_451876
  have hstable : (prefixWord ++ tailWord_451876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451876).length < 2 ^ (prefixWord ++ tailWord_451876).sum := by decide
  have hdescent : baseEnd_451876 < baseStart_451876 := by decide
  rcases family_descends (prefixWord ++ tailWord_451876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451893 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_451893 : Nat := 118140960795 + 451893 * 2 ^ 59
def prefixEnd_451893 : Nat := 4983230072969 + 3 ^ 40 * 451893 * 2
def baseEnd_451893 : Nat := 206256278579827289119367

theorem tailTrace_451893 : CollatzResearch.WordTrace tailWord_451893 prefixEnd_451893 206256278579827289119367 := by
  unfold tailWord_451893
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481891751876313025120333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10987927834584208683413555 16481891751876313025120333)
  ·
    refine ⟨6180709406953617384420125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16481891751876313025120333 6180709406953617384420125)
    ·
      refine ⟨2317766027607606519157547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6180709406953617384420125 2317766027607606519157547)
      ·
        refine ⟨3476649041411409778736321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317766027607606519157547 3476649041411409778736321)
        ·
          refine ⟨2607486781058557334052241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3476649041411409778736321 2607486781058557334052241)
          ·
            refine ⟨1955615085793918000539181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607486781058557334052241 1955615085793918000539181)
            ·
              refine ⟨733355657172719250202193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1955615085793918000539181 733355657172719250202193)
              ·
                refine ⟨550016742879539437651645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733355657172719250202193 550016742879539437651645)
                ·
                  refine ⟨206256278579827289119367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550016742879539437651645 206256278579827289119367)
                  ·
                    rfl

theorem cell20_451893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_451893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451893 prefixEnd_451893 := by exact prefixLift 451893
  have htrace : WordTrace (prefixWord ++ tailWord_451893) baseStart_451893 baseEnd_451893 := by
    simpa [prefixWord, tailWord_451893, baseEnd_451893] using wordTrace_append hprefix tailTrace_451893
  have hstable : (prefixWord ++ tailWord_451893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451893).length < 2 ^ (prefixWord ++ tailWord_451893).sum := by decide
  have hdescent : baseEnd_451893 < baseStart_451893 := by decide
  rcases family_descends (prefixWord ++ tailWord_451893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451900 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_451900 : Nat := 118140960795 + 451900 * 2 ^ 59
def prefixEnd_451900 : Nat := 4983230072969 + 3 ^ 40 * 451900 * 2
def baseEnd_451900 : Nat := 206259473570566375886005

theorem tailTrace_451900 : CollatzResearch.WordTrace tailWord_451900 prefixEnd_451900 206259473570566375886005 := by
  unfold tailWord_451900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241073531425476610312577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10988098041900635480416769 8241073531425476610312577)
  ·
    refine ⟨6180805148569107457734433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8241073531425476610312577 6180805148569107457734433)
    ·
      refine ⟨4635603861426830593300825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6180805148569107457734433 4635603861426830593300825)
      ·
        refine ⟨3476702896070122944975619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635603861426830593300825 3476702896070122944975619)
        ·
          refine ⟨5215054344105184417463429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476702896070122944975619 5215054344105184417463429)
          ·
            refine ⟨977822689519722078274393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5215054344105184417463429 977822689519722078274393)
            ·
              refine ⟨733367017139791558705795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977822689519722078274393 733367017139791558705795)
              ·
                refine ⟨1100050525709687338058693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733367017139791558705795 1100050525709687338058693)
                ·
                  refine ⟨206259473570566375886005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100050525709687338058693 206259473570566375886005)
                  ·
                    rfl

theorem cell20_451900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_451900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451900 prefixEnd_451900 := by exact prefixLift 451900
  have htrace : WordTrace (prefixWord ++ tailWord_451900) baseStart_451900 baseEnd_451900 := by
    simpa [prefixWord, tailWord_451900, baseEnd_451900] using wordTrace_append hprefix tailTrace_451900
  have hstable : (prefixWord ++ tailWord_451900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451900).length < 2 ^ (prefixWord ++ tailWord_451900).sum := by decide
  have hdescent : baseEnd_451900 < baseStart_451900 := by decide
  rcases family_descends (prefixWord ++ tailWord_451900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451914 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_451914 : Nat := 118140960795 + 451914 * 2 ^ 59
def prefixEnd_451914 : Nat := 4983230072969 + 3 ^ 40 * 451914 * 2
def baseEnd_451914 : Nat := 206265863552044549419281

theorem tailTrace_451914 : CollatzResearch.WordTrace tailWord_451914 prefixEnd_451914 206265863552044549419281 := by
  unfold tailWord_451914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4120664421200058402908699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10988438456533489074423197 4120664421200058402908699)
  ·
    refine ⟨6180996631800087604363049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4120664421200058402908699 6180996631800087604363049)
    ·
      refine ⟨4635747473850065703272287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6180996631800087604363049 4635747473850065703272287)
      ·
        refine ⟨6953621210775098554908431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635747473850065703272287 6953621210775098554908431)
        ·
          refine ⟨10430431816162647832362647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953621210775098554908431 10430431816162647832362647)
          ·
            refine ⟨15645647724243971748543971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430431816162647832362647 15645647724243971748543971)
            ·
              refine ⟨23468471586365957622815957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15645647724243971748543971 23468471586365957622815957)
              ·
                refine ⟨550042302805452131784749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23468471586365957622815957 550042302805452131784749)
                ·
                  refine ⟨206265863552044549419281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550042302805452131784749 206265863552044549419281)
                  ·
                    rfl

theorem cell20_451914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_451914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451914 prefixEnd_451914 := by exact prefixLift 451914
  have htrace : WordTrace (prefixWord ++ tailWord_451914) baseStart_451914 baseEnd_451914 := by
    simpa [prefixWord, tailWord_451914, baseEnd_451914] using wordTrace_append hprefix tailTrace_451914
  have hstable : (prefixWord ++ tailWord_451914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451914).length < 2 ^ (prefixWord ++ tailWord_451914).sum := by decide
  have hdescent : baseEnd_451914 < baseStart_451914 := by decide
  rcases family_descends (prefixWord ++ tailWord_451914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451921 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_451921 : Nat := 118140960795 + 451921 * 2 ^ 59
def prefixEnd_451921 : Nat := 4983230072969 + 3 ^ 40 * 451921 * 2
def baseEnd_451921 : Nat := 206269058542783636185919

theorem tailTrace_451921 : CollatzResearch.WordTrace tailWord_451921 prefixEnd_451921 206269058542783636185919 := by
  unfold tailWord_451921
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482912995774873807139617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10988608663849915871426411 16482912995774873807139617)
  ·
    refine ⟨12362184746831155355354713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16482912995774873807139617 12362184746831155355354713)
    ·
      refine ⟨9271638560123366516516035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12362184746831155355354713 9271638560123366516516035)
      ·
        refine ⟨13907457840185049774774053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271638560123366516516035 13907457840185049774774053)
        ·
          refine ⟨2607648345034696832770135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13907457840185049774774053 2607648345034696832770135)
          ·
            refine ⟨3911472517552045249155203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607648345034696832770135 3911472517552045249155203)
            ·
              refine ⟨5867208776328067873732805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911472517552045249155203 5867208776328067873732805)
              ·
                refine ⟨1100101645561512726324901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5867208776328067873732805 1100101645561512726324901)
                ·
                  refine ⟨206269058542783636185919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100101645561512726324901 206269058542783636185919)
                  ·
                    rfl

theorem cell20_451921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_451921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451921 prefixEnd_451921 := by exact prefixLift 451921
  have htrace : WordTrace (prefixWord ++ tailWord_451921) baseStart_451921 baseEnd_451921 := by
    simpa [prefixWord, tailWord_451921, baseEnd_451921] using wordTrace_append hprefix tailTrace_451921
  have hstable : (prefixWord ++ tailWord_451921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451921).length < 2 ^ (prefixWord ++ tailWord_451921).sum := by decide
  have hdescent : baseEnd_451921 < baseStart_451921 := by decide
  rcases family_descends (prefixWord ++ tailWord_451921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451926 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_451926 : Nat := 118140960795 + 451926 * 2 ^ 59
def prefixEnd_451926 : Nat := 4983230072969 + 3 ^ 40 * 451926 * 2
def baseEnd_451926 : Nat := 206271340679025841019233

theorem tailTrace_451926 : CollatzResearch.WordTrace tailWord_451926 prefixEnd_451926 206271340679025841019233 := by
  unfold tailWord_451926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030193460047297478816977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10988730240504506440714421 1030193460047297478816977)
  ·
    refine ⟨772645095035473109112733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1030193460047297478816977 772645095035473109112733)
    ·
      refine ⟨289741910638302415917275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 772645095035473109112733 289741910638302415917275)
      ·
        refine ⟨434612865957453623875913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289741910638302415917275 434612865957453623875913)
        ·
          refine ⟨325959649468090217906935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434612865957453623875913 325959649468090217906935)
          ·
            refine ⟨488939474202135326860403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325959649468090217906935 488939474202135326860403)
            ·
              refine ⟨733409211303202990290605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488939474202135326860403 733409211303202990290605)
              ·
                refine ⟨275028454238701121358977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733409211303202990290605 275028454238701121358977)
                ·
                  refine ⟨206271340679025841019233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275028454238701121358977 206271340679025841019233)
                  ·
                    rfl

theorem cell20_451926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_451926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451926 prefixEnd_451926 := by exact prefixLift 451926
  have htrace : WordTrace (prefixWord ++ tailWord_451926) baseStart_451926 baseEnd_451926 := by
    simpa [prefixWord, tailWord_451926, baseEnd_451926] using wordTrace_append hprefix tailTrace_451926
  have hstable : (prefixWord ++ tailWord_451926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451926).length < 2 ^ (prefixWord ++ tailWord_451926).sum := by decide
  have hdescent : baseEnd_451926 < baseStart_451926 := by decide
  rcases family_descends (prefixWord ++ tailWord_451926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451928 : List Nat := [2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_451928 : Nat := 118140960795 + 451928 * 2 ^ 59
def prefixEnd_451928 : Nat := 4983230072969 + 3 ^ 40 * 451928 * 2
def baseEnd_451928 : Nat := 68757417844507574317519

theorem tailTrace_451928 : CollatzResearch.WordTrace tailWord_451928 prefixEnd_451928 68757417844507574317519 := by
  unfold tailWord_451928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241584153374757001322219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10988778871166342668429625 8241584153374757001322219)
  ·
    refine ⟨12362376230062135501983329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241584153374757001322219 12362376230062135501983329)
    ·
      refine ⟨9271782172546601626487497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12362376230062135501983329 9271782172546601626487497)
      ·
        refine ⟨6953836629409951219865623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9271782172546601626487497 6953836629409951219865623)
        ·
          refine ⟨10430754944114926829798435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953836629409951219865623 10430754944114926829798435)
          ·
            refine ⟨15646132416172390244697653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430754944114926829798435 15646132416172390244697653)
            ·
              refine ⟨1466824914016161585440405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15646132416172390244697653 1466824914016161585440405)
              ·
                refine ⟨68757417844507574317519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1466824914016161585440405 68757417844507574317519)
                ·
                  rfl

theorem cell20_451928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_451928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451928 prefixEnd_451928 := by exact prefixLift 451928
  have htrace : WordTrace (prefixWord ++ tailWord_451928) baseStart_451928 baseEnd_451928 := by
    simpa [prefixWord, tailWord_451928, baseEnd_451928] using wordTrace_append hprefix tailTrace_451928
  have hstable : (prefixWord ++ tailWord_451928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451928).length < 2 ^ (prefixWord ++ tailWord_451928).sum := by decide
  have hdescent : baseEnd_451928 < baseStart_451928 := by decide
  rcases family_descends (prefixWord ++ tailWord_451928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451952 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_451952 : Nat := 118140960795 + 451952 * 2 ^ 59
def prefixEnd_451952 : Nat := 4983230072969 + 3 ^ 40 * 451952 * 2
def baseEnd_451952 : Nat := 206283207787485306152459

theorem tailTrace_451952 : CollatzResearch.WordTrace tailWord_451952 prefixEnd_451952 206283207787485306152459 := by
  unfold tailWord_451952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8242021829331283050759055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10989362439108377401012073 8242021829331283050759055)
  ·
    refine ⟨12363032743996924576138583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8242021829331283050759055 12363032743996924576138583)
    ·
      refine ⟨18544549115995386864207875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12363032743996924576138583 18544549115995386864207875)
      ·
        refine ⟨27816823673993080296311813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18544549115995386864207875 27816823673993080296311813)
        ·
          refine ⟨5215654438873702555558465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27816823673993080296311813 5215654438873702555558465)
          ·
            refine ⟨3911740829155276916668849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5215654438873702555558465 3911740829155276916668849)
            ·
              refine ⟨2933805621866457687501637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3911740829155276916668849 2933805621866457687501637)
              ·
                refine ⟨550088554099960816406557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2933805621866457687501637 550088554099960816406557)
                ·
                  refine ⟨206283207787485306152459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550088554099960816406557 206283207787485306152459)
                  ·
                    rfl

theorem cell20_451952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_451952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_451952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_451952 prefixEnd_451952 := by exact prefixLift 451952
  have htrace : WordTrace (prefixWord ++ tailWord_451952) baseStart_451952 baseEnd_451952 := by
    simpa [prefixWord, tailWord_451952, baseEnd_451952] using wordTrace_append hprefix tailTrace_451952
  have hstable : (prefixWord ++ tailWord_451952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451952).length < 2 ^ (prefixWord ++ tailWord_451952).sum := by decide
  have hdescent : baseEnd_451952 < baseStart_451952 := by decide
  rcases family_descends (prefixWord ++ tailWord_451952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452007 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_452007 : Nat := 118140960795 + 452007 * 2 ^ 59
def prefixEnd_452007 : Nat := 4983230072969 + 3 ^ 40 * 452007 * 2
def baseEnd_452007 : Nat := 206308311286149559318901

theorem tailTrace_452007 : CollatzResearch.WordTrace tailWord_452007 prefixEnd_452007 206308311286149559318901 := by
  unfold tailWord_452007
  simp only [CollatzResearch.WordTrace]
  refine ⟨16486049673463310494770275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10990699782308873663180183 16486049673463310494770275)
  ·
    refine ⟨24729074510194965742155413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16486049673463310494770275 24729074510194965742155413)
    ·
      refine ⟨1159175367665389019163535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24729074510194965742155413 1159175367665389019163535)
      ·
        refine ⟨1738763051498083528745303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159175367665389019163535 1738763051498083528745303)
        ·
          refine ⟨2608144577247125293117955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738763051498083528745303 2608144577247125293117955)
          ·
            refine ⟨3912216865870687939676933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608144577247125293117955 3912216865870687939676933)
            ·
              refine ⟨733540662350753988689425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3912216865870687939676933 733540662350753988689425)
              ·
                refine ⟨550155496763065491517069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733540662350753988689425 550155496763065491517069)
                ·
                  refine ⟨206308311286149559318901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550155496763065491517069 206308311286149559318901)
                  ·
                    rfl

theorem cell20_452007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_452007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452007 prefixEnd_452007 := by exact prefixLift 452007
  have htrace : WordTrace (prefixWord ++ tailWord_452007) baseStart_452007 baseEnd_452007 := by
    simpa [prefixWord, tailWord_452007, baseEnd_452007] using wordTrace_append hprefix tailTrace_452007
  have hstable : (prefixWord ++ tailWord_452007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452007).length < 2 ^ (prefixWord ++ tailWord_452007).sum := by decide
  have hdescent : baseEnd_452007 < baseStart_452007 := by decide
  rcases family_descends (prefixWord ++ tailWord_452007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452021 : List Nat := [1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_452021 : Nat := 118140960795 + 452021 * 2 ^ 59
def prefixEnd_452021 : Nat := 4983230072969 + 3 ^ 40 * 452021 * 2
def baseEnd_452021 : Nat := 68771567089209244284059

theorem tailTrace_452021 : CollatzResearch.WordTrace tailWord_452021 prefixEnd_452021 68771567089209244284059 := by
  unfold tailWord_452021
  simp only [CollatzResearch.WordTrace]
  refine ⟨16486560295412590885779917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10991040196941727257186611 16486560295412590885779917)
  ·
    refine ⟨6182460110779721582167469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16486560295412590885779917 6182460110779721582167469)
    ·
      refine ⟨2318422541542395593312801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6182460110779721582167469 2318422541542395593312801)
      ·
        refine ⟨1738816906156796694984601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2318422541542395593312801 1738816906156796694984601)
        ·
          refine ⟨1304112679617597521238451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1738816906156796694984601 1304112679617597521238451)
          ·
            refine ⟨1956169019426396281857677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304112679617597521238451 1956169019426396281857677)
            ·
              refine ⟨733563382284898605696629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1956169019426396281857677 733563382284898605696629)
              ·
                refine ⟨68771567089209244284059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733563382284898605696629 68771567089209244284059)
                ·
                  rfl

theorem cell20_452021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_452021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452021 prefixEnd_452021 := by exact prefixLift 452021
  have htrace : WordTrace (prefixWord ++ tailWord_452021) baseStart_452021 baseEnd_452021 := by
    simpa [prefixWord, tailWord_452021, baseEnd_452021] using wordTrace_append hprefix tailTrace_452021
  have hstable : (prefixWord ++ tailWord_452021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452021).length < 2 ^ (prefixWord ++ tailWord_452021).sum := by decide
  have hdescent : baseEnd_452021 < baseStart_452021 := by decide
  rcases family_descends (prefixWord ++ tailWord_452021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452069 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 2]
def baseStart_452069 : Nat := 118140960795 + 452069 * 2 ^ 59
def prefixEnd_452069 : Nat := 4983230072969 + 3 ^ 40 * 452069 * 2
def baseEnd_452069 : Nat := 206336609775552899251981

theorem tailTrace_452069 : CollatzResearch.WordTrace tailWord_452069 prefixEnd_452069 206336609775552899251981 := by
  unfold tailWord_452069
  simp only [CollatzResearch.WordTrace]
  refine ⟨16488310999238695083527261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10992207332825796722351507 16488310999238695083527261)
  ·
    refine ⟨6183116624714510656322723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16488310999238695083527261 6183116624714510656322723)
    ·
      refine ⟨9274674937071765984484085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6183116624714510656322723 9274674937071765984484085)
      ·
        refine ⟨869500775350478061045383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9274674937071765984484085 869500775350478061045383)
        ·
          refine ⟨1304251163025717091568075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869500775350478061045383 1304251163025717091568075)
          ·
            refine ⟨1956376744538575637352113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304251163025717091568075 1956376744538575637352113)
            ·
              refine ⟨1467282558403931728014085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956376744538575637352113 1467282558403931728014085)
              ·
                refine ⟨275115479700737199002641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1467282558403931728014085 275115479700737199002641)
                ·
                  refine ⟨206336609775552899251981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275115479700737199002641 206336609775552899251981)
                  ·
                    rfl

theorem cell20_452069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_452069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452069 prefixEnd_452069 := by exact prefixLift 452069
  have htrace : WordTrace (prefixWord ++ tailWord_452069) baseStart_452069 baseEnd_452069 := by
    simpa [prefixWord, tailWord_452069, baseEnd_452069] using wordTrace_append hprefix tailTrace_452069
  have hstable : (prefixWord ++ tailWord_452069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452069).length < 2 ^ (prefixWord ++ tailWord_452069).sum := by decide
  have hdescent : baseEnd_452069 < baseStart_452069 := by decide
  rcases family_descends (prefixWord ++ tailWord_452069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452097 : List Nat := [1, 2, 4, 1, 4, 1, 1, 6]
def baseStart_452097 : Nat := 118140960795 + 452097 * 2 ^ 59
def prefixEnd_452097 : Nat := 4983230072969 + 3 ^ 40 * 452097 * 2
def baseEnd_452097 : Nat := 68783129912836415439511

theorem tailTrace_452097 : CollatzResearch.WordTrace tailWord_452097 prefixEnd_452097 68783129912836415439511 := by
  unfold tailWord_452097
  simp only [CollatzResearch.WordTrace]
  refine ⟨16489332243137255865546545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10992888162091503910364363 16489332243137255865546545)
  ·
    refine ⟨12366999182352941899159909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16489332243137255865546545 12366999182352941899159909)
    ·
      refine ⟨2318812346691176606092483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12366999182352941899159909 2318812346691176606092483)
      ·
        refine ⟨3478218520036764909138725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318812346691176606092483 3478218520036764909138725)
        ·
          refine ⟨652165972506893420463511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3478218520036764909138725 652165972506893420463511)
          ·
            refine ⟨978248958760340130695267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652165972506893420463511 978248958760340130695267)
            ·
              refine ⟨1467373438140510196042901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978248958760340130695267 1467373438140510196042901)
              ·
                refine ⟨68783129912836415439511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1467373438140510196042901 68783129912836415439511)
                ·
                  rfl

theorem cell20_452097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_452097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452097 prefixEnd_452097 := by exact prefixLift 452097
  have htrace : WordTrace (prefixWord ++ tailWord_452097) baseStart_452097 baseEnd_452097 := by
    simpa [prefixWord, tailWord_452097, baseEnd_452097] using wordTrace_append hprefix tailTrace_452097
  have hstable : (prefixWord ++ tailWord_452097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452097).length < 2 ^ (prefixWord ++ tailWord_452097).sum := by decide
  have hdescent : baseEnd_452097 < baseStart_452097 := by decide
  rcases family_descends (prefixWord ++ tailWord_452097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452128 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_452128 : Nat := 118140960795 + 452128 * 2 ^ 59
def prefixEnd_452128 : Nat := 4983230072969 + 3 ^ 40 * 452128 * 2
def baseEnd_452128 : Nat := 206363538983210916285073

theorem tailTrace_452128 : CollatzResearch.WordTrace tailWord_452128 prefixEnd_452128 206363538983210916285073 := by
  unfold tailWord_452128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245231453012474079962519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10993641937349965439950025 8245231453012474079962519)
  ·
    refine ⟨12367847179518711119943779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8245231453012474079962519 12367847179518711119943779)
    ·
      refine ⟨18551770769278066679915669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367847179518711119943779 18551770769278066679915669)
      ·
        refine ⟨869614254809909375621047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18551770769278066679915669 869614254809909375621047)
        ·
          refine ⟨1304421382214864063431571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869614254809909375621047 1304421382214864063431571)
          ·
            refine ⟨1956632073322296095147357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304421382214864063431571 1956632073322296095147357)
            ·
              refine ⟨733737027495861035680259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1956632073322296095147357 733737027495861035680259)
              ·
                refine ⟨1100605541243791553520389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733737027495861035680259 1100605541243791553520389)
                ·
                  refine ⟨206363538983210916285073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1100605541243791553520389 206363538983210916285073)
                  ·
                    rfl

theorem cell20_452128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_452128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452128 prefixEnd_452128 := by exact prefixLift 452128
  have htrace : WordTrace (prefixWord ++ tailWord_452128) baseStart_452128 baseEnd_452128 := by
    simpa [prefixWord, tailWord_452128, baseEnd_452128] using wordTrace_append hprefix tailTrace_452128
  have hstable : (prefixWord ++ tailWord_452128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452128).length < 2 ^ (prefixWord ++ tailWord_452128).sum := by decide
  have hdescent : baseEnd_452128 < baseStart_452128 := by decide
  rcases family_descends (prefixWord ++ tailWord_452128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452173 : List Nat := [1, 6, 1, 1, 3, 8]
def baseStart_452173 : Nat := 118140960795 + 452173 * 2 ^ 59
def prefixEnd_452173 : Nat := 4983230072969 + 3 ^ 40 * 452173 * 2
def baseEnd_452173 : Nat := 7643854748495954066107

theorem tailTrace_452173 : CollatzResearch.WordTrace tailWord_452173 prefixEnd_452173 7643854748495954066107 := by
  unfold tailWord_452173
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492104190861920845313173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10994736127241280563542115 16492104190861920845313173)
  ·
    refine ⟨773067383946652539624055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16492104190861920845313173 773067383946652539624055)
    ·
      refine ⟨1159601075919978809436083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773067383946652539624055 1159601075919978809436083)
      ·
        refine ⟨1739401613879968214154125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159601075919978809436083 1739401613879968214154125)
        ·
          refine ⟨652275605204988080307797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1739401613879968214154125 652275605204988080307797)
          ·
            refine ⟨7643854748495954066107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 652275605204988080307797 7643854748495954066107)
            ·
              rfl

theorem cell20_452173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 8].length) (baseStart_452173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452173 prefixEnd_452173 := by exact prefixLift 452173
  have htrace : WordTrace (prefixWord ++ tailWord_452173) baseStart_452173 baseEnd_452173 := by
    simpa [prefixWord, tailWord_452173, baseEnd_452173] using wordTrace_append hprefix tailTrace_452173
  have hstable : (prefixWord ++ tailWord_452173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452173).length < 2 ^ (prefixWord ++ tailWord_452173).sum := by decide
  have hdescent : baseEnd_452173 < baseStart_452173 := by decide
  rcases family_descends (prefixWord ++ tailWord_452173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452183 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 2]
def baseStart_452183 : Nat := 118140960795 + 452183 * 2 ^ 59
def prefixEnd_452183 : Nat := 4983230072969 + 3 ^ 40 * 452183 * 2
def baseEnd_452183 : Nat := 206388642481875169451515

theorem tailTrace_452183 : CollatzResearch.WordTrace tailWord_452183 prefixEnd_452183 206388642481875169451515 := by
  unfold tailWord_452183
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492468920825692553177203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10994979280550461702118135 16492468920825692553177203)
  ·
    refine ⟨24738703381238538829765805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16492468920825692553177203 24738703381238538829765805)
    ·
      refine ⟨9277013767964452061162177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24738703381238538829765805 9277013767964452061162177)
      ·
        refine ⟨6957760325973339045871633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9277013767964452061162177 6957760325973339045871633)
        ·
          refine ⟨5218320244480004284403725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6957760325973339045871633 5218320244480004284403725)
          ·
            refine ⟨1956870091680001606651397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5218320244480004284403725 1956870091680001606651397)
            ·
              refine ⟨366913142190000301247137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1956870091680001606651397 366913142190000301247137)
              ·
                refine ⟨275184856642500225935353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366913142190000301247137 275184856642500225935353)
                ·
                  refine ⟨206388642481875169451515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275184856642500225935353 206388642481875169451515)
                  ·
                    rfl

theorem cell20_452183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 2].length) (baseStart_452183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452183 prefixEnd_452183 := by exact prefixLift 452183
  have htrace : WordTrace (prefixWord ++ tailWord_452183) baseStart_452183 baseEnd_452183 := by
    simpa [prefixWord, tailWord_452183, baseEnd_452183] using wordTrace_append hprefix tailTrace_452183
  have hstable : (prefixWord ++ tailWord_452183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452183).length < 2 ^ (prefixWord ++ tailWord_452183).sum := by decide
  have hdescent : baseEnd_452183 < baseStart_452183 := by decide
  rcases family_descends (prefixWord ++ tailWord_452183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452221 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 2]
def baseStart_452221 : Nat := 118140960795 + 452221 * 2 ^ 59
def prefixEnd_452221 : Nat := 4983230072969 + 3 ^ 40 * 452221 * 2
def baseEnd_452221 : Nat := 206405986717315926184693

theorem tailTrace_452221 : CollatzResearch.WordTrace tailWord_452221 prefixEnd_452221 206405986717315926184693 := by
  unfold tailWord_452221
  simp only [CollatzResearch.WordTrace]
  refine ⟨16493854894688025043060517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10995903263125350028707011 16493854894688025043060517)
  ·
    refine ⟨3092597792754004695573847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16493854894688025043060517 3092597792754004695573847)
    ·
      refine ⟨4638896689131007043360771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092597792754004695573847 4638896689131007043360771)
      ·
        refine ⟨6958345033696510565041157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638896689131007043360771 6958345033696510565041157)
        ·
          refine ⟨1304689693818095730945217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6958345033696510565041157 1304689693818095730945217)
          ·
            refine ⟨978517270363571798208913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304689693818095730945217 978517270363571798208913)
            ·
              refine ⟨733887952772678848656685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978517270363571798208913 733887952772678848656685)
              ·
                refine ⟨275207982289754568246257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 733887952772678848656685 275207982289754568246257)
                ·
                  refine ⟨206405986717315926184693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275207982289754568246257 206405986717315926184693)
                  ·
                    rfl

theorem cell20_452221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_452221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452221 prefixEnd_452221 := by exact prefixLift 452221
  have htrace : WordTrace (prefixWord ++ tailWord_452221) baseStart_452221 baseEnd_452221 := by
    simpa [prefixWord, tailWord_452221, baseEnd_452221] using wordTrace_append hprefix tailTrace_452221
  have hstable : (prefixWord ++ tailWord_452221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452221).length < 2 ^ (prefixWord ++ tailWord_452221).sum := by decide
  have hdescent : baseEnd_452221 < baseStart_452221 := by decide
  rcases family_descends (prefixWord ++ tailWord_452221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452252 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_452252 : Nat := 118140960795 + 452252 * 2 ^ 59
def prefixEnd_452252 : Nat := 4983230072969 + 3 ^ 40 * 452252 * 2
def baseEnd_452252 : Nat := 206420135962017596151233

theorem tailTrace_452252 : CollatzResearch.WordTrace tailWord_452252 prefixEnd_452252 206420135962017596151233 := by
  unfold tailWord_452252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247492778787858668719505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10996657038383811558292673 8247492778787858668719505)
  ·
    refine ⟨6185619584090894001539629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8247492778787858668719505 6185619584090894001539629)
    ·
      refine ⟨2319607344034085250577361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6185619584090894001539629 2319607344034085250577361)
      ·
        refine ⟨1739705508025563937933021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319607344034085250577361 1739705508025563937933021)
        ·
          refine ⟨652389565509586476724883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1739705508025563937933021 652389565509586476724883)
          ·
            refine ⟨978584348264379715087325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652389565509586476724883 978584348264379715087325)
            ·
              refine ⟨366969130599142393157747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 978584348264379715087325 366969130599142393157747)
              ·
                refine ⟨550453695898713589736621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366969130599142393157747 550453695898713589736621)
                ·
                  refine ⟨206420135962017596151233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550453695898713589736621 206420135962017596151233)
                  ·
                    rfl

theorem cell20_452252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_452252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452252 prefixEnd_452252 := by exact prefixLift 452252
  have htrace : WordTrace (prefixWord ++ tailWord_452252) baseStart_452252 baseEnd_452252 := by
    simpa [prefixWord, tailWord_452252, baseEnd_452252] using wordTrace_append hprefix tailTrace_452252
  have hstable : (prefixWord ++ tailWord_452252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452252).length < 2 ^ (prefixWord ++ tailWord_452252).sum := by decide
  have hdescent : baseEnd_452252 < baseStart_452252 := by decide
  rcases family_descends (prefixWord ++ tailWord_452252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452353 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_452353 : Nat := 118140960795 + 452353 * 2 ^ 59
def prefixEnd_452353 : Nat := 4983230072969 + 3 ^ 40 * 452353 * 2
def baseEnd_452353 : Nat := 206466235114110133784153

theorem tailTrace_452353 : CollatzResearch.WordTrace tailWord_452353 prefixEnd_452353 206466235114110133784153 := by
  unfold tailWord_452353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498669330209811586865713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10999112886806541057910475 16498669330209811586865713)
  ·
    refine ⟨12374001997657358690149285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16498669330209811586865713 12374001997657358690149285)
    ·
      refine ⟨2320125374560754754402991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12374001997657358690149285 2320125374560754754402991)
      ·
        refine ⟨3480188061841132131604487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320125374560754754402991 3480188061841132131604487)
        ·
          refine ⟨5220282092761698197406731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480188061841132131604487 5220282092761698197406731)
          ·
            refine ⟨7830423139142547296110097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220282092761698197406731 7830423139142547296110097)
            ·
              refine ⟨5872817354356910472082573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7830423139142547296110097 5872817354356910472082573)
              ·
                refine ⟨2202306507883841427030965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5872817354356910472082573 2202306507883841427030965)
                ·
                  refine ⟨206466235114110133784153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2202306507883841427030965 206466235114110133784153)
                  ·
                    rfl

theorem cell20_452353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_452353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452353 prefixEnd_452353 := by exact prefixLift 452353
  have htrace : WordTrace (prefixWord ++ tailWord_452353) baseStart_452353 baseEnd_452353 := by
    simpa [prefixWord, tailWord_452353, baseEnd_452353] using wordTrace_append hprefix tailTrace_452353
  have hstable : (prefixWord ++ tailWord_452353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452353).length < 2 ^ (prefixWord ++ tailWord_452353).sum := by decide
  have hdescent : baseEnd_452353 < baseStart_452353 := by decide
  rcases family_descends (prefixWord ++ tailWord_452353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452367 : List Nat := [1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_452367 : Nat := 118140960795 + 452367 * 2 ^ 59
def prefixEnd_452367 : Nat := 4983230072969 + 3 ^ 40 * 452367 * 2
def baseEnd_452367 : Nat := 68824208365196102439143

theorem tailTrace_452367 : CollatzResearch.WordTrace tailWord_452367 prefixEnd_452367 68824208365196102439143 := by
  unfold tailWord_452367
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499179952159091977875355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10999453301439394651916903 16499179952159091977875355)
  ·
    refine ⟨24748769928238637966813033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16499179952159091977875355 24748769928238637966813033)
    ·
      refine ⟨18561577446178978475109775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24748769928238637966813033 18561577446178978475109775)
      ·
        refine ⟨27842366169268467712664663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18561577446178978475109775 27842366169268467712664663)
        ·
          refine ⟨41763549253902701568996995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27842366169268467712664663 41763549253902701568996995)
          ·
            refine ⟨62645323880854052353495493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41763549253902701568996995 62645323880854052353495493)
            ·
              refine ⟨11745998227660134816280405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62645323880854052353495493 11745998227660134816280405)
              ·
                refine ⟨68824208365196102439143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11745998227660134816280405 68824208365196102439143)
                ·
                  rfl

theorem cell20_452367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_452367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452367 prefixEnd_452367 := by exact prefixLift 452367
  have htrace : WordTrace (prefixWord ++ tailWord_452367) baseStart_452367 baseEnd_452367 := by
    simpa [prefixWord, tailWord_452367, baseEnd_452367] using wordTrace_append hprefix tailTrace_452367
  have hstable : (prefixWord ++ tailWord_452367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452367).length < 2 ^ (prefixWord ++ tailWord_452367).sum := by decide
  have hdescent : baseEnd_452367 < baseStart_452367 := by decide
  rcases family_descends (prefixWord ++ tailWord_452367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452404 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_452404 : Nat := 118140960795 + 452404 * 2 ^ 59
def prefixEnd_452404 : Nat := 4983230072969 + 3 ^ 40 * 452404 * 2
def baseEnd_452404 : Nat := 206489512903780623083945

theorem tailTrace_452404 : CollatzResearch.WordTrace tailWord_452404 prefixEnd_452404 206489512903780623083945 := by
  unfold tailWord_452404
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250264726512523648486133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11000352968683364864648177 8250264726512523648486133)
  ·
    refine ⟨773462318110549092045575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8250264726512523648486133 773462318110549092045575)
    ·
      refine ⟨1160193477165823638068363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773462318110549092045575 1160193477165823638068363)
      ·
        refine ⟨1740290215748735457102545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160193477165823638068363 1740290215748735457102545)
        ·
          refine ⟨1305217661811551592826909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1740290215748735457102545 1305217661811551592826909)
          ·
            refine ⟨489456623179331847310091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1305217661811551592826909 489456623179331847310091)
            ·
              refine ⟨734184934768997770965137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489456623179331847310091 734184934768997770965137)
              ·
                refine ⟨550638701076748328223853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734184934768997770965137 550638701076748328223853)
                ·
                  refine ⟨206489512903780623083945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550638701076748328223853 206489512903780623083945)
                  ·
                    rfl

theorem cell20_452404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_452404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452404 prefixEnd_452404 := by exact prefixLift 452404
  have htrace : WordTrace (prefixWord ++ tailWord_452404) baseStart_452404 baseEnd_452404 := by
    simpa [prefixWord, tailWord_452404, baseEnd_452404] using wordTrace_append hprefix tailTrace_452404
  have hstable : (prefixWord ++ tailWord_452404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452404).length < 2 ^ (prefixWord ++ tailWord_452404).sum := by decide
  have hdescent : baseEnd_452404 < baseStart_452404 := by decide
  rcases family_descends (prefixWord ++ tailWord_452404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452408 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_452408 : Nat := 118140960795 + 452408 * 2 ^ 59
def prefixEnd_452408 : Nat := 4983230072969 + 3 ^ 40 * 452408 * 2
def baseEnd_452408 : Nat := 206491338612774386950595

theorem tailTrace_452408 : CollatzResearch.WordTrace tailWord_452408 prefixEnd_452408 206491338612774386950595 := by
  unfold tailWord_452408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250337672505277990058939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11000450230007037320078585 8250337672505277990058939)
  ·
    refine ⟨12375506508757916985088409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8250337672505277990058939 12375506508757916985088409)
    ·
      refine ⟨9281629881568437738816307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12375506508757916985088409 9281629881568437738816307)
      ·
        refine ⟨13922444822352656608224461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281629881568437738816307 13922444822352656608224461)
        ·
          refine ⟨5220916808382246228084173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13922444822352656608224461 5220916808382246228084173)
          ·
            refine ⟨1957843803143342335531565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5220916808382246228084173 1957843803143342335531565)
            ·
              refine ⟨734191426178753375824337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1957843803143342335531565 734191426178753375824337)
              ·
                refine ⟨550643569634065031868253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734191426178753375824337 550643569634065031868253)
                ·
                  refine ⟨206491338612774386950595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550643569634065031868253 206491338612774386950595)
                  ·
                    rfl

theorem cell20_452408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_452408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452408 prefixEnd_452408 := by exact prefixLift 452408
  have htrace : WordTrace (prefixWord ++ tailWord_452408) baseStart_452408 baseEnd_452408 := by
    simpa [prefixWord, tailWord_452408, baseEnd_452408] using wordTrace_append hprefix tailTrace_452408
  have hstable : (prefixWord ++ tailWord_452408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452408).length < 2 ^ (prefixWord ++ tailWord_452408).sum := by decide
  have hdescent : baseEnd_452408 < baseStart_452408 := by decide
  rcases family_descends (prefixWord ++ tailWord_452408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452460 : List Nat := [2, 2, 1, 1, 4, 4, 6]
def baseStart_452460 : Nat := 118140960795 + 452460 * 2 ^ 59
def prefixEnd_452460 : Nat := 4983230072969 + 3 ^ 40 * 452460 * 2
def baseEnd_452460 : Nat := 22946119203299257468561

theorem tailTrace_452460 : CollatzResearch.WordTrace tailWord_452460 prefixEnd_452460 22946119203299257468561 := by
  unfold tailWord_452460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251285970411084430505417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11001714627214779240673889 8251285970411084430505417)
  ·
    refine ⟨6188464477808313322879063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8251285970411084430505417 6188464477808313322879063)
    ·
      refine ⟨9282696716712469984318595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188464477808313322879063 9282696716712469984318595)
      ·
        refine ⟨13924045075068704976477893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9282696716712469984318595 13924045075068704976477893)
        ·
          refine ⟨2610758451575382183089605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13924045075068704976477893 2610758451575382183089605)
          ·
            refine ⟨489517209670384159329301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2610758451575382183089605 489517209670384159329301)
            ·
              refine ⟨22946119203299257468561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 489517209670384159329301 22946119203299257468561)
              ·
                rfl

theorem cell20_452460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 6].length) (baseStart_452460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452460 prefixEnd_452460 := by exact prefixLift 452460
  have htrace : WordTrace (prefixWord ++ tailWord_452460) baseStart_452460 baseEnd_452460 := by
    simpa [prefixWord, tailWord_452460, baseEnd_452460] using wordTrace_append hprefix tailTrace_452460
  have hstable : (prefixWord ++ tailWord_452460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452460).length < 2 ^ (prefixWord ++ tailWord_452460).sum := by decide
  have hdescent : baseEnd_452460 < baseStart_452460 := by decide
  rcases family_descends (prefixWord ++ tailWord_452460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452467 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_452467 : Nat := 118140960795 + 452467 * 2 ^ 59
def prefixEnd_452467 : Nat := 4983230072969 + 3 ^ 40 * 452467 * 2
def baseEnd_452467 : Nat := 206518267820432403983687

theorem tailTrace_452467 : CollatzResearch.WordTrace tailWord_452467 prefixEnd_452467 206518267820432403983687 := by
  unfold tailWord_452467
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502827251796809056515655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11001884834531206037677103 16502827251796809056515655)
  ·
    refine ⟨24754240877695213584773483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16502827251796809056515655 24754240877695213584773483)
    ·
      refine ⟨37131361316542820377160225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24754240877695213584773483 37131361316542820377160225)
      ·
        refine ⟨27848520987407115282870169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37131361316542820377160225 27848520987407115282870169)
        ·
          refine ⟨20886390740555336462152627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27848520987407115282870169 20886390740555336462152627)
          ·
            refine ⟨31329586110833004693228941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20886390740555336462152627 31329586110833004693228941)
            ·
              refine ⟨11748594791562376759960853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31329586110833004693228941 11748594791562376759960853)
              ·
                refine ⟨550715380854486410623165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11748594791562376759960853 550715380854486410623165)
                ·
                  refine ⟨206518267820432403983687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550715380854486410623165 206518267820432403983687)
                  ·
                    rfl

theorem cell20_452467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_452467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452467 prefixEnd_452467 := by exact prefixLift 452467
  have htrace : WordTrace (prefixWord ++ tailWord_452467) baseStart_452467 baseEnd_452467 := by
    simpa [prefixWord, tailWord_452467, baseEnd_452467] using wordTrace_append hprefix tailTrace_452467
  have hstable : (prefixWord ++ tailWord_452467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452467).length < 2 ^ (prefixWord ++ tailWord_452467).sum := by decide
  have hdescent : baseEnd_452467 < baseStart_452467 := by decide
  rcases family_descends (prefixWord ++ tailWord_452467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452543 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_452543 : Nat := 118140960795 + 452543 * 2 ^ 59
def prefixEnd_452543 : Nat := 4983230072969 + 3 ^ 40 * 452543 * 2
def baseEnd_452543 : Nat := 206552956291313917450043

theorem tailTrace_452543 : CollatzResearch.WordTrace tailWord_452543 prefixEnd_452543 206552956291313917450043 := by
  unfold tailWord_452543
  simp only [CollatzResearch.WordTrace]
  refine ⟨16505599199521474036282283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11003732799680982690854855 16505599199521474036282283)
  ·
    refine ⟨24758398799282211054423425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16505599199521474036282283 24758398799282211054423425)
    ·
      refine ⟨18568799099461658290817569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24758398799282211054423425 18568799099461658290817569)
      ·
        refine ⟨13926599324596243718113177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18568799099461658290817569 13926599324596243718113177)
        ·
          refine ⟨10444949493447182788584883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13926599324596243718113177 10444949493447182788584883)
          ·
            refine ⟨15667424240170774182877325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444949493447182788584883 15667424240170774182877325)
            ·
              refine ⟨5875284090064040318578997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15667424240170774182877325 5875284090064040318578997)
              ·
                refine ⟨550807883443503779866781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5875284090064040318578997 550807883443503779866781)
                ·
                  refine ⟨206552956291313917450043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550807883443503779866781 206552956291313917450043)
                  ·
                    rfl

theorem cell20_452543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_452543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452543 prefixEnd_452543 := by exact prefixLift 452543
  have htrace : WordTrace (prefixWord ++ tailWord_452543) baseStart_452543 baseEnd_452543 := by
    simpa [prefixWord, tailWord_452543, baseEnd_452543] using wordTrace_append hprefix tailTrace_452543
  have hstable : (prefixWord ++ tailWord_452543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452543).length < 2 ^ (prefixWord ++ tailWord_452543).sum := by decide
  have hdescent : baseEnd_452543 < baseStart_452543 := by decide
  rcases family_descends (prefixWord ++ tailWord_452543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452618 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_452618 : Nat := 118140960795 + 452618 * 2 ^ 59
def prefixEnd_452618 : Nat := 4983230072969 + 3 ^ 40 * 452618 * 2
def baseEnd_452618 : Nat := 206587188334946989949737

theorem tailTrace_452618 : CollatzResearch.WordTrace tailWord_452618 prefixEnd_452618 206587188334946989949737 := by
  unfold tailWord_452618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127083668562440461315627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11005556449499841230175005 4127083668562440461315627)
  ·
    refine ⟨6190625502843660691973441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4127083668562440461315627 6190625502843660691973441)
    ·
      refine ⟨4642969127132745518980081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6190625502843660691973441 4642969127132745518980081)
      ·
        refine ⟨3482226845349559139235061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642969127132745518980081 3482226845349559139235061)
        ·
          refine ⟨326458766751521169303287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3482226845349559139235061 326458766751521169303287)
          ·
            refine ⟨489688150127281753954931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326458766751521169303287 489688150127281753954931)
            ·
              refine ⟨734532225190922630932397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489688150127281753954931 734532225190922630932397)
              ·
                refine ⟨275449584446595986599649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 734532225190922630932397 275449584446595986599649)
                ·
                  refine ⟨206587188334946989949737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275449584446595986599649 206587188334946989949737)
                  ·
                    rfl

theorem cell20_452618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_452618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452618 prefixEnd_452618 := by exact prefixLift 452618
  have htrace : WordTrace (prefixWord ++ tailWord_452618) baseStart_452618 baseEnd_452618 := by
    simpa [prefixWord, tailWord_452618, baseEnd_452618] using wordTrace_append hprefix tailTrace_452618
  have hstable : (prefixWord ++ tailWord_452618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452618).length < 2 ^ (prefixWord ++ tailWord_452618).sum := by decide
  have hdescent : baseEnd_452618 < baseStart_452618 := by decide
  rcases family_descends (prefixWord ++ tailWord_452618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452629 : List Nat := [1, 3, 2, 1, 6, 1, 6]
def baseStart_452629 : Nat := 118140960795 + 452629 * 2 ^ 59
def prefixEnd_452629 : Nat := 4983230072969 + 3 ^ 40 * 452629 * 2
def baseEnd_452629 : Nat := 22954689892742204509225

theorem tailTrace_452629 : CollatzResearch.WordTrace tailWord_452629 prefixEnd_452629 22954689892742204509225 := by
  unfold tailWord_452629
  simp only [CollatzResearch.WordTrace]
  refine ⟨16508735877209910723912941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11005823918139940482608627 16508735877209910723912941)
  ·
    refine ⟨6190775953953716521467353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16508735877209910723912941 6190775953953716521467353)
    ·
      refine ⟨4643081965465287391100515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6190775953953716521467353 4643081965465287391100515)
      ·
        refine ⟨6964622948197931086650773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643081965465287391100515 6964622948197931086650773)
        ·
          refine ⟨326466700696778019686755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6964622948197931086650773 326466700696778019686755)
          ·
            refine ⟨489700051045167029530133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326466700696778019686755 489700051045167029530133)
            ·
              refine ⟨22954689892742204509225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 489700051045167029530133 22954689892742204509225)
              ·
                rfl

theorem cell20_452629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 6].length) (baseStart_452629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452629 prefixEnd_452629 := by exact prefixLift 452629
  have htrace : WordTrace (prefixWord ++ tailWord_452629) baseStart_452629 baseEnd_452629 := by
    simpa [prefixWord, tailWord_452629, baseEnd_452629] using wordTrace_append hprefix tailTrace_452629
  have hstable : (prefixWord ++ tailWord_452629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452629).length < 2 ^ (prefixWord ++ tailWord_452629).sum := by decide
  have hdescent : baseEnd_452629 < baseStart_452629 := by decide
  rcases family_descends (prefixWord ++ tailWord_452629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452650 : List Nat := [3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_452650 : Nat := 118140960795 + 452650 * 2 ^ 59
def prefixEnd_452650 : Nat := 4983230072969 + 3 ^ 40 * 452650 * 2
def baseEnd_452650 : Nat := 68867264668965700294313

theorem tailTrace_452650 : CollatzResearch.WordTrace tailWord_452650 prefixEnd_452650 68867264668965700294313 := by
  unfold tailWord_452650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127375452533457827606851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11006334540089220873618269 4127375452533457827606851)
  ·
    refine ⟨6191063178800186741410277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4127375452533457827606851 6191063178800186741410277)
    ·
      refine ⟨1160824346025035014014427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6191063178800186741410277 1160824346025035014014427)
      ·
        refine ⟨1741236519037552521021641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160824346025035014014427 1741236519037552521021641)
        ·
          refine ⟨1305927389278164390766231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741236519037552521021641 1305927389278164390766231)
          ·
            refine ⟨1958891083917246586149347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305927389278164390766231 1958891083917246586149347)
            ·
              refine ⟨2938336625875869879224021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958891083917246586149347 2938336625875869879224021)
              ·
                refine ⟨68867264668965700294313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2938336625875869879224021 68867264668965700294313)
                ·
                  rfl

theorem cell20_452650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_452650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452650 prefixEnd_452650 := by exact prefixLift 452650
  have htrace : WordTrace (prefixWord ++ tailWord_452650) baseStart_452650 baseEnd_452650 := by
    simpa [prefixWord, tailWord_452650, baseEnd_452650] using wordTrace_append hprefix tailTrace_452650
  have hstable : (prefixWord ++ tailWord_452650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452650).length < 2 ^ (prefixWord ++ tailWord_452650).sum := by decide
  have hdescent : baseEnd_452650 < baseStart_452650 := by decide
  rcases family_descends (prefixWord ++ tailWord_452650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452671 : List Nat := [1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_452671 : Nat := 118140960795 + 452671 * 2 ^ 59
def prefixEnd_452671 : Nat := 4983230072969 + 3 ^ 40 * 452671 * 2
def baseEnd_452671 : Nat := 68870459659704787060951

theorem tailTrace_452671 : CollatzResearch.WordTrace tailWord_452671 prefixEnd_452671 68870459659704787060951 := by
  unfold tailWord_452671
  simp only [CollatzResearch.WordTrace]
  refine ⟨16510267743057751896941867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11006845162038501264627911 16510267743057751896941867)
  ·
    refine ⟨24765401614586627845412801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16510267743057751896941867 24765401614586627845412801)
    ·
      refine ⟨18574051210939970884059601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24765401614586627845412801 18574051210939970884059601)
      ·
        refine ⟨13930538408204978163044701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18574051210939970884059601 13930538408204978163044701)
        ·
          refine ⟨5223951903076866811141763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13930538408204978163044701 5223951903076866811141763)
          ·
            refine ⟨7835927854615300216712645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223951903076866811141763 7835927854615300216712645)
            ·
              refine ⟨1469236472740368790633621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7835927854615300216712645 1469236472740368790633621)
              ·
                refine ⟨68870459659704787060951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1469236472740368790633621 68870459659704787060951)
                ·
                  rfl

theorem cell20_452671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_452671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452671 prefixEnd_452671 := by exact prefixLift 452671
  have htrace : WordTrace (prefixWord ++ tailWord_452671) baseStart_452671 baseEnd_452671 := by
    simpa [prefixWord, tailWord_452671, baseEnd_452671] using wordTrace_append hprefix tailTrace_452671
  have hstable : (prefixWord ++ tailWord_452671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452671).length < 2 ^ (prefixWord ++ tailWord_452671).sum := by decide
  have hdescent : baseEnd_452671 < baseStart_452671 := by decide
  rcases family_descends (prefixWord ++ tailWord_452671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452681 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 2]
def baseStart_452681 : Nat := 118140960795 + 452681 * 2 ^ 59
def prefixEnd_452681 : Nat := 4983230072969 + 3 ^ 40 * 452681 * 2
def baseEnd_452681 : Nat := 206615943251598770849479

theorem tailTrace_452681 : CollatzResearch.WordTrace tailWord_452681 prefixEnd_452681 206615943251598770849479 := by
  unfold tailWord_452681
  simp only [CollatzResearch.WordTrace]
  refine ⟨16510632473021523604805897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11007088315347682403203931 16510632473021523604805897)
  ·
    refine ⟨12382974354766142703604423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16510632473021523604805897 12382974354766142703604423)
    ·
      refine ⟨18574461532149214055406635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382974354766142703604423 18574461532149214055406635)
      ·
        refine ⟨27861692298223821083109953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18574461532149214055406635 27861692298223821083109953)
        ·
          refine ⟨20896269223667865812332465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27861692298223821083109953 20896269223667865812332465)
          ·
            refine ⟨15672201917750899359249349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20896269223667865812332465 15672201917750899359249349)
            ·
              refine ⟨2938537859578293629859253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15672201917750899359249349 2938537859578293629859253)
              ·
                refine ⟨275487924335465027799305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2938537859578293629859253 275487924335465027799305)
                ·
                  refine ⟨206615943251598770849479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275487924335465027799305 206615943251598770849479)
                  ·
                    rfl

theorem cell20_452681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_452681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452681 prefixEnd_452681 := by exact prefixLift 452681
  have htrace : WordTrace (prefixWord ++ tailWord_452681) baseStart_452681 baseEnd_452681 := by
    simpa [prefixWord, tailWord_452681, baseEnd_452681] using wordTrace_append hprefix tailTrace_452681
  have hstable : (prefixWord ++ tailWord_452681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452681).length < 2 ^ (prefixWord ++ tailWord_452681).sum := by decide
  have hdescent : baseEnd_452681 < baseStart_452681 := by decide
  rcases family_descends (prefixWord ++ tailWord_452681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452694 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_452694 : Nat := 118140960795 + 452694 * 2 ^ 59
def prefixEnd_452694 : Nat := 4983230072969 + 3 ^ 40 * 452694 * 2
def baseEnd_452694 : Nat := 206621876805828503416093

theorem tailTrace_452694 : CollatzResearch.WordTrace tailWord_452694 prefixEnd_452694 206621876805828503416093 := by
  unfold tailWord_452694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031944163873401676564321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11007404414649617883352757 1031944163873401676564321)
  ·
    refine ⟨773958122905051257423241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1031944163873401676564321 773958122905051257423241)
    ·
      refine ⟨580468592178788443067431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 773958122905051257423241 580468592178788443067431)
      ·
        refine ⟨870702888268182664601147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580468592178788443067431 870702888268182664601147)
        ·
          refine ⟨1306054332402273996901721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870702888268182664601147 1306054332402273996901721)
          ·
            refine ⟨979540749301705497676291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306054332402273996901721 979540749301705497676291)
            ·
              refine ⟨1469311123952558246514437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979540749301705497676291 1469311123952558246514437)
              ·
                refine ⟨275495835741104671221457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1469311123952558246514437 275495835741104671221457)
                ·
                  refine ⟨206621876805828503416093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275495835741104671221457 206621876805828503416093)
                  ·
                    rfl

theorem cell20_452694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_452694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452694 prefixEnd_452694 := by exact prefixLift 452694
  have htrace : WordTrace (prefixWord ++ tailWord_452694) baseStart_452694 baseEnd_452694 := by
    simpa [prefixWord, tailWord_452694, baseEnd_452694] using wordTrace_append hprefix tailTrace_452694
  have hstable : (prefixWord ++ tailWord_452694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452694).length < 2 ^ (prefixWord ++ tailWord_452694).sum := by decide
  have hdescent : baseEnd_452694 < baseStart_452694 := by decide
  rcases family_descends (prefixWord ++ tailWord_452694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452695 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_452695 : Nat := 118140960795 + 452695 * 2 ^ 59
def prefixEnd_452695 : Nat := 4983230072969 + 3 ^ 40 * 452695 * 2
def baseEnd_452695 : Nat := 206622333233076944382755

theorem tailTrace_452695 : CollatzResearch.WordTrace tailWord_452695 prefixEnd_452695 206622333233076944382755 := by
  unfold tailWord_452695
  simp only [CollatzResearch.WordTrace]
  refine ⟨16511143094970803995815539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11007428729980535997210359 16511143094970803995815539)
  ·
    refine ⟨24766714642456205993723309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16511143094970803995815539 24766714642456205993723309)
    ·
      refine ⟨9287517990921077247646241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24766714642456205993723309 9287517990921077247646241)
      ·
        refine ⟨6965638493190807935734681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9287517990921077247646241 6965638493190807935734681)
        ·
          refine ⟨5224228869893105951801011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6965638493190807935734681 5224228869893105951801011)
          ·
            refine ⟨7836343304839658927701517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224228869893105951801011 7836343304839658927701517)
            ·
              refine ⟨2938628739314872097888069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7836343304839658927701517 2938628739314872097888069)
              ·
                refine ⟨550992888621538518354013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2938628739314872097888069 550992888621538518354013)
                ·
                  refine ⟨206622333233076944382755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550992888621538518354013 206622333233076944382755)
                  ·
                    rfl

theorem cell20_452695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_452695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452695 prefixEnd_452695 := by exact prefixLift 452695
  have htrace : WordTrace (prefixWord ++ tailWord_452695) baseStart_452695 baseEnd_452695 := by
    simpa [prefixWord, tailWord_452695, baseEnd_452695] using wordTrace_append hprefix tailTrace_452695
  have hstable : (prefixWord ++ tailWord_452695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452695).length < 2 ^ (prefixWord ++ tailWord_452695).sum := by decide
  have hdescent : baseEnd_452695 < baseStart_452695 := by decide
  rcases family_descends (prefixWord ++ tailWord_452695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452740 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_452740 : Nat := 118140960795 + 452740 * 2 ^ 59
def prefixEnd_452740 : Nat := 4983230072969 + 3 ^ 40 * 452740 * 2
def baseEnd_452740 : Nat := 206642872459256787882571

theorem tailTrace_452740 : CollatzResearch.WordTrace tailWord_452740 prefixEnd_452740 206642872459256787882571 := by
  unfold tailWord_452740
  simp only [CollatzResearch.WordTrace]
  refine ⟨8256392189903888340601837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11008522919871851120802449 8256392189903888340601837)
  ·
    refine ⟨3096147071213958127725689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8256392189903888340601837 3096147071213958127725689)
    ·
      refine ⟨2322110303410468595794267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3096147071213958127725689 2322110303410468595794267)
      ·
        refine ⟨3483165455115702893691401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322110303410468595794267 3483165455115702893691401)
        ·
          refine ⟨2612374091336777170268551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3483165455115702893691401 2612374091336777170268551)
          ·
            refine ⟨3918561137005165755402827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612374091336777170268551 3918561137005165755402827)
            ·
              refine ⟨5877841705507748633104241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918561137005165755402827 5877841705507748633104241)
              ·
                refine ⟨4408381279130811474828181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877841705507748633104241 4408381279130811474828181)
                ·
                  refine ⟨206642872459256787882571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4408381279130811474828181 206642872459256787882571)
                  ·
                    rfl

theorem cell20_452740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_452740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452740 prefixEnd_452740 := by exact prefixLift 452740
  have htrace : WordTrace (prefixWord ++ tailWord_452740) baseStart_452740 baseEnd_452740 := by
    simpa [prefixWord, tailWord_452740, baseEnd_452740] using wordTrace_append hprefix tailTrace_452740
  have hstable : (prefixWord ++ tailWord_452740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452740).length < 2 ^ (prefixWord ++ tailWord_452740).sum := by decide
  have hdescent : baseEnd_452740 < baseStart_452740 := by decide
  rcases family_descends (prefixWord ++ tailWord_452740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452750 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_452750 : Nat := 118140960795 + 452750 * 2 ^ 59
def prefixEnd_452750 : Nat := 4983230072969 + 3 ^ 40 * 452750 * 2
def baseEnd_452750 : Nat := 206647436731741197549197

theorem tailTrace_452750 : CollatzResearch.WordTrace tailWord_452750 prefixEnd_452750 206647436731741197549197 := by
  unfold tailWord_452750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064143638721443548633463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11008766073181032259378469 2064143638721443548633463)
  ·
    refine ⟨3096215458082165322950195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2064143638721443548633463 3096215458082165322950195)
    ·
      refine ⟨4644323187123247984425293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3096215458082165322950195 4644323187123247984425293)
      ·
        refine ⟨1741621195171217994159485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4644323187123247984425293 1741621195171217994159485)
        ·
          refine ⟨653107948189206747809807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1741621195171217994159485 653107948189206747809807)
          ·
            refine ⟨979661922283810121714711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653107948189206747809807 979661922283810121714711)
            ·
              refine ⟨1469492883425715182572067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979661922283810121714711 1469492883425715182572067)
              ·
                refine ⟨2204239325138572773858101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469492883425715182572067 2204239325138572773858101)
                ·
                  refine ⟨206647436731741197549197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2204239325138572773858101 206647436731741197549197)
                  ·
                    rfl

theorem cell20_452750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_452750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452750 prefixEnd_452750 := by exact prefixLift 452750
  have htrace : WordTrace (prefixWord ++ tailWord_452750) baseStart_452750 baseEnd_452750 := by
    simpa [prefixWord, tailWord_452750, baseEnd_452750] using wordTrace_append hprefix tailTrace_452750
  have hstable : (prefixWord ++ tailWord_452750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452750).length < 2 ^ (prefixWord ++ tailWord_452750).sum := by decide
  have hdescent : baseEnd_452750 < baseStart_452750 := by decide
  rcases family_descends (prefixWord ++ tailWord_452750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452757 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 2]
def baseStart_452757 : Nat := 118140960795 + 452757 * 2 ^ 59
def prefixEnd_452757 : Nat := 4983230072969 + 3 ^ 40 * 452757 * 2
def baseEnd_452757 : Nat := 206650631722480284315835

theorem tailTrace_452757 : CollatzResearch.WordTrace tailWord_452757 prefixEnd_452757 206650631722480284315835 := by
  unfold tailWord_452757
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513404420746188584572525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11008936280497459056381683 16513404420746188584572525)
  ·
    refine ⟨6192526657779820719214697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16513404420746188584572525 6192526657779820719214697)
    ·
      refine ⟨4644394993334865539411023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6192526657779820719214697 4644394993334865539411023)
      ·
        refine ⟨6966592490002298309116535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4644394993334865539411023 6966592490002298309116535)
        ·
          refine ⟨10449888735003447463674803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966592490002298309116535 10449888735003447463674803)
          ·
            refine ⟨15674833102505171195512205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449888735003447463674803 15674833102505171195512205)
            ·
              refine ⟨5878062413439439198317077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15674833102505171195512205 5878062413439439198317077)
              ·
                refine ⟨275534175629973712421113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5878062413439439198317077 275534175629973712421113)
                ·
                  refine ⟨206650631722480284315835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275534175629973712421113 206650631722480284315835)
                  ·
                    rfl

theorem cell20_452757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_452757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452757 prefixEnd_452757 := by exact prefixLift 452757
  have htrace : WordTrace (prefixWord ++ tailWord_452757) baseStart_452757 baseEnd_452757 := by
    simpa [prefixWord, tailWord_452757, baseEnd_452757] using wordTrace_append hprefix tailTrace_452757
  have hstable : (prefixWord ++ tailWord_452757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452757).length < 2 ^ (prefixWord ++ tailWord_452757).sum := by decide
  have hdescent : baseEnd_452757 < baseStart_452757 := by decide
  rcases family_descends (prefixWord ++ tailWord_452757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452767 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 3]
def baseStart_452767 : Nat := 118140960795 + 452767 * 2 ^ 59
def prefixEnd_452767 : Nat := 4983230072969 + 3 ^ 40 * 452767 * 2
def baseEnd_452767 : Nat := 206655195994964693982461

theorem tailTrace_452767 : CollatzResearch.WordTrace tailWord_452767 prefixEnd_452767 206655195994964693982461 := by
  unfold tailWord_452767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513769150709960292436555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11009179433806640194957703 16513769150709960292436555)
  ·
    refine ⟨24770653726064940438654833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16513769150709960292436555 24770653726064940438654833)
    ·
      refine ⟨18577990294548705328991125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24770653726064940438654833 18577990294548705328991125)
      ·
        refine ⟨870843295056970562296459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18577990294548705328991125 870843295056970562296459)
        ·
          refine ⟨1306264942585455843444689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870843295056970562296459 1306264942585455843444689)
          ·
            refine ⟨979698706939091882583517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306264942585455843444689 979698706939091882583517)
            ·
              refine ⟨367387015102159455968819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979698706939091882583517 367387015102159455968819)
              ·
                refine ⟨551080522653239183953229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367387015102159455968819 551080522653239183953229)
                ·
                  refine ⟨206655195994964693982461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551080522653239183953229 206655195994964693982461)
                  ·
                    rfl

theorem cell20_452767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_452767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452767 prefixEnd_452767 := by exact prefixLift 452767
  have htrace : WordTrace (prefixWord ++ tailWord_452767) baseStart_452767 baseEnd_452767 := by
    simpa [prefixWord, tailWord_452767, baseEnd_452767] using wordTrace_append hprefix tailTrace_452767
  have hstable : (prefixWord ++ tailWord_452767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452767).length < 2 ^ (prefixWord ++ tailWord_452767).sum := by decide
  have hdescent : baseEnd_452767 < baseStart_452767 := by decide
  rcases family_descends (prefixWord ++ tailWord_452767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452781 : List Nat := [1, 5, 2, 1, 2, 1, 4, 4]
def baseStart_452781 : Nat := 118140960795 + 452781 * 2 ^ 59
def prefixEnd_452781 : Nat := 4983230072969 + 3 ^ 40 * 452781 * 2
def baseEnd_452781 : Nat := 68887195325480955838579

theorem tailTrace_452781 : CollatzResearch.WordTrace tailWord_452781 prefixEnd_452781 68887195325480955838579 := by
  unfold tailWord_452781
  simp only [CollatzResearch.WordTrace]
  refine ⟨16514279772659240683446197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11009519848439493788964131 16514279772659240683446197)
  ·
    refine ⟨1548213728686803814073081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16514279772659240683446197 1548213728686803814073081)
    ·
      refine ⟨1161160296515102860554811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1548213728686803814073081 1161160296515102860554811)
      ·
        refine ⟨1741740444772654290832217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161160296515102860554811 1741740444772654290832217)
        ·
          refine ⟨1306305333579490718124163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741740444772654290832217 1306305333579490718124163)
          ·
            refine ⟨1959458000369236077186245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306305333579490718124163 1959458000369236077186245)
            ·
              refine ⟨367398375069231764472421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1959458000369236077186245 367398375069231764472421)
              ·
                refine ⟨68887195325480955838579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367398375069231764472421 68887195325480955838579)
                ·
                  rfl

theorem cell20_452781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_452781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452781 prefixEnd_452781 := by exact prefixLift 452781
  have htrace : WordTrace (prefixWord ++ tailWord_452781) baseStart_452781 baseEnd_452781 := by
    simpa [prefixWord, tailWord_452781, baseEnd_452781] using wordTrace_append hprefix tailTrace_452781
  have hstable : (prefixWord ++ tailWord_452781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452781).length < 2 ^ (prefixWord ++ tailWord_452781).sum := by decide
  have hdescent : baseEnd_452781 < baseStart_452781 := by decide
  rcases family_descends (prefixWord ++ tailWord_452781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452792 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_452792 : Nat := 118140960795 + 452792 * 2 ^ 59
def prefixEnd_452792 : Nat := 4983230072969 + 3 ^ 40 * 452792 * 2
def baseEnd_452792 : Nat := 206666606676175718149025

theorem tailTrace_452792 : CollatzResearch.WordTrace tailWord_452792 prefixEnd_452792 206666606676175718149025 := by
  unfold tailWord_452792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257340487809694781048315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11009787317079593041397753 8257340487809694781048315)
  ·
    refine ⟨12386010731714542171572473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8257340487809694781048315 12386010731714542171572473)
    ·
      refine ⟨9289508048785906628679355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12386010731714542171572473 9289508048785906628679355)
      ·
        refine ⟨13934262073178859943019033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289508048785906628679355 13934262073178859943019033)
        ·
          refine ⟨10450696554884144957264275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13934262073178859943019033 10450696554884144957264275)
          ·
            refine ⟨15676044832326217435896413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10450696554884144957264275 15676044832326217435896413)
            ·
              refine ⟨5878516812122331538461155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15676044832326217435896413 5878516812122331538461155)
              ·
                refine ⟨8817775218183497307691733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878516812122331538461155 8817775218183497307691733)
                ·
                  refine ⟨206666606676175718149025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8817775218183497307691733 206666606676175718149025)
                  ·
                    rfl

theorem cell20_452792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_452792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452792 prefixEnd_452792 := by exact prefixLift 452792
  have htrace : WordTrace (prefixWord ++ tailWord_452792) baseStart_452792 baseEnd_452792 := by
    simpa [prefixWord, tailWord_452792, baseEnd_452792] using wordTrace_append hprefix tailTrace_452792
  have hstable : (prefixWord ++ tailWord_452792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452792).length < 2 ^ (prefixWord ++ tailWord_452792).sum := by decide
  have hdescent : baseEnd_452792 < baseStart_452792 := by decide
  rcases family_descends (prefixWord ++ tailWord_452792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452822 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_452822 : Nat := 118140960795 + 452822 * 2 ^ 59
def prefixEnd_452822 : Nat := 4983230072969 + 3 ^ 40 * 452822 * 2
def baseEnd_452822 : Nat := 206680299493628947148903

theorem tailTrace_452822 : CollatzResearch.WordTrace tailWord_452822 prefixEnd_452822 206680299493628947148903 := by
  unfold tailWord_452822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032235947844419042855545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11010516777007136457125813 1032235947844419042855545)
  ·
    refine ⟨774176960883314282141659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1032235947844419042855545 774176960883314282141659)
    ·
      refine ⟨1161265441324971423212489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774176960883314282141659 1161265441324971423212489)
      ·
        refine ⟨870949080993728567409367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1161265441324971423212489 870949080993728567409367)
        ·
          refine ⟨1306423621490592851114051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870949080993728567409367 1306423621490592851114051)
          ·
            refine ⟨1959635432235889276671077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306423621490592851114051 1959635432235889276671077)
            ·
              refine ⟨367431643544229239375827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1959635432235889276671077 367431643544229239375827)
              ·
                refine ⟨551147465316343859063741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367431643544229239375827 551147465316343859063741)
                ·
                  refine ⟨206680299493628947148903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551147465316343859063741 206680299493628947148903)
                  ·
                    rfl

theorem cell20_452822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_452822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452822 prefixEnd_452822 := by exact prefixLift 452822
  have htrace : WordTrace (prefixWord ++ tailWord_452822) baseStart_452822 baseEnd_452822 := by
    simpa [prefixWord, tailWord_452822, baseEnd_452822] using wordTrace_append hprefix tailTrace_452822
  have hstable : (prefixWord ++ tailWord_452822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452822).length < 2 ^ (prefixWord ++ tailWord_452822).sum := by decide
  have hdescent : baseEnd_452822 < baseStart_452822 := by decide
  rcases family_descends (prefixWord ++ tailWord_452822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452826 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_452826 : Nat := 118140960795 + 452826 * 2 ^ 59
def prefixEnd_452826 : Nat := 4983230072969 + 3 ^ 40 * 452826 * 2
def baseEnd_452826 : Nat := 206682125202622711015553

theorem tailTrace_452826 : CollatzResearch.WordTrace tailWord_452826 prefixEnd_452826 206682125202622711015553 := by
  unfold tailWord_452826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128980264374053342208583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11010614038330808912556221 4128980264374053342208583)
  ·
    refine ⟨6193470396561080013312875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128980264374053342208583 6193470396561080013312875)
    ·
      refine ⟨9290205594841620019969313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193470396561080013312875 9290205594841620019969313)
      ·
        refine ⟨6967654196131215014976985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9290205594841620019969313 6967654196131215014976985)
        ·
          refine ⟨5225740647098411261232739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6967654196131215014976985 5225740647098411261232739)
          ·
            refine ⟨7838610970647616891849109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225740647098411261232739 7838610970647616891849109)
            ·
              refine ⟨367434889249107041805427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7838610970647616891849109 367434889249107041805427)
              ·
                refine ⟨551152333873660562708141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367434889249107041805427 551152333873660562708141)
                ·
                  refine ⟨206682125202622711015553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551152333873660562708141 206682125202622711015553)
                  ·
                    rfl

theorem cell20_452826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_452826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452826 prefixEnd_452826 := by exact prefixLift 452826
  have htrace : WordTrace (prefixWord ++ tailWord_452826) baseStart_452826 baseEnd_452826 := by
    simpa [prefixWord, tailWord_452826, baseEnd_452826] using wordTrace_append hprefix tailTrace_452826
  have hstable : (prefixWord ++ tailWord_452826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452826).length < 2 ^ (prefixWord ++ tailWord_452826).sum := by decide
  have hdescent : baseEnd_452826 < baseStart_452826 := by decide
  rcases family_descends (prefixWord ++ tailWord_452826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452885 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_452885 : Nat := 118140960795 + 452885 * 2 ^ 59
def prefixEnd_452885 : Nat := 4983230072969 + 3 ^ 40 * 452885 * 2
def baseEnd_452885 : Nat := 206709054410280728048645

theorem tailTrace_452885 : CollatzResearch.WordTrace tailWord_452885 prefixEnd_452885 206709054410280728048645 := by
  unfold tailWord_452885
  simp only [CollatzResearch.WordTrace]
  refine ⟨16518072964282466445232109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11012048642854977630154739 16518072964282466445232109)
  ·
    refine ⟨6194277361605924916962041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16518072964282466445232109 6194277361605924916962041)
    ·
      refine ⟨4645708021204443687721531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6194277361605924916962041 4645708021204443687721531)
      ·
        refine ⟨6968562031806665531582297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645708021204443687721531 6968562031806665531582297)
        ·
          refine ⟨5226421523854999148686723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6968562031806665531582297 5226421523854999148686723)
          ·
            refine ⟨7839632285782498723030085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226421523854999148686723 7839632285782498723030085)
            ·
              refine ⟨1469931053584218510568141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7839632285782498723030085 1469931053584218510568141)
              ·
                refine ⟨551224145094081941463053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1469931053584218510568141 551224145094081941463053)
                ·
                  refine ⟨206709054410280728048645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551224145094081941463053 206709054410280728048645)
                  ·
                    rfl

theorem cell20_452885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_452885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452885 prefixEnd_452885 := by exact prefixLift 452885
  have htrace : WordTrace (prefixWord ++ tailWord_452885) baseStart_452885 baseEnd_452885 := by
    simpa [prefixWord, tailWord_452885, baseEnd_452885] using wordTrace_append hprefix tailTrace_452885
  have hstable : (prefixWord ++ tailWord_452885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452885).length < 2 ^ (prefixWord ++ tailWord_452885).sum := by decide
  have hdescent : baseEnd_452885 < baseStart_452885 := by decide
  rcases family_descends (prefixWord ++ tailWord_452885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452916 : List Nat := [2, 5, 1, 1, 1, 3, 7]
def baseStart_452916 : Nat := 118140960795 + 452916 * 2 ^ 59
def prefixEnd_452916 : Nat := 4983230072969 + 3 ^ 40 * 452916 * 2
def baseEnd_452916 : Nat := 22969244850553599779465

theorem tailTrace_452916 : CollatzResearch.WordTrace tailWord_452916 prefixEnd_452916 22969244850553599779465 := by
  unfold tailWord_452916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259601813585079369805301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11012802418113439159740401 8259601813585079369805301)
  ·
    refine ⟨774337670023601190919247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8259601813585079369805301 774337670023601190919247)
    ·
      refine ⟨1161506505035401786378871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774337670023601190919247 1161506505035401786378871)
      ·
        refine ⟨1742259757553102679568307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161506505035401786378871 1742259757553102679568307)
        ·
          refine ⟨2613389636329654019352461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742259757553102679568307 2613389636329654019352461)
          ·
            refine ⟨980021113623620257257173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2613389636329654019352461 980021113623620257257173)
            ·
              refine ⟨22969244850553599779465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 980021113623620257257173 22969244850553599779465)
              ·
                rfl

theorem cell20_452916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_452916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452916 prefixEnd_452916 := by exact prefixLift 452916
  have htrace : WordTrace (prefixWord ++ tailWord_452916) baseStart_452916 baseEnd_452916 := by
    simpa [prefixWord, tailWord_452916, baseEnd_452916] using wordTrace_append hprefix tailTrace_452916
  have hstable : (prefixWord ++ tailWord_452916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452916).length < 2 ^ (prefixWord ++ tailWord_452916).sum := by decide
  have hdescent : baseEnd_452916 < baseStart_452916 := by decide
  rcases family_descends (prefixWord ++ tailWord_452916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452926 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_452926 : Nat := 118140960795 + 452926 * 2 ^ 59
def prefixEnd_452926 : Nat := 4983230072969 + 3 ^ 40 * 452926 * 2
def baseEnd_452926 : Nat := 206727767927466807681811

theorem tailTrace_452926 : CollatzResearch.WordTrace tailWord_452926 prefixEnd_452926 206727767927466807681811 := by
  unfold tailWord_452926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064946044641741305934329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11013045571422620298316421 2064946044641741305934329)
  ·
    refine ⟨1548709533481305979450747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2064946044641741305934329 1548709533481305979450747)
    ·
      refine ⟨2323064300221958969176121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548709533481305979450747 2323064300221958969176121)
      ·
        refine ⟨1742298225166469226882091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2323064300221958969176121 1742298225166469226882091)
        ·
          refine ⟨2613447337749703840323137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742298225166469226882091 2613447337749703840323137)
          ·
            refine ⟨1960085503312277880242353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2613447337749703840323137 1960085503312277880242353)
            ·
              refine ⟨1470064127484208410181765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960085503312277880242353 1470064127484208410181765)
              ·
                refine ⟨275637023903289076909081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1470064127484208410181765 275637023903289076909081)
                ·
                  refine ⟨206727767927466807681811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275637023903289076909081 206727767927466807681811)
                  ·
                    rfl

theorem cell20_452926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_452926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452926 prefixEnd_452926 := by exact prefixLift 452926
  have htrace : WordTrace (prefixWord ++ tailWord_452926) baseStart_452926 baseEnd_452926 := by
    simpa [prefixWord, tailWord_452926, baseEnd_452926] using wordTrace_append hprefix tailTrace_452926
  have hstable : (prefixWord ++ tailWord_452926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452926).length < 2 ^ (prefixWord ++ tailWord_452926).sum := by decide
  have hdescent : baseEnd_452926 < baseStart_452926 := by decide
  rcases family_descends (prefixWord ++ tailWord_452926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452940 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_452940 : Nat := 118140960795 + 452940 * 2 ^ 59
def prefixEnd_452940 : Nat := 4983230072969 + 3 ^ 40 * 452940 * 2
def baseEnd_452940 : Nat := 206734157908944981215087

theorem tailTrace_452940 : CollatzResearch.WordTrace tailWord_452940 prefixEnd_452940 206734157908944981215087 := by
  unfold tailWord_452940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260039489541605419242137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11013385986055473892322849 8260039489541605419242137)
  ·
    refine ⟨6195029617156204064431603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8260039489541605419242137 6195029617156204064431603)
    ·
      refine ⟨9292544425734306096647405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6195029617156204064431603 9292544425734306096647405)
      ·
        refine ⟨3484704159650364786242777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9292544425734306096647405 3484704159650364786242777)
        ·
          refine ⟨2613528119737773589682083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3484704159650364786242777 2613528119737773589682083)
          ·
            refine ⟨3920292179606660384523125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613528119737773589682083 3920292179606660384523125)
            ·
              refine ⟨367527391838124411049043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3920292179606660384523125 367527391838124411049043)
              ·
                refine ⟨551291087757186616573565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367527391838124411049043 551291087757186616573565)
                ·
                  refine ⟨206734157908944981215087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551291087757186616573565 206734157908944981215087)
                  ·
                    rfl

theorem cell20_452940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_452940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452940 prefixEnd_452940 := by exact prefixLift 452940
  have htrace : WordTrace (prefixWord ++ tailWord_452940) baseStart_452940 baseEnd_452940 := by
    simpa [prefixWord, tailWord_452940, baseEnd_452940] using wordTrace_append hprefix tailTrace_452940
  have hstable : (prefixWord ++ tailWord_452940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452940).length < 2 ^ (prefixWord ++ tailWord_452940).sum := by decide
  have hdescent : baseEnd_452940 < baseStart_452940 := by decide
  rcases family_descends (prefixWord ++ tailWord_452940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452981 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 2]
def baseStart_452981 : Nat := 118140960795 + 452981 * 2 ^ 59
def prefixEnd_452981 : Nat := 4983230072969 + 3 ^ 40 * 452981 * 2
def baseEnd_452981 : Nat := 206752871426131060848253

theorem tailTrace_452981 : CollatzResearch.WordTrace tailWord_452981 prefixEnd_452981 206752871426131060848253 := by
  unfold tailWord_452981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521574371934674840726797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11014382914623116560484531 16521574371934674840726797)
  ·
    refine ⟨6195590389475503065272549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16521574371934674840726797 6195590389475503065272549)
    ·
      refine ⟨1161673198026656824738603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6195590389475503065272549 1161673198026656824738603)
      ·
        refine ⟨1742509797039985237107905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161673198026656824738603 1742509797039985237107905)
        ·
          refine ⟨1306882347779988927830929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1742509797039985237107905 1306882347779988927830929)
          ·
            refine ⟨980161760834991695873197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306882347779988927830929 980161760834991695873197)
            ·
              refine ⟨367560660313121885952449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980161760834991695873197 367560660313121885952449)
              ·
                refine ⟨275670495234841414464337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367560660313121885952449 275670495234841414464337)
                ·
                  refine ⟨206752871426131060848253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275670495234841414464337 206752871426131060848253)
                  ·
                    rfl

theorem cell20_452981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_452981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452981 prefixEnd_452981 := by exact prefixLift 452981
  have htrace : WordTrace (prefixWord ++ tailWord_452981) baseStart_452981 baseEnd_452981 := by
    simpa [prefixWord, tailWord_452981, baseEnd_452981] using wordTrace_append hprefix tailTrace_452981
  have hstable : (prefixWord ++ tailWord_452981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452981).length < 2 ^ (prefixWord ++ tailWord_452981).sum := by decide
  have hdescent : baseEnd_452981 < baseStart_452981 := by decide
  rcases family_descends (prefixWord ++ tailWord_452981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452995 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 3]
def baseStart_452995 : Nat := 118140960795 + 452995 * 2 ^ 59
def prefixEnd_452995 : Nat := 4983230072969 + 3 ^ 40 * 452995 * 2
def baseEnd_452995 : Nat := 206759261407609234381529

theorem tailTrace_452995 : CollatzResearch.WordTrace tailWord_452995 prefixEnd_452995 206759261407609234381529 := by
  unfold tailWord_452995
  simp only [CollatzResearch.WordTrace]
  refine ⟨16522084993883955231736439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11014723329255970154490959 16522084993883955231736439)
  ·
    refine ⟨24783127490825932847604659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16522084993883955231736439 24783127490825932847604659)
    ·
      refine ⟨37174691236238899271406989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24783127490825932847604659 37174691236238899271406989)
      ·
        refine ⟨13940509213589587226777621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37174691236238899271406989 13940509213589587226777621)
        ·
          refine ⟨653461369387011901255201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13940509213589587226777621 653461369387011901255201)
          ·
            refine ⟨490096027040258925941401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653461369387011901255201 490096027040258925941401)
            ·
              refine ⟨367572020280194194456051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490096027040258925941401 367572020280194194456051)
              ·
                refine ⟨551358030420291291684077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367572020280194194456051 551358030420291291684077)
                ·
                  refine ⟨206759261407609234381529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551358030420291291684077 206759261407609234381529)
                  ·
                    rfl

theorem cell20_452995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_452995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452995 prefixEnd_452995 := by exact prefixLift 452995
  have htrace : WordTrace (prefixWord ++ tailWord_452995) baseStart_452995 baseEnd_452995 := by
    simpa [prefixWord, tailWord_452995, baseEnd_452995] using wordTrace_append hprefix tailTrace_452995
  have hstable : (prefixWord ++ tailWord_452995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452995).length < 2 ^ (prefixWord ++ tailWord_452995).sum := by decide
  have hdescent : baseEnd_452995 < baseStart_452995 := by decide
  rcases family_descends (prefixWord ++ tailWord_452995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452999 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_452999 : Nat := 118140960795 + 452999 * 2 ^ 59
def prefixEnd_452999 : Nat := 4983230072969 + 3 ^ 40 * 452999 * 2
def baseEnd_452999 : Nat := 206761087116602998248179

theorem tailTrace_452999 : CollatzResearch.WordTrace tailWord_452999 prefixEnd_452999 206761087116602998248179 := by
  unfold tailWord_452999
  simp only [CollatzResearch.WordTrace]
  refine ⟨16522230885869463914882051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11014820590579642609921367 16522230885869463914882051)
  ·
    refine ⟨24783346328804195872323077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16522230885869463914882051 24783346328804195872323077)
    ·
      refine ⟨4646877436650786726060577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24783346328804195872323077 4646877436650786726060577)
      ·
        refine ⟨3485158077488090044545433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4646877436650786726060577 3485158077488090044545433)
        ·
          refine ⟨2613868558116067533409075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485158077488090044545433 2613868558116067533409075)
          ·
            refine ⟨3920802837174101300113613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613868558116067533409075 3920802837174101300113613)
            ·
              refine ⟨1470301063940287987542605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3920802837174101300113613 1470301063940287987542605)
              ·
                refine ⟨551362898977607995328477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470301063940287987542605 551362898977607995328477)
                ·
                  refine ⟨206761087116602998248179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551362898977607995328477 206761087116602998248179)
                  ·
                    rfl

theorem cell20_452999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_452999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_452999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_452999 prefixEnd_452999 := by exact prefixLift 452999
  have htrace : WordTrace (prefixWord ++ tailWord_452999) baseStart_452999 baseEnd_452999 := by
    simpa [prefixWord, tailWord_452999, baseEnd_452999] using wordTrace_append hprefix tailTrace_452999
  have hstable : (prefixWord ++ tailWord_452999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452999).length < 2 ^ (prefixWord ++ tailWord_452999).sum := by decide
  have hdescent : baseEnd_452999 < baseStart_452999 := by decide
  rcases family_descends (prefixWord ++ tailWord_452999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453023 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 2]
def baseStart_453023 : Nat := 118140960795 + 453023 * 2 ^ 59
def prefixEnd_453023 : Nat := 4983230072969 + 3 ^ 40 * 453023 * 2
def baseEnd_453023 : Nat := 206772041370565581448081

theorem tailTrace_453023 : CollatzResearch.WordTrace tailWord_453023 prefixEnd_453023 206772041370565581448081 := by
  unfold tailWord_453023
  simp only [CollatzResearch.WordTrace]
  refine ⟨16523106237782516013755723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11015404158521677342503815 16523106237782516013755723)
  ·
    refine ⟨24784659356673774020633585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16523106237782516013755723 24784659356673774020633585)
    ·
      refine ⟨18588494517505330515475189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24784659356673774020633585 18588494517505330515475189)
      ·
        refine ⟨1742671361016124735825799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18588494517505330515475189 1742671361016124735825799)
        ·
          refine ⟨2614007041524187103738699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742671361016124735825799 2614007041524187103738699)
          ·
            refine ⟨3921010562286280655608049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614007041524187103738699 3921010562286280655608049)
            ·
              refine ⟨2940757921714710491706037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921010562286280655608049 2940757921714710491706037)
              ·
                refine ⟨275696055160754108597441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2940757921714710491706037 275696055160754108597441)
                ·
                  refine ⟨206772041370565581448081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275696055160754108597441 206772041370565581448081)
                  ·
                    rfl

theorem cell20_453023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 2].length) (baseStart_453023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453023 prefixEnd_453023 := by exact prefixLift 453023
  have htrace : WordTrace (prefixWord ++ tailWord_453023) baseStart_453023 baseEnd_453023 := by
    simpa [prefixWord, tailWord_453023, baseEnd_453023] using wordTrace_append hprefix tailTrace_453023
  have hstable : (prefixWord ++ tailWord_453023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453023).length < 2 ^ (prefixWord ++ tailWord_453023).sum := by decide
  have hdescent : baseEnd_453023 < baseStart_453023 := by decide
  rcases family_descends (prefixWord ++ tailWord_453023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453057 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 4]
def baseStart_453057 : Nat := 118140960795 + 453057 * 2 ^ 59
def prefixEnd_453057 : Nat := 4983230072969 + 3 ^ 40 * 453057 * 2
def baseEnd_453057 : Nat := 206787559897012574314609

theorem tailTrace_453057 : CollatzResearch.WordTrace tailWord_453057 prefixEnd_453057 206787559897012574314609 := by
  unfold tailWord_453057
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524346319659339820493425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11016230879772893213662283 16524346319659339820493425)
  ·
    refine ⟨12393259739744504865370069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16524346319659339820493425 12393259739744504865370069)
    ·
      refine ⟨290467025150261832782111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12393259739744504865370069 290467025150261832782111)
      ·
        refine ⟨435700537725392749173167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290467025150261832782111 435700537725392749173167)
        ·
          refine ⟨653550806588089123759751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435700537725392749173167 653550806588089123759751)
          ·
            refine ⟨980326209882133685639627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653550806588089123759751 980326209882133685639627)
            ·
              refine ⟨1470489314823200528459441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980326209882133685639627 1470489314823200528459441)
              ·
                refine ⟨1102866986117400396344581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470489314823200528459441 1102866986117400396344581)
                ·
                  refine ⟨206787559897012574314609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1102866986117400396344581 206787559897012574314609)
                  ·
                    rfl

theorem cell20_453057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_453057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453057 prefixEnd_453057 := by exact prefixLift 453057
  have htrace : WordTrace (prefixWord ++ tailWord_453057) baseStart_453057 baseEnd_453057 := by
    simpa [prefixWord, tailWord_453057, baseEnd_453057] using wordTrace_append hprefix tailTrace_453057
  have hstable : (prefixWord ++ tailWord_453057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453057).length < 2 ^ (prefixWord ++ tailWord_453057).sum := by decide
  have hdescent : baseEnd_453057 < baseStart_453057 := by decide
  rcases family_descends (prefixWord ++ tailWord_453057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453065 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_453065 : Nat := 118140960795 + 453065 * 2 ^ 59
def prefixEnd_453065 : Nat := 4983230072969 + 3 ^ 40 * 453065 * 2
def baseEnd_453065 : Nat := 206791211315000102047909

theorem tailTrace_453065 : CollatzResearch.WordTrace tailWord_453065 prefixEnd_453065 206791211315000102047909 := by
  unfold tailWord_453065
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524638103630357186784649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11016425402420238124523099 16524638103630357186784649)
  ·
    refine ⟨12393478577722767890088487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16524638103630357186784649 12393478577722767890088487)
    ·
      refine ⟨18590217866584151835132731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393478577722767890088487 18590217866584151835132731)
      ·
        refine ⟨27885326799876227752699097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18590217866584151835132731 27885326799876227752699097)
        ·
          refine ⟨20913995099907170814524323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27885326799876227752699097 20913995099907170814524323)
          ·
            refine ⟨31370992649860756221786485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20913995099907170814524323 31370992649860756221786485)
            ·
              refine ⟨2941030560924445895792483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31370992649860756221786485 2941030560924445895792483)
              ·
                refine ⟨4411545841386668843688725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941030560924445895792483 4411545841386668843688725)
                ·
                  refine ⟨206791211315000102047909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4411545841386668843688725 206791211315000102047909)
                  ·
                    rfl

theorem cell20_453065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_453065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453065 prefixEnd_453065 := by exact prefixLift 453065
  have htrace : WordTrace (prefixWord ++ tailWord_453065) baseStart_453065 baseEnd_453065 := by
    simpa [prefixWord, tailWord_453065, baseEnd_453065] using wordTrace_append hprefix tailTrace_453065
  have hstable : (prefixWord ++ tailWord_453065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453065).length < 2 ^ (prefixWord ++ tailWord_453065).sum := by decide
  have hdescent : baseEnd_453065 < baseStart_453065 := by decide
  rcases family_descends (prefixWord ++ tailWord_453065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453237 : List Nat := [1, 3, 4, 2, 2, 1, 3, 4]
def baseStart_453237 : Nat := 118140960795 + 453237 * 2 ^ 59
def prefixEnd_453237 : Nat := 4983230072969 + 3 ^ 40 * 453237 * 2
def baseEnd_453237 : Nat := 68956572267243982771291

theorem tailTrace_453237 : CollatzResearch.WordTrace tailWord_453237 prefixEnd_453237 68956572267243982771291 := by
  unfold tailWord_453237
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530911459007230562045965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11020607639338153708030643 16530911459007230562045965)
  ·
    refine ⟨6199091797127711460767237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16530911459007230562045965 6199091797127711460767237)
    ·
      refine ⟨1162329711961445898893857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6199091797127711460767237 1162329711961445898893857)
      ·
        refine ⟨871747283971084424170393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162329711961445898893857 871747283971084424170393)
        ·
          refine ⟨653810462978313318127795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871747283971084424170393 653810462978313318127795)
          ·
            refine ⟨980715694467469977191693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653810462978313318127795 980715694467469977191693)
            ·
              refine ⟨367768385425301241446885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980715694467469977191693 367768385425301241446885)
              ·
                refine ⟨68956572267243982771291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367768385425301241446885 68956572267243982771291)
                ·
                  rfl

theorem cell20_453237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_453237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453237 prefixEnd_453237 := by exact prefixLift 453237
  have htrace : WordTrace (prefixWord ++ tailWord_453237) baseStart_453237 baseEnd_453237 := by
    simpa [prefixWord, tailWord_453237, baseEnd_453237] using wordTrace_append hprefix tailTrace_453237
  have hstable : (prefixWord ++ tailWord_453237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453237).length < 2 ^ (prefixWord ++ tailWord_453237).sum := by decide
  have hdescent : baseEnd_453237 < baseStart_453237 := by decide
  rcases family_descends (prefixWord ++ tailWord_453237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453255 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_453255 : Nat := 118140960795 + 453255 * 2 ^ 59
def prefixEnd_453255 : Nat := 4983230072969 + 3 ^ 40 * 453255 * 2
def baseEnd_453255 : Nat := 206877932492203885713799

theorem tailTrace_453255 : CollatzResearch.WordTrace tailWord_453255 prefixEnd_453255 206877932492203885713799 := by
  unfold tailWord_453255
  simp only [CollatzResearch.WordTrace]
  refine ⟨16531567972942019636201219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11021045315294679757467479 16531567972942019636201219)
  ·
    refine ⟨24797351959413029454301829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16531567972942019636201219 24797351959413029454301829)
    ·
      refine ⟨4649503492389943022681593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24797351959413029454301829 4649503492389943022681593)
      ·
        refine ⟨3487127619292457267011195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4649503492389943022681593 3487127619292457267011195)
        ·
          refine ⟨5230691428938685900516793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487127619292457267011195 5230691428938685900516793)
          ·
            refine ⟨3923018571704014425387595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230691428938685900516793 3923018571704014425387595)
            ·
              refine ⟨5884527857556021638081393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923018571704014425387595 5884527857556021638081393)
              ·
                refine ⟨4413395893167016228561045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5884527857556021638081393 4413395893167016228561045)
                ·
                  refine ⟨206877932492203885713799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4413395893167016228561045 206877932492203885713799)
                  ·
                    rfl

theorem cell20_453255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_453255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453255 prefixEnd_453255 := by exact prefixLift 453255
  have htrace : WordTrace (prefixWord ++ tailWord_453255) baseStart_453255 baseEnd_453255 := by
    simpa [prefixWord, tailWord_453255, baseEnd_453255] using wordTrace_append hprefix tailTrace_453255
  have hstable : (prefixWord ++ tailWord_453255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453255).length < 2 ^ (prefixWord ++ tailWord_453255).sum := by decide
  have hdescent : baseEnd_453255 < baseStart_453255 := by decide
  rcases family_descends (prefixWord ++ tailWord_453255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453268 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 2]
def baseStart_453268 : Nat := 118140960795 + 453268 * 2 ^ 59
def prefixEnd_453268 : Nat := 4983230072969 + 3 ^ 40 * 453268 * 2
def baseEnd_453268 : Nat := 206883866046433618280413

theorem tailTrace_453268 : CollatzResearch.WordTrace tailWord_453268 prefixEnd_453268 206883866046433618280413 := by
  unfold tailWord_453268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266021060947461428212229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11021361414596615237616305 8266021060947461428212229)
  ·
    refine ⟨1549878948927649017789793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8266021060947461428212229 1549878948927649017789793)
    ·
      refine ⟨1162409211695736763342345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1549878948927649017789793 1162409211695736763342345)
      ·
        refine ⟨871806908771802572506759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162409211695736763342345 871806908771802572506759)
        ·
          refine ⟨1307710363157703858760139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871806908771802572506759 1307710363157703858760139)
          ·
            refine ⟨1961565544736555788140209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307710363157703858760139 1961565544736555788140209)
            ·
              refine ⟨1471174158552416841105157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961565544736555788140209 1471174158552416841105157)
              ·
                refine ⟨275845154728578157707217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1471174158552416841105157 275845154728578157707217)
                ·
                  refine ⟨206883866046433618280413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275845154728578157707217 206883866046433618280413)
                  ·
                    rfl

theorem cell20_453268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_453268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453268 prefixEnd_453268 := by exact prefixLift 453268
  have htrace : WordTrace (prefixWord ++ tailWord_453268) baseStart_453268 baseEnd_453268 := by
    simpa [prefixWord, tailWord_453268, baseEnd_453268] using wordTrace_append hprefix tailTrace_453268
  have hstable : (prefixWord ++ tailWord_453268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453268).length < 2 ^ (prefixWord ++ tailWord_453268).sum := by decide
  have hdescent : baseEnd_453268 < baseStart_453268 := by decide
  rcases family_descends (prefixWord ++ tailWord_453268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453272 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_453272 : Nat := 118140960795 + 453272 * 2 ^ 59
def prefixEnd_453272 : Nat := 4983230072969 + 3 ^ 40 * 453272 * 2
def baseEnd_453272 : Nat := 206885691755427382147063

theorem tailTrace_453272 : CollatzResearch.WordTrace tailWord_453272 prefixEnd_453272 206885691755427382147063 := by
  unfold tailWord_453272
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266094006940215769785035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11021458675920287693046713 8266094006940215769785035)
  ·
    refine ⟨12399141010410323654677553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8266094006940215769785035 12399141010410323654677553)
    ·
      refine ⟨9299355757807742741008165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12399141010410323654677553 9299355757807742741008165)
      ·
        refine ⟨1743629204588951763939031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9299355757807742741008165 1743629204588951763939031)
        ·
          refine ⟨2615443806883427645908547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743629204588951763939031 2615443806883427645908547)
          ·
            refine ⟨3923165710325141468862821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615443806883427645908547 3923165710325141468862821)
            ·
              refine ⟨735593570685964025411779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3923165710325141468862821 735593570685964025411779)
              ·
                refine ⟨1103390356028946038117669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735593570685964025411779 1103390356028946038117669)
                ·
                  refine ⟨206885691755427382147063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103390356028946038117669 206885691755427382147063)
                  ·
                    rfl

theorem cell20_453272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_453272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453272 prefixEnd_453272 := by exact prefixLift 453272
  have htrace : WordTrace (prefixWord ++ tailWord_453272) baseStart_453272 baseEnd_453272 := by
    simpa [prefixWord, tailWord_453272, baseEnd_453272] using wordTrace_append hprefix tailTrace_453272
  have hstable : (prefixWord ++ tailWord_453272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453272).length < 2 ^ (prefixWord ++ tailWord_453272).sum := by decide
  have hdescent : baseEnd_453272 < baseStart_453272 := by decide
  rcases family_descends (prefixWord ++ tailWord_453272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453302 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_453302 : Nat := 118140960795 + 453302 * 2 ^ 59
def prefixEnd_453302 : Nat := 4983230072969 + 3 ^ 40 * 453302 * 2
def baseEnd_453302 : Nat := 206899384572880611146941

theorem tailTrace_453302 : CollatzResearch.WordTrace tailWord_453302 prefixEnd_453302 206899384572880611146941 := by
  unfold tailWord_453302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033330137735734166447635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11022188135847831108774773 1033330137735734166447635)
  ·
    refine ⟨1549995206603601249671453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1033330137735734166447635 1549995206603601249671453)
    ·
      refine ⟨581248202476350468626795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1549995206603601249671453 581248202476350468626795)
      ·
        refine ⟨871872303714525702940193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581248202476350468626795 871872303714525702940193)
        ·
          refine ⟨653904227785894277205145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871872303714525702940193 653904227785894277205145)
          ·
            refine ⟨490428170839420707903859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653904227785894277205145 490428170839420707903859)
            ·
              refine ⟨735642256259131061855789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490428170839420707903859 735642256259131061855789)
              ·
                refine ⟨275865846097174148195921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 735642256259131061855789 275865846097174148195921)
                ·
                  refine ⟨206899384572880611146941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275865846097174148195921 206899384572880611146941)
                  ·
                    rfl

theorem cell20_453302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_453302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453302 prefixEnd_453302 := by exact prefixLift 453302
  have htrace : WordTrace (prefixWord ++ tailWord_453302) baseStart_453302 baseEnd_453302 := by
    simpa [prefixWord, tailWord_453302, baseEnd_453302] using wordTrace_append hprefix tailTrace_453302
  have hstable : (prefixWord ++ tailWord_453302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453302).length < 2 ^ (prefixWord ++ tailWord_453302).sum := by decide
  have hdescent : baseEnd_453302 < baseStart_453302 := by decide
  rcases family_descends (prefixWord ++ tailWord_453302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453313 : List Nat := [1, 2, 6, 2, 1, 2, 6]
def baseStart_453313 : Nat := 118140960795 + 453313 * 2 ^ 59
def prefixEnd_453313 : Nat := 4983230072969 + 3 ^ 40 * 453313 * 2
def baseEnd_453313 : Nat := 22989378363623717975581

theorem tailTrace_453313 : CollatzResearch.WordTrace tailWord_453313 prefixEnd_453313 22989378363623717975581 := by
  unfold tailWord_453313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16533683406731895541812593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11022455604487930361208395 16533683406731895541812593)
  ·
    refine ⟨12400262555048921656359445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16533683406731895541812593 12400262555048921656359445)
    ·
      refine ⟨581262307267918202641849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12400262555048921656359445 581262307267918202641849)
      ·
        refine ⟨435946730450938651981387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581262307267918202641849 435946730450938651981387)
        ·
          refine ⟨653920095676407977972081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435946730450938651981387 653920095676407977972081)
          ·
            refine ⟨490440071757305983479061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653920095676407977972081 490440071757305983479061)
            ·
              refine ⟨22989378363623717975581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 490440071757305983479061 22989378363623717975581)
              ·
                rfl

theorem cell20_453313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_453313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453313 prefixEnd_453313 := by exact prefixLift 453313
  have htrace : WordTrace (prefixWord ++ tailWord_453313) baseStart_453313 baseEnd_453313 := by
    simpa [prefixWord, tailWord_453313, baseEnd_453313] using wordTrace_append hprefix tailTrace_453313
  have hstable : (prefixWord ++ tailWord_453313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453313).length < 2 ^ (prefixWord ++ tailWord_453313).sum := by decide
  have hdescent : baseEnd_453313 < baseStart_453313 := by decide
  rcases family_descends (prefixWord ++ tailWord_453313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453407 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_453407 : Nat := 118140960795 + 453407 * 2 ^ 59
def prefixEnd_453407 : Nat := 4983230072969 + 3 ^ 40 * 453407 * 2
def baseEnd_453407 : Nat := 206947309433966912646511

theorem tailTrace_453407 : CollatzResearch.WordTrace tailWord_453407 prefixEnd_453407 206947309433966912646511 := by
  unfold tailWord_453407
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537111868391349595734475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11024741245594233063822983 16537111868391349595734475)
  ·
    refine ⟨24805667802587024393601713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16537111868391349595734475 24805667802587024393601713)
    ·
      refine ⟨18604250851940268295201285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24805667802587024393601713 18604250851940268295201285)
      ·
        refine ⟨3488297034738800305350241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18604250851940268295201285 3488297034738800305350241)
        ·
          refine ⟨2616222776054100229012681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488297034738800305350241 2616222776054100229012681)
          ·
            refine ⟨1962167082040575171759511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616222776054100229012681 1962167082040575171759511)
            ·
              refine ⟨2943250623060862757639267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962167082040575171759511 2943250623060862757639267)
              ·
                refine ⟨4414875934591294136458901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943250623060862757639267 4414875934591294136458901)
                ·
                  refine ⟨206947309433966912646511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4414875934591294136458901 206947309433966912646511)
                  ·
                    rfl

theorem cell20_453407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_453407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453407 prefixEnd_453407 := by exact prefixLift 453407
  have htrace : WordTrace (prefixWord ++ tailWord_453407) baseStart_453407 baseEnd_453407 := by
    simpa [prefixWord, tailWord_453407, baseEnd_453407] using wordTrace_append hprefix tailTrace_453407
  have hstable : (prefixWord ++ tailWord_453407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453407).length < 2 ^ (prefixWord ++ tailWord_453407).sum := by decide
  have hdescent : baseEnd_453407 < baseStart_453407 := by decide
  rcases family_descends (prefixWord ++ tailWord_453407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453410 : List Nat := [3, 3, 1, 1, 2, 3, 3, 4]
def baseStart_453410 : Nat := 118140960795 + 453410 * 2 ^ 59
def prefixEnd_453410 : Nat := 4983230072969 + 3 ^ 40 * 453410 * 2
def baseEnd_453410 : Nat := 68982892905237411848833

theorem tailTrace_453410 : CollatzResearch.WordTrace tailWord_453410 prefixEnd_453410 68982892905237411848833 := by
  unfold tailWord_453410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134305321845120277023421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11024814191586987405395789 4134305321845120277023421)
  ·
    refine ⟨1550364495691920103883783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4134305321845120277023421 1550364495691920103883783)
    ·
      refine ⟨2325546743537880155825675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550364495691920103883783 2325546743537880155825675)
      ·
        refine ⟨3488320115306820233738513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325546743537880155825675 3488320115306820233738513)
        ·
          refine ⟨2616240086480115175303885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488320115306820233738513 2616240086480115175303885)
          ·
            refine ⟨981090032430043190738957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2616240086480115175303885 981090032430043190738957)
            ·
              refine ⟨367908762161266196527109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981090032430043190738957 367908762161266196527109)
              ·
                refine ⟨68982892905237411848833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367908762161266196527109 68982892905237411848833)
                ·
                  rfl

theorem cell20_453410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_453410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453410 prefixEnd_453410 := by exact prefixLift 453410
  have htrace : WordTrace (prefixWord ++ tailWord_453410) baseStart_453410 baseEnd_453410 := by
    simpa [prefixWord, tailWord_453410, baseEnd_453410] using wordTrace_append hprefix tailTrace_453410
  have hstable : (prefixWord ++ tailWord_453410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453410).length < 2 ^ (prefixWord ++ tailWord_453410).sum := by decide
  have hdescent : baseEnd_453410 < baseStart_453410 := by decide
  rcases family_descends (prefixWord ++ tailWord_453410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453430 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_453430 : Nat := 118140960795 + 453430 * 2 ^ 59
def prefixEnd_453430 : Nat := 4983230072969 + 3 ^ 40 * 453430 * 2
def baseEnd_453430 : Nat := 206957807260681054879751

theorem tailTrace_453430 : CollatzResearch.WordTrace tailWord_453430 prefixEnd_453430 206957807260681054879751 := by
  unfold tailWord_453430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033621921706751532738859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11025300498205349682547829 1033621921706751532738859)
  ·
    refine ⟨1550432882560127299108289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1033621921706751532738859 1550432882560127299108289)
    ·
      refine ⟨1162824661920095474331217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1550432882560127299108289 1162824661920095474331217)
      ·
        refine ⟨872118496440071605748413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162824661920095474331217 872118496440071605748413)
        ·
          refine ⟨327044436165026852155655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 872118496440071605748413 327044436165026852155655)
          ·
            refine ⟨490566654247540278233483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327044436165026852155655 490566654247540278233483)
            ·
              refine ⟨735849981371310417350225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490566654247540278233483 735849981371310417350225)
              ·
                refine ⟨551887486028482813012669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735849981371310417350225 551887486028482813012669)
                ·
                  refine ⟨206957807260681054879751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551887486028482813012669 206957807260681054879751)
                  ·
                    rfl

theorem cell20_453430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_453430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453430 prefixEnd_453430 := by exact prefixLift 453430
  have htrace : WordTrace (prefixWord ++ tailWord_453430) baseStart_453430 baseEnd_453430 := by
    simpa [prefixWord, tailWord_453430, baseEnd_453430] using wordTrace_append hprefix tailTrace_453430
  have hstable : (prefixWord ++ tailWord_453430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453430).length < 2 ^ (prefixWord ++ tailWord_453430).sum := by decide
  have hdescent : baseEnd_453430 < baseStart_453430 := by decide
  rcases family_descends (prefixWord ++ tailWord_453430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453434 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_453434 : Nat := 118140960795 + 453434 * 2 ^ 59
def prefixEnd_453434 : Nat := 4983230072969 + 3 ^ 40 * 453434 * 2
def baseEnd_453434 : Nat := 206959632969674818746401

theorem tailTrace_453434 : CollatzResearch.WordTrace tailWord_453434 prefixEnd_453434 206959632969674818746401 := by
  unfold tailWord_453434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134524159823383301741839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11025397759529022137978237 4134524159823383301741839)
  ·
    refine ⟨6201786239735074952612759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4134524159823383301741839 6201786239735074952612759)
    ·
      refine ⟨9302679359602612428919139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6201786239735074952612759 9302679359602612428919139)
      ·
        refine ⟨13954019039403918643378709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302679359602612428919139 13954019039403918643378709)
        ·
          refine ⟨654094642472058686408377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13954019039403918643378709 654094642472058686408377)
          ·
            refine ⟨490570981854044014806283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654094642472058686408377 490570981854044014806283)
            ·
              refine ⟨735856472781066022209425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490570981854044014806283 735856472781066022209425)
              ·
                refine ⟨551892354585799516657069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735856472781066022209425 551892354585799516657069)
                ·
                  refine ⟨206959632969674818746401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551892354585799516657069 206959632969674818746401)
                  ·
                    rfl

theorem cell20_453434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_453434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453434 prefixEnd_453434 := by exact prefixLift 453434
  have htrace : WordTrace (prefixWord ++ tailWord_453434) baseStart_453434 baseEnd_453434 := by
    simpa [prefixWord, tailWord_453434, baseEnd_453434] using wordTrace_append hprefix tailTrace_453434
  have hstable : (prefixWord ++ tailWord_453434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453434).length < 2 ^ (prefixWord ++ tailWord_453434).sum := by decide
  have hdescent : baseEnd_453434 < baseStart_453434 := by decide
  rcases family_descends (prefixWord ++ tailWord_453434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453476 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_453476 : Nat := 118140960795 + 453476 * 2 ^ 59
def prefixEnd_453476 : Nat := 4983230072969 + 3 ^ 40 * 453476 * 2
def baseEnd_453476 : Nat := 206978802914109339346229

theorem tailTrace_453476 : CollatzResearch.WordTrace tailWord_453476 prefixEnd_453476 206978802914109339346229 := by
  unfold tailWord_453476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269814252570687189998141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11026419003427582919997521 8269814252570687189998141)
  ·
    refine ⟨3101180344714007696249303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8269814252570687189998141 3101180344714007696249303)
    ·
      refine ⟨4651770517071011544373955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101180344714007696249303 4651770517071011544373955)
      ·
        refine ⟨6977655775606517316560933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651770517071011544373955 6977655775606517316560933)
        ·
          refine ⟨1308310457926221996855175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6977655775606517316560933 1308310457926221996855175)
          ·
            refine ⟨1962465686889332995282763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308310457926221996855175 1962465686889332995282763)
            ·
              refine ⟨2943698530333999492924145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962465686889332995282763 2943698530333999492924145)
              ·
                refine ⟨2207773897750499619693109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943698530333999492924145 2207773897750499619693109)
                ·
                  refine ⟨206978802914109339346229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2207773897750499619693109 206978802914109339346229)
                  ·
                    rfl

theorem cell20_453476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_453476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453476 prefixEnd_453476 := by exact prefixLift 453476
  have htrace : WordTrace (prefixWord ++ tailWord_453476) baseStart_453476 baseEnd_453476 := by
    simpa [prefixWord, tailWord_453476, baseEnd_453476] using wordTrace_append hprefix tailTrace_453476
  have hstable : (prefixWord ++ tailWord_453476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453476).length < 2 ^ (prefixWord ++ tailWord_453476).sum := by decide
  have hdescent : baseEnd_453476 < baseStart_453476 := by decide
  rcases family_descends (prefixWord ++ tailWord_453476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453479 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 2]
def baseStart_453479 : Nat := 118140960795 + 453479 * 2 ^ 59
def prefixEnd_453479 : Nat := 4983230072969 + 3 ^ 40 * 453479 * 2
def baseEnd_453479 : Nat := 206980172195854662246217

theorem tailTrace_453479 : CollatzResearch.WordTrace tailWord_453479 prefixEnd_453479 206980172195854662246217 := by
  unfold tailWord_453479
  simp only [CollatzResearch.WordTrace]
  refine ⟨16539737924130505892355491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11026491949420337261570327 16539737924130505892355491)
  ·
    refine ⟨24809606886195758838533237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16539737924130505892355491 24809606886195758838533237)
    ·
      refine ⟨2325900645580852391112491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24809606886195758838533237 2325900645580852391112491)
      ·
        refine ⟨3488850968371278586668737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325900645580852391112491 3488850968371278586668737)
        ·
          refine ⟨2616638226278458940001553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488850968371278586668737 2616638226278458940001553)
          ·
            refine ⟨1962478669708844205001165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616638226278458940001553 1962478669708844205001165)
            ·
              refine ⟨735929501140816576875437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1962478669708844205001165 735929501140816576875437)
              ·
                refine ⟨275973562927806216328289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 735929501140816576875437 275973562927806216328289)
                ·
                  refine ⟨206980172195854662246217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275973562927806216328289 206980172195854662246217)
                  ·
                    rfl

theorem cell20_453479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 2].length) (baseStart_453479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453479 prefixEnd_453479 := by exact prefixLift 453479
  have htrace : WordTrace (prefixWord ++ tailWord_453479) baseStart_453479 baseEnd_453479 := by
    simpa [prefixWord, tailWord_453479, baseEnd_453479] using wordTrace_append hprefix tailTrace_453479
  have hstable : (prefixWord ++ tailWord_453479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453479).length < 2 ^ (prefixWord ++ tailWord_453479).sum := by decide
  have hdescent : baseEnd_453479 < baseStart_453479 := by decide
  rcases family_descends (prefixWord ++ tailWord_453479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453486 : List Nat := [4, 1, 2, 3, 2, 2, 6]
def baseStart_453486 : Nat := 118140960795 + 453486 * 2 ^ 59
def prefixEnd_453486 : Nat := 4983230072969 + 3 ^ 40 * 453486 * 2
def baseEnd_453486 : Nat := 22998151909621527668095

theorem tailTrace_453486 : CollatzResearch.WordTrace tailWord_453486 prefixEnd_453486 22998151909621527668095 := by
  unfold tailWord_453486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067499154388143260982539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11026662156736764058573541 2067499154388143260982539)
  ·
    refine ⟨3101248731582214891473809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2067499154388143260982539 3101248731582214891473809)
    ·
      refine ⟨2325936548686661168605357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3101248731582214891473809 2325936548686661168605357)
      ·
        refine ⟨872226205757497938227009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2325936548686661168605357 872226205757497938227009)
        ·
          refine ⟨654169654318123453670257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872226205757497938227009 654169654318123453670257)
          ·
            refine ⟨490627240738592590252693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654169654318123453670257 490627240738592590252693)
            ·
              refine ⟨22998151909621527668095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 490627240738592590252693 22998151909621527668095)
              ·
                rfl

theorem cell20_453486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 6].length) (baseStart_453486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453486 prefixEnd_453486 := by exact prefixLift 453486
  have htrace : WordTrace (prefixWord ++ tailWord_453486) baseStart_453486 baseEnd_453486 := by
    simpa [prefixWord, tailWord_453486, baseEnd_453486] using wordTrace_append hprefix tailTrace_453486
  have hstable : (prefixWord ++ tailWord_453486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453486).length < 2 ^ (prefixWord ++ tailWord_453486).sum := by decide
  have hdescent : baseEnd_453486 < baseStart_453486 := by decide
  rcases family_descends (prefixWord ++ tailWord_453486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453490 : List Nat := [3, 2, 1, 2, 1, 1, 10]
def baseStart_453490 : Nat := 118140960795 + 453490 * 2 ^ 59
def prefixEnd_453490 : Nat := 4983230072969 + 3 ^ 40 * 453490 * 2
def baseEnd_453490 : Nat := 22998354766176390319945

theorem tailTrace_453490 : CollatzResearch.WordTrace tailWord_453490 prefixEnd_453490 22998354766176390319945 := by
  unfold tailWord_453490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135034781772663692751481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11026759418060436514003949 4135034781772663692751481)
  ·
    refine ⟨3101276086329497769563611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4135034781772663692751481 3101276086329497769563611)
    ·
      refine ⟨4651914129494246654345417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101276086329497769563611 4651914129494246654345417)
      ·
        refine ⟨3488935597120684990759063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4651914129494246654345417 3488935597120684990759063)
        ·
          refine ⟨5233403395681027486138595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488935597120684990759063 5233403395681027486138595)
          ·
            refine ⟨7850105093521541229207893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233403395681027486138595 7850105093521541229207893)
            ·
              refine ⟨22998354766176390319945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7850105093521541229207893 22998354766176390319945)
              ·
                rfl

theorem cell20_453490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_453490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453490 prefixEnd_453490 := by exact prefixLift 453490
  have htrace : WordTrace (prefixWord ++ tailWord_453490) baseStart_453490 baseEnd_453490 := by
    simpa [prefixWord, tailWord_453490, baseEnd_453490] using wordTrace_append hprefix tailTrace_453490
  have hstable : (prefixWord ++ tailWord_453490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453490).length < 2 ^ (prefixWord ++ tailWord_453490).sum := by decide
  have hdescent : baseEnd_453490 < baseStart_453490 := by decide
  rcases family_descends (prefixWord ++ tailWord_453490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453500 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 2]
def baseStart_453500 : Nat := 118140960795 + 453500 * 2 ^ 59
def prefixEnd_453500 : Nat := 4983230072969 + 3 ^ 40 * 453500 * 2
def baseEnd_453500 : Nat := 206989757168071922546131

theorem tailTrace_453500 : CollatzResearch.WordTrace tailWord_453500 prefixEnd_453500 206989757168071922546131 := by
  unfold tailWord_453500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270251928527213239434977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11027002571369617652579969 8270251928527213239434977)
  ·
    refine ⟨6202688946395409929576233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8270251928527213239434977 6202688946395409929576233)
    ·
      refine ⟨4652016709796557447182175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6202688946395409929576233 4652016709796557447182175)
      ·
        refine ⟨6978025064694836170773263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652016709796557447182175 6978025064694836170773263)
        ·
          refine ⟨10467037597042254256159895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6978025064694836170773263 10467037597042254256159895)
          ·
            refine ⟨15700556395563381384239843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467037597042254256159895 15700556395563381384239843)
            ·
              refine ⟨23550834593345072076359765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15700556395563381384239843 23550834593345072076359765)
              ·
                refine ⟨275986342890762563394841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 23550834593345072076359765 275986342890762563394841)
                ·
                  refine ⟨206989757168071922546131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275986342890762563394841 206989757168071922546131)
                  ·
                    rfl

theorem cell20_453500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_453500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453500 prefixEnd_453500 := by exact prefixLift 453500
  have htrace : WordTrace (prefixWord ++ tailWord_453500) baseStart_453500 baseEnd_453500 := by
    simpa [prefixWord, tailWord_453500, baseEnd_453500] using wordTrace_append hprefix tailTrace_453500
  have hstable : (prefixWord ++ tailWord_453500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453500).length < 2 ^ (prefixWord ++ tailWord_453500).sum := by decide
  have hdescent : baseEnd_453500 < baseStart_453500 := by decide
  rcases family_descends (prefixWord ++ tailWord_453500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453576 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_453576 : Nat := 118140960795 + 453576 * 2 ^ 59
def prefixEnd_453576 : Nat := 4983230072969 + 3 ^ 40 * 453576 * 2
def baseEnd_453576 : Nat := 207024445638953436012487

theorem tailTrace_453576 : CollatzResearch.WordTrace tailWord_453576 prefixEnd_453576 207024445638953436012487 := by
  unfold tailWord_453576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271637902389545729318291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11028850536519394305757721 8271637902389545729318291)
  ·
    refine ⟨12407456853584318593977437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8271637902389545729318291 12407456853584318593977437)
    ·
      refine ⟨4652796320094119472741539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12407456853584318593977437 4652796320094119472741539)
      ·
        refine ⟨6979194480141179209112309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652796320094119472741539 6979194480141179209112309)
        ·
          refine ⟨654299482513235550854279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6979194480141179209112309 654299482513235550854279)
          ·
            refine ⟨981449223769853326281419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654299482513235550854279 981449223769853326281419)
            ·
              refine ⟨1472173835654779989422129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981449223769853326281419 1472173835654779989422129)
              ·
                refine ⟨1104130376741084992066597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472173835654779989422129 1104130376741084992066597)
                ·
                  refine ⟨207024445638953436012487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104130376741084992066597 207024445638953436012487)
                  ·
                    rfl

theorem cell20_453576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_453576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453576 prefixEnd_453576 := by exact prefixLift 453576
  have htrace : WordTrace (prefixWord ++ tailWord_453576) baseStart_453576 baseEnd_453576 := by
    simpa [prefixWord, tailWord_453576, baseEnd_453576] using wordTrace_append hprefix tailTrace_453576
  have hstable : (prefixWord ++ tailWord_453576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453576).length < 2 ^ (prefixWord ++ tailWord_453576).sum := by decide
  have hdescent : baseEnd_453576 < baseStart_453576 := by decide
  rcases family_descends (prefixWord ++ tailWord_453576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453583 : List Nat := [1, 1, 2, 1, 1, 7, 3, 4]
def baseStart_453583 : Nat := 118140960795 + 453583 * 2 ^ 59
def prefixEnd_453583 : Nat := 4983230072969 + 3 ^ 40 * 453583 * 2
def baseEnd_453583 : Nat := 69009213543230840926375

theorem tailTrace_453583 : CollatzResearch.WordTrace tailWord_453583 prefixEnd_453583 69009213543230840926375 := by
  unfold tailWord_453583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16543531115753731654141403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11029020743835821102760935 16543531115753731654141403)
  ·
    refine ⟨24815296673630597481212105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16543531115753731654141403 24815296673630597481212105)
    ·
      refine ⟨18611472505222948110909079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24815296673630597481212105 18611472505222948110909079)
      ·
        refine ⟨27917208757834422166363619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18611472505222948110909079 27917208757834422166363619)
        ·
          refine ⟨41875813136751633249545429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27917208757834422166363619 41875813136751633249545429)
          ·
            refine ⟨981464370392616404286221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 41875813136751633249545429 981464370392616404286221)
            ·
              refine ⟨368049138897231151607333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981464370392616404286221 368049138897231151607333)
              ·
                refine ⟨69009213543230840926375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368049138897231151607333 69009213543230840926375)
                ·
                  rfl

theorem cell20_453583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_453583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453583 prefixEnd_453583 := by exact prefixLift 453583
  have htrace : WordTrace (prefixWord ++ tailWord_453583) baseStart_453583 baseEnd_453583 := by
    simpa [prefixWord, tailWord_453583, baseEnd_453583] using wordTrace_append hprefix tailTrace_453583
  have hstable : (prefixWord ++ tailWord_453583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453583).length < 2 ^ (prefixWord ++ tailWord_453583).sum := by decide
  have hdescent : baseEnd_453583 < baseStart_453583 := by decide
  rcases family_descends (prefixWord ++ tailWord_453583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453593 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 2]
def baseStart_453593 : Nat := 118140960795 + 453593 * 2 ^ 59
def prefixEnd_453593 : Nat := 4983230072969 + 3 ^ 40 * 453593 * 2
def baseEnd_453593 : Nat := 207032204902176932445751

theorem tailTrace_453593 : CollatzResearch.WordTrace tailWord_453593 prefixEnd_453593 207032204902176932445751 := by
  unfold tailWord_453593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16543895845717503362005433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11029263897145002241336955 16543895845717503362005433)
  ·
    refine ⟨12407921884288127521504075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16543895845717503362005433 12407921884288127521504075)
    ·
      refine ⟨18611882826432191282256113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12407921884288127521504075 18611882826432191282256113)
      ·
        refine ⟨13958912119824143461692085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18611882826432191282256113 13958912119824143461692085)
        ·
          refine ⟨1308648011233513449533633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13958912119824143461692085 1308648011233513449533633)
          ·
            refine ⟨981486008425135087150225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308648011233513449533633 981486008425135087150225)
            ·
              refine ⟨736114506318851315362669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981486008425135087150225 736114506318851315362669)
              ·
                refine ⟨276042939869569243261001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736114506318851315362669 276042939869569243261001)
                ·
                  refine ⟨207032204902176932445751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276042939869569243261001 207032204902176932445751)
                  ·
                    rfl

theorem cell20_453593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_453593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453593 prefixEnd_453593 := by exact prefixLift 453593
  have htrace : WordTrace (prefixWord ++ tailWord_453593) baseStart_453593 baseEnd_453593 := by
    simpa [prefixWord, tailWord_453593, baseEnd_453593] using wordTrace_append hprefix tailTrace_453593
  have hstable : (prefixWord ++ tailWord_453593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453593).length < 2 ^ (prefixWord ++ tailWord_453593).sum := by decide
  have hdescent : baseEnd_453593 < baseStart_453593 := by decide
  rcases family_descends (prefixWord ++ tailWord_453593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453607 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_453607 : Nat := 118140960795 + 453607 * 2 ^ 59
def prefixEnd_453607 : Nat := 4983230072969 + 3 ^ 40 * 453607 * 2
def baseEnd_453607 : Nat := 207038594883655105979027

theorem tailTrace_453607 : CollatzResearch.WordTrace tailWord_453607 prefixEnd_453607 207038594883655105979027 := by
  unfold tailWord_453607
  simp only [CollatzResearch.WordTrace]
  refine ⟨16544406467666783753015075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11029604311777855835343383 16544406467666783753015075)
  ·
    refine ⟨24816609701500175629522613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16544406467666783753015075 24816609701500175629522613)
    ·
      refine ⟨2326557159515641465267745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24816609701500175629522613 2326557159515641465267745)
      ·
        refine ⟨1744917869636731098950809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326557159515641465267745 1744917869636731098950809)
        ·
          refine ⟨1308688402227548324213107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744917869636731098950809 1308688402227548324213107)
          ·
            refine ⟨1963032603341322486319661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308688402227548324213107 1963032603341322486319661)
            ·
              refine ⟨736137226252995932369873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1963032603341322486319661 736137226252995932369873)
              ·
                refine ⟨552102919689746949277405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736137226252995932369873 552102919689746949277405)
                ·
                  refine ⟨207038594883655105979027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552102919689746949277405 207038594883655105979027)
                  ·
                    rfl

theorem cell20_453607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_453607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453607 prefixEnd_453607 := by exact prefixLift 453607
  have htrace : WordTrace (prefixWord ++ tailWord_453607) baseStart_453607 baseEnd_453607 := by
    simpa [prefixWord, tailWord_453607, baseEnd_453607] using wordTrace_append hprefix tailTrace_453607
  have hstable : (prefixWord ++ tailWord_453607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453607).length < 2 ^ (prefixWord ++ tailWord_453607).sum := by decide
  have hdescent : baseEnd_453607 < baseStart_453607 := by decide
  rcases family_descends (prefixWord ++ tailWord_453607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453634 : List Nat := [3, 4, 1, 3, 1, 2, 2, 4]
def baseStart_453634 : Nat := 118140960795 + 453634 * 2 ^ 59
def prefixEnd_453634 : Nat := 4983230072969 + 3 ^ 40 * 453634 * 2
def baseEnd_453634 : Nat := 69016972806454337359639

theorem tailTrace_453634 : CollatzResearch.WordTrace tailWord_453634 prefixEnd_453634 69016972806454337359639 := by
  unfold tailWord_453634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136347809642241841061989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11030260825712644909498637 4136347809642241841061989)
  ·
    refine ⟨775565214307920345199123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4136347809642241841061989 775565214307920345199123)
    ·
      refine ⟨1163347821461880517798685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775565214307920345199123 1163347821461880517798685)
      ·
        refine ⟨436255433048205194174507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1163347821461880517798685 436255433048205194174507)
        ·
          refine ⟨654383149572307791261761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436255433048205194174507 654383149572307791261761)
          ·
            refine ⟨490787362179230843446321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654383149572307791261761 490787362179230843446321)
            ·
              refine ⟨368090521634423132584741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490787362179230843446321 368090521634423132584741)
              ·
                refine ⟨69016972806454337359639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368090521634423132584741 69016972806454337359639)
                ·
                  rfl

theorem cell20_453634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_453634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453634 prefixEnd_453634 := by exact prefixLift 453634
  have htrace : WordTrace (prefixWord ++ tailWord_453634) baseStart_453634 baseEnd_453634 := by
    simpa [prefixWord, tailWord_453634, baseEnd_453634] using wordTrace_append hprefix tailTrace_453634
  have hstable : (prefixWord ++ tailWord_453634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453634).length < 2 ^ (prefixWord ++ tailWord_453634).sum := by decide
  have hdescent : baseEnd_453634 < baseStart_453634 := by decide
  rcases family_descends (prefixWord ++ tailWord_453634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453666 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_453666 : Nat := 118140960795 + 453666 * 2 ^ 59
def prefixEnd_453666 : Nat := 4983230072969 + 3 ^ 40 * 453666 * 2
def baseEnd_453666 : Nat := 207065524091313123012119

theorem tailTrace_453666 : CollatzResearch.WordTrace tailWord_453666 prefixEnd_453666 207065524091313123012119 := by
  unfold tailWord_453666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136639593613259207353213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11031038916302024552941901 4136639593613259207353213)
  ·
    refine ⟨1551239847604972202757455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4136639593613259207353213 1551239847604972202757455)
    ·
      refine ⟨2326859771407458304136183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551239847604972202757455 2326859771407458304136183)
      ·
        refine ⟨3490289657111187456204275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2326859771407458304136183 3490289657111187456204275)
        ·
          refine ⟨5235434485666781184306413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490289657111187456204275 5235434485666781184306413)
          ·
            refine ⟨1963287932125042944114905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5235434485666781184306413 1963287932125042944114905)
            ·
              refine ⟨1472465949093782208086179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963287932125042944114905 1472465949093782208086179)
              ·
                refine ⟨2208698923640673312129269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472465949093782208086179 2208698923640673312129269)
                ·
                  refine ⟨207065524091313123012119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2208698923640673312129269 207065524091313123012119)
                  ·
                    rfl

theorem cell20_453666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_453666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453666 prefixEnd_453666 := by exact prefixLift 453666
  have htrace : WordTrace (prefixWord ++ tailWord_453666) baseStart_453666 baseEnd_453666 := by
    simpa [prefixWord, tailWord_453666, baseEnd_453666] using wordTrace_append hprefix tailTrace_453666
  have hstable : (prefixWord ++ tailWord_453666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453666).length < 2 ^ (prefixWord ++ tailWord_453666).sum := by decide
  have hdescent : baseEnd_453666 < baseStart_453666 := by decide
  rcases family_descends (prefixWord ++ tailWord_453666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453669 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 2]
def baseStart_453669 : Nat := 118140960795 + 453669 * 2 ^ 59
def prefixEnd_453669 : Nat := 4983230072969 + 3 ^ 40 * 453669 * 2
def baseEnd_453669 : Nat := 207066893373058445912107

theorem tailTrace_453669 : CollatzResearch.WordTrace tailWord_453669 prefixEnd_453669 207066893373058445912107 := by
  unfold tailWord_453669
  simp only [CollatzResearch.WordTrace]
  refine ⟨16546667793442168341772061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11031111862294778894514707 16546667793442168341772061)
  ·
    refine ⟨6205000422540813128164523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16546667793442168341772061 6205000422540813128164523)
    ·
      refine ⟨9307500633811219692246785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6205000422540813128164523 9307500633811219692246785)
      ·
        refine ⟨6980625475358414769185089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9307500633811219692246785 6980625475358414769185089)
        ·
          refine ⟨5235469106518811076888817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6980625475358414769185089 5235469106518811076888817)
          ·
            refine ⟨3926601829889108307666613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5235469106518811076888817 3926601829889108307666613)
            ·
              refine ⟨368118921552103903843745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3926601829889108307666613 368118921552103903843745)
              ·
                refine ⟨276089191164077927882809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368118921552103903843745 276089191164077927882809)
                ·
                  refine ⟨207066893373058445912107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276089191164077927882809 207066893373058445912107)
                  ·
                    rfl

theorem cell20_453669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_453669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453669 prefixEnd_453669 := by exact prefixLift 453669
  have htrace : WordTrace (prefixWord ++ tailWord_453669) baseStart_453669 baseEnd_453669 := by
    simpa [prefixWord, tailWord_453669, baseEnd_453669] using wordTrace_append hprefix tailTrace_453669
  have hstable : (prefixWord ++ tailWord_453669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453669).length < 2 ^ (prefixWord ++ tailWord_453669).sum := by decide
  have hdescent : baseEnd_453669 < baseStart_453669 := by decide
  rcases family_descends (prefixWord ++ tailWord_453669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453680 : List Nat := [2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_453680 : Nat := 118140960795 + 453680 * 2 ^ 59
def prefixEnd_453680 : Nat := 4983230072969 + 3 ^ 40 * 453680 * 2
def baseEnd_453680 : Nat := 69023971357597098848465

theorem tailTrace_453680 : CollatzResearch.WordTrace tailWord_453680 prefixEnd_453680 69023971357597098848465 := by
  unfold tailWord_453680
  simp only [CollatzResearch.WordTrace]
  refine ⟨8273534498201158610211247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11031379330934878146948329 8273534498201158610211247)
  ·
    refine ⟨12410301747301737915316871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8273534498201158610211247 12410301747301737915316871)
    ·
      refine ⟨18615452620952606872975307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12410301747301737915316871 18615452620952606872975307)
      ·
        refine ⟨27923178931428910309462961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18615452620952606872975307 27923178931428910309462961)
        ·
          refine ⟨20942384198571682732097221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27923178931428910309462961 20942384198571682732097221)
          ·
            refine ⟨3926697037232190512268229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20942384198571682732097221 3926697037232190512268229)
            ·
              refine ⟨736255694481035721050293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3926697037232190512268229 736255694481035721050293)
              ·
                refine ⟨69023971357597098848465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 736255694481035721050293 69023971357597098848465)
                ·
                  rfl

theorem cell20_453680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_453680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453680 prefixEnd_453680 := by exact prefixLift 453680
  have htrace : WordTrace (prefixWord ++ tailWord_453680) baseStart_453680 baseEnd_453680 := by
    simpa [prefixWord, tailWord_453680, baseEnd_453680] using wordTrace_append hprefix tailTrace_453680
  have hstable : (prefixWord ++ tailWord_453680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453680).length < 2 ^ (prefixWord ++ tailWord_453680).sum := by decide
  have hdescent : baseEnd_453680 < baseStart_453680 := by decide
  rcases family_descends (prefixWord ++ tailWord_453680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453728 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 2]
def baseStart_453728 : Nat := 118140960795 + 453728 * 2 ^ 59
def prefixEnd_453728 : Nat := 4983230072969 + 3 ^ 40 * 453728 * 2
def baseEnd_453728 : Nat := 207093822580716462945199

theorem tailTrace_453728 : CollatzResearch.WordTrace tailWord_453728 prefixEnd_453728 207093822580716462945199 := by
  unfold tailWord_453728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8274409850114210709084919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11032546466818947612113225 8274409850114210709084919)
  ·
    refine ⟨12411614775171316063627379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8274409850114210709084919 12411614775171316063627379)
    ·
      refine ⟨18617422162756974095441069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12411614775171316063627379 18617422162756974095441069)
      ·
        refine ⟨6981533311033865285790401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18617422162756974095441069 6981533311033865285790401)
        ·
          refine ⟨5236149983275398964342801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6981533311033865285790401 5236149983275398964342801)
          ·
            refine ⟨3927112487456549223257101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5236149983275398964342801 3927112487456549223257101)
            ·
              refine ⟨1472667182796205958721413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3927112487456549223257101 1472667182796205958721413)
              ·
                refine ⟨276125096774288617260265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1472667182796205958721413 276125096774288617260265)
                ·
                  refine ⟨207093822580716462945199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276125096774288617260265 207093822580716462945199)
                  ·
                    rfl

theorem cell20_453728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_453728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453728 prefixEnd_453728 := by exact prefixLift 453728
  have htrace : WordTrace (prefixWord ++ tailWord_453728) baseStart_453728 baseEnd_453728 := by
    simpa [prefixWord, tailWord_453728, baseEnd_453728] using wordTrace_append hprefix tailTrace_453728
  have hstable : (prefixWord ++ tailWord_453728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453728).length < 2 ^ (prefixWord ++ tailWord_453728).sum := by decide
  have hdescent : baseEnd_453728 < baseStart_453728 := by decide
  rcases family_descends (prefixWord ++ tailWord_453728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453735 : List Nat := [1, 1, 5, 1, 1, 5, 1, 5]
def baseStart_453735 : Nat := 118140960795 + 453735 * 2 ^ 59
def prefixEnd_453735 : Nat := 4983230072969 + 3 ^ 40 * 453735 * 2
def baseEnd_453735 : Nat := 69032339190485183237279

theorem tailTrace_453735 : CollatzResearch.WordTrace tailWord_453735 prefixEnd_453735 69032339190485183237279 := by
  unfold tailWord_453735
  simp only [CollatzResearch.WordTrace]
  refine ⟨16549075011203061613674659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11032716674135374409116439 16549075011203061613674659)
  ·
    refine ⟨24823612516804592420511989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16549075011203061613674659 24823612516804592420511989)
    ·
      refine ⟨2327213673450430539422999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24823612516804592420511989 2327213673450430539422999)
      ·
        refine ⟨3490820510175645809134499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327213673450430539422999 3490820510175645809134499)
        ·
          refine ⟨5236230765263468713701749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490820510175645809134499 5236230765263468713701749)
          ·
            refine ⟨490896634243450191909539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5236230765263468713701749 490896634243450191909539)
            ·
              refine ⟨736344951365175287864309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490896634243450191909539 736344951365175287864309)
              ·
                refine ⟨69032339190485183237279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 736344951365175287864309 69032339190485183237279)
                ·
                  rfl

theorem cell20_453735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_453735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453735 prefixEnd_453735 := by exact prefixLift 453735
  have htrace : WordTrace (prefixWord ++ tailWord_453735) baseStart_453735 baseEnd_453735 := by
    simpa [prefixWord, tailWord_453735, baseEnd_453735] using wordTrace_append hprefix tailTrace_453735
  have hstable : (prefixWord ++ tailWord_453735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453735).length < 2 ^ (prefixWord ++ tailWord_453735).sum := by decide
  have hdescent : baseEnd_453735 < baseStart_453735 := by decide
  rcases family_descends (prefixWord ++ tailWord_453735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453758 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_453758 : Nat := 118140960795 + 453758 * 2 ^ 59
def prefixEnd_453758 : Nat := 4983230072969 + 3 ^ 40 * 453758 * 2
def baseEnd_453758 : Nat := 207107515398169691945077

theorem tailTrace_453758 : CollatzResearch.WordTrace tailWord_453758 prefixEnd_453758 207107515398169691945077 := by
  unfold tailWord_453758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068739236264967067720241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11033275926746491027841285 2068739236264967067720241)
  ·
    refine ⟨1551554427198725300790181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2068739236264967067720241 1551554427198725300790181)
    ·
      refine ⟨290916455099760993898159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1551554427198725300790181 290916455099760993898159)
      ·
        refine ⟨436374682649641490847239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290916455099760993898159 436374682649641490847239)
        ·
          refine ⟨654562023974462236270859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436374682649641490847239 654562023974462236270859)
          ·
            refine ⟨981843035961693354406289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654562023974462236270859 981843035961693354406289)
            ·
              refine ⟨736382276971270015804717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981843035961693354406289 736382276971270015804717)
              ·
                refine ⟨276143353864226255926769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736382276971270015804717 276143353864226255926769)
                ·
                  refine ⟨207107515398169691945077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276143353864226255926769 207107515398169691945077)
                  ·
                    rfl

theorem cell20_453758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_453758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453758 prefixEnd_453758 := by exact prefixLift 453758
  have htrace : WordTrace (prefixWord ++ tailWord_453758) baseStart_453758 baseEnd_453758 := by
    simpa [prefixWord, tailWord_453758, baseEnd_453758] using wordTrace_append hprefix tailTrace_453758
  have hstable : (prefixWord ++ tailWord_453758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453758).length < 2 ^ (prefixWord ++ tailWord_453758).sum := by decide
  have hdescent : baseEnd_453758 < baseStart_453758 := by decide
  rcases family_descends (prefixWord ++ tailWord_453758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453763 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_453763 : Nat := 118140960795 + 453763 * 2 ^ 59
def prefixEnd_453763 : Nat := 4983230072969 + 3 ^ 40 * 453763 * 2
def baseEnd_453763 : Nat := 207109797534411896778389

theorem tailTrace_453763 : CollatzResearch.WordTrace tailWord_453763 prefixEnd_453763 207109797534411896778389 := by
  unfold tailWord_453763
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550096255101622395693943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11033397503401081597129295 16550096255101622395693943)
  ·
    refine ⟨24825144382652433593540915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16550096255101622395693943 24825144382652433593540915)
    ·
      refine ⟨37237716573978650390311373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825144382652433593540915 37237716573978650390311373)
      ·
        refine ⟨13964143715241993896366765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37237716573978650390311373 13964143715241993896366765)
        ·
          refine ⟨5236553893215747711137537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13964143715241993896366765 5236553893215747711137537)
          ·
            refine ⟨3927415419911810783353153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5236553893215747711137537 3927415419911810783353153)
            ·
              refine ⟨2945561564933858087514865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3927415419911810783353153 2945561564933858087514865)
              ·
                refine ⟨2209171173700393565636149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945561564933858087514865 2209171173700393565636149)
                ·
                  refine ⟨207109797534411896778389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209171173700393565636149 207109797534411896778389)
                  ·
                    rfl

theorem cell20_453763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_453763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453763 prefixEnd_453763 := by exact prefixLift 453763
  have htrace : WordTrace (prefixWord ++ tailWord_453763) baseStart_453763 baseEnd_453763 := by
    simpa [prefixWord, tailWord_453763, baseEnd_453763] using wordTrace_append hprefix tailTrace_453763
  have hstable : (prefixWord ++ tailWord_453763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453763).length < 2 ^ (prefixWord ++ tailWord_453763).sum := by decide
  have hdescent : baseEnd_453763 < baseStart_453763 := by decide
  rcases family_descends (prefixWord ++ tailWord_453763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453797 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 3]
def baseStart_453797 : Nat := 118140960795 + 453797 * 2 ^ 59
def prefixEnd_453797 : Nat := 4983230072969 + 3 ^ 40 * 453797 * 2
def baseEnd_453797 : Nat := 207125316060858889644917

theorem tailTrace_453797 : CollatzResearch.WordTrace tailWord_453797 prefixEnd_453797 207125316060858889644917 := by
  unfold tailWord_453797
  simp only [CollatzResearch.WordTrace]
  refine ⟨16551336336978446202431645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11034224224652297468287763 16551336336978446202431645)
  ·
    refine ⟨6206751126366917325911867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16551336336978446202431645 6206751126366917325911867)
    ·
      refine ⟨9310126689550375988867801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206751126366917325911867 9310126689550375988867801)
      ·
        refine ⟨6982595017162781991650851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9310126689550375988867801 6982595017162781991650851)
        ·
          refine ⟨10473892525744172987476277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982595017162781991650851 10473892525744172987476277)
          ·
            refine ⟨981927424288516217575901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10473892525744172987476277 981927424288516217575901)
            ·
              refine ⟨368222784108193581590963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981927424288516217575901 368222784108193581590963)
              ·
                refine ⟨552334176162290372386445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368222784108193581590963 552334176162290372386445)
                ·
                  refine ⟨207125316060858889644917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552334176162290372386445 207125316060858889644917)
                  ·
                    rfl

theorem cell20_453797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_453797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453797 prefixEnd_453797 := by exact prefixLift 453797
  have htrace : WordTrace (prefixWord ++ tailWord_453797) baseStart_453797 baseEnd_453797 := by
    simpa [prefixWord, tailWord_453797, baseEnd_453797] using wordTrace_append hprefix tailTrace_453797
  have hstable : (prefixWord ++ tailWord_453797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453797).length < 2 ^ (prefixWord ++ tailWord_453797).sum := by decide
  have hdescent : baseEnd_453797 < baseStart_453797 := by decide
  rcases family_descends (prefixWord ++ tailWord_453797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453828 : List Nat := [2, 3, 3, 1, 4, 1, 6]
def baseStart_453828 : Nat := 118140960795 + 453828 * 2 ^ 59
def prefixEnd_453828 : Nat := 4983230072969 + 3 ^ 40 * 453828 * 2
def baseEnd_453828 : Nat := 23015496145062284401273

theorem tailTrace_453828 : CollatzResearch.WordTrace tailWord_453828 prefixEnd_453828 23015496145062284401273 := by
  unfold tailWord_453828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276233499933069248405069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11034977999910758997873425 8276233499933069248405069)
  ·
    refine ⟨3103587562474900968151901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8276233499933069248405069 3103587562474900968151901)
    ·
      refine ⟨1163845335928087863056963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3103587562474900968151901 1163845335928087863056963)
      ·
        refine ⟨1745768003892131794585445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163845335928087863056963 1745768003892131794585445)
        ·
          refine ⟨327331500729774711484771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1745768003892131794585445 327331500729774711484771)
          ·
            refine ⟨490997251094662067227157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327331500729774711484771 490997251094662067227157)
            ·
              refine ⟨23015496145062284401273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 490997251094662067227157 23015496145062284401273)
              ·
                rfl

theorem cell20_453828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 6].length) (baseStart_453828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453828 prefixEnd_453828 := by exact prefixLift 453828
  have htrace : WordTrace (prefixWord ++ tailWord_453828) baseStart_453828 baseEnd_453828 := by
    simpa [prefixWord, tailWord_453828, baseEnd_453828] using wordTrace_append hprefix tailTrace_453828
  have hstable : (prefixWord ++ tailWord_453828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453828).length < 2 ^ (prefixWord ++ tailWord_453828).sum := by decide
  have hdescent : baseEnd_453828 < baseStart_453828 := by decide
  rcases family_descends (prefixWord ++ tailWord_453828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453838 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_453838 : Nat := 118140960795 + 453838 * 2 ^ 59
def prefixEnd_453838 : Nat := 4983230072969 + 3 ^ 40 * 453838 * 2
def baseEnd_453838 : Nat := 207144029578044969278083

theorem tailTrace_453838 : CollatzResearch.WordTrace tailWord_453838 prefixEnd_453838 207144029578044969278083 := by
  unfold tailWord_453838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069103966228738775584271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11035221153219940136449445 2069103966228738775584271)
  ·
    refine ⟨3103655949343108163376407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069103966228738775584271 3103655949343108163376407)
    ·
      refine ⟨4655483924014662245064611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103655949343108163376407 4655483924014662245064611)
      ·
        refine ⟨6983225886021993367596917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655483924014662245064611 6983225886021993367596917)
        ·
          refine ⟨654677426814561878212211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6983225886021993367596917 654677426814561878212211)
          ·
            refine ⟨982016140221842817318317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654677426814561878212211 982016140221842817318317)
            ·
              refine ⟨368256052583191056494369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 982016140221842817318317 368256052583191056494369)
              ·
                refine ⟨276192039437393292370777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368256052583191056494369 276192039437393292370777)
                ·
                  refine ⟨207144029578044969278083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276192039437393292370777 207144029578044969278083)
                  ·
                    rfl

theorem cell20_453838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_453838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453838 prefixEnd_453838 := by exact prefixLift 453838
  have htrace : WordTrace (prefixWord ++ tailWord_453838) baseStart_453838 baseEnd_453838 := by
    simpa [prefixWord, tailWord_453838, baseEnd_453838] using wordTrace_append hprefix tailTrace_453838
  have hstable : (prefixWord ++ tailWord_453838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453838).length < 2 ^ (prefixWord ++ tailWord_453838).sum := by decide
  have hdescent : baseEnd_453838 < baseStart_453838 := by decide
  rcases family_descends (prefixWord ++ tailWord_453838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453856 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_453856 : Nat := 118140960795 + 453856 * 2 ^ 59
def prefixEnd_453856 : Nat := 4983230072969 + 3 ^ 40 * 453856 * 2
def baseEnd_453856 : Nat := 207152245268516906678009

theorem tailTrace_453856 : CollatzResearch.WordTrace tailWord_453856 prefixEnd_453856 207152245268516906678009 := by
  unfold tailWord_453856
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276744121882349639414711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11035658829176466185886281 8276744121882349639414711)
  ·
    refine ⟨12415116182823524459122067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8276744121882349639414711 12415116182823524459122067)
    ·
      refine ⟨18622674274235286688683101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12415116182823524459122067 18622674274235286688683101)
      ·
        refine ⟨6983502852838232508256163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18622674274235286688683101 6983502852838232508256163)
        ·
          refine ⟨10475254279257348762384245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6983502852838232508256163 10475254279257348762384245)
          ·
            refine ⟨982055088680376446473523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10475254279257348762384245 982055088680376446473523)
            ·
              refine ⟨1473082633020564669710285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982055088680376446473523 1473082633020564669710285)
              ·
                refine ⟨552405987382711751141357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1473082633020564669710285 552405987382711751141357)
                ·
                  refine ⟨207152245268516906678009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552405987382711751141357 207152245268516906678009)
                  ·
                    rfl

theorem cell20_453856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_453856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453856 prefixEnd_453856 := by exact prefixLift 453856
  have htrace : WordTrace (prefixWord ++ tailWord_453856) baseStart_453856 baseEnd_453856 := by
    simpa [prefixWord, tailWord_453856, baseEnd_453856] using wordTrace_append hprefix tailTrace_453856
  have hstable : (prefixWord ++ tailWord_453856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453856).length < 2 ^ (prefixWord ++ tailWord_453856).sum := by decide
  have hdescent : baseEnd_453856 < baseStart_453856 := by decide
  rcases family_descends (prefixWord ++ tailWord_453856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453870 : List Nat := [4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_453870 : Nat := 118140960795 + 453870 * 2 ^ 59
def prefixEnd_453870 : Nat := 4983230072969 + 3 ^ 40 * 453870 * 2
def baseEnd_453870 : Nat := 69052878416665026737095

theorem tailTrace_453870 : CollatzResearch.WordTrace tailWord_453870 prefixEnd_453870 69052878416665026737095 := by
  unfold tailWord_453870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069249858214247458729883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11035999243809319779892709 2069249858214247458729883)
  ·
    refine ⟨3103874787321371188094825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069249858214247458729883 3103874787321371188094825)
    ·
      refine ⟨2327906090491028391071119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3103874787321371188094825 2327906090491028391071119)
      ·
        refine ⟨3491859135736542586606679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327906090491028391071119 3491859135736542586606679)
        ·
          refine ⟨5237788703604813879910019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491859135736542586606679 5237788703604813879910019)
          ·
            refine ⟨7856683055407220819865029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237788703604813879910019 7856683055407220819865029)
            ·
              refine ⟨1473128072888853903724693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7856683055407220819865029 1473128072888853903724693)
              ·
                refine ⟨69052878416665026737095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1473128072888853903724693 69052878416665026737095)
                ·
                  rfl

theorem cell20_453870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_453870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453870 prefixEnd_453870 := by exact prefixLift 453870
  have htrace : WordTrace (prefixWord ++ tailWord_453870) baseStart_453870 baseEnd_453870 := by
    simpa [prefixWord, tailWord_453870, baseEnd_453870] using wordTrace_append hprefix tailTrace_453870
  have hstable : (prefixWord ++ tailWord_453870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453870).length < 2 ^ (prefixWord ++ tailWord_453870).sum := by decide
  have hdescent : baseEnd_453870 < baseStart_453870 := by decide
  rcases family_descends (prefixWord ++ tailWord_453870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453890 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_453890 : Nat := 118140960795 + 453890 * 2 ^ 59
def prefixEnd_453890 : Nat := 4983230072969 + 3 ^ 40 * 453890 * 2
def baseEnd_453890 : Nat := 207167763794963899544537

theorem tailTrace_453890 : CollatzResearch.WordTrace tailWord_453890 prefixEnd_453890 207167763794963899544537 := by
  unfold tailWord_453890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138682081410380771391781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11036485550427682057044749 4138682081410380771391781)
  ·
    refine ⟨776002890264446394635959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4138682081410380771391781 776002890264446394635959)
    ·
      refine ⟨1164004335396669591953939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776002890264446394635959 1164004335396669591953939)
      ·
        refine ⟨1746006503095004387930909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164004335396669591953939 1746006503095004387930909)
        ·
          refine ⟨654752438660626645474091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1746006503095004387930909 654752438660626645474091)
          ·
            refine ⟨982128657990939968211137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654752438660626645474091 982128657990939968211137)
            ·
              refine ⟨736596493493204976158353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982128657990939968211137 736596493493204976158353)
              ·
                refine ⟨552447370119903732118765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736596493493204976158353 552447370119903732118765)
                ·
                  refine ⟨207167763794963899544537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552447370119903732118765 207167763794963899544537)
                  ·
                    rfl

theorem cell20_453890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_453890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453890 prefixEnd_453890 := by exact prefixLift 453890
  have htrace : WordTrace (prefixWord ++ tailWord_453890) baseStart_453890 baseEnd_453890 := by
    simpa [prefixWord, tailWord_453890, baseEnd_453890] using wordTrace_append hprefix tailTrace_453890
  have hstable : (prefixWord ++ tailWord_453890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453890).length < 2 ^ (prefixWord ++ tailWord_453890).sum := by decide
  have hdescent : baseEnd_453890 < baseStart_453890 := by decide
  rcases family_descends (prefixWord ++ tailWord_453890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453891 : List Nat := [1, 1, 1, 3, 2, 12]
def baseStart_453891 : Nat := 118140960795 + 453891 * 2 ^ 59
def prefixEnd_453891 : Nat := 4983230072969 + 3 ^ 40 * 453891 * 2
def baseEnd_453891 : Nat := 7672897045267123722637

theorem tailTrace_453891 : CollatzResearch.WordTrace tailWord_453891 prefixEnd_453891 7672897045267123722637 := by
  unfold tailWord_453891
  simp only [CollatzResearch.WordTrace]
  refine ⟨16554764798637900256353527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11036509865758600170902351 16554764798637900256353527)
  ·
    refine ⟨24832147197956850384530291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16554764798637900256353527 24832147197956850384530291)
    ·
      refine ⟨37248220796935275576795437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24832147197956850384530291 37248220796935275576795437)
      ·
        refine ⟨13968082798850728341298289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37248220796935275576795437 13968082798850728341298289)
        ·
          refine ⟨10476062099138046255973717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13968082798850728341298289 10476062099138046255973717)
          ·
            refine ⟨7672897045267123722637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10476062099138046255973717 7672897045267123722637)
            ·
              rfl

theorem cell20_453891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 12].length) (baseStart_453891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453891 prefixEnd_453891 := by exact prefixLift 453891
  have htrace : WordTrace (prefixWord ++ tailWord_453891) baseStart_453891 baseEnd_453891 := by
    simpa [prefixWord, tailWord_453891, baseEnd_453891] using wordTrace_append hprefix tailTrace_453891
  have hstable : (prefixWord ++ tailWord_453891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453891).length < 2 ^ (prefixWord ++ tailWord_453891).sum := by decide
  have hdescent : baseEnd_453891 < baseStart_453891 := by decide
  rcases family_descends (prefixWord ++ tailWord_453891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453925 : List Nat := [1, 3, 1, 2, 4, 2, 3, 4]
def baseStart_453925 : Nat := 118140960795 + 453925 * 2 ^ 59
def prefixEnd_453925 : Nat := 4983230072969 + 3 ^ 40 * 453925 * 2
def baseEnd_453925 : Nat := 69061246249553111125909

theorem tailTrace_453925 : CollatzResearch.WordTrace tailWord_453925 prefixEnd_453925 69061246249553111125909 := by
  unfold tailWord_453925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556004880514724063091229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037336587009816042060819 16556004880514724063091229)
  ·
    refine ⟨6208501830193021523659211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16556004880514724063091229 6208501830193021523659211)
    ·
      refine ⟨9312752745289532285488817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6208501830193021523659211 9312752745289532285488817)
      ·
        refine ⟨6984564558967149214116613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9312752745289532285488817 6984564558967149214116613)
        ·
          refine ⟨1309605854806340477646865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6984564558967149214116613 1309605854806340477646865)
          ·
            refine ⟨982204391104755358235149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309605854806340477646865 982204391104755358235149)
            ·
              refine ⟨368326646664283259338181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 982204391104755358235149 368326646664283259338181)
              ·
                refine ⟨69061246249553111125909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368326646664283259338181 69061246249553111125909)
                ·
                  rfl

theorem cell20_453925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_453925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453925 prefixEnd_453925 := by exact prefixLift 453925
  have htrace : WordTrace (prefixWord ++ tailWord_453925) baseStart_453925 baseEnd_453925 := by
    simpa [prefixWord, tailWord_453925, baseEnd_453925] using wordTrace_append hprefix tailTrace_453925
  have hstable : (prefixWord ++ tailWord_453925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453925).length < 2 ^ (prefixWord ++ tailWord_453925).sum := by decide
  have hdescent : baseEnd_453925 < baseStart_453925 := by decide
  rcases family_descends (prefixWord ++ tailWord_453925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453942 : List Nat := [5, 1, 2, 3, 1, 1, 7]
def baseStart_453942 : Nat := 118140960795 + 453942 * 2 ^ 59
def prefixEnd_453942 : Nat := 4983230072969 + 3 ^ 40 * 453942 * 2
def baseEnd_453942 : Nat := 23021277556875869978999

theorem tailTrace_453942 : CollatzResearch.WordTrace tailWord_453942 prefixEnd_453942 23021277556875869978999 := by
  unfold tailWord_453942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034789057590820997903755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11037749947635423977640053 1034789057590820997903755)
  ·
    refine ⟨1552183586386231496855633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034789057590820997903755 1552183586386231496855633)
    ·
      refine ⟨1164137689789673622641725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552183586386231496855633 1164137689789673622641725)
      ·
        refine ⟨436551633671127608490647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1164137689789673622641725 436551633671127608490647)
        ·
          refine ⟨654827450506691412735971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436551633671127608490647 654827450506691412735971)
          ·
            refine ⟨982241175760037119103957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654827450506691412735971 982241175760037119103957)
            ·
              refine ⟨23021277556875869978999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 982241175760037119103957 23021277556875869978999)
              ·
                rfl

theorem cell20_453942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 7].length) (baseStart_453942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453942 prefixEnd_453942 := by exact prefixLift 453942
  have htrace : WordTrace (prefixWord ++ tailWord_453942) baseStart_453942 baseEnd_453942 := by
    simpa [prefixWord, tailWord_453942, baseEnd_453942] using wordTrace_append hprefix tailTrace_453942
  have hstable : (prefixWord ++ tailWord_453942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453942).length < 2 ^ (prefixWord ++ tailWord_453942).sum := by decide
  have hdescent : baseEnd_453942 < baseStart_453942 := by decide
  rcases family_descends (prefixWord ++ tailWord_453942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453949 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 5]
def baseStart_453949 : Nat := 118140960795 + 453949 * 2 ^ 59
def prefixEnd_453949 : Nat := 4983230072969 + 3 ^ 40 * 453949 * 2
def baseEnd_453949 : Nat := 207194693002621916577629

theorem tailTrace_453949 : CollatzResearch.WordTrace tailWord_453949 prefixEnd_453949 207194693002621916577629 := by
  unfold tailWord_453949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556880232427776161964901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037920154951850774643267 16556880232427776161964901)
  ·
    refine ⟨3104415043580208030368419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16556880232427776161964901 3104415043580208030368419)
    ·
      refine ⟨4656622565370312045552629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3104415043580208030368419 4656622565370312045552629)
      ·
        refine ⟨436558365503466754270559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4656622565370312045552629 436558365503466754270559)
        ·
          refine ⟨654837548255200131405839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436558365503466754270559 654837548255200131405839)
          ·
            refine ⟨982256322382800197108759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654837548255200131405839 982256322382800197108759)
            ·
              refine ⟨1473384483574200295663139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982256322382800197108759 1473384483574200295663139)
              ·
                refine ⟨2210076725361300443494709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473384483574200295663139 2210076725361300443494709)
                ·
                  refine ⟨207194693002621916577629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2210076725361300443494709 207194693002621916577629)
                  ·
                    rfl

theorem cell20_453949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_453949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453949 prefixEnd_453949 := by exact prefixLift 453949
  have htrace : WordTrace (prefixWord ++ tailWord_453949) baseStart_453949 baseEnd_453949 := by
    simpa [prefixWord, tailWord_453949, baseEnd_453949] using wordTrace_append hprefix tailTrace_453949
  have hstable : (prefixWord ++ tailWord_453949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453949).length < 2 ^ (prefixWord ++ tailWord_453949).sum := by decide
  have hdescent : baseEnd_453949 < baseStart_453949 := by decide
  rcases family_descends (prefixWord ++ tailWord_453949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453956 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_453956 : Nat := 118140960795 + 453956 * 2 ^ 59
def prefixEnd_453956 : Nat := 4983230072969 + 3 ^ 40 * 453956 * 2
def baseEnd_453956 : Nat := 207197887993361003344267

theorem tailTrace_453956 : CollatzResearch.WordTrace tailWord_453956 prefixEnd_453956 207197887993361003344267 := by
  unfold tailWord_453956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8278567771701208178734861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11038090362268277571646481 8278567771701208178734861)
  ·
    refine ⟨3104462914387953067025573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8278567771701208178734861 3104462914387953067025573)
    ·
      refine ⟨582086796447741200067295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3104462914387953067025573 582086796447741200067295)
      ·
        refine ⟨873130194671611800100943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582086796447741200067295 873130194671611800100943)
        ·
          refine ⟨1309695292007417700151415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873130194671611800100943 1309695292007417700151415)
          ·
            refine ⟨1964542938011126550227123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309695292007417700151415 1964542938011126550227123)
            ·
              refine ⟨2946814407016689825340685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964542938011126550227123 2946814407016689825340685)
              ·
                refine ⟨1105055402631258684502757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946814407016689825340685 1105055402631258684502757)
                ·
                  refine ⟨207197887993361003344267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105055402631258684502757 207197887993361003344267)
                  ·
                    rfl

theorem cell20_453956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_453956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453956 prefixEnd_453956 := by exact prefixLift 453956
  have htrace : WordTrace (prefixWord ++ tailWord_453956) baseStart_453956 baseEnd_453956 := by
    simpa [prefixWord, tailWord_453956, baseEnd_453956] using wordTrace_append hprefix tailTrace_453956
  have hstable : (prefixWord ++ tailWord_453956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453956).length < 2 ^ (prefixWord ++ tailWord_453956).sum := by decide
  have hdescent : baseEnd_453956 < baseStart_453956 := by decide
  rcases family_descends (prefixWord ++ tailWord_453956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453984 : List Nat := [2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_453984 : Nat := 118140960795 + 453984 * 2 ^ 59
def prefixEnd_453984 : Nat := 4983230072969 + 3 ^ 40 * 453984 * 2
def baseEnd_453984 : Nat := 69070222652105783470273

theorem tailTrace_453984 : CollatzResearch.WordTrace tailWord_453984 prefixEnd_453984 69070222652105783470273 := by
  unfold tailWord_453984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279078393650488569744503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11038771191533984759659337 8279078393650488569744503)
  ·
    refine ⟨12418617590475732854616755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8279078393650488569744503 12418617590475732854616755)
    ·
      refine ⟨18627926385713599281925133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12418617590475732854616755 18627926385713599281925133)
      ·
        refine ⟨6985472394642599730721925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18627926385713599281925133 6985472394642599730721925)
        ·
          refine ⟨1309776073995487449510361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6985472394642599730721925 1309776073995487449510361)
          ·
            refine ⟨982332055496615587132771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309776073995487449510361 982332055496615587132771)
            ·
              refine ⟨1473498083244923380699157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982332055496615587132771 1473498083244923380699157)
              ·
                refine ⟨69070222652105783470273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1473498083244923380699157 69070222652105783470273)
                ·
                  rfl

theorem cell20_453984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_453984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_453984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_453984 prefixEnd_453984 := by exact prefixLift 453984
  have htrace : WordTrace (prefixWord ++ tailWord_453984) baseStart_453984 baseEnd_453984 := by
    simpa [prefixWord, tailWord_453984, baseEnd_453984] using wordTrace_append hprefix tailTrace_453984
  have hstable : (prefixWord ++ tailWord_453984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453984).length < 2 ^ (prefixWord ++ tailWord_453984).sum := by decide
  have hdescent : baseEnd_453984 < baseStart_453984 := by decide
  rcases family_descends (prefixWord ++ tailWord_453984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454018 : List Nat := [3, 4, 2, 1, 1, 2, 2, 5]
def baseStart_454018 : Nat := 118140960795 + 454018 * 2 ^ 59
def prefixEnd_454018 : Nat := 4983230072969 + 3 ^ 40 * 454018 * 2
def baseEnd_454018 : Nat := 69075395494254781092449

theorem tailTrace_454018 : CollatzResearch.WordTrace tailWord_454018 prefixEnd_454018 69075395494254781092449 := by
  unfold tailWord_454018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139849217294450236556677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11039597912785200630817805 4139849217294450236556677)
  ·
    refine ⟨776221728242709419354377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4139849217294450236556677 776221728242709419354377)
    ·
      refine ⟨582166296182032064515783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776221728242709419354377 582166296182032064515783)
      ·
        refine ⟨873249444273048096773675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582166296182032064515783 873249444273048096773675)
        ·
          refine ⟨1309874166409572145160513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873249444273048096773675 1309874166409572145160513)
          ·
            refine ⟨982405624807179108870385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309874166409572145160513 982405624807179108870385)
            ·
              refine ⟨736804218605384331652789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982405624807179108870385 736804218605384331652789)
              ·
                refine ⟨69075395494254781092449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 736804218605384331652789 69075395494254781092449)
                ·
                  rfl

theorem cell20_454018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_454018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454018 prefixEnd_454018 := by exact prefixLift 454018
  have htrace : WordTrace (prefixWord ++ tailWord_454018) baseStart_454018 baseEnd_454018 := by
    simpa [prefixWord, tailWord_454018, baseEnd_454018] using wordTrace_append hprefix tailTrace_454018
  have hstable : (prefixWord ++ tailWord_454018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454018).length < 2 ^ (prefixWord ++ tailWord_454018).sum := by decide
  have hdescent : baseEnd_454018 < baseStart_454018 := by decide
  rcases family_descends (prefixWord ++ tailWord_454018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454122 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_454122 : Nat := 118140960795 + 454122 * 2 ^ 59
def prefixEnd_454122 : Nat := 4983230072969 + 3 ^ 40 * 454122 * 2
def baseEnd_454122 : Nat := 207273654916602203810255

theorem tailTrace_454122 : CollatzResearch.WordTrace tailWord_454122 prefixEnd_454122 207273654916602203810255 := by
  unfold tailWord_454122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140797515200256677003155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11042126707200684472008413 4140797515200256677003155)
  ·
    refine ⟨6211196272800385015504733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4140797515200256677003155 6211196272800385015504733)
    ·
      refine ⟨2329198602300144380814275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6211196272800385015504733 2329198602300144380814275)
      ·
        refine ⟨3493797903450216571221413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2329198602300144380814275 3493797903450216571221413)
        ·
          refine ⟨655087106896915607104015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3493797903450216571221413 655087106896915607104015)
          ·
            refine ⟨982630660345373410656023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655087106896915607104015 982630660345373410656023)
            ·
              refine ⟨1473945990518060115984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982630660345373410656023 1473945990518060115984035)
              ·
                refine ⟨2210918985777090173976053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473945990518060115984035 2210918985777090173976053)
                ·
                  refine ⟨207273654916602203810255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2210918985777090173976053 207273654916602203810255)
                  ·
                    rfl

theorem cell20_454122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_454122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454122 prefixEnd_454122 := by exact prefixLift 454122
  have htrace : WordTrace (prefixWord ++ tailWord_454122) baseStart_454122 baseEnd_454122 := by
    simpa [prefixWord, tailWord_454122, baseEnd_454122] using wordTrace_append hprefix tailTrace_454122
  have hstable : (prefixWord ++ tailWord_454122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454122).length < 2 ^ (prefixWord ++ tailWord_454122).sum := by decide
  have hdescent : baseEnd_454122 < baseStart_454122 := by decide
  rcases family_descends (prefixWord ++ tailWord_454122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454129 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_454129 : Nat := 118140960795 + 454129 * 2 ^ 59
def prefixEnd_454129 : Nat := 4983230072969 + 3 ^ 40 * 454129 * 2
def baseEnd_454129 : Nat := 207276849907341290576893

theorem tailTrace_454129 : CollatzResearch.WordTrace tailWord_454129 prefixEnd_454129 207276849907341290576893 := by
  unfold tailWord_454129
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563445371775666903517441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11042296914517111269011627 16563445371775666903517441)
  ·
    refine ⟨12422584028831750177638081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16563445371775666903517441 12422584028831750177638081)
    ·
      refine ⟨9316938021623812633228561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12422584028831750177638081 9316938021623812633228561)
      ·
        refine ⟨6987703516217859474921421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9316938021623812633228561 6987703516217859474921421)
        ·
          refine ⟨2620388818581697303095533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6987703516217859474921421 2620388818581697303095533)
          ·
            refine ⟨982645806968136488660825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2620388818581697303095533 982645806968136488660825)
            ·
              refine ⟨736984355226102366495619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982645806968136488660825 736984355226102366495619)
              ·
                refine ⟨1105476532839153549743429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736984355226102366495619 1105476532839153549743429)
                ·
                  refine ⟨207276849907341290576893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105476532839153549743429 207276849907341290576893)
                  ·
                    rfl

theorem cell20_454129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_454129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454129 prefixEnd_454129 := by exact prefixLift 454129
  have htrace : WordTrace (prefixWord ++ tailWord_454129) baseStart_454129 baseEnd_454129 := by
    simpa [prefixWord, tailWord_454129, baseEnd_454129] using wordTrace_append hprefix tailTrace_454129
  have hstable : (prefixWord ++ tailWord_454129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454129).length < 2 ^ (prefixWord ++ tailWord_454129).sum := by decide
  have hdescent : baseEnd_454129 < baseStart_454129 := by decide
  rcases family_descends (prefixWord ++ tailWord_454129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454146 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_454146 : Nat := 118140960795 + 454146 * 2 ^ 59
def prefixEnd_454146 : Nat := 4983230072969 + 3 ^ 40 * 454146 * 2
def baseEnd_454146 : Nat := 207284609170564787010157

theorem tailTrace_454146 : CollatzResearch.WordTrace tailWord_454146 prefixEnd_454146 207284609170564787010157 := by
  unfold tailWord_454146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4141016353178519701721573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11042710275142719204590861 4141016353178519701721573)
  ·
    refine ⟨776440566220972444072795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4141016353178519701721573 776440566220972444072795)
    ·
      refine ⟨1164660849331458666109193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776440566220972444072795 1164660849331458666109193)
      ·
        refine ⟨873495636998593999581895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1164660849331458666109193 873495636998593999581895)
        ·
          refine ⟨1310243455497890999372843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873495636998593999581895 1310243455497890999372843)
          ·
            refine ⟨1965365183246836499059265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310243455497890999372843 1965365183246836499059265)
            ·
              refine ⟨1474023887435127374294449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965365183246836499059265 1474023887435127374294449)
              ·
                refine ⟨1105517915576345530720837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474023887435127374294449 1105517915576345530720837)
                ·
                  refine ⟨207284609170564787010157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105517915576345530720837 207284609170564787010157)
                  ·
                    rfl

theorem cell20_454146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_454146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454146 prefixEnd_454146 := by exact prefixLift 454146
  have htrace : WordTrace (prefixWord ++ tailWord_454146) baseStart_454146 baseEnd_454146 := by
    simpa [prefixWord, tailWord_454146, baseEnd_454146] using wordTrace_append hprefix tailTrace_454146
  have hstable : (prefixWord ++ tailWord_454146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454146).length < 2 ^ (prefixWord ++ tailWord_454146).sum := by decide
  have hdescent : baseEnd_454146 < baseStart_454146 := by decide
  rcases family_descends (prefixWord ++ tailWord_454146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454181 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_454181 : Nat := 118140960795 + 454181 * 2 ^ 59
def prefixEnd_454181 : Nat := 4983230072969 + 3 ^ 40 * 454181 * 2
def baseEnd_454181 : Nat := 207300584124260220843347

theorem tailTrace_454181 : CollatzResearch.WordTrace tailWord_454181 prefixEnd_454181 207300584124260220843347 := by
  unfold tailWord_454181
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565341967587279784410397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11043561311724853189606931 16565341967587279784410397)
  ·
    refine ⟨6212003237845229919153899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16565341967587279784410397 6212003237845229919153899)
    ·
      refine ⟨9318004856767844878730849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6212003237845229919153899 9318004856767844878730849)
      ·
        refine ⟨6988503642575883659048137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9318004856767844878730849 6988503642575883659048137)
        ·
          refine ⟨5241377731931912744286103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6988503642575883659048137 5241377731931912744286103)
          ·
            refine ⟨7862066597897869116429155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241377731931912744286103 7862066597897869116429155)
            ·
              refine ⟨11793099896846803674643733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7862066597897869116429155 11793099896846803674643733)
              ·
                refine ⟨552801557664693922248925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11793099896846803674643733 552801557664693922248925)
                ·
                  refine ⟨207300584124260220843347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552801557664693922248925 207300584124260220843347)
                  ·
                    rfl

theorem cell20_454181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_454181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454181 prefixEnd_454181 := by exact prefixLift 454181
  have htrace : WordTrace (prefixWord ++ tailWord_454181) baseStart_454181 baseEnd_454181 := by
    simpa [prefixWord, tailWord_454181, baseEnd_454181] using wordTrace_append hprefix tailTrace_454181
  have hstable : (prefixWord ++ tailWord_454181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454181).length < 2 ^ (prefixWord ++ tailWord_454181).sum := by decide
  have hdescent : baseEnd_454181 < baseStart_454181 := by decide
  rcases family_descends (prefixWord ++ tailWord_454181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454195 : List Nat := [1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_454195 : Nat := 118140960795 + 454195 * 2 ^ 59
def prefixEnd_454195 : Nat := 4983230072969 + 3 ^ 40 * 454195 * 2
def baseEnd_454195 : Nat := 69102324701912798125541

theorem tailTrace_454195 : CollatzResearch.WordTrace tailWord_454195 prefixEnd_454195 69102324701912798125541 := by
  unfold tailWord_454195
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565852589536560175420039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11043901726357706783613359 16565852589536560175420039)
  ·
    refine ⟨24848778884304840263130059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16565852589536560175420039 24848778884304840263130059)
    ·
      refine ⟨37273168326457260394695089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24848778884304840263130059 37273168326457260394695089)
      ·
        refine ⟨27954876244842945296021317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37273168326457260394695089 27954876244842945296021317)
        ·
          refine ⟨5241539295908052243003997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27954876244842945296021317 5241539295908052243003997)
          ·
            refine ⟨1965577235965519591126499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5241539295908052243003997 1965577235965519591126499)
            ·
              refine ⟨2948365853948279386689749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965577235965519591126499 2948365853948279386689749)
              ·
                refine ⟨69102324701912798125541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2948365853948279386689749 69102324701912798125541)
                ·
                  rfl

theorem cell20_454195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_454195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454195 prefixEnd_454195 := by exact prefixLift 454195
  have htrace : WordTrace (prefixWord ++ tailWord_454195) baseStart_454195 baseEnd_454195 := by
    simpa [prefixWord, tailWord_454195, baseEnd_454195] using wordTrace_append hprefix tailTrace_454195
  have hstable : (prefixWord ++ tailWord_454195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454195).length < 2 ^ (prefixWord ++ tailWord_454195).sum := by decide
  have hdescent : baseEnd_454195 < baseStart_454195 := by decide
  rcases family_descends (prefixWord ++ tailWord_454195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454236 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_454236 : Nat := 118140960795 + 454236 * 2 ^ 59
def prefixEnd_454236 : Nat := 4983230072969 + 3 ^ 40 * 454236 * 2
def baseEnd_454236 : Nat := 207325687622924474009789

theorem tailTrace_454236 : CollatzResearch.WordTrace tailWord_454236 prefixEnd_454236 207325687622924474009789 := by
  unfold tailWord_454236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283673991194012088831281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11044898654925349451775041 8283673991194012088831281)
  ·
    refine ⟨6212755493395509066623461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8283673991194012088831281 6212755493395509066623461)
    ·
      refine ⟨1164891655011657949991899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6212755493395509066623461 1164891655011657949991899)
      ·
        refine ⟨1747337482517486924987849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164891655011657949991899 1747337482517486924987849)
        ·
          refine ⟨1310503111888115193740887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1747337482517486924987849 1310503111888115193740887)
          ·
            refine ⟨1965754667832172790611331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310503111888115193740887 1965754667832172790611331)
            ·
              refine ⟨2948632001748259185916997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965754667832172790611331 2948632001748259185916997)
              ·
                refine ⟨552868500327798597359437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2948632001748259185916997 552868500327798597359437)
                ·
                  refine ⟨207325687622924474009789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552868500327798597359437 207325687622924474009789)
                  ·
                    rfl

theorem cell20_454236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_454236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454236 prefixEnd_454236 := by exact prefixLift 454236
  have htrace : WordTrace (prefixWord ++ tailWord_454236) baseStart_454236 baseEnd_454236 := by
    simpa [prefixWord, tailWord_454236, baseEnd_454236] using wordTrace_append hprefix tailTrace_454236
  have hstable : (prefixWord ++ tailWord_454236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454236).length < 2 ^ (prefixWord ++ tailWord_454236).sum := by decide
  have hdescent : baseEnd_454236 < baseStart_454236 := by decide
  rcases family_descends (prefixWord ++ tailWord_454236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454250 : List Nat := [3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_454250 : Nat := 118140960795 + 454250 * 2 ^ 59
def prefixEnd_454250 : Nat := 4983230072969 + 3 ^ 40 * 454250 * 2
def baseEnd_454250 : Nat := 69110692534800882514355

theorem tailTrace_454250 : CollatzResearch.WordTrace tailWord_454250 prefixEnd_454250 69110692534800882514355 := by
  unfold tailWord_454250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4141964651084326142168051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11045239069558203045781469 4141964651084326142168051)
  ·
    refine ⟨6212946976626489213252077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4141964651084326142168051 6212946976626489213252077)
    ·
      refine ⟨2329855116234933454969529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6212946976626489213252077 2329855116234933454969529)
      ·
        refine ⟨1747391337176200091227147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2329855116234933454969529 1747391337176200091227147)
        ·
          refine ⟨2621087005764300136840721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747391337176200091227147 2621087005764300136840721)
          ·
            refine ⟨1965815254323225102630541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2621087005764300136840721 1965815254323225102630541)
            ·
              refine ⟨737180720371209413486453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1965815254323225102630541 737180720371209413486453)
              ·
                refine ⟨69110692534800882514355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 737180720371209413486453 69110692534800882514355)
                ·
                  rfl

theorem cell20_454250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_454250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454250 prefixEnd_454250 := by exact prefixLift 454250
  have htrace : WordTrace (prefixWord ++ tailWord_454250) baseStart_454250 baseEnd_454250 := by
    simpa [prefixWord, tailWord_454250, baseEnd_454250] using wordTrace_append hprefix tailTrace_454250
  have hstable : (prefixWord ++ tailWord_454250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454250).length < 2 ^ (prefixWord ++ tailWord_454250).sum := by decide
  have hdescent : baseEnd_454250 < baseStart_454250 := by decide
  rcases family_descends (prefixWord ++ tailWord_454250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454281 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 2]
def baseStart_454281 : Nat := 118140960795 + 454281 * 2 ^ 59
def prefixEnd_454281 : Nat := 4983230072969 + 3 ^ 40 * 454281 * 2
def baseEnd_454281 : Nat := 207346226849104317509605

theorem tailTrace_454281 : CollatzResearch.WordTrace tailWord_454281 prefixEnd_454281 207346226849104317509605 := by
  unfold tailWord_454281
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568989267224996863050697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11045992844816664575367131 16568989267224996863050697)
  ·
    refine ⟨12426741950418747647288023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16568989267224996863050697 12426741950418747647288023)
    ·
      refine ⟨18640112925628121470932035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12426741950418747647288023 18640112925628121470932035)
      ·
        refine ⟨27960169388442182206398053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18640112925628121470932035 27960169388442182206398053)
        ·
          refine ⟨5242531760332909163699635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27960169388442182206398053 5242531760332909163699635)
          ·
            refine ⟨7863797640499363745549453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242531760332909163699635 7863797640499363745549453)
            ·
              refine ⟨2948924115187261404581045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7863797640499363745549453 2948924115187261404581045)
              ·
                refine ⟨276461635798805756679473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2948924115187261404581045 276461635798805756679473)
                ·
                  refine ⟨207346226849104317509605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276461635798805756679473 207346226849104317509605)
                  ·
                    rfl

theorem cell20_454281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_454281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454281 prefixEnd_454281 := by exact prefixLift 454281
  have htrace : WordTrace (prefixWord ++ tailWord_454281) baseStart_454281 baseEnd_454281 := by
    simpa [prefixWord, tailWord_454281, baseEnd_454281] using wordTrace_append hprefix tailTrace_454281
  have hstable : (prefixWord ++ tailWord_454281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454281).length < 2 ^ (prefixWord ++ tailWord_454281).sum := by decide
  have hdescent : baseEnd_454281 < baseStart_454281 := by decide
  rcases family_descends (prefixWord ++ tailWord_454281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454295 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_454295 : Nat := 118140960795 + 454295 * 2 ^ 59
def prefixEnd_454295 : Nat := 4983230072969 + 3 ^ 40 * 454295 * 2
def baseEnd_454295 : Nat := 207352616830582491042881

theorem tailTrace_454295 : CollatzResearch.WordTrace tailWord_454295 prefixEnd_454295 207352616830582491042881 := by
  unfold tailWord_454295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16569499889174277254060339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11046333259449518169373559 16569499889174277254060339)
  ·
    refine ⟨24854249833761415881090509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16569499889174277254060339 24854249833761415881090509)
    ·
      refine ⟨9320343687660530955408941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24854249833761415881090509 9320343687660530955408941)
      ·
        refine ⟨3495128882872699108278353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9320343687660530955408941 3495128882872699108278353)
        ·
          refine ⟨2621346662154524331208765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495128882872699108278353 2621346662154524331208765)
          ·
            refine ⟨983004998307946624203287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2621346662154524331208765 983004998307946624203287)
            ·
              refine ⟨1474507497461919936304931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983004998307946624203287 1474507497461919936304931)
              ·
                refine ⟨2211761246192879904457397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474507497461919936304931 2211761246192879904457397)
                ·
                  refine ⟨207352616830582491042881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2211761246192879904457397 207352616830582491042881)
                  ·
                    rfl

theorem cell20_454295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_454295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454295 prefixEnd_454295 := by exact prefixLift 454295
  have htrace : WordTrace (prefixWord ++ tailWord_454295) baseStart_454295 baseEnd_454295 := by
    simpa [prefixWord, tailWord_454295, baseEnd_454295] using wordTrace_append hprefix tailTrace_454295
  have hstable : (prefixWord ++ tailWord_454295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454295).length < 2 ^ (prefixWord ++ tailWord_454295).sum := by decide
  have hdescent : baseEnd_454295 < baseStart_454295 := by decide
  rcases family_descends (prefixWord ++ tailWord_454295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454378 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_454378 : Nat := 118140960795 + 454378 * 2 ^ 59
def prefixEnd_454378 : Nat := 4983230072969 + 3 ^ 40 * 454378 * 2
def baseEnd_454378 : Nat := 207390500292203091275875

theorem tailTrace_454378 : CollatzResearch.WordTrace tailWord_454378 prefixEnd_454378 207390500292203091275875 := by
  unfold tailWord_454378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143131786968395607332947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11048351431915721619554525 4143131786968395607332947)
  ·
    refine ⟨6214697680452593410999421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143131786968395607332947 6214697680452593410999421)
    ·
      refine ⟨2330511630169722529124783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6214697680452593410999421 2330511630169722529124783)
      ·
        refine ⟨3495767445254583793687175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330511630169722529124783 3495767445254583793687175)
        ·
          refine ⟨5243651167881875690530763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495767445254583793687175 5243651167881875690530763)
          ·
            refine ⟨7865476751822813535796145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243651167881875690530763 7865476751822813535796145)
            ·
              refine ⟨5899107563867110151847109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865476751822813535796145 5899107563867110151847109)
              ·
                refine ⟨1106082668225083153471333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5899107563867110151847109 1106082668225083153471333)
                ·
                  refine ⟨207390500292203091275875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106082668225083153471333 207390500292203091275875)
                  ·
                    rfl

theorem cell20_454378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_454378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454378 prefixEnd_454378 := by exact prefixLift 454378
  have htrace : WordTrace (prefixWord ++ tailWord_454378) baseStart_454378 baseEnd_454378 := by
    simpa [prefixWord, tailWord_454378, baseEnd_454378] using wordTrace_append hprefix tailTrace_454378
  have hstable : (prefixWord ++ tailWord_454378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454378).length < 2 ^ (prefixWord ++ tailWord_454378).sum := by decide
  have hdescent : baseEnd_454378 < baseStart_454378 := by decide
  rcases family_descends (prefixWord ++ tailWord_454378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454385 : List Nat := [1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_454385 : Nat := 118140960795 + 454385 * 2 ^ 59
def prefixEnd_454385 : Nat := 4983230072969 + 3 ^ 40 * 454385 * 2
def baseEnd_454385 : Nat := 69131231760980726014171

theorem tailTrace_454385 : CollatzResearch.WordTrace tailWord_454385 prefixEnd_454385 69131231760980726014171 := by
  unfold tailWord_454385
  simp only [CollatzResearch.WordTrace]
  refine ⟨16572782458848222624836609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11048521639232148416557739 16572782458848222624836609)
  ·
    refine ⟨12429586844136166968627457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16572782458848222624836609 12429586844136166968627457)
    ·
      refine ⟨9322190133102125226470593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12429586844136166968627457 9322190133102125226470593)
      ·
        refine ⟨6991642599826593919852945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9322190133102125226470593 6991642599826593919852945)
        ·
          refine ⟨5243731949869945439889709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6991642599826593919852945 5243731949869945439889709)
          ·
            refine ⟨1966399481201229539958641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5243731949869945439889709 1966399481201229539958641)
            ·
              refine ⟨1474799610900922154968981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966399481201229539958641 1474799610900922154968981)
              ·
                refine ⟨69131231760980726014171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1474799610900922154968981 69131231760980726014171)
                ·
                  rfl

theorem cell20_454385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_454385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454385 prefixEnd_454385 := by exact prefixLift 454385
  have htrace : WordTrace (prefixWord ++ tailWord_454385) baseStart_454385 baseEnd_454385 := by
    simpa [prefixWord, tailWord_454385, baseEnd_454385] using wordTrace_append hprefix tailTrace_454385
  have hstable : (prefixWord ++ tailWord_454385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454385).length < 2 ^ (prefixWord ++ tailWord_454385).sum := by decide
  have hdescent : baseEnd_454385 < baseStart_454385 := by decide
  rcases family_descends (prefixWord ++ tailWord_454385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454392 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_454392 : Nat := 118140960795 + 454392 * 2 ^ 59
def prefixEnd_454392 : Nat := 4983230072969 + 3 ^ 40 * 454392 * 2
def baseEnd_454392 : Nat := 207396890273681264809151

theorem tailTrace_454392 : CollatzResearch.WordTrace tailWord_454392 prefixEnd_454392 207396890273681264809151 := by
  unfold tailWord_454392
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286518884911431410170715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11048691846548575213560953 8286518884911431410170715)
  ·
    refine ⟨12429778327367147115256073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8286518884911431410170715 12429778327367147115256073)
    ·
      refine ⟨9322333745525360336442055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12429778327367147115256073 9322333745525360336442055)
      ·
        refine ⟨13983500618288040504663083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9322333745525360336442055 13983500618288040504663083)
        ·
          refine ⟨20975250927432060756994625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983500618288040504663083 20975250927432060756994625)
          ·
            refine ⟨15731438195574045567745969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20975250927432060756994625 15731438195574045567745969)
            ·
              refine ⟨11798578646680534175809477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15731438195574045567745969 11798578646680534175809477)
              ·
                refine ⟨2212233496252600157964277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11798578646680534175809477 2212233496252600157964277)
                ·
                  refine ⟨207396890273681264809151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2212233496252600157964277 207396890273681264809151)
                  ·
                    rfl

theorem cell20_454392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_454392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454392 prefixEnd_454392 := by exact prefixLift 454392
  have htrace : WordTrace (prefixWord ++ tailWord_454392) baseStart_454392 baseEnd_454392 := by
    simpa [prefixWord, tailWord_454392, baseEnd_454392] using wordTrace_append hprefix tailTrace_454392
  have hstable : (prefixWord ++ tailWord_454392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454392).length < 2 ^ (prefixWord ++ tailWord_454392).sum := by decide
  have hdescent : baseEnd_454392 < baseStart_454392 := by decide
  rcases family_descends (prefixWord ++ tailWord_454392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454412 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 2]
def baseStart_454412 : Nat := 118140960795 + 454412 * 2 ^ 59
def prefixEnd_454412 : Nat := 4983230072969 + 3 ^ 40 * 454412 * 2
def baseEnd_454412 : Nat := 207406018818650084142403

theorem tailTrace_454412 : CollatzResearch.WordTrace tailWord_454412 prefixEnd_454412 207406018818650084142403 := by
  unfold tailWord_454412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286883614875203118034745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11049178153166937490712993 8286883614875203118034745)
  ·
    refine ⟨6215162711156402338526059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8286883614875203118034745 6215162711156402338526059)
    ·
      refine ⟨9322744066734603507789089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215162711156402338526059 9322744066734603507789089)
      ·
        refine ⟨6992058050050952630841817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9322744066734603507789089 6992058050050952630841817)
        ·
          refine ⟨5244043537538214473131363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6992058050050952630841817 5244043537538214473131363)
          ·
            refine ⟨7866065306307321709697045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244043537538214473131363 7866065306307321709697045)
            ·
              refine ⟨368721811233155705142049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7866065306307321709697045 368721811233155705142049)
              ·
                refine ⟨276541358424866778856537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368721811233155705142049 276541358424866778856537)
                ·
                  refine ⟨207406018818650084142403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276541358424866778856537 207406018818650084142403)
                  ·
                    rfl

theorem cell20_454412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_454412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454412 prefixEnd_454412 := by exact prefixLift 454412
  have htrace : WordTrace (prefixWord ++ tailWord_454412) baseStart_454412 baseEnd_454412 := by
    simpa [prefixWord, tailWord_454412, baseEnd_454412] using wordTrace_append hprefix tailTrace_454412
  have hstable : (prefixWord ++ tailWord_454412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454412).length < 2 ^ (prefixWord ++ tailWord_454412).sum := by decide
  have hdescent : baseEnd_454412 < baseStart_454412 := by decide
  rcases family_descends (prefixWord ++ tailWord_454412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454450 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_454450 : Nat := 118140960795 + 454450 * 2 ^ 59
def prefixEnd_454450 : Nat := 4983230072969 + 3 ^ 40 * 454450 * 2
def baseEnd_454450 : Nat := 207423363054090840875581

theorem tailTrace_454450 : CollatzResearch.WordTrace tailWord_454450 prefixEnd_454450 207423363054090840875581 := by
  unfold tailWord_454450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143788300903184681488201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11050102135741825817301869 4143788300903184681488201)
  ·
    refine ⟨3107841225677388511116151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4143788300903184681488201 3107841225677388511116151)
    ·
      refine ⟨4661761838516082766674227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107841225677388511116151 4661761838516082766674227)
      ·
        refine ⟨6992642757774124150011341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661761838516082766674227 6992642757774124150011341)
        ·
          refine ⟨2622241034165296556254253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6992642757774124150011341 2622241034165296556254253)
          ·
            refine ⟨983340387811986208595345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2622241034165296556254253 983340387811986208595345)
            ·
              refine ⟨737505290858989656446509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983340387811986208595345 737505290858989656446509)
              ·
                refine ⟨276564484072121121167441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737505290858989656446509 276564484072121121167441)
                ·
                  refine ⟨207423363054090840875581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276564484072121121167441 207423363054090840875581)
                  ·
                    rfl

theorem cell20_454450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_454450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454450 prefixEnd_454450 := by exact prefixLift 454450
  have htrace : WordTrace (prefixWord ++ tailWord_454450) baseStart_454450 baseEnd_454450 := by
    simpa [prefixWord, tailWord_454450, baseEnd_454450] using wordTrace_append hprefix tailTrace_454450
  have hstable : (prefixWord ++ tailWord_454450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454450).length < 2 ^ (prefixWord ++ tailWord_454450).sum := by decide
  have hdescent : baseEnd_454450 < baseStart_454450 := by decide
  rcases family_descends (prefixWord ++ tailWord_454450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454471 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 2]
def baseStart_454471 : Nat := 118140960795 + 454471 * 2 ^ 59
def prefixEnd_454471 : Nat := 4983230072969 + 3 ^ 40 * 454471 * 2
def baseEnd_454471 : Nat := 207432948026308101175495

theorem tailTrace_454471 : CollatzResearch.WordTrace tailWord_454471 prefixEnd_454471 207432948026308101175495 := by
  unfold tailWord_454471
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575919136536659312467267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11050612757691106208311511 16575919136536659312467267)
  ·
    refine ⟨24863878704804988968700901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16575919136536659312467267 24863878704804988968700901)
    ·
      refine ⟨4661977257150935431631419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24863878704804988968700901 4661977257150935431631419)
      ·
        refine ⟨6992965885726403147447129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661977257150935431631419 6992965885726403147447129)
        ·
          refine ⟨5244724414294802360585347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6992965885726403147447129 5244724414294802360585347)
          ·
            refine ⟨7867086621442203540878021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244724414294802360585347 7867086621442203540878021)
            ·
              refine ⟨1475078741520413163914629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7867086621442203540878021 1475078741520413163914629)
              ·
                refine ⟨276577264035077468233993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1475078741520413163914629 276577264035077468233993)
                ·
                  refine ⟨207432948026308101175495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276577264035077468233993 207432948026308101175495)
                  ·
                    rfl

theorem cell20_454471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 2].length) (baseStart_454471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454471 prefixEnd_454471 := by exact prefixLift 454471
  have htrace : WordTrace (prefixWord ++ tailWord_454471) baseStart_454471 baseEnd_454471 := by
    simpa [prefixWord, tailWord_454471, baseEnd_454471] using wordTrace_append hprefix tailTrace_454471
  have hstable : (prefixWord ++ tailWord_454471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454471).length < 2 ^ (prefixWord ++ tailWord_454471).sum := by decide
  have hdescent : baseEnd_454471 < baseStart_454471 := by decide
  rcases family_descends (prefixWord ++ tailWord_454471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454526 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_454526 : Nat := 118140960795 + 454526 * 2 ^ 59
def prefixEnd_454526 : Nat := 4983230072969 + 3 ^ 40 * 454526 * 2
def baseEnd_454526 : Nat := 207458051524972354341937

theorem tailTrace_454526 : CollatzResearch.WordTrace tailWord_454526 prefixEnd_454526 207458051524972354341937 := by
  unfold tailWord_454526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072240643917175463214929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11051950100891602470479621 2072240643917175463214929)
  ·
    refine ⟨1554180482937881597411197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2072240643917175463214929 1554180482937881597411197)
    ·
      refine ⟨582817681101705599029199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1554180482937881597411197 582817681101705599029199)
      ·
        refine ⟨874226521652558398543799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582817681101705599029199 874226521652558398543799)
        ·
          refine ⟨1311339782478837597815699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874226521652558398543799 1311339782478837597815699)
          ·
            refine ⟨1967009673718256396723549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311339782478837597815699 1967009673718256396723549)
            ·
              refine ⟨737628627644346148771331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1967009673718256396723549 737628627644346148771331)
              ·
                refine ⟨1106442941466519223156997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737628627644346148771331 1106442941466519223156997)
                ·
                  refine ⟨207458051524972354341937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106442941466519223156997 207458051524972354341937)
                  ·
                    rfl

theorem cell20_454526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_454526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454526 prefixEnd_454526 := by exact prefixLift 454526
  have htrace : WordTrace (prefixWord ++ tailWord_454526) baseStart_454526 baseEnd_454526 := by
    simpa [prefixWord, tailWord_454526, baseEnd_454526] using wordTrace_append hprefix tailTrace_454526
  have hstable : (prefixWord ++ tailWord_454526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454526).length < 2 ^ (prefixWord ++ tailWord_454526).sum := by decide
  have hdescent : baseEnd_454526 < baseStart_454526 := by decide
  rcases family_descends (prefixWord ++ tailWord_454526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454536 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 3]
def baseStart_454536 : Nat := 118140960795 + 454536 * 2 ^ 59
def prefixEnd_454536 : Nat := 4983230072969 + 3 ^ 40 * 454536 * 2
def baseEnd_454536 : Nat := 207462615797456764008563

theorem tailTrace_454536 : CollatzResearch.WordTrace tailWord_454536 prefixEnd_454536 207462615797456764008563 := by
  unfold tailWord_454536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289144940650587706791731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11052193254200783609055641 8289144940650587706791731)
  ·
    refine ⟨12433717410975881560187597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289144940650587706791731 12433717410975881560187597)
    ·
      refine ⟨4662644029115955585070349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12433717410975881560187597 4662644029115955585070349)
      ·
        refine ⟨1748491510918483344401381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4662644029115955585070349 1748491510918483344401381)
        ·
          refine ⟨327842158297215627075259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1748491510918483344401381 327842158297215627075259)
          ·
            refine ⟨491763237445823440612889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327842158297215627075259 491763237445823440612889)
            ·
              refine ⟨368822428084367580459667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491763237445823440612889 368822428084367580459667)
              ·
                refine ⟨553233642126551370689501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368822428084367580459667 553233642126551370689501)
                ·
                  refine ⟨207462615797456764008563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553233642126551370689501 207462615797456764008563)
                  ·
                    rfl

theorem cell20_454536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_454536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454536 prefixEnd_454536 := by exact prefixLift 454536
  have htrace : WordTrace (prefixWord ++ tailWord_454536) baseStart_454536 baseEnd_454536 := by
    simpa [prefixWord, tailWord_454536, baseEnd_454536] using wordTrace_append hprefix tailTrace_454536
  have hstable : (prefixWord ++ tailWord_454536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454536).length < 2 ^ (prefixWord ++ tailWord_454536).sum := by decide
  have hdescent : baseEnd_454536 < baseStart_454536 := by decide
  rcases family_descends (prefixWord ++ tailWord_454536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454537 : List Nat := [1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_454537 : Nat := 118140960795 + 454537 * 2 ^ 59
def prefixEnd_454537 : Nat := 4983230072969 + 3 ^ 40 * 454537 * 2
def baseEnd_454537 : Nat := 69154357408235068325075

theorem tailTrace_454537 : CollatzResearch.WordTrace tailWord_454537 prefixEnd_454537 69154357408235068325075 := by
  unfold tailWord_454537
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578326354297552584369865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11052217569531701722913243 16578326354297552584369865)
  ·
    refine ⟨12433744765723164438277399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16578326354297552584369865 12433744765723164438277399)
    ·
      refine ⟨18650617148584746657416099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12433744765723164438277399 18650617148584746657416099)
      ·
        refine ⟨27975925722877119986124149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18650617148584746657416099 27975925722877119986124149)
        ·
          refine ⟨2622743036519729998699139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27975925722877119986124149 2622743036519729998699139)
          ·
            refine ⟨3934114554779594998048709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622743036519729998699139 3934114554779594998048709)
            ·
              refine ⟨737646479021174062134133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3934114554779594998048709 737646479021174062134133)
              ·
                refine ⟨69154357408235068325075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 737646479021174062134133 69154357408235068325075)
                ·
                  rfl

theorem cell20_454537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_454537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454537 prefixEnd_454537 := by exact prefixLift 454537
  have htrace : WordTrace (prefixWord ++ tailWord_454537) baseStart_454537 baseEnd_454537 := by
    simpa [prefixWord, tailWord_454537, baseEnd_454537] using wordTrace_append hprefix tailTrace_454537
  have hstable : (prefixWord ++ tailWord_454537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454537).length < 2 ^ (prefixWord ++ tailWord_454537).sum := by decide
  have hdescent : baseEnd_454537 < baseStart_454537 := by decide
  rcases family_descends (prefixWord ++ tailWord_454537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454581 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 2]
def baseStart_454581 : Nat := 118140960795 + 454581 * 2 ^ 59
def prefixEnd_454581 : Nat := 4983230072969 + 3 ^ 40 * 454581 * 2
def baseEnd_454581 : Nat := 207483155023636607508379

theorem tailTrace_454581 : CollatzResearch.WordTrace tailWord_454581 prefixEnd_454581 207483155023636607508379 := by
  unfold tailWord_454581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579931166138148098971597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11053287444092098732647731 16579931166138148098971597)
  ·
    refine ⟨6217474187301805537114349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16579931166138148098971597 6217474187301805537114349)
    ·
      refine ⟨2331552820238177076417881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6217474187301805537114349 2331552820238177076417881)
      ·
        refine ⟨1748664615178632807313411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2331552820238177076417881 1748664615178632807313411)
        ·
          refine ⟨2622996922767949210970117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748664615178632807313411 2622996922767949210970117)
          ·
            refine ⟨491811923018990477056897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2622996922767949210970117 491811923018990477056897)
            ·
              refine ⟨368858942264242857792673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491811923018990477056897 368858942264242857792673)
              ·
                refine ⟨276644206698182143344505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368858942264242857792673 276644206698182143344505)
                ·
                  refine ⟨207483155023636607508379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276644206698182143344505 207483155023636607508379)
                  ·
                    rfl

theorem cell20_454581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_454581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454581 prefixEnd_454581 := by exact prefixLift 454581
  have htrace : WordTrace (prefixWord ++ tailWord_454581) baseStart_454581 baseEnd_454581 := by
    simpa [prefixWord, tailWord_454581, baseEnd_454581] using wordTrace_append hprefix tailTrace_454581
  have hstable : (prefixWord ++ tailWord_454581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454581).length < 2 ^ (prefixWord ++ tailWord_454581).sum := by decide
  have hdescent : baseEnd_454581 < baseStart_454581 := by decide
  rcases family_descends (prefixWord ++ tailWord_454581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454585 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 2]
def baseStart_454585 : Nat := 118140960795 + 454585 * 2 ^ 59
def prefixEnd_454585 : Nat := 4983230072969 + 3 ^ 40 * 454585 * 2
def baseEnd_454585 : Nat := 207484980732630371375029

theorem tailTrace_454585 : CollatzResearch.WordTrace tailWord_454585 prefixEnd_454585 207484980732630371375029 := by
  unfold tailWord_454585
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580077058123656782117209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11053384705415771188078139 16580077058123656782117209)
  ·
    refine ⟨12435057793592742586587907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16580077058123656782117209 12435057793592742586587907)
    ·
      refine ⟨18652586690389113879881861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435057793592742586587907 18652586690389113879881861)
      ·
        refine ⟨3497360004447958852477849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18652586690389113879881861 3497360004447958852477849)
        ·
          refine ⟨2623020003335969139358387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497360004447958852477849 2623020003335969139358387)
          ·
            refine ⟨3934530005003953709037581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623020003335969139358387 3934530005003953709037581)
            ·
              refine ⟨1475448751876482640889093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3934530005003953709037581 1475448751876482640889093)
              ·
                refine ⟨276646640976840495166705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1475448751876482640889093 276646640976840495166705)
                ·
                  refine ⟨207484980732630371375029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276646640976840495166705 207484980732630371375029)
                  ·
                    rfl

theorem cell20_454585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_454585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454585 prefixEnd_454585 := by exact prefixLift 454585
  have htrace : WordTrace (prefixWord ++ tailWord_454585) baseStart_454585 baseEnd_454585 := by
    simpa [prefixWord, tailWord_454585, baseEnd_454585] using wordTrace_append hprefix tailTrace_454585
  have hstable : (prefixWord ++ tailWord_454585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454585).length < 2 ^ (prefixWord ++ tailWord_454585).sum := by decide
  have hdescent : baseEnd_454585 < baseStart_454585 := by decide
  rcases family_descends (prefixWord ++ tailWord_454585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454588 : List Nat := [2, 2, 2, 5, 2, 1, 1, 5]
def baseStart_454588 : Nat := 118140960795 + 454588 * 2 ^ 59
def prefixEnd_454588 : Nat := 4983230072969 + 3 ^ 40 * 454588 * 2
def baseEnd_454588 : Nat := 69162116671458564758339

theorem tailTrace_454588 : CollatzResearch.WordTrace tailWord_454588 prefixEnd_454588 69162116671458564758339 := by
  unfold tailWord_454588
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290093238556394147238209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11053457651408525529650945 8290093238556394147238209)
  ·
    refine ⟨6217569928917295610428657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8290093238556394147238209 6217569928917295610428657)
    ·
      refine ⟨4663177446687971707821493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6217569928917295610428657 4663177446687971707821493)
      ·
        refine ⟨437172885626997347608265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4663177446687971707821493 437172885626997347608265)
        ·
          refine ⟨327879664220248010706199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437172885626997347608265 327879664220248010706199)
          ·
            refine ⟨491819496330372016059299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327879664220248010706199 491819496330372016059299)
            ·
              refine ⟨737729244495558024088949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491819496330372016059299 737729244495558024088949)
              ·
                refine ⟨69162116671458564758339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 737729244495558024088949 69162116671458564758339)
                ·
                  rfl

theorem cell20_454588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_454588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454588 prefixEnd_454588 := by exact prefixLift 454588
  have htrace : WordTrace (prefixWord ++ tailWord_454588) baseStart_454588 baseEnd_454588 := by
    simpa [prefixWord, tailWord_454588, baseEnd_454588] using wordTrace_append hprefix tailTrace_454588
  have hstable : (prefixWord ++ tailWord_454588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454588).length < 2 ^ (prefixWord ++ tailWord_454588).sum := by decide
  have hdescent : baseEnd_454588 < baseStart_454588 := by decide
  rcases family_descends (prefixWord ++ tailWord_454588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454606 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_454606 : Nat := 118140960795 + 454606 * 2 ^ 59
def prefixEnd_454606 : Nat := 4983230072969 + 3 ^ 40 * 454606 * 2
def baseEnd_454606 : Nat := 207494565704847631674943

theorem tailTrace_454606 : CollatzResearch.WordTrace tailWord_454606 prefixEnd_454606 207494565704847631674943 := by
  unfold tailWord_454606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072605373880947171078959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11053895327365051579087781 2072605373880947171078959)
  ·
    refine ⟨3108908060821420756618439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2072605373880947171078959 3108908060821420756618439)
    ·
      refine ⟨4663362091232131134927659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108908060821420756618439 4663362091232131134927659)
      ·
        refine ⟨6995043136848196702391489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663362091232131134927659 6995043136848196702391489)
        ·
          refine ⟨5246282352636147526793617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6995043136848196702391489 5246282352636147526793617)
          ·
            refine ⟨3934711764477110645095213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5246282352636147526793617 3934711764477110645095213)
            ·
              refine ⟨1475516911678916491910705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3934711764477110645095213 1475516911678916491910705)
              ·
                refine ⟨1106637683759187368933029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475516911678916491910705 1106637683759187368933029)
                ·
                  refine ⟨207494565704847631674943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106637683759187368933029 207494565704847631674943)
                  ·
                    rfl

theorem cell20_454606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_454606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454606 prefixEnd_454606 := by exact prefixLift 454606
  have htrace : WordTrace (prefixWord ++ tailWord_454606) baseStart_454606 baseEnd_454606 := by
    simpa [prefixWord, tailWord_454606, baseEnd_454606] using wordTrace_append hprefix tailTrace_454606
  have hstable : (prefixWord ++ tailWord_454606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454606).length < 2 ^ (prefixWord ++ tailWord_454606).sum := by decide
  have hdescent : baseEnd_454606 < baseStart_454606 := by decide
  rcases family_descends (prefixWord ++ tailWord_454606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454623 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 2]
def baseStart_454623 : Nat := 118140960795 + 454623 * 2 ^ 59
def prefixEnd_454623 : Nat := 4983230072969 + 3 ^ 40 * 454623 * 2
def baseEnd_454623 : Nat := 207502324968071128108207

theorem tailTrace_454623 : CollatzResearch.WordTrace tailWord_454623 prefixEnd_454623 207502324968071128108207 := by
  unfold tailWord_454623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16581463031985989272000523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11054308687990659514667015 16581463031985989272000523)
  ·
    refine ⟨24872194547978983908000785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16581463031985989272000523 24872194547978983908000785)
    ·
      refine ⟨18654145910984237931000589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24872194547978983908000785 18654145910984237931000589)
      ·
        refine ⟨6995304716619089224125221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18654145910984237931000589 6995304716619089224125221)
        ·
          refine ⟨1311619634366079229523479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6995304716619089224125221 1311619634366079229523479)
          ·
            refine ⟨1967429451549118844285219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311619634366079229523479 1967429451549118844285219)
            ·
              refine ⟨2951144177323678266427829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967429451549118844285219 2951144177323678266427829)
              ·
                refine ⟨276669766624094837477609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2951144177323678266427829 276669766624094837477609)
                ·
                  refine ⟨207502324968071128108207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276669766624094837477609 207502324968071128108207)
                  ·
                    rfl

theorem cell20_454623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 2].length) (baseStart_454623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454623 prefixEnd_454623 := by exact prefixLift 454623
  have htrace : WordTrace (prefixWord ++ tailWord_454623) baseStart_454623 baseEnd_454623 := by
    simpa [prefixWord, tailWord_454623, baseEnd_454623] using wordTrace_append hprefix tailTrace_454623
  have hstable : (prefixWord ++ tailWord_454623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454623).length < 2 ^ (prefixWord ++ tailWord_454623).sum := by decide
  have hdescent : baseEnd_454623 < baseStart_454623 := by decide
  rcases family_descends (prefixWord ++ tailWord_454623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454672 : List Nat := [2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_454672 : Nat := 118140960795 + 454672 * 2 ^ 59
def prefixEnd_454672 : Nat := 4983230072969 + 3 ^ 40 * 454672 * 2
def baseEnd_454672 : Nat := 69174896634414911824891

theorem tailTrace_454672 : CollatzResearch.WordTrace tailWord_454672 prefixEnd_454672 69174896634414911824891 := by
  unfold tailWord_454672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291625104404235320267135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11055500139205647093689513 8291625104404235320267135)
  ·
    refine ⟨12437437656606352980400703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8291625104404235320267135 12437437656606352980400703)
    ·
      refine ⟨18656156484909529470601055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12437437656606352980400703 18656156484909529470601055)
      ·
        refine ⟨27984234727364294205901583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18656156484909529470601055 27984234727364294205901583)
        ·
          refine ⟨41976352091046441308852375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27984234727364294205901583 41976352091046441308852375)
          ·
            refine ⟨62964528136569661963278563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41976352091046441308852375 62964528136569661963278563)
            ·
              refine ⟨94446792204854492944917845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62964528136569661963278563 94446792204854492944917845)
              ·
                refine ⟨69174896634414911824891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 94446792204854492944917845 69174896634414911824891)
                ·
                  rfl

theorem cell20_454672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_454672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454672 prefixEnd_454672 := by exact prefixLift 454672
  have htrace : WordTrace (prefixWord ++ tailWord_454672) baseStart_454672 baseEnd_454672 := by
    simpa [prefixWord, tailWord_454672, baseEnd_454672] using wordTrace_append hprefix tailTrace_454672
  have hstable : (prefixWord ++ tailWord_454672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454672).length < 2 ^ (prefixWord ++ tailWord_454672).sum := by decide
  have hdescent : baseEnd_454672 < baseStart_454672 := by decide
  rcases family_descends (prefixWord ++ tailWord_454672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454695 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 4]
def baseStart_454695 : Nat := 118140960795 + 454695 * 2 ^ 59
def prefixEnd_454695 : Nat := 4983230072969 + 3 ^ 40 * 454695 * 2
def baseEnd_454695 : Nat := 207535187729958877707913

theorem tailTrace_454695 : CollatzResearch.WordTrace tailWord_454695 prefixEnd_454695 207535187729958877707913 := by
  unfold tailWord_454695
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584089087725145568621539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056059391816763712414359 16584089087725145568621539)
  ·
    refine ⟨24876133631587718352932309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16584089087725145568621539 24876133631587718352932309)
    ·
      refine ⟨583034381990337148896851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24876133631587718352932309 583034381990337148896851)
      ·
        refine ⟨874551572985505723345277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583034381990337148896851 874551572985505723345277)
        ·
          refine ⟨327956839869564646254479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874551572985505723345277 327956839869564646254479)
          ·
            refine ⟨491935259804346969381719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327956839869564646254479 491935259804346969381719)
            ·
              refine ⟨737902889706520454072579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491935259804346969381719 737902889706520454072579)
              ·
                refine ⟨1106854334559780681108869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737902889706520454072579 1106854334559780681108869)
                ·
                  refine ⟨207535187729958877707913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106854334559780681108869 207535187729958877707913)
                  ·
                    rfl

theorem cell20_454695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 4].length) (baseStart_454695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454695 prefixEnd_454695 := by exact prefixLift 454695
  have htrace : WordTrace (prefixWord ++ tailWord_454695) baseStart_454695 baseEnd_454695 := by
    simpa [prefixWord, tailWord_454695, baseEnd_454695] using wordTrace_append hprefix tailTrace_454695
  have hstable : (prefixWord ++ tailWord_454695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454695).length < 2 ^ (prefixWord ++ tailWord_454695).sum := by decide
  have hdescent : baseEnd_454695 < baseStart_454695 := by decide
  rcases family_descends (prefixWord ++ tailWord_454695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454703 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_454703 : Nat := 118140960795 + 454703 * 2 ^ 59
def prefixEnd_454703 : Nat := 4983230072969 + 3 ^ 40 * 454703 * 2
def baseEnd_454703 : Nat := 207538839147946405441213

theorem tailTrace_454703 : CollatzResearch.WordTrace tailWord_454703 prefixEnd_454703 207538839147946405441213 := by
  unfold tailWord_454703
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584380871696162934912763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056253914464108623275175 16584380871696162934912763)
  ·
    refine ⟨24876571307544244402369145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16584380871696162934912763 24876571307544244402369145)
    ·
      refine ⟨18657428480658183301776859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24876571307544244402369145 18657428480658183301776859)
      ·
        refine ⟨27986142720987274952665289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18657428480658183301776859 27986142720987274952665289)
        ·
          refine ⟨20989607040740456214498967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27986142720987274952665289 20989607040740456214498967)
          ·
            refine ⟨31484410561110684321748451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20989607040740456214498967 31484410561110684321748451)
            ·
              refine ⟨47226615841666026482622677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31484410561110684321748451 47226615841666026482622677)
              ·
                refine ⟨1106873808789047495686469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47226615841666026482622677 1106873808789047495686469)
                ·
                  refine ⟨207538839147946405441213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106873808789047495686469 207538839147946405441213)
                  ·
                    rfl

theorem cell20_454703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_454703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454703 prefixEnd_454703 := by exact prefixLift 454703
  have htrace : WordTrace (prefixWord ++ tailWord_454703) baseStart_454703 baseEnd_454703 := by
    simpa [prefixWord, tailWord_454703, baseEnd_454703] using wordTrace_append hprefix tailTrace_454703
  have hstable : (prefixWord ++ tailWord_454703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454703).length < 2 ^ (prefixWord ++ tailWord_454703).sum := by decide
  have hdescent : baseEnd_454703 < baseStart_454703 := by decide
  rcases family_descends (prefixWord ++ tailWord_454703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454750 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_454750 : Nat := 118140960795 + 454750 * 2 ^ 59
def prefixEnd_454750 : Nat := 4983230072969 + 3 ^ 40 * 454750 * 2
def baseEnd_454750 : Nat := 207560291228623130874355

theorem tailTrace_454750 : CollatzResearch.WordTrace tailWord_454750 prefixEnd_454750 207560291228623130874355 := by
  unfold tailWord_454750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073261887815736245234213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11057396735017259974582469 2073261887815736245234213)
  ·
    refine ⟨388736603965450545981415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2073261887815736245234213 388736603965450545981415)
    ·
      refine ⟨583104905948175818972123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388736603965450545981415 583104905948175818972123)
      ·
        refine ⟨874657358922263728458185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583104905948175818972123 874657358922263728458185)
        ·
          refine ⟨655993019191697796343639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874657358922263728458185 655993019191697796343639)
          ·
            refine ⟨983989528787546694515459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655993019191697796343639 983989528787546694515459)
            ·
              refine ⟨1475984293181320041773189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983989528787546694515459 1475984293181320041773189)
              ·
                refine ⟨276747054971497507832473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1475984293181320041773189 276747054971497507832473)
                ·
                  refine ⟨207560291228623130874355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276747054971497507832473 207560291228623130874355)
                  ·
                    rfl

theorem cell20_454750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_454750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454750 prefixEnd_454750 := by exact prefixLift 454750
  have htrace : WordTrace (prefixWord ++ tailWord_454750) baseStart_454750 baseEnd_454750 := by
    simpa [prefixWord, tailWord_454750, baseEnd_454750] using wordTrace_append hprefix tailTrace_454750
  have hstable : (prefixWord ++ tailWord_454750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454750).length < 2 ^ (prefixWord ++ tailWord_454750).sum := by decide
  have hdescent : baseEnd_454750 < baseStart_454750 := by decide
  rcases family_descends (prefixWord ++ tailWord_454750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454792 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 2]
def baseStart_454792 : Nat := 118140960795 + 454792 * 2 ^ 59
def prefixEnd_454792 : Nat := 4983230072969 + 3 ^ 40 * 454792 * 2
def baseEnd_454792 : Nat := 207579461173057651474183

theorem tailTrace_454792 : CollatzResearch.WordTrace tailWord_454792 prefixEnd_454792 207579461173057651474183 := by
  unfold tailWord_454792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293813484186865567451315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11058417978915820756601753 8293813484186865567451315)
  ·
    refine ⟨12440720226280298351176973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8293813484186865567451315 12440720226280298351176973)
    ·
      refine ⟨4665270084855111881691365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12440720226280298351176973 4665270084855111881691365)
      ·
        refine ⟨874738140910333477817131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4665270084855111881691365 874738140910333477817131)
        ·
          refine ⟨1312107211365500216725697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874738140910333477817131 1312107211365500216725697)
          ·
            refine ⟨984080408524125162544273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312107211365500216725697 984080408524125162544273)
            ·
              refine ⟨738060306393093871908205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984080408524125162544273 738060306393093871908205)
              ·
                refine ⟨276772614897410201965577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738060306393093871908205 276772614897410201965577)
                ·
                  refine ⟨207579461173057651474183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276772614897410201965577 207579461173057651474183)
                  ·
                    rfl

theorem cell20_454792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_454792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454792 prefixEnd_454792 := by exact prefixLift 454792
  have htrace : WordTrace (prefixWord ++ tailWord_454792) baseStart_454792 baseEnd_454792 := by
    simpa [prefixWord, tailWord_454792, baseEnd_454792] using wordTrace_append hprefix tailTrace_454792
  have hstable : (prefixWord ++ tailWord_454792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454792).length < 2 ^ (prefixWord ++ tailWord_454792).sum := by decide
  have hdescent : baseEnd_454792 < baseStart_454792 := by decide
  rcases family_descends (prefixWord ++ tailWord_454792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454813 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 2]
def baseStart_454813 : Nat := 118140960795 + 454813 * 2 ^ 59
def prefixEnd_454813 : Nat := 4983230072969 + 3 ^ 40 * 454813 * 2
def baseEnd_454813 : Nat := 207589046145274911774097

theorem tailTrace_454813 : CollatzResearch.WordTrace tailWord_454813 prefixEnd_454813 207589046145274911774097 := by
  unfold tailWord_454813
  simp only [CollatzResearch.WordTrace]
  refine ⟨16588392901297651721417093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11058928600865101147611395 16588392901297651721417093)
  ·
    refine ⟨3110323668993309697765705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16588392901297651721417093 3110323668993309697765705)
    ·
      refine ⟨2332742751744982273324279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3110323668993309697765705 2332742751744982273324279)
      ·
        refine ⟨3499114127617473409986419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332742751744982273324279 3499114127617473409986419)
        ·
          refine ⟨5248671191426210114979629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499114127617473409986419 5248671191426210114979629)
          ·
            refine ⟨1968251696784828793117361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5248671191426210114979629 1968251696784828793117361)
            ·
              refine ⟨1476188772588621594838021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968251696784828793117361 1476188772588621594838021)
              ·
                refine ⟨276785394860366549032129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1476188772588621594838021 276785394860366549032129)
                ·
                  refine ⟨207589046145274911774097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276785394860366549032129 207589046145274911774097)
                  ·
                    rfl

theorem cell20_454813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_454813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454813 prefixEnd_454813 := by exact prefixLift 454813
  have htrace : WordTrace (prefixWord ++ tailWord_454813) baseStart_454813 baseEnd_454813 := by
    simpa [prefixWord, tailWord_454813, baseEnd_454813] using wordTrace_append hprefix tailTrace_454813
  have hstable : (prefixWord ++ tailWord_454813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454813).length < 2 ^ (prefixWord ++ tailWord_454813).sum := by decide
  have hdescent : baseEnd_454813 < baseStart_454813 := by decide
  rcases family_descends (prefixWord ++ tailWord_454813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454823 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 3]
def baseStart_454823 : Nat := 118140960795 + 454823 * 2 ^ 59
def prefixEnd_454823 : Nat := 4983230072969 + 3 ^ 40 * 454823 * 2
def baseEnd_454823 : Nat := 207593610417759321440723

theorem tailTrace_454823 : CollatzResearch.WordTrace tailWord_454823 prefixEnd_454823 207593610417759321440723 := by
  unfold tailWord_454823
  simp only [CollatzResearch.WordTrace]
  refine ⟨16588757631261423429281123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11059171754174282286187415 16588757631261423429281123)
  ·
    refine ⟨24883136446892135143921685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16588757631261423429281123 24883136446892135143921685)
    ·
      refine ⟨1166397020948068834871329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24883136446892135143921685 1166397020948068834871329)
      ·
        refine ⟨874797765711051626153497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166397020948068834871329 874797765711051626153497)
        ·
          refine ⟨656098324283288719615123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874797765711051626153497 656098324283288719615123)
          ·
            refine ⟨984147486424933079422685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656098324283288719615123 984147486424933079422685)
            ·
              refine ⟨369055307409349904783507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 984147486424933079422685 369055307409349904783507)
              ·
                refine ⟨553582961114024857175261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369055307409349904783507 553582961114024857175261)
                ·
                  refine ⟨207593610417759321440723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553582961114024857175261 207593610417759321440723)
                  ·
                    rfl

theorem cell20_454823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_454823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454823 prefixEnd_454823 := by exact prefixLift 454823
  have htrace : WordTrace (prefixWord ++ tailWord_454823) baseStart_454823 baseEnd_454823 := by
    simpa [prefixWord, tailWord_454823, baseEnd_454823] using wordTrace_append hprefix tailTrace_454823
  have hstable : (prefixWord ++ tailWord_454823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454823).length < 2 ^ (prefixWord ++ tailWord_454823).sum := by decide
  have hdescent : baseEnd_454823 < baseStart_454823 := by decide
  rcases family_descends (prefixWord ++ tailWord_454823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454848 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_454848 : Nat := 118140960795 + 454848 * 2 ^ 59
def prefixEnd_454848 : Nat := 4983230072969 + 3 ^ 40 * 454848 * 2
def baseEnd_454848 : Nat := 207605021098970345607287

theorem tailTrace_454848 : CollatzResearch.WordTrace tailWord_454848 prefixEnd_454848 207605021098970345607287 := by
  unfold tailWord_454848
  simp only [CollatzResearch.WordTrace]
  refine ⟨8294834728085426349470599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11059779637447235132627465 8294834728085426349470599)
  ·
    refine ⟨12442252092128139524205899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8294834728085426349470599 12442252092128139524205899)
    ·
      refine ⟨18663378138192209286308849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12442252092128139524205899 18663378138192209286308849)
      ·
        refine ⟨13997533603644156964731637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18663378138192209286308849 13997533603644156964731637)
        ·
          refine ⟨1312268775341639715443591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13997533603644156964731637 1312268775341639715443591)
          ·
            refine ⟨1968403163012459573165387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312268775341639715443591 1968403163012459573165387)
            ·
              refine ⟨2952604744518689359748081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968403163012459573165387 2952604744518689359748081)
              ·
                refine ⟨2214453558389017019811061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952604744518689359748081 2214453558389017019811061)
                ·
                  refine ⟨207605021098970345607287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2214453558389017019811061 207605021098970345607287)
                  ·
                    rfl

theorem cell20_454848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_454848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454848 prefixEnd_454848 := by exact prefixLift 454848
  have htrace : WordTrace (prefixWord ++ tailWord_454848) baseStart_454848 baseEnd_454848 := by
    simpa [prefixWord, tailWord_454848, baseEnd_454848] using wordTrace_append hprefix tailTrace_454848
  have hstable : (prefixWord ++ tailWord_454848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454848).length < 2 ^ (prefixWord ++ tailWord_454848).sum := by decide
  have hdescent : baseEnd_454848 < baseStart_454848 := by decide
  rcases family_descends (prefixWord ++ tailWord_454848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454872 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_454872 : Nat := 118140960795 + 454872 * 2 ^ 59
def prefixEnd_454872 : Nat := 4983230072969 + 3 ^ 40 * 454872 * 2
def baseEnd_454872 : Nat := 207615975352932928807189

theorem tailTrace_454872 : CollatzResearch.WordTrace tailWord_454872 prefixEnd_454872 207615975352932928807189 := by
  unfold tailWord_454872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295272404041952398907435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11060363205389269865209913 8295272404041952398907435)
  ·
    refine ⟨12442908606062928598361153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295272404041952398907435 12442908606062928598361153)
    ·
      refine ⟨9332181454547196448770865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12442908606062928598361153 9332181454547196448770865)
      ·
        refine ⟨6999136090910397336578149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9332181454547196448770865 6999136090910397336578149)
        ·
          refine ⟨1312338017045699500608403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6999136090910397336578149 1312338017045699500608403)
          ·
            refine ⟨1968507025568549250912605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312338017045699500608403 1968507025568549250912605)
            ·
              refine ⟨738190134588205969092227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1968507025568549250912605 738190134588205969092227)
              ·
                refine ⟨1107285201882308953638341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738190134588205969092227 1107285201882308953638341)
                ·
                  refine ⟨207615975352932928807189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107285201882308953638341 207615975352932928807189)
                  ·
                    rfl

theorem cell20_454872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_454872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454872 prefixEnd_454872 := by exact prefixLift 454872
  have htrace : WordTrace (prefixWord ++ tailWord_454872) baseStart_454872 baseEnd_454872 := by
    simpa [prefixWord, tailWord_454872, baseEnd_454872] using wordTrace_append hprefix tailTrace_454872
  have hstable : (prefixWord ++ tailWord_454872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454872).length < 2 ^ (prefixWord ++ tailWord_454872).sum := by decide
  have hdescent : baseEnd_454872 < baseStart_454872 := by decide
  rcases family_descends (prefixWord ++ tailWord_454872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454948 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_454948 : Nat := 118140960795 + 454948 * 2 ^ 59
def prefixEnd_454948 : Nat := 4983230072969 + 3 ^ 40 * 454948 * 2
def baseEnd_454948 : Nat := 207650663823814442273545

theorem tailTrace_454948 : CollatzResearch.WordTrace tailWord_454948 prefixEnd_454948 207650663823814442273545 := by
  unfold tailWord_454948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296658377904284888790749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11062211170539046518387665 8296658377904284888790749)
  ·
    refine ⟨3111246891714106833296531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8296658377904284888790749 3111246891714106833296531)
    ·
      refine ⟨4666870337571160249944797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111246891714106833296531 4666870337571160249944797)
      ·
        refine ⟨1750076376589185093729299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4666870337571160249944797 1750076376589185093729299)
        ·
          refine ⟨2625114564883777640593949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750076376589185093729299 2625114564883777640593949)
          ·
            refine ⟨984417961831416615222731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2625114564883777640593949 984417961831416615222731)
            ·
              refine ⟨1476626942747124922834097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984417961831416615222731 1476626942747124922834097)
              ·
                refine ⟨1107470207060343692125573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476626942747124922834097 1107470207060343692125573)
                ·
                  refine ⟨207650663823814442273545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107470207060343692125573 207650663823814442273545)
                  ·
                    rfl

theorem cell20_454948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_454948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454948 prefixEnd_454948 := by exact prefixLift 454948
  have htrace : WordTrace (prefixWord ++ tailWord_454948) baseStart_454948 baseEnd_454948 := by
    simpa [prefixWord, tailWord_454948, baseEnd_454948] using wordTrace_append hprefix tailTrace_454948
  have hstable : (prefixWord ++ tailWord_454948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454948).length < 2 ^ (prefixWord ++ tailWord_454948).sum := by decide
  have hdescent : baseEnd_454948 < baseStart_454948 := by decide
  rcases family_descends (prefixWord ++ tailWord_454948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454965 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 2]
def baseStart_454965 : Nat := 118140960795 + 454965 * 2 ^ 59
def prefixEnd_454965 : Nat := 4983230072969 + 3 ^ 40 * 454965 * 2
def baseEnd_454965 : Nat := 207658423087037938706809

theorem tailTrace_454965 : CollatzResearch.WordTrace tailWord_454965 prefixEnd_454965 207658423087037938706809 := by
  unfold tailWord_454965
  simp only [CollatzResearch.WordTrace]
  refine ⟨16593936796746981680950349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11062624531164654453966899 16593936796746981680950349)
  ·
    refine ⟨6222726298780118130356381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16593936796746981680950349 6222726298780118130356381)
    ·
      refine ⟨2333522362042544298883643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6222726298780118130356381 2333522362042544298883643)
      ·
        refine ⟨3500283543063816448325465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333522362042544298883643 3500283543063816448325465)
        ·
          refine ⟨2625212657297862336244099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3500283543063816448325465 2625212657297862336244099)
          ·
            refine ⟨3937818985946793504366149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625212657297862336244099 3937818985946793504366149)
            ·
              refine ⟨738341059865023782068653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3937818985946793504366149 738341059865023782068653)
              ·
                refine ⟨276877897449383918275745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738341059865023782068653 276877897449383918275745)
                ·
                  refine ⟨207658423087037938706809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276877897449383918275745 207658423087037938706809)
                  ·
                    rfl

theorem cell20_454965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_454965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454965 prefixEnd_454965 := by exact prefixLift 454965
  have htrace : WordTrace (prefixWord ++ tailWord_454965) baseStart_454965 baseEnd_454965 := by
    simpa [prefixWord, tailWord_454965, baseEnd_454965] using wordTrace_append hprefix tailTrace_454965
  have hstable : (prefixWord ++ tailWord_454965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454965).length < 2 ^ (prefixWord ++ tailWord_454965).sum := by decide
  have hdescent : baseEnd_454965 < baseStart_454965 := by decide
  rcases family_descends (prefixWord ++ tailWord_454965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454996 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_454996 : Nat := 118140960795 + 454996 * 2 ^ 59
def prefixEnd_454996 : Nat := 4983230072969 + 3 ^ 40 * 454996 * 2
def baseEnd_454996 : Nat := 207672572331739608673349

theorem tailTrace_454996 : CollatzResearch.WordTrace tailWord_454996 prefixEnd_454996 207672572331739608673349 := by
  unfold tailWord_454996
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297533729817336987664421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11063378306423115983552561 8297533729817336987664421)
  ·
    refine ⟨1555787574340750685187079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8297533729817336987664421 1555787574340750685187079)
    ·
      refine ⟨2333681361511126027780619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555787574340750685187079 2333681361511126027780619)
      ·
        refine ⟨3500522042266689041670929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333681361511126027780619 3500522042266689041670929)
        ·
          refine ⟨2625391531700016781253197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3500522042266689041670929 2625391531700016781253197)
          ·
            refine ⟨984521824387506292969949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2625391531700016781253197 984521824387506292969949)
            ·
              refine ⟨369195684145314859863731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 984521824387506292969949 369195684145314859863731)
              ·
                refine ⟨553793526217972289795597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369195684145314859863731 553793526217972289795597)
                ·
                  refine ⟨207672572331739608673349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553793526217972289795597 207672572331739608673349)
                  ·
                    rfl

theorem cell20_454996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_454996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_454996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_454996 prefixEnd_454996 := by exact prefixLift 454996
  have htrace : WordTrace (prefixWord ++ tailWord_454996) baseStart_454996 baseEnd_454996 := by
    simpa [prefixWord, tailWord_454996, baseEnd_454996] using wordTrace_append hprefix tailTrace_454996
  have hstable : (prefixWord ++ tailWord_454996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454996).length < 2 ^ (prefixWord ++ tailWord_454996).sum := by decide
  have hdescent : baseEnd_454996 < baseStart_454996 := by decide
  rcases family_descends (prefixWord ++ tailWord_454996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455007 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_455007 : Nat := 118140960795 + 455007 * 2 ^ 59
def prefixEnd_455007 : Nat := 4983230072969 + 3 ^ 40 * 455007 * 2
def baseEnd_455007 : Nat := 207677593031472459306637

theorem tailTrace_455007 : CollatzResearch.WordTrace tailWord_455007 prefixEnd_455007 207677593031472459306637 := by
  unfold tailWord_455007
  simp only [CollatzResearch.WordTrace]
  refine ⟨16595468662594822853979275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11063645775063215235986183 16595468662594822853979275)
  ·
    refine ⟨24893202993892234280968913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16595468662594822853979275 24893202993892234280968913)
    ·
      refine ⟨18669902245419175710726685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24893202993892234280968913 18669902245419175710726685)
      ·
        refine ⟨7001213342032190891522507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18669902245419175710726685 7001213342032190891522507)
        ·
          refine ⟨10501820013048286337283761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7001213342032190891522507 10501820013048286337283761)
          ·
            refine ⟨7876365009786214752962821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10501820013048286337283761 7876365009786214752962821)
            ·
              refine ⟨1476818439334915266180529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7876365009786214752962821 1476818439334915266180529)
              ·
                refine ⟨1107613829501186449635397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476818439334915266180529 1107613829501186449635397)
                ·
                  refine ⟨207677593031472459306637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107613829501186449635397 207677593031472459306637)
                  ·
                    rfl

theorem cell20_455007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_455007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455007 prefixEnd_455007 := by exact prefixLift 455007
  have htrace : WordTrace (prefixWord ++ tailWord_455007) baseStart_455007 baseEnd_455007 := by
    simpa [prefixWord, tailWord_455007, baseEnd_455007] using wordTrace_append hprefix tailTrace_455007
  have hstable : (prefixWord ++ tailWord_455007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455007).length < 2 ^ (prefixWord ++ tailWord_455007).sum := by decide
  have hdescent : baseEnd_455007 < baseStart_455007 := by decide
  rcases family_descends (prefixWord ++ tailWord_455007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455010 : List Nat := [3, 3, 2, 1, 1, 2, 4, 4]
def baseStart_455010 : Nat := 118140960795 + 455010 * 2 ^ 59
def prefixEnd_455010 : Nat := 4983230072969 + 3 ^ 40 * 455010 * 2
def baseEnd_455010 : Nat := 69226320771072594068875

theorem tailTrace_455010 : CollatzResearch.WordTrace tailWord_455010 prefixEnd_455010 69226320771072594068875 := by
  unfold tailWord_455010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148894520395988591584621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11063718721055969577558989 4148894520395988591584621)
  ·
    refine ⟨1555835445148495721844233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4148894520395988591584621 1555835445148495721844233)
    ·
      refine ⟨1166876583861371791383175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1555835445148495721844233 1166876583861371791383175)
      ·
        refine ⟨1750314875792057687074763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166876583861371791383175 1750314875792057687074763)
        ·
          refine ⟨2625472313688086530612145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750314875792057687074763 2625472313688086530612145)
          ·
            refine ⟨1969104235266064897959109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625472313688086530612145 1969104235266064897959109)
            ·
              refine ⟨369207044112387168367333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1969104235266064897959109 369207044112387168367333)
              ·
                refine ⟨69226320771072594068875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369207044112387168367333 69226320771072594068875)
                ·
                  rfl

theorem cell20_455010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_455010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455010 prefixEnd_455010 := by exact prefixLift 455010
  have htrace : WordTrace (prefixWord ++ tailWord_455010) baseStart_455010 baseEnd_455010 := by
    simpa [prefixWord, tailWord_455010, baseEnd_455010] using wordTrace_append hprefix tailTrace_455010
  have hstable : (prefixWord ++ tailWord_455010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455010).length < 2 ^ (prefixWord ++ tailWord_455010).sum := by decide
  have hdescent : baseEnd_455010 < baseStart_455010 := by decide
  rcases family_descends (prefixWord ++ tailWord_455010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455020 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 2]
def baseStart_455020 : Nat := 118140960795 + 455020 * 2 ^ 59
def prefixEnd_455020 : Nat := 4983230072969 + 3 ^ 40 * 455020 * 2
def baseEnd_455020 : Nat := 207683526585702191873251

theorem tailTrace_455020 : CollatzResearch.WordTrace tailWord_455020 prefixEnd_455020 207683526585702191873251 := by
  unfold tailWord_455020
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297971405773863037101257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11063961874365150716135009 8297971405773863037101257)
  ·
    refine ⟨6223478554330397277825943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8297971405773863037101257 6223478554330397277825943)
    ·
      refine ⟨9335217831495595916738915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223478554330397277825943 9335217831495595916738915)
      ·
        refine ⟨14002826747243393875108373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335217831495595916738915 14002826747243393875108373)
        ·
          refine ⟨656382503777034087895705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14002826747243393875108373 656382503777034087895705)
          ·
            refine ⟨492286877832775565921779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656382503777034087895705 492286877832775565921779)
            ·
              refine ⟨738430316749163348882669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492286877832775565921779 738430316749163348882669)
              ·
                refine ⟨276911368780936255831001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738430316749163348882669 276911368780936255831001)
                ·
                  refine ⟨207683526585702191873251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276911368780936255831001 207683526585702191873251)
                  ·
                    rfl

theorem cell20_455020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_455020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455020 prefixEnd_455020 := by exact prefixLift 455020
  have htrace : WordTrace (prefixWord ++ tailWord_455020) baseStart_455020 baseEnd_455020 := by
    simpa [prefixWord, tailWord_455020, baseEnd_455020] using wordTrace_append hprefix tailTrace_455020
  have hstable : (prefixWord ++ tailWord_455020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455020).length < 2 ^ (prefixWord ++ tailWord_455020).sum := by decide
  have hdescent : baseEnd_455020 < baseStart_455020 := by decide
  rcases family_descends (prefixWord ++ tailWord_455020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455041 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 4]
def baseStart_455041 : Nat := 118140960795 + 455041 * 2 ^ 59
def prefixEnd_455041 : Nat := 4983230072969 + 3 ^ 40 * 455041 * 2
def baseEnd_455041 : Nat := 207693111557919452173165

theorem tailTrace_455041 : CollatzResearch.WordTrace tailWord_455041 prefixEnd_455041 207693111557919452173165 := by
  unfold tailWord_455041
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596708744471646660716977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11064472496314431107144651 16596708744471646660716977)
  ·
    refine ⟨12447531558353734995537733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16596708744471646660716977 12447531558353734995537733)
    ·
      refine ⟨2333912167191325311663325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12447531558353734995537733 2333912167191325311663325)
      ·
        refine ⟨875217062696746991873747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2333912167191325311663325 875217062696746991873747)
        ·
          refine ⟨1312825594045120487810621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875217062696746991873747 1312825594045120487810621)
          ·
            refine ⟨492309597766920182928983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1312825594045120487810621 492309597766920182928983)
            ·
              refine ⟨738464396650380274393475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492309597766920182928983 738464396650380274393475)
              ·
                refine ⟨1107696594975570411590213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738464396650380274393475 1107696594975570411590213)
                ·
                  refine ⟨207693111557919452173165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107696594975570411590213 207693111557919452173165)
                  ·
                    rfl

theorem cell20_455041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_455041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455041 prefixEnd_455041 := by exact prefixLift 455041
  have htrace : WordTrace (prefixWord ++ tailWord_455041) baseStart_455041 baseEnd_455041 := by
    simpa [prefixWord, tailWord_455041, baseEnd_455041] using wordTrace_append hprefix tailTrace_455041
  have hstable : (prefixWord ++ tailWord_455041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455041).length < 2 ^ (prefixWord ++ tailWord_455041).sum := by decide
  have hdescent : baseEnd_455041 < baseStart_455041 := by decide
  rcases family_descends (prefixWord ++ tailWord_455041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455052 : List Nat := [2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_455052 : Nat := 118140960795 + 455052 * 2 ^ 59
def prefixEnd_455052 : Nat := 4983230072969 + 3 ^ 40 * 455052 * 2
def baseEnd_455052 : Nat := 69232710752550767602151

theorem tailTrace_455052 : CollatzResearch.WordTrace tailWord_455052 prefixEnd_455052 69232710752550767602151 := by
  unfold tailWord_455052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8298554973715897769683705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11064739964954530359578273 8298554973715897769683705)
  ·
    refine ⟨6223916230286923327262779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8298554973715897769683705 6223916230286923327262779)
    ·
      refine ⟨9335874345430384990894169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223916230286923327262779 9335874345430384990894169)
      ·
        refine ⟨7001905759072788743170627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9335874345430384990894169 7001905759072788743170627)
        ·
          refine ⟨10502858638609183114755941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7001905759072788743170627 10502858638609183114755941)
          ·
            refine ⟨1969285994739221834016739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10502858638609183114755941 1969285994739221834016739)
            ·
              refine ⟨2953928992108832751025109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969285994739221834016739 2953928992108832751025109)
              ·
                refine ⟨69232710752550767602151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2953928992108832751025109 69232710752550767602151)
                ·
                  rfl

theorem cell20_455052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_455052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455052 prefixEnd_455052 := by exact prefixLift 455052
  have htrace : WordTrace (prefixWord ++ tailWord_455052) baseStart_455052 baseEnd_455052 := by
    simpa [prefixWord, tailWord_455052, baseEnd_455052] using wordTrace_append hprefix tailTrace_455052
  have hstable : (prefixWord ++ tailWord_455052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455052).length < 2 ^ (prefixWord ++ tailWord_455052).sum := by decide
  have hdescent : baseEnd_455052 < baseStart_455052 := by decide
  rcases family_descends (prefixWord ++ tailWord_455052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455114 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_455114 : Nat := 118140960795 + 455114 * 2 ^ 59
def prefixEnd_455114 : Nat := 4983230072969 + 3 ^ 40 * 455114 * 2
def baseEnd_455114 : Nat := 207726430747055642739533

theorem tailTrace_455114 : CollatzResearch.WordTrace tailWord_455114 prefixEnd_455114 207726430747055642739533 := by
  unfold tailWord_455114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149842818301795032031099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11066247515471453418749597 4149842818301795032031099)
  ·
    refine ⟨6224764227452692548046649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149842818301795032031099 6224764227452692548046649)
    ·
      refine ⟨4668573170589519411034987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6224764227452692548046649 4668573170589519411034987)
      ·
        refine ⟨7002859755884279116552481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4668573170589519411034987 7002859755884279116552481)
        ·
          refine ⟨5252144816913209337414361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7002859755884279116552481 5252144816913209337414361)
          ·
            refine ⟨3939108612684907003060771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252144816913209337414361 3939108612684907003060771)
            ·
              refine ⟨5908662919027360504591157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939108612684907003060771 5908662919027360504591157)
              ·
                refine ⟨553937148658815047305421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5908662919027360504591157 553937148658815047305421)
                ·
                  refine ⟨207726430747055642739533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553937148658815047305421 207726430747055642739533)
                  ·
                    rfl

theorem cell20_455114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_455114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455114 prefixEnd_455114 := by exact prefixLift 455114
  have htrace : WordTrace (prefixWord ++ tailWord_455114) baseStart_455114 baseEnd_455114 := by
    simpa [prefixWord, tailWord_455114, baseEnd_455114] using wordTrace_append hprefix tailTrace_455114
  have hstable : (prefixWord ++ tailWord_455114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455114).length < 2 ^ (prefixWord ++ tailWord_455114).sum := by decide
  have hdescent : baseEnd_455114 < baseStart_455114 := by decide
  rcases family_descends (prefixWord ++ tailWord_455114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455124 : List Nat := [2, 4, 1, 2, 2, 2, 3, 4]
def baseStart_455124 : Nat := 118140960795 + 455124 * 2 ^ 59
def prefixEnd_455124 : Nat := 4983230072969 + 3 ^ 40 * 455124 * 2
def baseEnd_455124 : Nat := 69243665006513350802053

theorem tailTrace_455124 : CollatzResearch.WordTrace tailWord_455124 prefixEnd_455124 69243665006513350802053 := by
  unfold tailWord_455124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8299868001585475917994213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11066490668780634557325617 8299868001585475917994213)
  ·
    refine ⟨1556225250297276734623915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8299868001585475917994213 1556225250297276734623915)
    ·
      refine ⟨2334337875445915101935873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556225250297276734623915 2334337875445915101935873)
      ·
        refine ⟨1750753406584436326451905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334337875445915101935873 1750753406584436326451905)
        ·
          refine ⟨1313065054938327244838929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750753406584436326451905 1313065054938327244838929)
          ·
            refine ⟨984798791203745433629197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313065054938327244838929 984798791203745433629197)
            ·
              refine ⟨369299546701404537610949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 984798791203745433629197 369299546701404537610949)
              ·
                refine ⟨69243665006513350802053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369299546701404537610949 69243665006513350802053)
                ·
                  rfl

theorem cell20_455124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_455124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455124 prefixEnd_455124 := by exact prefixLift 455124
  have htrace : WordTrace (prefixWord ++ tailWord_455124) baseStart_455124 baseEnd_455124 := by
    simpa [prefixWord, tailWord_455124, baseEnd_455124] using wordTrace_append hprefix tailTrace_455124
  have hstable : (prefixWord ++ tailWord_455124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455124).length < 2 ^ (prefixWord ++ tailWord_455124).sum := by decide
  have hdescent : baseEnd_455124 < baseStart_455124 := by decide
  rcases family_descends (prefixWord ++ tailWord_455124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455200 : List Nat := [2, 1, 1, 6, 3, 1, 6]
def baseStart_455200 : Nat := 118140960795 + 455200 * 2 ^ 59
def prefixEnd_455200 : Nat := 4983230072969 + 3 ^ 40 * 455200 * 2
def baseEnd_455200 : Nat := 23085075943380173985835

theorem tailTrace_455200 : CollatzResearch.WordTrace tailWord_455200 prefixEnd_455200 23085075943380173985835 := by
  unfold tailWord_455200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301253975447808407877527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11068338633930411210503369 8301253975447808407877527)
  ·
    refine ⟨12451880963171712611816291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8301253975447808407877527 12451880963171712611816291)
    ·
      refine ⟨18677821444757568917724437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12451880963171712611816291 18677821444757568917724437)
      ·
        refine ⟨875522880223011043018333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18677821444757568917724437 875522880223011043018333)
        ·
          refine ⟨328321080083629141131875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 875522880223011043018333 328321080083629141131875)
          ·
            refine ⟨492481620125443711697813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328321080083629141131875 492481620125443711697813)
            ·
              refine ⟨23085075943380173985835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 492481620125443711697813 23085075943380173985835)
              ·
                rfl

theorem cell20_455200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 6].length) (baseStart_455200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455200 prefixEnd_455200 := by exact prefixLift 455200
  have htrace : WordTrace (prefixWord ++ tailWord_455200) baseStart_455200 baseEnd_455200 := by
    simpa [prefixWord, tailWord_455200, baseEnd_455200] using wordTrace_append hprefix tailTrace_455200
  have hstable : (prefixWord ++ tailWord_455200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455200).length < 2 ^ (prefixWord ++ tailWord_455200).sum := by decide
  have hdescent : baseEnd_455200 < baseStart_455200 := by decide
  rcases family_descends (prefixWord ++ tailWord_455200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455210 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_455210 : Nat := 118140960795 + 455210 * 2 ^ 59
def prefixEnd_455210 : Nat := 4983230072969 + 3 ^ 40 * 455210 * 2
def baseEnd_455210 : Nat := 207770247762905975539141

theorem tailTrace_455210 : CollatzResearch.WordTrace tailWord_455210 prefixEnd_455210 207770247762905975539141 := by
  unfold tailWord_455210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150718170214847130904771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11068581787239592349079389 4150718170214847130904771)
  ·
    refine ⟨6226077255322270696357157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150718170214847130904771 6226077255322270696357157)
    ·
      refine ⟨1167389485372925755566967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6226077255322270696357157 1167389485372925755566967)
      ·
        refine ⟨1751084228059388633350451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167389485372925755566967 1751084228059388633350451)
        ·
          refine ⟨2626626342089082950025677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751084228059388633350451 2626626342089082950025677)
          ·
            refine ⟨984984878283406106259629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2626626342089082950025677 984984878283406106259629)
            ·
              refine ⟨369369329356277289847361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 984984878283406106259629 369369329356277289847361)
              ·
                refine ⟨277026997017207967385521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369369329356277289847361 277026997017207967385521)
                ·
                  refine ⟨207770247762905975539141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277026997017207967385521 207770247762905975539141)
                  ·
                    rfl

theorem cell20_455210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_455210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455210 prefixEnd_455210 := by exact prefixLift 455210
  have htrace : WordTrace (prefixWord ++ tailWord_455210) baseStart_455210 baseEnd_455210 := by
    simpa [prefixWord, tailWord_455210, baseEnd_455210] using wordTrace_append hprefix tailTrace_455210
  have hstable : (prefixWord ++ tailWord_455210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455210).length < 2 ^ (prefixWord ++ tailWord_455210).sum := by decide
  have hdescent : baseEnd_455210 < baseStart_455210 := by decide
  rcases family_descends (prefixWord ++ tailWord_455210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455220 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_455220 : Nat := 118140960795 + 455220 * 2 ^ 59
def prefixEnd_455220 : Nat := 4983230072969 + 3 ^ 40 * 455220 * 2
def baseEnd_455220 : Nat := 207774812035390385205767

theorem tailTrace_455220 : CollatzResearch.WordTrace tailWord_455220 prefixEnd_455220 207774812035390385205767 := by
  unfold tailWord_455220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301618705411580115741557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11068824940548773487655409 8301618705411580115741557)
  ·
    refine ⟨778276753632335635850771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8301618705411580115741557 778276753632335635850771)
    ·
      refine ⟨1167415130448503453776157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778276753632335635850771 1167415130448503453776157)
      ·
        refine ⟨437780673918188795166059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1167415130448503453776157 437780673918188795166059)
        ·
          refine ⟨656671010877283192749089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437780673918188795166059 656671010877283192749089)
          ·
            refine ⟨492503258157962394561817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656671010877283192749089 492503258157962394561817)
            ·
              refine ⟨369377443618471795921363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492503258157962394561817 369377443618471795921363)
              ·
                refine ⟨554066165427707693882045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369377443618471795921363 554066165427707693882045)
                ·
                  refine ⟨207774812035390385205767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554066165427707693882045 207774812035390385205767)
                  ·
                    rfl

theorem cell20_455220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_455220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455220 prefixEnd_455220 := by exact prefixLift 455220
  have htrace : WordTrace (prefixWord ++ tailWord_455220) baseStart_455220 baseEnd_455220 := by
    simpa [prefixWord, tailWord_455220, baseEnd_455220] using wordTrace_append hprefix tailTrace_455220
  have hstable : (prefixWord ++ tailWord_455220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455220).length < 2 ^ (prefixWord ++ tailWord_455220).sum := by decide
  have hdescent : baseEnd_455220 < baseStart_455220 := by decide
  rcases family_descends (prefixWord ++ tailWord_455220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455238 : List Nat := [6, 1, 1, 1, 2, 1, 2, 6]
def baseStart_455238 : Nat := 118140960795 + 455238 * 2 ^ 59
def prefixEnd_455238 : Nat := 4983230072969 + 3 ^ 40 * 455238 * 2
def baseEnd_455238 : Nat := 69261009241954107535231

theorem tailTrace_455238 : CollatzResearch.WordTrace tailWord_455238 prefixEnd_455238 69261009241954107535231 := by
  unfold tailWord_455238
  simp only [CollatzResearch.WordTrace]
  refine ⟨518871685148685915801199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11069262616505299537092245 518871685148685915801199)
  ·
    refine ⟨778307527723028873701799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 518871685148685915801199 778307527723028873701799)
    ·
      refine ⟨1167461291584543310552699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778307527723028873701799 1167461291584543310552699)
      ·
        refine ⟨1751191937376814965829049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167461291584543310552699 1751191937376814965829049)
        ·
          refine ⟨1313393953032611224371787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1751191937376814965829049 1313393953032611224371787)
          ·
            refine ⟨1970090929548916836557681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313393953032611224371787 1970090929548916836557681)
            ·
              refine ⟨1477568197161687627418261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970090929548916836557681 1477568197161687627418261)
              ·
                refine ⟨69261009241954107535231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1477568197161687627418261 69261009241954107535231)
                ·
                  rfl

theorem cell20_455238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_455238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455238 prefixEnd_455238 := by exact prefixLift 455238
  have htrace : WordTrace (prefixWord ++ tailWord_455238) baseStart_455238 baseEnd_455238 := by
    simpa [prefixWord, tailWord_455238, baseEnd_455238] using wordTrace_append hprefix tailTrace_455238
  have hstable : (prefixWord ++ tailWord_455238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455238).length < 2 ^ (prefixWord ++ tailWord_455238).sum := by decide
  have hdescent : baseEnd_455238 < baseStart_455238 := by decide
  rcases family_descends (prefixWord ++ tailWord_455238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455242 : List Nat := [3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_455242 : Nat := 118140960795 + 455242 * 2 ^ 59
def prefixEnd_455242 : Nat := 4983230072969 + 3 ^ 40 * 455242 * 2
def baseEnd_455242 : Nat := 69261617811618695490781

theorem tailTrace_455242 : CollatzResearch.WordTrace tailWord_455242 prefixEnd_455242 69261617811618695490781 := by
  unfold tailWord_455242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4151009954185864497195995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11069359877828971992522653 4151009954185864497195995)
  ·
    refine ⟨6226514931278796745793993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4151009954185864497195995 6226514931278796745793993)
    ·
      refine ⟨4669886198459097559345495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6226514931278796745793993 4669886198459097559345495)
      ·
        refine ⟨7004829297688646339018243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669886198459097559345495 7004829297688646339018243)
        ·
          refine ⟨10507243946532969508527365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004829297688646339018243 10507243946532969508527365)
          ·
            refine ⟨1970108239974931782848881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10507243946532969508527365 1970108239974931782848881)
            ·
              refine ⟨1477581179981198837136661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970108239974931782848881 1477581179981198837136661)
              ·
                refine ⟨69261617811618695490781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1477581179981198837136661 69261617811618695490781)
                ·
                  rfl

theorem cell20_455242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_455242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455242 prefixEnd_455242 := by exact prefixLift 455242
  have htrace : WordTrace (prefixWord ++ tailWord_455242) baseStart_455242 baseEnd_455242 := by
    simpa [prefixWord, tailWord_455242, baseEnd_455242] using wordTrace_append hprefix tailTrace_455242
  have hstable : (prefixWord ++ tailWord_455242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455242).length < 2 ^ (prefixWord ++ tailWord_455242).sum := by decide
  have hdescent : baseEnd_455242 < baseStart_455242 := by decide
  rcases family_descends (prefixWord ++ tailWord_455242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455269 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 2]
def baseStart_455269 : Nat := 118140960795 + 455269 * 2 ^ 59
def prefixEnd_455269 : Nat := 4983230072969 + 3 ^ 40 * 455269 * 2
def baseEnd_455269 : Nat := 207797176970563992572233

theorem tailTrace_455269 : CollatzResearch.WordTrace tailWord_455269 prefixEnd_455269 207797176970563992572233 := by
  unfold tailWord_455269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605024587645641600016861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11070016391763761066677907 16605024587645641600016861)
  ·
    refine ⟨6226884220367115600006323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16605024587645641600016861 6226884220367115600006323)
    ·
      refine ⟨9340326330550673400009485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226884220367115600006323 9340326330550673400009485)
      ·
        refine ⟨3502622373956502525003557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9340326330550673400009485 3502622373956502525003557)
        ·
          refine ⟨656741695116844223438167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3502622373956502525003557 656741695116844223438167)
          ·
            refine ⟨985112542675266335157251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656741695116844223438167 985112542675266335157251)
            ·
              refine ⟨1477668814012899502735877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985112542675266335157251 1477668814012899502735877)
              ·
                refine ⟨277062902627418656762977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1477668814012899502735877 277062902627418656762977)
                ·
                  refine ⟨207797176970563992572233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277062902627418656762977 207797176970563992572233)
                  ·
                    rfl

theorem cell20_455269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_455269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455269 prefixEnd_455269 := by exact prefixLift 455269
  have htrace : WordTrace (prefixWord ++ tailWord_455269) baseStart_455269 baseEnd_455269 := by
    simpa [prefixWord, tailWord_455269, baseEnd_455269] using wordTrace_append hprefix tailTrace_455269
  have hstable : (prefixWord ++ tailWord_455269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455269).length < 2 ^ (prefixWord ++ tailWord_455269).sum := by decide
  have hdescent : baseEnd_455269 < baseStart_455269 := by decide
  rcases family_descends (prefixWord ++ tailWord_455269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455297 : List Nat := [1, 2, 4, 2, 1, 1, 5, 4]
def baseStart_455297 : Nat := 118140960795 + 455297 * 2 ^ 59
def prefixEnd_455297 : Nat := 4983230072969 + 3 ^ 40 * 455297 * 2
def baseEnd_455297 : Nat := 69269985644506779879595

theorem tailTrace_455297 : CollatzResearch.WordTrace tailWord_455297 prefixEnd_455297 69269985644506779879595 := by
  unfold tailWord_455297
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606045831544202382036145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11070697221029468254690763 16606045831544202382036145)
  ·
    refine ⟨12454534373658151786527109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16606045831544202382036145 12454534373658151786527109)
    ·
      refine ⟨2335225195060903459973833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12454534373658151786527109 2335225195060903459973833)
      ·
        refine ⟨1751418896295677594980375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2335225195060903459973833 1751418896295677594980375)
        ·
          refine ⟨2627128344443516392470563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751418896295677594980375 2627128344443516392470563)
          ·
            refine ⟨3940692516665274588705845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627128344443516392470563 3940692516665274588705845)
            ·
              refine ⟨369439923437369492691173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3940692516665274588705845 369439923437369492691173)
              ·
                refine ⟨69269985644506779879595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369439923437369492691173 69269985644506779879595)
                ·
                  rfl

theorem cell20_455297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_455297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455297 prefixEnd_455297 := by exact prefixLift 455297
  have htrace : WordTrace (prefixWord ++ tailWord_455297) baseStart_455297 baseEnd_455297 := by
    simpa [prefixWord, tailWord_455297, baseEnd_455297] using wordTrace_append hprefix tailTrace_455297
  have hstable : (prefixWord ++ tailWord_455297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455297).length < 2 ^ (prefixWord ++ tailWord_455297).sum := by decide
  have hdescent : baseEnd_455297 < baseStart_455297 := by decide
  rcases family_descends (prefixWord ++ tailWord_455297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455328 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_455328 : Nat := 118140960795 + 455328 * 2 ^ 59
def prefixEnd_455328 : Nat := 4983230072969 + 3 ^ 40 * 455328 * 2
def baseEnd_455328 : Nat := 207824106178222009605325

theorem tailTrace_455328 : CollatzResearch.WordTrace tailWord_455328 prefixEnd_455328 207824106178222009605325 := by
  unfold tailWord_455328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303588247215947338207319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11071450996287929784276425 8303588247215947338207319)
  ·
    refine ⟨12455382370823921007310979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8303588247215947338207319 12455382370823921007310979)
    ·
      refine ⟨18683073556235881510966469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455382370823921007310979 18683073556235881510966469)
      ·
        refine ⟨3503076291794227783306213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18683073556235881510966469 3503076291794227783306213)
        ·
          refine ⟨656826804711417709369915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3503076291794227783306213 656826804711417709369915)
          ·
            refine ⟨985240207067126564054873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656826804711417709369915 985240207067126564054873)
            ·
              refine ⟨738930155300344923041155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985240207067126564054873 738930155300344923041155)
              ·
                refine ⟨1108395232950517384561733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738930155300344923041155 1108395232950517384561733)
                ·
                  refine ⟨207824106178222009605325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1108395232950517384561733 207824106178222009605325)
                  ·
                    rfl

theorem cell20_455328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_455328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455328 prefixEnd_455328 := by exact prefixLift 455328
  have htrace : WordTrace (prefixWord ++ tailWord_455328) baseStart_455328 baseEnd_455328 := by
    simpa [prefixWord, tailWord_455328, baseEnd_455328] using wordTrace_append hprefix tailTrace_455328
  have hstable : (prefixWord ++ tailWord_455328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455328).length < 2 ^ (prefixWord ++ tailWord_455328).sum := by decide
  have hdescent : baseEnd_455328 < baseStart_455328 := by decide
  rcases family_descends (prefixWord ++ tailWord_455328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455356 : List Nat := [2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_455356 : Nat := 118140960795 + 455356 * 2 ^ 59
def prefixEnd_455356 : Nat := 4983230072969 + 3 ^ 40 * 455356 * 2
def baseEnd_455356 : Nat := 69278962047059452223959

theorem tailTrace_455356 : CollatzResearch.WordTrace tailWord_455356 prefixEnd_455356 69278962047059452223959 := by
  unfold tailWord_455356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8304098869165227729216961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11072131825553636972289281 8304098869165227729216961)
  ·
    refine ⟨6228074151873920796912721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8304098869165227729216961 6228074151873920796912721)
    ·
      refine ⟨4671055613905440597684541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6228074151873920796912721 4671055613905440597684541)
      ·
        refine ⟨1751645855214540224131703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4671055613905440597684541 1751645855214540224131703)
        ·
          refine ⟨2627468782821810336197555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751645855214540224131703 2627468782821810336197555)
          ·
            refine ⟨3941203174232715504296333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627468782821810336197555 3941203174232715504296333)
            ·
              refine ⟨1477951190337268314111125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3941203174232715504296333 1477951190337268314111125)
              ·
                refine ⟨69278962047059452223959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1477951190337268314111125 69278962047059452223959)
                ·
                  rfl

theorem cell20_455356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_455356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455356 prefixEnd_455356 := by exact prefixLift 455356
  have htrace : WordTrace (prefixWord ++ tailWord_455356) baseStart_455356 baseEnd_455356 := by
    simpa [prefixWord, tailWord_455356, baseEnd_455356] using wordTrace_append hprefix tailTrace_455356
  have hstable : (prefixWord ++ tailWord_455356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455356).length < 2 ^ (prefixWord ++ tailWord_455356).sum := by decide
  have hdescent : baseEnd_455356 < baseStart_455356 := by decide
  rcases family_descends (prefixWord ++ tailWord_455356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455383 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 2]
def baseStart_455383 : Nat := 118140960795 + 455383 * 2 ^ 59
def prefixEnd_455383 : Nat := 4983230072969 + 3 ^ 40 * 455383 * 2
def baseEnd_455383 : Nat := 207849209676886262771767

theorem tailTrace_455383 : CollatzResearch.WordTrace tailWord_455383 prefixEnd_455383 207849209676886262771767 := by
  unfold tailWord_455383
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609182509232639069666803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11072788339488426046444535 16609182509232639069666803)
  ·
    refine ⟨24913773763848958604500205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16609182509232639069666803 24913773763848958604500205)
    ·
      refine ⟨9342665161443359476687577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24913773763848958604500205 9342665161443359476687577)
      ·
        refine ⟨7006998871082519607515683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9342665161443359476687577 7006998871082519607515683)
        ·
          refine ⟨10510498306623779411273525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006998871082519607515683 10510498306623779411273525)
          ·
            refine ⟨985359216245979319806893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10510498306623779411273525 985359216245979319806893)
            ·
              refine ⟨369509706092242244927585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 985359216245979319806893 369509706092242244927585)
              ·
                refine ⟨277132279569181683695689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369509706092242244927585 277132279569181683695689)
                ·
                  refine ⟨207849209676886262771767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277132279569181683695689 207849209676886262771767)
                  ·
                    rfl

theorem cell20_455383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 2].length) (baseStart_455383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455383 prefixEnd_455383 := by exact prefixLift 455383
  have htrace : WordTrace (prefixWord ++ tailWord_455383) baseStart_455383 baseEnd_455383 := by
    simpa [prefixWord, tailWord_455383, baseEnd_455383] using wordTrace_append hprefix tailTrace_455383
  have hstable : (prefixWord ++ tailWord_455383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455383).length < 2 ^ (prefixWord ++ tailWord_455383).sum := by decide
  have hdescent : baseEnd_455383 < baseStart_455383 := by decide
  rcases family_descends (prefixWord ++ tailWord_455383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455397 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 3]
def baseStart_455397 : Nat := 118140960795 + 455397 * 2 ^ 59
def prefixEnd_455397 : Nat := 4983230072969 + 3 ^ 40 * 455397 * 2
def baseEnd_455397 : Nat := 207855599658364436305043

theorem tailTrace_455397 : CollatzResearch.WordTrace tailWord_455397 prefixEnd_455397 207855599658364436305043 := by
  unfold tailWord_455397
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609693131181919460676445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11073128754121279640450963 16609693131181919460676445)
  ·
    refine ⟨6228634924193219797753667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16609693131181919460676445 6228634924193219797753667)
    ·
      refine ⟨9342952386289829696630501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228634924193219797753667 9342952386289829696630501)
      ·
        refine ⟨1751803572429343068118219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9342952386289829696630501 1751803572429343068118219)
        ·
          refine ⟨2627705358644014602177329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751803572429343068118219 2627705358644014602177329)
          ·
            refine ⟨1970779018983010951632997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627705358644014602177329 1970779018983010951632997)
            ·
              refine ⟨369521066059314553431187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1970779018983010951632997 369521066059314553431187)
              ·
                refine ⟨554281599088971830146781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369521066059314553431187 554281599088971830146781)
                ·
                  refine ⟨207855599658364436305043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554281599088971830146781 207855599658364436305043)
                  ·
                    rfl

theorem cell20_455397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_455397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455397 prefixEnd_455397 := by exact prefixLift 455397
  have htrace : WordTrace (prefixWord ++ tailWord_455397) baseStart_455397 baseEnd_455397 := by
    simpa [prefixWord, tailWord_455397, baseEnd_455397] using wordTrace_append hprefix tailTrace_455397
  have hstable : (prefixWord ++ tailWord_455397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455397).length < 2 ^ (prefixWord ++ tailWord_455397).sum := by decide
  have hdescent : baseEnd_455397 < baseStart_455397 := by decide
  rcases family_descends (prefixWord ++ tailWord_455397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455408 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_455408 : Nat := 118140960795 + 455408 * 2 ^ 59
def prefixEnd_455408 : Nat := 4983230072969 + 3 ^ 40 * 455408 * 2
def baseEnd_455408 : Nat := 207860620358097286938331

theorem tailTrace_455408 : CollatzResearch.WordTrace tailWord_455408 prefixEnd_455408 207860620358097286938331 := by
  unfold tailWord_455408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305047167071034169663439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11073396222761378892884585 8305047167071034169663439)
  ·
    refine ⟨12457570750606551254495159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8305047167071034169663439 12457570750606551254495159)
    ·
      refine ⟨18686356125909826881742739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457570750606551254495159 18686356125909826881742739)
      ·
        refine ⟨28029534188864740322614109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18686356125909826881742739 28029534188864740322614109)
        ·
          refine ⟨10511075320824277620980291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28029534188864740322614109 10511075320824277620980291)
          ·
            refine ⟨15766612981236416431470437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511075320824277620980291 15766612981236416431470437)
            ·
              refine ⟨2956239933981828080900707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15766612981236416431470437 2956239933981828080900707)
              ·
                refine ⟨4434359900972742121351061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956239933981828080900707 4434359900972742121351061)
                ·
                  refine ⟨207860620358097286938331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4434359900972742121351061 207860620358097286938331)
                  ·
                    rfl

theorem cell20_455408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_455408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455408 prefixEnd_455408 := by exact prefixLift 455408
  have htrace : WordTrace (prefixWord ++ tailWord_455408) baseStart_455408 baseEnd_455408 := by
    simpa [prefixWord, tailWord_455408, baseEnd_455408] using wordTrace_append hprefix tailTrace_455408
  have hstable : (prefixWord ++ tailWord_455408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455408).length < 2 ^ (prefixWord ++ tailWord_455408).sum := by decide
  have hdescent : baseEnd_455408 < baseStart_455408 := by decide
  rcases family_descends (prefixWord ++ tailWord_455408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455456 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_455456 : Nat := 118140960795 + 455456 * 2 ^ 59
def prefixEnd_455456 : Nat := 4983230072969 + 3 ^ 40 * 455456 * 2
def baseEnd_455456 : Nat := 207882528866022453338135

theorem tailTrace_455456 : CollatzResearch.WordTrace tailWord_455456 prefixEnd_455456 207882528866022453338135 := by
  unfold tailWord_455456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305922518984086268537111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11074563358645448358049481 8305922518984086268537111)
  ·
    refine ⟨12458883778476129402805667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8305922518984086268537111 12458883778476129402805667)
    ·
      refine ⟨18688325667714194104208501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458883778476129402805667 18688325667714194104208501)
      ·
        refine ⟨1752030531348205697269547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18688325667714194104208501 1752030531348205697269547)
        ·
          refine ⟨2628045797022308545904321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752030531348205697269547 2628045797022308545904321)
          ·
            refine ⟨1971034347766731409428241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2628045797022308545904321 1971034347766731409428241)
            ·
              refine ⟨1478275760825048557071181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971034347766731409428241 1478275760825048557071181)
              ·
                refine ⟨554353410309393208901693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1478275760825048557071181 554353410309393208901693)
                ·
                  refine ⟨207882528866022453338135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554353410309393208901693 207882528866022453338135)
                  ·
                    rfl

theorem cell20_455456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_455456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455456 prefixEnd_455456 := by exact prefixLift 455456
  have htrace : WordTrace (prefixWord ++ tailWord_455456) baseStart_455456 baseEnd_455456 := by
    simpa [prefixWord, tailWord_455456, baseEnd_455456] using wordTrace_append hprefix tailTrace_455456
  have hstable : (prefixWord ++ tailWord_455456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455456).length < 2 ^ (prefixWord ++ tailWord_455456).sum := by decide
  have hdescent : baseEnd_455456 < baseStart_455456 := by decide
  rcases family_descends (prefixWord ++ tailWord_455456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455476 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 2]
def baseStart_455476 : Nat := 118140960795 + 455476 * 2 ^ 59
def prefixEnd_455476 : Nat := 4983230072969 + 3 ^ 40 * 455476 * 2
def baseEnd_455476 : Nat := 207891657410991272671387

theorem tailTrace_455476 : CollatzResearch.WordTrace tailWord_455476 prefixEnd_455476 207891657410991272671387 := by
  unfold tailWord_455476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306287248947857976401141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11075049665263810635201521 8306287248947857976401141)
  ·
    refine ⟨778714429588861685287607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8306287248947857976401141 778714429588861685287607)
    ·
      refine ⟨1168071644383292527931411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778714429588861685287607 1168071644383292527931411)
      ·
        refine ⟨1752107466574938791897117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168071644383292527931411 1752107466574938791897117)
        ·
          refine ⟨657040299965602046961419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1752107466574938791897117 657040299965602046961419)
          ·
            refine ⟨985560449948403070442129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657040299965602046961419 985560449948403070442129)
            ·
              refine ⟨739170337461302302831597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985560449948403070442129 739170337461302302831597)
              ·
                refine ⟨277188876547988363561849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739170337461302302831597 277188876547988363561849)
                ·
                  refine ⟨207891657410991272671387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277188876547988363561849 207891657410991272671387)
                  ·
                    rfl

theorem cell20_455476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_455476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455476 prefixEnd_455476 := by exact prefixLift 455476
  have htrace : WordTrace (prefixWord ++ tailWord_455476) baseStart_455476 baseEnd_455476 := by
    simpa [prefixWord, tailWord_455476, baseEnd_455476] using wordTrace_append hprefix tailTrace_455476
  have hstable : (prefixWord ++ tailWord_455476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455476).length < 2 ^ (prefixWord ++ tailWord_455476).sum := by decide
  have hdescent : baseEnd_455476 < baseStart_455476 := by decide
  rcases family_descends (prefixWord ++ tailWord_455476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455480 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 2]
def baseStart_455480 : Nat := 118140960795 + 455480 * 2 ^ 59
def prefixEnd_455480 : Nat := 4983230072969 + 3 ^ 40 * 455480 * 2
def baseEnd_455480 : Nat := 207893483119985036538037

theorem tailTrace_455480 : CollatzResearch.WordTrace tailWord_455480 prefixEnd_455480 207893483119985036538037 := by
  unfold tailWord_455480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306360194940612317973947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11075146926587483090631929 8306360194940612317973947)
  ·
    refine ⟨12459540292410918476960921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8306360194940612317973947 12459540292410918476960921)
    ·
      refine ⟨9344655219308188857720691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12459540292410918476960921 9344655219308188857720691)
      ·
        refine ⟨14016982828962283286581037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9344655219308188857720691 14016982828962283286581037)
        ·
          refine ⟨5256368560860856232467889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14016982828962283286581037 5256368560860856232467889)
          ·
            refine ⟨3942276420645642174350917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256368560860856232467889 3942276420645642174350917)
            ·
              refine ⟨739176828871057907690797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3942276420645642174350917 739176828871057907690797)
              ·
                refine ⟨277191310826646715384049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739176828871057907690797 277191310826646715384049)
                ·
                  refine ⟨207893483119985036538037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277191310826646715384049 207893483119985036538037)
                  ·
                    rfl

theorem cell20_455480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_455480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455480 prefixEnd_455480 := by exact prefixLift 455480
  have htrace : WordTrace (prefixWord ++ tailWord_455480) baseStart_455480 baseEnd_455480 := by
    simpa [prefixWord, tailWord_455480, baseEnd_455480] using wordTrace_append hprefix tailTrace_455480
  have hstable : (prefixWord ++ tailWord_455480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455480).length < 2 ^ (prefixWord ++ tailWord_455480).sum := by decide
  have hdescent : baseEnd_455480 < baseStart_455480 := by decide
  rcases family_descends (prefixWord ++ tailWord_455480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455484 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_455484 : Nat := 118140960795 + 455484 * 2 ^ 59
def prefixEnd_455484 : Nat := 4983230072969 + 3 ^ 40 * 455484 * 2
def baseEnd_455484 : Nat := 207895308828978800404687

theorem tailTrace_455484 : CollatzResearch.WordTrace tailWord_455484 prefixEnd_455484 207895308828978800404687 := by
  unfold tailWord_455484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306433140933366659546753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11075244187911155546062337 8306433140933366659546753)
  ·
    refine ⟨6229824855700024994660065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8306433140933366659546753 6229824855700024994660065)
    ·
      refine ⟨4672368641775018745995049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229824855700024994660065 4672368641775018745995049)
      ·
        refine ⟨3504276481331264059496287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4672368641775018745995049 3504276481331264059496287)
        ·
          refine ⟨5256414721996896089244431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504276481331264059496287 5256414721996896089244431)
          ·
            refine ⟨7884622082995344133866647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256414721996896089244431 7884622082995344133866647)
            ·
              refine ⟨11826933124493016200799971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884622082995344133866647 11826933124493016200799971)
              ·
                refine ⟨17740399686739524301199957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826933124493016200799971 17740399686739524301199957)
                ·
                  refine ⟨207895308828978800404687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17740399686739524301199957 207895308828978800404687)
                  ·
                    rfl

theorem cell20_455484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_455484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455484 prefixEnd_455484 := by exact prefixLift 455484
  have htrace : WordTrace (prefixWord ++ tailWord_455484) baseStart_455484 baseEnd_455484 := by
    simpa [prefixWord, tailWord_455484, baseEnd_455484] using wordTrace_append hprefix tailTrace_455484
  have hstable : (prefixWord ++ tailWord_455484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455484).length < 2 ^ (prefixWord ++ tailWord_455484).sum := by decide
  have hdescent : baseEnd_455484 < baseStart_455484 := by decide
  rcases family_descends (prefixWord ++ tailWord_455484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455491 : List Nat := [1, 1, 1, 3, 1, 4, 9]
def baseStart_455491 : Nat := 118140960795 + 455491 * 2 ^ 59
def prefixEnd_455491 : Nat := 4983230072969 + 3 ^ 40 * 455491 * 2
def baseEnd_455491 : Nat := 23099833757746431907925

theorem tailTrace_455491 : CollatzResearch.WordTrace tailWord_455491 prefixEnd_455491 23099833757746431907925 := by
  unfold tailWord_455491
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613121592841373514598327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11075414395227582343065551 16613121592841373514598327)
  ·
    refine ⟨24919682389262060271897491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16613121592841373514598327 24919682389262060271897491)
    ·
      refine ⟨37379523583893090407846237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24919682389262060271897491 37379523583893090407846237)
      ·
        refine ⟨14017321343959908902942339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37379523583893090407846237 14017321343959908902942339)
        ·
          refine ⟨21025982015939863354413509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14017321343959908902942339 21025982015939863354413509)
          ·
            refine ⟨3942371627988724378952533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21025982015939863354413509 3942371627988724378952533)
            ·
              refine ⟨23099833757746431907925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3942371627988724378952533 23099833757746431907925)
              ·
                rfl

theorem cell20_455491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_455491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455491 prefixEnd_455491 := by exact prefixLift 455491
  have htrace : WordTrace (prefixWord ++ tailWord_455491) baseStart_455491 baseEnd_455491 := by
    simpa [prefixWord, tailWord_455491, baseEnd_455491] using wordTrace_append hprefix tailTrace_455491
  have hstable : (prefixWord ++ tailWord_455491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455491).length < 2 ^ (prefixWord ++ tailWord_455491).sum := by decide
  have hdescent : baseEnd_455491 < baseStart_455491 := by decide
  rcases family_descends (prefixWord ++ tailWord_455491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455511 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 3]
def baseStart_455511 : Nat := 118140960795 + 455511 * 2 ^ 59
def prefixEnd_455511 : Nat := 4983230072969 + 3 ^ 40 * 455511 * 2
def baseEnd_455511 : Nat := 207907632364686706504577

theorem tailTrace_455511 : CollatzResearch.WordTrace tailWord_455511 prefixEnd_455511 207907632364686706504577 := by
  unfold tailWord_455511
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613851052768916930326387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11075900701845944620217591 16613851052768916930326387)
  ·
    refine ⟨24920776579153375395489581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16613851052768916930326387 24920776579153375395489581)
    ·
      refine ⟨9345291217182515773308593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24920776579153375395489581 9345291217182515773308593)
      ·
        refine ⟨7008968412886886829981445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9345291217182515773308593 7008968412886886829981445)
        ·
          refine ⟨1314181577416291280621521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7008968412886886829981445 1314181577416291280621521)
          ·
            refine ⟨985636183062218460466141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314181577416291280621521 985636183062218460466141)
            ·
              refine ⟨369613568648331922674803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 985636183062218460466141 369613568648331922674803)
              ·
                refine ⟨554420352972497884012205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369613568648331922674803 554420352972497884012205)
                ·
                  refine ⟨207907632364686706504577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554420352972497884012205 207907632364686706504577)
                  ·
                    rfl

theorem cell20_455511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_455511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455511 prefixEnd_455511 := by exact prefixLift 455511
  have htrace : WordTrace (prefixWord ++ tailWord_455511) baseStart_455511 baseEnd_455511 := by
    simpa [prefixWord, tailWord_455511, baseEnd_455511] using wordTrace_append hprefix tailTrace_455511
  have hstable : (prefixWord ++ tailWord_455511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455511).length < 2 ^ (prefixWord ++ tailWord_455511).sum := by decide
  have hdescent : baseEnd_455511 < baseStart_455511 := by decide
  rcases family_descends (prefixWord ++ tailWord_455511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455604 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_455604 : Nat := 118140960795 + 455604 * 2 ^ 59
def prefixEnd_455604 : Nat := 4983230072969 + 3 ^ 40 * 455604 * 2
def baseEnd_455604 : Nat := 207950080098791716404197

theorem tailTrace_455604 : CollatzResearch.WordTrace tailWord_455604 prefixEnd_455604 207950080098791716404197 := by
  unfold tailWord_455604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308621520715996906730933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11078162027621329208974577 8308621520715996906730933)
  ·
    refine ⟨778933267567124710006025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8308621520715996906730933 778933267567124710006025)
    ·
      refine ⟨584199950675343532504519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 778933267567124710006025 584199950675343532504519)
      ·
        refine ⟨876299926013015298756779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584199950675343532504519 876299926013015298756779)
        ·
          refine ⟨1314449889019522948135169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876299926013015298756779 1314449889019522948135169)
          ·
            refine ⟨985837416764642211101377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314449889019522948135169 985837416764642211101377)
            ·
              refine ⟨739378062573481658326033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985837416764642211101377 739378062573481658326033)
              ·
                refine ⟨554533546930111243744525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739378062573481658326033 554533546930111243744525)
                ·
                  refine ⟨207950080098791716404197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554533546930111243744525 207950080098791716404197)
                  ·
                    rfl

theorem cell20_455604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_455604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455604 prefixEnd_455604 := by exact prefixLift 455604
  have htrace : WordTrace (prefixWord ++ tailWord_455604) baseStart_455604 baseEnd_455604 := by
    simpa [prefixWord, tailWord_455604, baseEnd_455604] using wordTrace_append hprefix tailTrace_455604
  have hstable : (prefixWord ++ tailWord_455604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455604).length < 2 ^ (prefixWord ++ tailWord_455604).sum := by decide
  have hdescent : baseEnd_455604 < baseStart_455604 := by decide
  rcases family_descends (prefixWord ++ tailWord_455604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455608 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_455608 : Nat := 118140960795 + 455608 * 2 ^ 59
def prefixEnd_455608 : Nat := 4983230072969 + 3 ^ 40 * 455608 * 2
def baseEnd_455608 : Nat := 207951905807785480270847

theorem tailTrace_455608 : CollatzResearch.WordTrace tailWord_455608 prefixEnd_455608 207951905807785480270847 := by
  unfold tailWord_455608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308694466708751248303739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11078259288945001664404985 8308694466708751248303739)
  ·
    refine ⟨12463041700063126872455609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8308694466708751248303739 12463041700063126872455609)
    ·
      refine ⟨9347281275047345154341707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12463041700063126872455609 9347281275047345154341707)
      ·
        refine ⟨14020921912571017731512561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9347281275047345154341707 14020921912571017731512561)
        ·
          refine ⟨10515691434428263298634421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14020921912571017731512561 10515691434428263298634421)
          ·
            refine ⟨985846071977649684246977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10515691434428263298634421 985846071977649684246977)
            ·
              refine ⟨739384553983237263185233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985846071977649684246977 739384553983237263185233)
              ·
                refine ⟨554538415487427947388925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739384553983237263185233 554538415487427947388925)
                ·
                  refine ⟨207951905807785480270847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554538415487427947388925 207951905807785480270847)
                  ·
                    rfl

theorem cell20_455608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_455608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455608 prefixEnd_455608 := by exact prefixLift 455608
  have htrace : WordTrace (prefixWord ++ tailWord_455608) baseStart_455608 baseEnd_455608 := by
    simpa [prefixWord, tailWord_455608, baseEnd_455608] using wordTrace_append hprefix tailTrace_455608
  have hstable : (prefixWord ++ tailWord_455608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455608).length < 2 ^ (prefixWord ++ tailWord_455608).sum := by decide
  have hdescent : baseEnd_455608 < baseStart_455608 := by decide
  rcases family_descends (prefixWord ++ tailWord_455608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455670 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_455670 : Nat := 118140960795 + 455670 * 2 ^ 59
def prefixEnd_455670 : Nat := 4983230072969 + 3 ^ 40 * 455670 * 2
def baseEnd_455670 : Nat := 207980204297188820203927

theorem tailTrace_455670 : CollatzResearch.WordTrace tailWord_455670 prefixEnd_455670 207980204297188820203927 := by
  unfold tailWord_455670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038728141199555442835279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11079766839461924723576309 1038728141199555442835279)
  ·
    refine ⟨1558092211799333164252919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1038728141199555442835279 1558092211799333164252919)
    ·
      refine ⟨2337138317698999746379379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558092211799333164252919 2337138317698999746379379)
      ·
        refine ⟨3505707476548499619569069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337138317698999746379379 3505707476548499619569069)
        ·
          refine ⟨1314640303705687357338401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3505707476548499619569069 1314640303705687357338401)
          ·
            refine ⟨985980227779265518003801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314640303705687357338401 985980227779265518003801)
            ·
              refine ⟨739485170834449138502851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985980227779265518003801 739485170834449138502851)
              ·
                refine ⟨1109227756251673707754277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739485170834449138502851 1109227756251673707754277)
                ·
                  refine ⟨207980204297188820203927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109227756251673707754277 207980204297188820203927)
                  ·
                    rfl

theorem cell20_455670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_455670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455670 prefixEnd_455670 := by exact prefixLift 455670
  have htrace : WordTrace (prefixWord ++ tailWord_455670) baseStart_455670 baseEnd_455670 := by
    simpa [prefixWord, tailWord_455670, baseEnd_455670] using wordTrace_append hprefix tailTrace_455670
  have hstable : (prefixWord ++ tailWord_455670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455670).length < 2 ^ (prefixWord ++ tailWord_455670).sum := by decide
  have hdescent : baseEnd_455670 < baseStart_455670 := by decide
  rcases family_descends (prefixWord ++ tailWord_455670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455736 : List Nat := [2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_455736 : Nat := 118140960795 + 455736 * 2 ^ 59
def prefixEnd_455736 : Nat := 4983230072969 + 3 ^ 40 * 455736 * 2
def baseEnd_455736 : Nat := 69336776165195308001219

theorem tailTrace_455736 : CollatzResearch.WordTrace tailWord_455736 prefixEnd_455736 69336776165195308001219 := by
  unfold tailWord_455736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311028738476890178633531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11081371651302520238178041 8311028738476890178633531)
  ·
    refine ⟨12466543107715335267950297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8311028738476890178633531 12466543107715335267950297)
    ·
      refine ⟨9349907330786501450962723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12466543107715335267950297 9349907330786501450962723)
      ·
        refine ⟨14024860996179752176444085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349907330786501450962723 14024860996179752176444085)
        ·
          refine ⟨1314830718391851766541633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14024860996179752176444085 1314830718391851766541633)
          ·
            refine ⟨986123038793888824906225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314830718391851766541633 986123038793888824906225)
            ·
              refine ⟨739592279095416618679669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986123038793888824906225 739592279095416618679669)
              ·
                refine ⟨69336776165195308001219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 739592279095416618679669 69336776165195308001219)
                ·
                  rfl

theorem cell20_455736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_455736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455736 prefixEnd_455736 := by exact prefixLift 455736
  have htrace : WordTrace (prefixWord ++ tailWord_455736) baseStart_455736 baseEnd_455736 := by
    simpa [prefixWord, tailWord_455736, baseEnd_455736] using wordTrace_append hprefix tailTrace_455736
  have hstable : (prefixWord ++ tailWord_455736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455736).length < 2 ^ (prefixWord ++ tailWord_455736).sum := by decide
  have hdescent : baseEnd_455736 < baseStart_455736 := by decide
  rcases family_descends (prefixWord ++ tailWord_455736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455767 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 2]
def baseStart_455767 : Nat := 118140960795 + 455767 * 2 ^ 59
def prefixEnd_455767 : Nat := 4983230072969 + 3 ^ 40 * 455767 * 2
def baseEnd_455767 : Nat := 208024477740287593970197

theorem tailTrace_455767 : CollatzResearch.WordTrace tailWord_455767 prefixEnd_455767 208024477740287593970197 := by
  unfold tailWord_455767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623188139841472651645555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11082125426560981767763703 16623188139841472651645555)
  ·
    refine ⟨24934782209762208977468333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16623188139841472651645555 24934782209762208977468333)
    ·
      refine ⟨9350543328660828366550625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24934782209762208977468333 9350543328660828366550625)
      ·
        refine ⟨7012907496495621274912969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9350543328660828366550625 7012907496495621274912969)
        ·
          refine ⟨5259680622371715956184727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7012907496495621274912969 5259680622371715956184727)
          ·
            refine ⟨7889520933557573934277091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259680622371715956184727 7889520933557573934277091)
            ·
              refine ⟨11834281400336360901415637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889520933557573934277091 11834281400336360901415637)
              ·
                refine ⟨277365970320383458626929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11834281400336360901415637 277365970320383458626929)
                ·
                  refine ⟨208024477740287593970197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277365970320383458626929 208024477740287593970197)
                  ·
                    rfl

theorem cell20_455767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 2].length) (baseStart_455767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455767 prefixEnd_455767 := by exact prefixLift 455767
  have htrace : WordTrace (prefixWord ++ tailWord_455767) baseStart_455767 baseEnd_455767 := by
    simpa [prefixWord, tailWord_455767, baseEnd_455767] using wordTrace_append hprefix tailTrace_455767
  have hstable : (prefixWord ++ tailWord_455767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455767).length < 2 ^ (prefixWord ++ tailWord_455767).sum := by decide
  have hdescent : baseEnd_455767 < baseStart_455767 := by decide
  rcases family_descends (prefixWord ++ tailWord_455767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455788 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_455788 : Nat := 118140960795 + 455788 * 2 ^ 59
def prefixEnd_455788 : Nat := 4983230072969 + 3 ^ 40 * 455788 * 2
def baseEnd_455788 : Nat := 208034062712504854270111

theorem tailTrace_455788 : CollatzResearch.WordTrace tailWord_455788 prefixEnd_455788 208034062712504854270111 := by
  unfold tailWord_455788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311977036382696619080009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11082636048510262158773345 8311977036382696619080009)
  ·
    refine ⟨6233982777287022464310007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8311977036382696619080009 6233982777287022464310007)
    ·
      refine ⟨9350974165930533696465011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233982777287022464310007 9350974165930533696465011)
      ·
        refine ⟨14026461248895800544697517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350974165930533696465011 14026461248895800544697517)
        ·
          refine ⟨5259922968335925204261569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14026461248895800544697517 5259922968335925204261569)
          ·
            refine ⟨3944942226251943903196177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5259922968335925204261569 3944942226251943903196177)
            ·
              refine ⟨2958706669688957927397133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3944942226251943903196177 2958706669688957927397133)
              ·
                refine ⟨1109515001133359222773925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2958706669688957927397133 1109515001133359222773925)
                ·
                  refine ⟨208034062712504854270111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109515001133359222773925 208034062712504854270111)
                  ·
                    rfl

theorem cell20_455788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_455788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455788 prefixEnd_455788 := by exact prefixLift 455788
  have htrace : WordTrace (prefixWord ++ tailWord_455788) baseStart_455788 baseEnd_455788 := by
    simpa [prefixWord, tailWord_455788, baseEnd_455788] using wordTrace_append hprefix tailTrace_455788
  have hstable : (prefixWord ++ tailWord_455788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455788).length < 2 ^ (prefixWord ++ tailWord_455788).sum := by decide
  have hdescent : baseEnd_455788 < baseStart_455788 := by decide
  rcases family_descends (prefixWord ++ tailWord_455788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455798 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_455798 : Nat := 118140960795 + 455798 * 2 ^ 59
def prefixEnd_455798 : Nat := 4983230072969 + 3 ^ 40 * 455798 * 2
def baseEnd_455798 : Nat := 208038626984989263936737

theorem tailTrace_455798 : CollatzResearch.WordTrace tailWord_455798 prefixEnd_455798 208038626984989263936737 := by
  unfold tailWord_455798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039019925170572809126503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11082879201819443297349365 1039019925170572809126503)
  ·
    refine ⟨1558529887755859213689755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039019925170572809126503 1558529887755859213689755)
    ·
      refine ⟨2337794831633788820534633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558529887755859213689755 2337794831633788820534633)
      ·
        refine ⟨1753346123725341615400975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337794831633788820534633 1753346123725341615400975)
        ·
          refine ⟨2630019185588012423101463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753346123725341615400975 2630019185588012423101463)
          ·
            refine ⟨3945028778382018634652195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630019185588012423101463 3945028778382018634652195)
            ·
              refine ⟨5917543167573027951978293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945028778382018634652195 5917543167573027951978293)
              ·
                refine ⟨554769671959971370497965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5917543167573027951978293 554769671959971370497965)
                ·
                  refine ⟨208038626984989263936737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554769671959971370497965 208038626984989263936737)
                  ·
                    rfl

theorem cell20_455798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_455798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455798 prefixEnd_455798 := by exact prefixLift 455798
  have htrace : WordTrace (prefixWord ++ tailWord_455798) baseStart_455798 baseEnd_455798 := by
    simpa [prefixWord, tailWord_455798, baseEnd_455798] using wordTrace_append hprefix tailTrace_455798
  have hstable : (prefixWord ++ tailWord_455798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455798).length < 2 ^ (prefixWord ++ tailWord_455798).sum := by decide
  have hdescent : baseEnd_455798 < baseStart_455798 := by decide
  rcases family_descends (prefixWord ++ tailWord_455798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455822 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_455822 : Nat := 118140960795 + 455822 * 2 ^ 59
def prefixEnd_455822 : Nat := 4983230072969 + 3 ^ 40 * 455822 * 2
def baseEnd_455822 : Nat := 208049581238951847136639

theorem tailTrace_455822 : CollatzResearch.WordTrace tailWord_455822 prefixEnd_455822 208049581238951847136639 := by
  unfold tailWord_455822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078149269330277130612215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11083462769761478029931813 2078149269330277130612215)
  ·
    refine ⟨3117223903995415695918323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078149269330277130612215 3117223903995415695918323)
    ·
      refine ⟨4675835855993123543877485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117223903995415695918323 4675835855993123543877485)
      ·
        refine ⟨1753438445997421328954057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4675835855993123543877485 1753438445997421328954057)
        ·
          refine ⟨1315078834498065996715543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753438445997421328954057 1315078834498065996715543)
          ·
            refine ⟨1972618251747098995073315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315078834498065996715543 1972618251747098995073315)
            ·
              refine ⟨2958927377620648492609973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972618251747098995073315 2958927377620648492609973)
              ·
                refine ⟨277399441651935796182185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2958927377620648492609973 277399441651935796182185)
                ·
                  refine ⟨208049581238951847136639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277399441651935796182185 208049581238951847136639)
                  ·
                    rfl

theorem cell20_455822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_455822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455822 prefixEnd_455822 := by exact prefixLift 455822
  have htrace : WordTrace (prefixWord ++ tailWord_455822) baseStart_455822 baseEnd_455822 := by
    simpa [prefixWord, tailWord_455822, baseEnd_455822] using wordTrace_append hprefix tailTrace_455822
  have hstable : (prefixWord ++ tailWord_455822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455822).length < 2 ^ (prefixWord ++ tailWord_455822).sum := by decide
  have hdescent : baseEnd_455822 < baseStart_455822 := by decide
  rcases family_descends (prefixWord ++ tailWord_455822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455836 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_455836 : Nat := 118140960795 + 455836 * 2 ^ 59
def prefixEnd_455836 : Nat := 4983230072969 + 3 ^ 40 * 455836 * 2
def baseEnd_455836 : Nat := 208055971220430020669915

theorem tailTrace_455836 : CollatzResearch.WordTrace tailWord_455836 prefixEnd_455836 208055971220430020669915 := by
  unfold tailWord_455836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312852388295748717953681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11083803184394331623938241 8312852388295748717953681)
  ·
    refine ⟨6234639291221811538465261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8312852388295748717953681 6234639291221811538465261)
    ·
      refine ⟨2337989734208179326924473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6234639291221811538465261 2337989734208179326924473)
      ·
        refine ⟨1753492300656134495193355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337989734208179326924473 1753492300656134495193355)
        ·
          refine ⟨2630238450984201742790033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753492300656134495193355 2630238450984201742790033)
          ·
            refine ⟨1972678838238151307092525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2630238450984201742790033 1972678838238151307092525)
            ·
              refine ⟨739754564339306740159697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1972678838238151307092525 739754564339306740159697)
              ·
                refine ⟨554815923254480055119773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739754564339306740159697 554815923254480055119773)
                ·
                  refine ⟨208055971220430020669915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554815923254480055119773 208055971220430020669915)
                  ·
                    rfl

theorem cell20_455836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_455836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455836 prefixEnd_455836 := by exact prefixLift 455836
  have htrace : WordTrace (prefixWord ++ tailWord_455836) baseStart_455836 baseEnd_455836 := by
    simpa [prefixWord, tailWord_455836, baseEnd_455836] using wordTrace_append hprefix tailTrace_455836
  have hstable : (prefixWord ++ tailWord_455836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455836).length < 2 ^ (prefixWord ++ tailWord_455836).sum := by decide
  have hdescent : baseEnd_455836 < baseStart_455836 := by decide
  rcases family_descends (prefixWord ++ tailWord_455836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455894 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_455894 : Nat := 118140960795 + 455894 * 2 ^ 59
def prefixEnd_455894 : Nat := 4983230072969 + 3 ^ 40 * 455894 * 2
def baseEnd_455894 : Nat := 208082444000839596736345

theorem tailTrace_455894 : CollatzResearch.WordTrace tailWord_455894 prefixEnd_455894 208082444000839596736345 := by
  unfold tailWord_455894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039238763148835833844921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11085213473587582227679157 1039238763148835833844921)
  ·
    refine ⟨779429072361626875383691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1039238763148835833844921 779429072361626875383691)
    ·
      refine ⟨1169143608542440313075537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779429072361626875383691 1169143608542440313075537)
      ·
        refine ⟨876857706406830234806653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1169143608542440313075537 876857706406830234806653)
        ·
          refine ⟨328821639902561338052495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 876857706406830234806653 328821639902561338052495)
          ·
            refine ⟨493232459853842007078743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328821639902561338052495 493232459853842007078743)
            ·
              refine ⟨739848689780763010618115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493232459853842007078743 739848689780763010618115)
              ·
                refine ⟨1109773034671144515927173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739848689780763010618115 1109773034671144515927173)
                ·
                  refine ⟨208082444000839596736345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109773034671144515927173 208082444000839596736345)
                  ·
                    rfl

theorem cell20_455894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_455894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455894 prefixEnd_455894 := by exact prefixLift 455894
  have htrace : WordTrace (prefixWord ++ tailWord_455894) baseStart_455894 baseEnd_455894 := by
    simpa [prefixWord, tailWord_455894, baseEnd_455894] using wordTrace_append hprefix tailTrace_455894
  have hstable : (prefixWord ++ tailWord_455894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455894).length < 2 ^ (prefixWord ++ tailWord_455894).sum := by decide
  have hdescent : baseEnd_455894 < baseStart_455894 := by decide
  rcases family_descends (prefixWord ++ tailWord_455894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455950 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_455950 : Nat := 118140960795 + 455950 * 2 ^ 59
def prefixEnd_455950 : Nat := 4983230072969 + 3 ^ 40 * 455950 * 2
def baseEnd_455950 : Nat := 208108003926752290869449

theorem tailTrace_455950 : CollatzResearch.WordTrace tailWord_455950 prefixEnd_455950 208108003926752290869449 := by
  unfold tailWord_455950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078732837272311863194663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11086575132118996603704869 2078732837272311863194663)
  ·
    refine ⟨3118099255908467794791995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078732837272311863194663 3118099255908467794791995)
    ·
      refine ⟨4677148883862701692187993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3118099255908467794791995 4677148883862701692187993)
      ·
        refine ⟨3507861662897026269140995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4677148883862701692187993 3507861662897026269140995)
        ·
          refine ⟨5261792494345539403711493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507861662897026269140995 5261792494345539403711493)
          ·
            refine ⟨986586092689788638195905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5261792494345539403711493 986586092689788638195905)
            ·
              refine ⟨739939569517341478646929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986586092689788638195905 739939569517341478646929)
              ·
                refine ⟨554954677138006108985197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739939569517341478646929 554954677138006108985197)
                ·
                  refine ⟨208108003926752290869449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554954677138006108985197 208108003926752290869449)
                  ·
                    rfl

theorem cell20_455950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_455950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455950 prefixEnd_455950 := by exact prefixLift 455950
  have htrace : WordTrace (prefixWord ++ tailWord_455950) baseStart_455950 baseEnd_455950 := by
    simpa [prefixWord, tailWord_455950, baseEnd_455950] using wordTrace_append hprefix tailTrace_455950
  have hstable : (prefixWord ++ tailWord_455950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455950).length < 2 ^ (prefixWord ++ tailWord_455950).sum := by decide
  have hdescent : baseEnd_455950 < baseStart_455950 := by decide
  rcases family_descends (prefixWord ++ tailWord_455950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455961 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_455961 : Nat := 118140960795 + 455961 * 2 ^ 59
def prefixEnd_455961 : Nat := 4983230072969 + 3 ^ 40 * 455961 * 2
def baseEnd_455961 : Nat := 208113024626485141502737

theorem tailTrace_455961 : CollatzResearch.WordTrace tailWord_455961 prefixEnd_455961 208113024626485141502737 := by
  unfold tailWord_455961
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630263901138643784207737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11086842600759095856138491 16630263901138643784207737)
  ·
    refine ⟨12472697925853982838155803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16630263901138643784207737 12472697925853982838155803)
    ·
      refine ⟨18709046888780974257233705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12472697925853982838155803 18709046888780974257233705)
      ·
        refine ⟨14031785166585730692925279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18709046888780974257233705 14031785166585730692925279)
        ·
          refine ⟨21047677749878596039387919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14031785166585730692925279 21047677749878596039387919)
          ·
            refine ⟨31571516624817894059081879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21047677749878596039387919 31571516624817894059081879)
            ·
              refine ⟨47357274937226841088622819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31571516624817894059081879 47357274937226841088622819)
              ·
                refine ⟨71035912405840261632934229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47357274937226841088622819 71035912405840261632934229)
                ·
                  refine ⟨208113024626485141502737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71035912405840261632934229 208113024626485141502737)
                  ·
                    rfl

theorem cell20_455961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_455961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455961 prefixEnd_455961 := by exact prefixLift 455961
  have htrace : WordTrace (prefixWord ++ tailWord_455961) baseStart_455961 baseEnd_455961 := by
    simpa [prefixWord, tailWord_455961, baseEnd_455961] using wordTrace_append hprefix tailTrace_455961
  have hstable : (prefixWord ++ tailWord_455961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455961).length < 2 ^ (prefixWord ++ tailWord_455961).sum := by decide
  have hdescent : baseEnd_455961 < baseStart_455961 := by decide
  rcases family_descends (prefixWord ++ tailWord_455961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455971 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_455971 : Nat := 118140960795 + 455971 * 2 ^ 59
def prefixEnd_455971 : Nat := 4983230072969 + 3 ^ 40 * 455971 * 2
def baseEnd_455971 : Nat := 208117588898969551169363

theorem tailTrace_455971 : CollatzResearch.WordTrace tailWord_455971 prefixEnd_455971 208117588898969551169363 := by
  unfold tailWord_455971
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630628631102415492071767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11087085754068276994714511 16630628631102415492071767)
  ·
    refine ⟨24945942946653623238107651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16630628631102415492071767 24945942946653623238107651)
    ·
      refine ⟨37418914419980434857161477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24945942946653623238107651 37418914419980434857161477)
      ·
        refine ⟨7016046453746331535717777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37418914419980434857161477 7016046453746331535717777)
        ·
          refine ⟨5262034840309748651788333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7016046453746331535717777 5262034840309748651788333)
          ·
            refine ⟨1973263065116155744420625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5262034840309748651788333 1973263065116155744420625)
            ·
              refine ⟨1479947298837116808315469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973263065116155744420625 1479947298837116808315469)
              ·
                refine ⟨554980237063918803118301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479947298837116808315469 554980237063918803118301)
                ·
                  refine ⟨208117588898969551169363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554980237063918803118301 208117588898969551169363)
                  ·
                    rfl

theorem cell20_455971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_455971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455971 prefixEnd_455971 := by exact prefixLift 455971
  have htrace : WordTrace (prefixWord ++ tailWord_455971) baseStart_455971 baseEnd_455971 := by
    simpa [prefixWord, tailWord_455971, baseEnd_455971] using wordTrace_append hprefix tailTrace_455971
  have hstable : (prefixWord ++ tailWord_455971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455971).length < 2 ^ (prefixWord ++ tailWord_455971).sum := by decide
  have hdescent : baseEnd_455971 < baseStart_455971 := by decide
  rcases family_descends (prefixWord ++ tailWord_455971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455992 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_455992 : Nat := 118140960795 + 455992 * 2 ^ 59
def prefixEnd_455992 : Nat := 4983230072969 + 3 ^ 40 * 455992 * 2
def baseEnd_455992 : Nat := 208127173871186811469277

theorem tailTrace_455992 : CollatzResearch.WordTrace tailWord_455992 prefixEnd_455992 208127173871186811469277 := by
  unfold tailWord_455992
  simp only [CollatzResearch.WordTrace]
  refine ⟨8315697282013168039293115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11087596376017557385724153 8315697282013168039293115)
  ·
    refine ⟨12473545923019752058939673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8315697282013168039293115 12473545923019752058939673)
    ·
      refine ⟨9355159442264814044204755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12473545923019752058939673 9355159442264814044204755)
      ·
        refine ⟨14032739163397221066307133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9355159442264814044204755 14032739163397221066307133)
        ·
          refine ⟨5262277186273957899865175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14032739163397221066307133 5262277186273957899865175)
          ·
            refine ⟨7893415779410936849797763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262277186273957899865175 7893415779410936849797763)
            ·
              refine ⟨11840123669116405274696645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893415779410936849797763 11840123669116405274696645)
              ·
                refine ⟨2220023187959325989005621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11840123669116405274696645 2220023187959325989005621)
                ·
                  refine ⟨208127173871186811469277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2220023187959325989005621 208127173871186811469277)
                  ·
                    rfl

theorem cell20_455992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_455992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_455992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_455992 prefixEnd_455992 := by exact prefixLift 455992
  have htrace : WordTrace (prefixWord ++ tailWord_455992) baseStart_455992 baseEnd_455992 := by
    simpa [prefixWord, tailWord_455992, baseEnd_455992] using wordTrace_append hprefix tailTrace_455992
  have hstable : (prefixWord ++ tailWord_455992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455992).length < 2 ^ (prefixWord ++ tailWord_455992).sum := by decide
  have hdescent : baseEnd_455992 < baseStart_455992 := by decide
  rcases family_descends (prefixWord ++ tailWord_455992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456009 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_456009 : Nat := 118140960795 + 456009 * 2 ^ 59
def prefixEnd_456009 : Nat := 4983230072969 + 3 ^ 40 * 456009 * 2
def baseEnd_456009 : Nat := 208134933134410307902541

theorem tailTrace_456009 : CollatzResearch.WordTrace tailWord_456009 prefixEnd_456009 208134933134410307902541 := by
  unfold tailWord_456009
  simp only [CollatzResearch.WordTrace]
  refine ⟨16632014604964747981955081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11088009736643165321303387 16632014604964747981955081)
  ·
    refine ⟨12474010953723560986466311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16632014604964747981955081 12474010953723560986466311)
    ·
      refine ⟨18711016430585341479699467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474010953723560986466311 18711016430585341479699467)
      ·
        refine ⟨28066524645878012219549201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18711016430585341479699467 28066524645878012219549201)
        ·
          refine ⟨21049893484408509164661901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28066524645878012219549201 21049893484408509164661901)
          ·
            refine ⟨7893710056653190936748213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21049893484408509164661901 7893710056653190936748213)
            ·
              refine ⟨740035317811236650320145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7893710056653190936748213 740035317811236650320145)
              ·
                refine ⟨555026488358427487740109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740035317811236650320145 555026488358427487740109)
                ·
                  refine ⟨208134933134410307902541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555026488358427487740109 208134933134410307902541)
                  ·
                    rfl

theorem cell20_456009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_456009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456009 prefixEnd_456009 := by exact prefixLift 456009
  have htrace : WordTrace (prefixWord ++ tailWord_456009) baseStart_456009 baseEnd_456009 := by
    simpa [prefixWord, tailWord_456009, baseEnd_456009] using wordTrace_append hprefix tailTrace_456009
  have hstable : (prefixWord ++ tailWord_456009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456009).length < 2 ^ (prefixWord ++ tailWord_456009).sum := by decide
  have hdescent : baseEnd_456009 < baseStart_456009 := by decide
  rcases family_descends (prefixWord ++ tailWord_456009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456016 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_456016 : Nat := 118140960795 + 456016 * 2 ^ 59
def prefixEnd_456016 : Nat := 4983230072969 + 3 ^ 40 * 456016 * 2
def baseEnd_456016 : Nat := 208138128125149394669179

theorem tailTrace_456016 : CollatzResearch.WordTrace tailWord_456016 prefixEnd_456016 208138128125149394669179 := by
  unfold tailWord_456016
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316134957969694088729951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11088179943959592118306601 8316134957969694088729951)
  ·
    refine ⟨12474202436954541133094927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316134957969694088729951 12474202436954541133094927)
    ·
      refine ⟨18711303655431811699642391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474202436954541133094927 18711303655431811699642391)
      ·
        refine ⟨28066955483147717549463587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18711303655431811699642391 28066955483147717549463587)
        ·
          refine ⟨42100433224721576324195381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28066955483147717549463587 42100433224721576324195381)
          ·
            refine ⟨3946915614817647780393317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42100433224721576324195381 3946915614817647780393317)
            ·
              refine ⟨740046677778308958823747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3946915614817647780393317 740046677778308958823747)
              ·
                refine ⟨1110070016667463438235621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740046677778308958823747 1110070016667463438235621)
                ·
                  refine ⟨208138128125149394669179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110070016667463438235621 208138128125149394669179)
                  ·
                    rfl

theorem cell20_456016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_456016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456016 prefixEnd_456016 := by exact prefixLift 456016
  have htrace : WordTrace (prefixWord ++ tailWord_456016) baseStart_456016 baseEnd_456016 := by
    simpa [prefixWord, tailWord_456016, baseEnd_456016] using wordTrace_append hprefix tailTrace_456016
  have hstable : (prefixWord ++ tailWord_456016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456016).length < 2 ^ (prefixWord ++ tailWord_456016).sum := by decide
  have hdescent : baseEnd_456016 < baseStart_456016 := by decide
  rcases family_descends (prefixWord ++ tailWord_456016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456040 : List Nat := [2, 1, 4, 2, 3, 1, 1, 6]
def baseStart_456040 : Nat := 118140960795 + 456040 * 2 ^ 59
def prefixEnd_456040 : Nat := 4983230072969 + 3 ^ 40 * 456040 * 2
def baseEnd_456040 : Nat := 69383027459703992623027

theorem tailTrace_456040 : CollatzResearch.WordTrace tailWord_456040 prefixEnd_456040 69383027459703992623027 := by
  unfold tailWord_456040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316572633926220138166787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11088763511901626850889049 8316572633926220138166787)
  ·
    refine ⟨12474858950889330207250181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316572633926220138166787 12474858950889330207250181)
    ·
      refine ⟨2339036053291749413859409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12474858950889330207250181 2339036053291749413859409)
      ·
        refine ⟨1754277039968812060394557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339036053291749413859409 1754277039968812060394557)
        ·
          refine ⟨657853889988304522647959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1754277039968812060394557 657853889988304522647959)
          ·
            refine ⟨986780834982456783971939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657853889988304522647959 986780834982456783971939)
            ·
              refine ⟨1480171252473685175957909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986780834982456783971939 1480171252473685175957909)
              ·
                refine ⟨69383027459703992623027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1480171252473685175957909 69383027459703992623027)
                ·
                  rfl

theorem cell20_456040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_456040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456040 prefixEnd_456040 := by exact prefixLift 456040
  have htrace : WordTrace (prefixWord ++ tailWord_456040) baseStart_456040 baseEnd_456040 := by
    simpa [prefixWord, tailWord_456040, baseEnd_456040] using wordTrace_append hprefix tailTrace_456040
  have hstable : (prefixWord ++ tailWord_456040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456040).length < 2 ^ (prefixWord ++ tailWord_456040).sum := by decide
  have hdescent : baseEnd_456040 < baseStart_456040 := by decide
  rcases family_descends (prefixWord ++ tailWord_456040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456046 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_456046 : Nat := 118140960795 + 456046 * 2 ^ 59
def prefixEnd_456046 : Nat := 4983230072969 + 3 ^ 40 * 456046 * 2
def baseEnd_456046 : Nat := 208151820942602623669057

theorem tailTrace_456046 : CollatzResearch.WordTrace tailWord_456046 prefixEnd_456046 208151820942602623669057 := by
  unfold tailWord_456046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079170513228837912631499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11088909403887135534034661 2079170513228837912631499)
  ·
    refine ⟨3118755769843256868947249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2079170513228837912631499 3118755769843256868947249)
    ·
      refine ⟨2339066827382442651710437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3118755769843256868947249 2339066827382442651710437)
      ·
        refine ⟨438575030134207997195707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2339066827382442651710437 438575030134207997195707)
        ·
          refine ⟨657862545201311995793561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438575030134207997195707 657862545201311995793561)
          ·
            refine ⟨493396908900983996845171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657862545201311995793561 493396908900983996845171)
            ·
              refine ⟨740095363351475995267757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493396908900983996845171 740095363351475995267757)
              ·
                refine ⟨277535761256803498225409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 740095363351475995267757 277535761256803498225409)
                ·
                  refine ⟨208151820942602623669057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277535761256803498225409 208151820942602623669057)
                  ·
                    rfl

theorem cell20_456046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_456046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456046 prefixEnd_456046 := by exact prefixLift 456046
  have htrace : WordTrace (prefixWord ++ tailWord_456046) baseStart_456046 baseEnd_456046 := by
    simpa [prefixWord, tailWord_456046, baseEnd_456046] using wordTrace_append hprefix tailTrace_456046
  have hstable : (prefixWord ++ tailWord_456046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456046).length < 2 ^ (prefixWord ++ tailWord_456046).sum := by decide
  have hdescent : baseEnd_456046 < baseStart_456046 := by decide
  rcases family_descends (prefixWord ++ tailWord_456046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456071 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 4]
def baseStart_456071 : Nat := 118140960795 + 456071 * 2 ^ 59
def prefixEnd_456071 : Nat := 4983230072969 + 3 ^ 40 * 456071 * 2
def baseEnd_456071 : Nat := 208163231623813647835621

theorem tailTrace_456071 : CollatzResearch.WordTrace tailWord_456071 prefixEnd_456071 208163231623813647835621 := by
  unfold tailWord_456071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634275930740132570712067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11089517287160088380474711 16634275930740132570712067)
  ·
    refine ⟨24951413896110198856068101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16634275930740132570712067 24951413896110198856068101)
    ·
      refine ⟨4678390105520662285512769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24951413896110198856068101 4678390105520662285512769)
      ·
        refine ⟨3508792579140496714134577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4678390105520662285512769 3508792579140496714134577)
        ·
          refine ⟨2631594434355372535600933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3508792579140496714134577 2631594434355372535600933)
          ·
            refine ⟨493423956441632350425175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2631594434355372535600933 493423956441632350425175)
            ·
              refine ⟨740135934662448525637763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493423956441632350425175 740135934662448525637763)
              ·
                refine ⟨1110203901993672788456645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740135934662448525637763 1110203901993672788456645)
                ·
                  refine ⟨208163231623813647835621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110203901993672788456645 208163231623813647835621)
                  ·
                    rfl

theorem cell20_456071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_456071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456071 prefixEnd_456071 := by exact prefixLift 456071
  have htrace : WordTrace (prefixWord ++ tailWord_456071) baseStart_456071 baseEnd_456071 := by
    simpa [prefixWord, tailWord_456071, baseEnd_456071] using wordTrace_append hprefix tailTrace_456071
  have hstable : (prefixWord ++ tailWord_456071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456071).length < 2 ^ (prefixWord ++ tailWord_456071).sum := by decide
  have hdescent : baseEnd_456071 < baseStart_456071 := by decide
  rcases family_descends (prefixWord ++ tailWord_456071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456154 : List Nat := [3, 1, 1, 2, 3, 3, 3, 4]
def baseStart_456154 : Nat := 118140960795 + 456154 * 2 ^ 59
def prefixEnd_456154 : Nat := 4983230072969 + 3 ^ 40 * 456154 * 2
def baseEnd_456154 : Nat := 69400371695144749356205

theorem tailTrace_456154 : CollatzResearch.WordTrace tailWord_456154 prefixEnd_456154 69400371695144749356205 := by
  unfold tailWord_456154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159325797359859436495879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11091535459626291830655677 4159325797359859436495879)
  ·
    refine ⟨6238988696039789154743819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4159325797359859436495879 6238988696039789154743819)
    ·
      refine ⟨9358483044059683732115729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6238988696039789154743819 9358483044059683732115729)
      ·
        refine ⟨7018862283044762799086797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9358483044059683732115729 7018862283044762799086797)
        ·
          refine ⟨2632073356141786049657549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7018862283044762799086797 2632073356141786049657549)
          ·
            refine ⟨987027508553169768621581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2632073356141786049657549 987027508553169768621581)
            ·
              refine ⟨370135315707438663233093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987027508553169768621581 370135315707438663233093)
              ·
                refine ⟨69400371695144749356205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370135315707438663233093 69400371695144749356205)
                ·
                  rfl

theorem cell20_456154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_456154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456154 prefixEnd_456154 := by exact prefixLift 456154
  have htrace : WordTrace (prefixWord ++ tailWord_456154) baseStart_456154 baseEnd_456154 := by
    simpa [prefixWord, tailWord_456154, baseEnd_456154] using wordTrace_append hprefix tailTrace_456154
  have hstable : (prefixWord ++ tailWord_456154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456154).length < 2 ^ (prefixWord ++ tailWord_456154).sum := by decide
  have hdescent : baseEnd_456154 < baseStart_456154 := by decide
  rcases family_descends (prefixWord ++ tailWord_456154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456178 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_456178 : Nat := 118140960795 + 456178 * 2 ^ 59
def prefixEnd_456178 : Nat := 4983230072969 + 3 ^ 40 * 456178 * 2
def baseEnd_456178 : Nat := 208212069339396831268517

theorem tailTrace_456178 : CollatzResearch.WordTrace tailWord_456178 prefixEnd_456178 208212069339396831268517 := by
  unfold tailWord_456178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159544635338122461214297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11092119027568326563238125 4159544635338122461214297)
  ·
    refine ⟨3119658476503591845910723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4159544635338122461214297 3119658476503591845910723)
    ·
      refine ⟨4679487714755387768866085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119658476503591845910723 4679487714755387768866085)
      ·
        refine ⟨877403946516635206662391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4679487714755387768866085 877403946516635206662391)
        ·
          refine ⟨1316105919774952809993587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877403946516635206662391 1316105919774952809993587)
          ·
            refine ⟨1974158879662429214990381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316105919774952809993587 1974158879662429214990381)
            ·
              refine ⟨740309579873410955621393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974158879662429214990381 740309579873410955621393)
              ·
                refine ⟨555232184905058216716045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740309579873410955621393 555232184905058216716045)
                ·
                  refine ⟨208212069339396831268517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555232184905058216716045 208212069339396831268517)
                  ·
                    rfl

theorem cell20_456178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_456178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456178 prefixEnd_456178 := by exact prefixLift 456178
  have htrace : WordTrace (prefixWord ++ tailWord_456178) baseStart_456178 baseEnd_456178 := by
    simpa [prefixWord, tailWord_456178, baseEnd_456178] using wordTrace_append hprefix tailTrace_456178
  have hstable : (prefixWord ++ tailWord_456178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456178).length < 2 ^ (prefixWord ++ tailWord_456178).sum := by decide
  have hdescent : baseEnd_456178 < baseStart_456178 := by decide
  rcases family_descends (prefixWord ++ tailWord_456178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456205 : List Nat := [1, 7, 1, 1, 2, 2, 2, 4]
def baseStart_456205 : Nat := 118140960795 + 456205 * 2 ^ 59
def prefixEnd_456205 : Nat := 4983230072969 + 3 ^ 40 * 456205 * 2
def baseEnd_456205 : Nat := 69408130958368245789469

theorem tailTrace_456205 : CollatzResearch.WordTrace tailWord_456205 prefixEnd_456205 69408130958368245789469 := by
  unfold tailWord_456205
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639163312254673456090069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11092775541503115637393379 16639163312254673456090069)
  ·
    refine ⟨389980390130968909127111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16639163312254673456090069 389980390130968909127111)
    ·
      refine ⟨584970585196453363690667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389980390130968909127111 584970585196453363690667)
      ·
        refine ⟨877455877794680045536001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584970585196453363690667 877455877794680045536001)
        ·
          refine ⟨658091908346010034152001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877455877794680045536001 658091908346010034152001)
          ·
            refine ⟨493568931259507525614001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658091908346010034152001 493568931259507525614001)
            ·
              refine ⟨370176698444630644210501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493568931259507525614001 370176698444630644210501)
              ·
                refine ⟨69408130958368245789469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370176698444630644210501 69408130958368245789469)
                ·
                  rfl

theorem cell20_456205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_456205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456205 prefixEnd_456205 := by exact prefixLift 456205
  have htrace : WordTrace (prefixWord ++ tailWord_456205) baseStart_456205 baseEnd_456205 := by
    simpa [prefixWord, tailWord_456205, baseEnd_456205] using wordTrace_append hprefix tailTrace_456205
  have hstable : (prefixWord ++ tailWord_456205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456205).length < 2 ^ (prefixWord ++ tailWord_456205).sum := by decide
  have hdescent : baseEnd_456205 < baseStart_456205 := by decide
  rcases family_descends (prefixWord ++ tailWord_456205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456213 : List Nat := [1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_456213 : Nat := 118140960795 + 456213 * 2 ^ 59
def prefixEnd_456213 : Nat := 4983230072969 + 3 ^ 40 * 456213 * 2
def baseEnd_456213 : Nat := 69409348097697421700569

theorem tailTrace_456213 : CollatzResearch.WordTrace tailWord_456213 prefixEnd_456213 69409348097697421700569 := by
  unfold tailWord_456213
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639455096225690822381293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11092970064150460548254195 16639455096225690822381293)
  ·
    refine ⟨6239795661084634058392985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16639455096225690822381293 6239795661084634058392985)
    ·
      refine ⟨4679846745813475543794739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6239795661084634058392985 4679846745813475543794739)
      ·
        refine ⟨7019770118720213315692109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4679846745813475543794739 7019770118720213315692109)
        ·
          refine ⟨2632413794520079993384541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7019770118720213315692109 2632413794520079993384541)
          ·
            refine ⟨987155172945029997519203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2632413794520079993384541 987155172945029997519203)
            ·
              refine ⟨1480732759417544996278805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987155172945029997519203 1480732759417544996278805)
              ·
                refine ⟨69409348097697421700569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1480732759417544996278805 69409348097697421700569)
                ·
                  rfl

theorem cell20_456213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_456213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456213 prefixEnd_456213 := by exact prefixLift 456213
  have htrace : WordTrace (prefixWord ++ tailWord_456213) baseStart_456213 baseEnd_456213 := by
    simpa [prefixWord, tailWord_456213, baseEnd_456213] using wordTrace_append hprefix tailTrace_456213
  have hstable : (prefixWord ++ tailWord_456213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456213).length < 2 ^ (prefixWord ++ tailWord_456213).sum := by decide
  have hdescent : baseEnd_456213 < baseStart_456213 := by decide
  rcases family_descends (prefixWord ++ tailWord_456213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456220 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_456220 : Nat := 118140960795 + 456220 * 2 ^ 59
def prefixEnd_456220 : Nat := 4983230072969 + 3 ^ 40 * 456220 * 2
def baseEnd_456220 : Nat := 208231239283831351868345

theorem tailTrace_456220 : CollatzResearch.WordTrace tailWord_456220 prefixEnd_456220 208231239283831351868345 := by
  unfold tailWord_456220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319855203600165508943057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11093140271466887345257409 8319855203600165508943057)
  ·
    refine ⟨6239891402700124131707293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8319855203600165508943057 6239891402700124131707293)
    ·
      refine ⟨2339959276012546549390235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6239891402700124131707293 2339959276012546549390235)
      ·
        refine ⟨3509938914018819824085353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339959276012546549390235 3509938914018819824085353)
        ·
          refine ⟨2632454185514114868064015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509938914018819824085353 2632454185514114868064015)
          ·
            refine ⟨3948681278271172302096023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632454185514114868064015 3948681278271172302096023)
            ·
              refine ⟨5923021917406758453144035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948681278271172302096023 5923021917406758453144035)
              ·
                refine ⟨8884532876110137679716053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923021917406758453144035 8884532876110137679716053)
                ·
                  refine ⟨208231239283831351868345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8884532876110137679716053 208231239283831351868345)
                  ·
                    rfl

theorem cell20_456220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_456220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456220 prefixEnd_456220 := by exact prefixLift 456220
  have htrace : WordTrace (prefixWord ++ tailWord_456220) baseStart_456220 baseEnd_456220 := by
    simpa [prefixWord, tailWord_456220, baseEnd_456220] using wordTrace_append hprefix tailTrace_456220
  have hstable : (prefixWord ++ tailWord_456220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456220).length < 2 ^ (prefixWord ++ tailWord_456220).sum := by decide
  have hdescent : baseEnd_456220 < baseStart_456220 := by decide
  rcases family_descends (prefixWord ++ tailWord_456220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456223 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 2]
def baseStart_456223 : Nat := 118140960795 + 456223 * 2 ^ 59
def prefixEnd_456223 : Nat := 4983230072969 + 3 ^ 40 * 456223 * 2
def baseEnd_456223 : Nat := 208232608565576674768333

theorem tailTrace_456223 : CollatzResearch.WordTrace tailWord_456223 prefixEnd_456223 208232608565576674768333 := by
  unfold tailWord_456223
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639819826189462530245323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11093213217459641686830215 16639819826189462530245323)
  ·
    refine ⟨24959729739284193795367985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16639819826189462530245323 24959729739284193795367985)
    ·
      refine ⟨18719797304463145346525989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24959729739284193795367985 18719797304463145346525989)
      ·
        refine ⟨3509961994586839752473623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18719797304463145346525989 3509961994586839752473623)
        ·
          refine ⟨5264942991880259628710435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509961994586839752473623 5264942991880259628710435)
          ·
            refine ⟨7897414487820389443065653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264942991880259628710435 7897414487820389443065653)
            ·
              refine ⟨740382608233161510287405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7897414487820389443065653 740382608233161510287405)
              ·
                refine ⟨277643478087435566357777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 740382608233161510287405 277643478087435566357777)
                ·
                  refine ⟨208232608565576674768333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277643478087435566357777 208232608565576674768333)
                  ·
                    rfl

theorem cell20_456223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 2].length) (baseStart_456223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456223 prefixEnd_456223 := by exact prefixLift 456223
  have htrace : WordTrace (prefixWord ++ tailWord_456223) baseStart_456223 baseEnd_456223 := by
    simpa [prefixWord, tailWord_456223, baseEnd_456223] using wordTrace_append hprefix tailTrace_456223
  have hstable : (prefixWord ++ tailWord_456223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456223).length < 2 ^ (prefixWord ++ tailWord_456223).sum := by decide
  have hdescent : baseEnd_456223 < baseStart_456223 := by decide
  rcases family_descends (prefixWord ++ tailWord_456223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456265 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_456265 : Nat := 118140960795 + 456265 * 2 ^ 59
def prefixEnd_456265 : Nat := 4983230072969 + 3 ^ 40 * 456265 * 2
def baseEnd_456265 : Nat := 208251778510011195368161

theorem tailTrace_456265 : CollatzResearch.WordTrace tailWord_456265 prefixEnd_456265 208251778510011195368161 := by
  unfold tailWord_456265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641351692037303703274249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11094234461358202468849499 16641351692037303703274249)
  ·
    refine ⟨12481013769027977777455687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16641351692037303703274249 12481013769027977777455687)
    ·
      refine ⟨18721520653541966666183531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481013769027977777455687 18721520653541966666183531)
      ·
        refine ⟨28082280980312949999275297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721520653541966666183531 28082280980312949999275297)
        ·
          refine ⟨21061710735234712499456473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28082280980312949999275297 21061710735234712499456473)
          ·
            refine ⟨15796283051426034374592355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21061710735234712499456473 15796283051426034374592355)
            ·
              refine ⟨23694424577139051561888533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796283051426034374592355 23694424577139051561888533)
              ·
                refine ⟨1110676152053393041963525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23694424577139051561888533 1110676152053393041963525)
                ·
                  refine ⟨208251778510011195368161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110676152053393041963525 208251778510011195368161)
                  ·
                    rfl

theorem cell20_456265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_456265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456265 prefixEnd_456265 := by exact prefixLift 456265
  have htrace : WordTrace (prefixWord ++ tailWord_456265) baseStart_456265 baseEnd_456265 := by
    simpa [prefixWord, tailWord_456265, baseEnd_456265] using wordTrace_append hprefix tailTrace_456265
  have hstable : (prefixWord ++ tailWord_456265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456265).length < 2 ^ (prefixWord ++ tailWord_456265).sum := by decide
  have hdescent : baseEnd_456265 < baseStart_456265 := by decide
  rcases family_descends (prefixWord ++ tailWord_456265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456272 : List Nat := [2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_456272 : Nat := 118140960795 + 456272 * 2 ^ 59
def prefixEnd_456272 : Nat := 4983230072969 + 3 ^ 40 * 456272 * 2
def baseEnd_456272 : Nat := 69418324500250094044933

theorem tailTrace_456272 : CollatzResearch.WordTrace tailWord_456272 prefixEnd_456272 69418324500250094044933 := by
  unfold tailWord_456272
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320803501505971949389535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11094404668674629265852713 8320803501505971949389535)
  ·
    refine ⟨12481205252258957924084303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8320803501505971949389535 12481205252258957924084303)
    ·
      refine ⟨18721807878388436886126455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481205252258957924084303 18721807878388436886126455)
      ·
        refine ⟨28082711817582655329189683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721807878388436886126455 28082711817582655329189683)
        ·
          refine ⟨42124067726373982993784525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28082711817582655329189683 42124067726373982993784525)
          ·
            refine ⟨15796525397390243622669197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42124067726373982993784525 15796525397390243622669197)
            ·
              refine ⟨5923697024021341358500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15796525397390243622669197 5923697024021341358500949)
              ·
                refine ⟨69418324500250094044933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5923697024021341358500949 69418324500250094044933)
                ·
                  rfl

theorem cell20_456272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_456272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456272 prefixEnd_456272 := by exact prefixLift 456272
  have htrace : WordTrace (prefixWord ++ tailWord_456272) baseStart_456272 baseEnd_456272 := by
    simpa [prefixWord, tailWord_456272, baseEnd_456272] using wordTrace_append hprefix tailTrace_456272
  have hstable : (prefixWord ++ tailWord_456272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456272).length < 2 ^ (prefixWord ++ tailWord_456272).sum := by decide
  have hdescent : baseEnd_456272 < baseStart_456272 := by decide
  rcases family_descends (prefixWord ++ tailWord_456272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456285 : List Nat := [1, 4, 4, 2, 2, 7]
def baseStart_456285 : Nat := 118140960795 + 456285 * 2 ^ 59
def prefixEnd_456285 : Nat := 4983230072969 + 3 ^ 40 * 456285 * 2
def baseEnd_456285 : Nat := 7713366927962222766719

theorem tailTrace_456285 : CollatzResearch.WordTrace tailWord_456285 prefixEnd_456285 7713366927962222766719 := by
  unfold tailWord_456285
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642081151964847119002309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11094720767976564746001539 16642081151964847119002309)
  ·
    refine ⟨3120390215993408834812933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16642081151964847119002309 3120390215993408834812933)
    ·
      refine ⟨585073165498764156527425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3120390215993408834812933 585073165498764156527425)
      ·
        refine ⟨438804874124073117395569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585073165498764156527425 438804874124073117395569)
        ·
          refine ⟨329103655593054838046677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438804874124073117395569 329103655593054838046677)
          ·
            refine ⟨7713366927962222766719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 329103655593054838046677 7713366927962222766719)
            ·
              rfl

theorem cell20_456285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 7].length) (baseStart_456285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456285 prefixEnd_456285 := by exact prefixLift 456285
  have htrace : WordTrace (prefixWord ++ tailWord_456285) baseStart_456285 baseEnd_456285 := by
    simpa [prefixWord, tailWord_456285, baseEnd_456285] using wordTrace_append hprefix tailTrace_456285
  have hstable : (prefixWord ++ tailWord_456285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456285).length < 2 ^ (prefixWord ++ tailWord_456285).sum := by decide
  have hdescent : baseEnd_456285 < baseStart_456285 := by decide
  rcases family_descends (prefixWord ++ tailWord_456285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456303 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_456303 : Nat := 118140960795 + 456303 * 2 ^ 59
def prefixEnd_456303 : Nat := 4983230072969 + 3 ^ 40 * 456303 * 2
def baseEnd_456303 : Nat := 208269122745451952101339

theorem tailTrace_456303 : CollatzResearch.WordTrace tailWord_456303 prefixEnd_456303 208269122745451952101339 := by
  unfold tailWord_456303
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642737665899636193157563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11095158443933090795438375 16642737665899636193157563)
  ·
    refine ⟨24964106498849454289736345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16642737665899636193157563 24964106498849454289736345)
    ·
      refine ⟨18723079874137090717302259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24964106498849454289736345 18723079874137090717302259)
      ·
        refine ⟨28084619811205636075953389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18723079874137090717302259 28084619811205636075953389)
        ·
          refine ⟨10531732429202113528482521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28084619811205636075953389 10531732429202113528482521)
          ·
            refine ⟨7898799321901585146361891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10531732429202113528482521 7898799321901585146361891)
            ·
              refine ⟨11848198982852377719542837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898799321901585146361891 11848198982852377719542837)
              ·
                refine ⟨1110768654642410411207141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11848198982852377719542837 1110768654642410411207141)
                ·
                  refine ⟨208269122745451952101339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110768654642410411207141 208269122745451952101339)
                  ·
                    rfl

theorem cell20_456303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_456303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456303 prefixEnd_456303 := by exact prefixLift 456303
  have htrace : WordTrace (prefixWord ++ tailWord_456303) baseStart_456303 baseEnd_456303 := by
    simpa [prefixWord, tailWord_456303, baseEnd_456303] using wordTrace_append hprefix tailTrace_456303
  have hstable : (prefixWord ++ tailWord_456303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456303).length < 2 ^ (prefixWord ++ tailWord_456303).sum := by decide
  have hdescent : baseEnd_456303 < baseStart_456303 := by decide
  rcases family_descends (prefixWord ++ tailWord_456303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456306 : List Nat := [3, 2, 1, 2, 3, 3, 1, 5]
def baseStart_456306 : Nat := 118140960795 + 456306 * 2 ^ 59
def prefixEnd_456306 : Nat := 4983230072969 + 3 ^ 40 * 456306 * 2
def baseEnd_456306 : Nat := 69423497342399091667109

theorem tailTrace_456306 : CollatzResearch.WordTrace tailWord_456306 prefixEnd_456306 69423497342399091667109 := by
  unfold tailWord_456306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160711771222191926379193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11095231389925845137011181 4160711771222191926379193)
  ·
    refine ⟨3120533828416643944784395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4160711771222191926379193 3120533828416643944784395)
    ·
      refine ⟨4680800742624965917176593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120533828416643944784395 4680800742624965917176593)
      ·
        refine ⟨3510600556968724437882445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4680800742624965917176593 3510600556968724437882445)
        ·
          refine ⟨1316475208863271664205917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3510600556968724437882445 1316475208863271664205917)
          ·
            refine ⟨493678203323726874077219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1316475208863271664205917 493678203323726874077219)
            ·
              refine ⟨740517304985590311115829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493678203323726874077219 740517304985590311115829)
              ·
                refine ⟨69423497342399091667109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740517304985590311115829 69423497342399091667109)
                ·
                  rfl

theorem cell20_456306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_456306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456306 prefixEnd_456306 := by exact prefixLift 456306
  have htrace : WordTrace (prefixWord ++ tailWord_456306) baseStart_456306 baseEnd_456306 := by
    simpa [prefixWord, tailWord_456306, baseEnd_456306] using wordTrace_append hprefix tailTrace_456306
  have hstable : (prefixWord ++ tailWord_456306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456306).length < 2 ^ (prefixWord ++ tailWord_456306).sum := by decide
  have hdescent : baseEnd_456306 < baseStart_456306 := by decide
  rcases family_descends (prefixWord ++ tailWord_456306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456354 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_456354 : Nat := 118140960795 + 456354 * 2 ^ 59
def prefixEnd_456354 : Nat := 4983230072969 + 3 ^ 40 * 456354 * 2
def baseEnd_456354 : Nat := 208292400535122441401131

theorem tailTrace_456354 : CollatzResearch.WordTrace tailWord_456354 prefixEnd_456354 208292400535122441401131 := by
  unfold tailWord_456354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161149447178717975816029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11096398525809914602176077 4161149447178717975816029)
  ·
    refine ⟨1560431042692019240931011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4161149447178717975816029 1560431042692019240931011)
    ·
      refine ⟨2340646564038028861396517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560431042692019240931011 2340646564038028861396517)
      ·
        refine ⟨438871230757130411511847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2340646564038028861396517 438871230757130411511847)
        ·
          refine ⟨658306846135695617267771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438871230757130411511847 658306846135695617267771)
          ·
            refine ⟨987460269203543425901657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658306846135695617267771 987460269203543425901657)
            ·
              refine ⟨740595201902657569426243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987460269203543425901657 740595201902657569426243)
              ·
                refine ⟨1110892802853986354139365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740595201902657569426243 1110892802853986354139365)
                ·
                  refine ⟨208292400535122441401131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110892802853986354139365 208292400535122441401131)
                  ·
                    rfl

theorem cell20_456354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_456354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456354 prefixEnd_456354 := by exact prefixLift 456354
  have htrace : WordTrace (prefixWord ++ tailWord_456354) baseStart_456354 baseEnd_456354 := by
    simpa [prefixWord, tailWord_456354, baseEnd_456354] using wordTrace_append hprefix tailTrace_456354
  have hstable : (prefixWord ++ tailWord_456354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456354).length < 2 ^ (prefixWord ++ tailWord_456354).sum := by decide
  have hdescent : baseEnd_456354 < baseStart_456354 := by decide
  rcases family_descends (prefixWord ++ tailWord_456354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456365 : List Nat := [1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_456365 : Nat := 118140960795 + 456365 * 2 ^ 59
def prefixEnd_456365 : Nat := 4983230072969 + 3 ^ 40 * 456365 * 2
def baseEnd_456365 : Nat := 69432473744951764011473

theorem tailTrace_456365 : CollatzResearch.WordTrace tailWord_456365 prefixEnd_456365 69432473744951764011473 := by
  unfold tailWord_456365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644998991675020781914549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11096665994450013854609699 16644998991675020781914549)
  ·
    refine ⟨1560468655469533198304489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16644998991675020781914549 1560468655469533198304489)
    ·
      refine ⟨1170351491602149898728367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1560468655469533198304489 1170351491602149898728367)
      ·
        refine ⟨1755527237403224848092551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170351491602149898728367 1755527237403224848092551)
        ·
          refine ⟨2633290856104837272138827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755527237403224848092551 2633290856104837272138827)
          ·
            refine ⟨3949936284157255908208241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633290856104837272138827 3949936284157255908208241)
            ·
              refine ⟨2962452213117941931156181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949936284157255908208241 2962452213117941931156181)
              ·
                refine ⟨69432473744951764011473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2962452213117941931156181 69432473744951764011473)
                ·
                  rfl

theorem cell20_456365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_456365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456365 prefixEnd_456365 := by exact prefixLift 456365
  have htrace : WordTrace (prefixWord ++ tailWord_456365) baseStart_456365 baseEnd_456365 := by
    simpa [prefixWord, tailWord_456365, baseEnd_456365] using wordTrace_append hprefix tailTrace_456365
  have hstable : (prefixWord ++ tailWord_456365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456365).length < 2 ^ (prefixWord ++ tailWord_456365).sum := by decide
  have hdescent : baseEnd_456365 < baseStart_456365 := by decide
  rcases family_descends (prefixWord ++ tailWord_456365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456382 : List Nat := [4, 2, 1, 1, 2, 2, 4, 4]
def baseStart_456382 : Nat := 118140960795 + 456382 * 2 ^ 59
def prefixEnd_456382 : Nat := 4983230072969 + 3 ^ 40 * 456382 * 2
def baseEnd_456382 : Nat := 69435060166026262822561

theorem tailTrace_456382 : CollatzResearch.WordTrace tailWord_456382 prefixEnd_456382 69435060166026262822561 := by
  unfold tailWord_456382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080702379076679085660425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11097079355075621790188933 2080702379076679085660425)
  ·
    refine ⟨1560526784307509314245319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2080702379076679085660425 1560526784307509314245319)
    ·
      refine ⟨2340790176461263971367979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560526784307509314245319 2340790176461263971367979)
      ·
        refine ⟨3511185264691895957051969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340790176461263971367979 3511185264691895957051969)
        ·
          refine ⟨2633388948518921967788977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3511185264691895957051969 2633388948518921967788977)
          ·
            refine ⟨1975041711389191475841733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633388948518921967788977 1975041711389191475841733)
            ·
              refine ⟨370320320885473401720325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1975041711389191475841733 370320320885473401720325)
              ·
                refine ⟨69435060166026262822561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370320320885473401720325 69435060166026262822561)
                ·
                  rfl

theorem cell20_456382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_456382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456382 prefixEnd_456382 := by exact prefixLift 456382
  have htrace : WordTrace (prefixWord ++ tailWord_456382) baseStart_456382 baseEnd_456382 := by
    simpa [prefixWord, tailWord_456382, baseEnd_456382] using wordTrace_append hprefix tailTrace_456382
  have hstable : (prefixWord ++ tailWord_456382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456382).length < 2 ^ (prefixWord ++ tailWord_456382).sum := by decide
  have hdescent : baseEnd_456382 < baseStart_456382 := by decide
  rcases family_descends (prefixWord ++ tailWord_456382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456410 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_456410 : Nat := 118140960795 + 456410 * 2 ^ 59
def prefixEnd_456410 : Nat := 4983230072969 + 3 ^ 40 * 456410 * 2
def baseEnd_456410 : Nat := 208317960461035135534235

theorem tailTrace_456410 : CollatzResearch.WordTrace tailWord_456410 prefixEnd_456410 208317960461035135534235 := by
  unfold tailWord_456410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161660069127998366825671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11097760184341328978201789 4161660069127998366825671)
  ·
    refine ⟨6242490103691997550238507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4161660069127998366825671 6242490103691997550238507)
    ·
      refine ⟨9363735155537996325357761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242490103691997550238507 9363735155537996325357761)
      ·
        refine ⟨7022801366653497244018321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9363735155537996325357761 7022801366653497244018321)
        ·
          refine ⟨5267101024990122933013741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7022801366653497244018321 5267101024990122933013741)
          ·
            refine ⟨1975162884371296099880153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5267101024990122933013741 1975162884371296099880153)
            ·
              refine ⟨1481372163278472074910115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975162884371296099880153 1481372163278472074910115)
              ·
                refine ⟨2222058244917708112365173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481372163278472074910115 2222058244917708112365173)
                ·
                  refine ⟨208317960461035135534235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2222058244917708112365173 208317960461035135534235)
                  ·
                    rfl

theorem cell20_456410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_456410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456410 prefixEnd_456410 := by exact prefixLift 456410
  have htrace : WordTrace (prefixWord ++ tailWord_456410) baseStart_456410 baseEnd_456410 := by
    simpa [prefixWord, tailWord_456410, baseEnd_456410] using wordTrace_append hprefix tailTrace_456410
  have hstable : (prefixWord ++ tailWord_456410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456410).length < 2 ^ (prefixWord ++ tailWord_456410).sum := by decide
  have hdescent : baseEnd_456410 < baseStart_456410 := by decide
  rcases family_descends (prefixWord ++ tailWord_456410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456427 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 3]
def baseStart_456427 : Nat := 118140960795 + 456427 * 2 ^ 59
def prefixEnd_456427 : Nat := 4983230072969 + 3 ^ 40 * 456427 * 2
def baseEnd_456427 : Nat := 208325719724258631967499

theorem tailTrace_456427 : CollatzResearch.WordTrace tailWord_456427 prefixEnd_456427 208325719724258631967499 := by
  unfold tailWord_456427
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647260317450405370671535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11098173544966936913781023 16647260317450405370671535)
  ·
    refine ⟨24970890476175608056007303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647260317450405370671535 24970890476175608056007303)
    ·
      refine ⟨37456335714263412084010955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24970890476175608056007303 37456335714263412084010955)
      ·
        refine ⟨56184503571395118126016433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37456335714263412084010955 56184503571395118126016433)
        ·
          refine ⟨42138377678546338594512325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56184503571395118126016433 42138377678546338594512325)
          ·
            refine ⟨7900945814727438486471061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42138377678546338594512325 7900945814727438486471061)
            ·
              refine ⟨370356835065348679053331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7900945814727438486471061 370356835065348679053331)
              ·
                refine ⟨555535252598023018579997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370356835065348679053331 555535252598023018579997)
                ·
                  refine ⟨208325719724258631967499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555535252598023018579997 208325719724258631967499)
                  ·
                    rfl

theorem cell20_456427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_456427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456427 prefixEnd_456427 := by exact prefixLift 456427
  have htrace : WordTrace (prefixWord ++ tailWord_456427) baseStart_456427 baseEnd_456427 := by
    simpa [prefixWord, tailWord_456427, baseEnd_456427] using wordTrace_append hprefix tailTrace_456427
  have hstable : (prefixWord ++ tailWord_456427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456427).length < 2 ^ (prefixWord ++ tailWord_456427).sum := by decide
  have hdescent : baseEnd_456427 < baseStart_456427 := by decide
  rcases family_descends (prefixWord ++ tailWord_456427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456454 : List Nat := [6, 2, 2, 1, 9]
def baseStart_456454 : Nat := 118140960795 + 456454 * 2 ^ 59
def prefixEnd_456454 : Nat := 4983230072969 + 3 ^ 40 * 456454 * 2
def baseEnd_456454 : Nat := 2572074608147735037869

theorem tailTrace_456454 : CollatzResearch.WordTrace tailWord_456454 prefixEnd_456454 2572074608147735037869 := by
  unfold tailWord_456454
  simp only [CollatzResearch.WordTrace]
  refine ⟨520257659011018405684513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11098830058901725987936277 520257659011018405684513)
  ·
    refine ⟨390193244258263804263385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 520257659011018405684513 390193244258263804263385)
    ·
      refine ⟨292644933193697853197539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390193244258263804263385 292644933193697853197539)
      ·
        refine ⟨438967399790546779796309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292644933193697853197539 438967399790546779796309)
        ·
          refine ⟨2572074608147735037869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 438967399790546779796309 2572074608147735037869)
          ·
            rfl

theorem cell20_456454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 9].length) (baseStart_456454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456454 prefixEnd_456454 := by exact prefixLift 456454
  have htrace : WordTrace (prefixWord ++ tailWord_456454) baseStart_456454 baseEnd_456454 := by
    simpa [prefixWord, tailWord_456454, baseEnd_456454] using wordTrace_append hprefix tailTrace_456454
  have hstable : (prefixWord ++ tailWord_456454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456454).length < 2 ^ (prefixWord ++ tailWord_456454).sum := by decide
  have hdescent : baseEnd_456454 < baseStart_456454 := by decide
  rcases family_descends (prefixWord ++ tailWord_456454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456538 : List Nat := [3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_456538 : Nat := 118140960795 + 456538 * 2 ^ 59
def prefixEnd_456538 : Nat := 4983230072969 + 3 ^ 40 * 456538 * 2
def baseEnd_456538 : Nat := 69458794382945193089015

theorem tailTrace_456538 : CollatzResearch.WordTrace tailWord_456538 prefixEnd_456538 69458794382945193089015 := by
  unfold tailWord_456538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162827205012067831990567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11100872546698847551974845 4162827205012067831990567)
  ·
    refine ⟨6244240807518101747985851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4162827205012067831990567 6244240807518101747985851)
    ·
      refine ⟨9366361211277152621978777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6244240807518101747985851 9366361211277152621978777)
      ·
        refine ⟨7024770908457864466484083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9366361211277152621978777 7024770908457864466484083)
        ·
          refine ⟨10537156362686796699726125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024770908457864466484083 10537156362686796699726125)
          ·
            refine ⟨3951433636007548762397297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10537156362686796699726125 3951433636007548762397297)
            ·
              refine ⟨2963575227005661571797973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951433636007548762397297 2963575227005661571797973)
              ·
                refine ⟨69458794382945193089015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2963575227005661571797973 69458794382945193089015)
                ·
                  rfl

theorem cell20_456538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_456538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456538 prefixEnd_456538 := by exact prefixLift 456538
  have htrace : WordTrace (prefixWord ++ tailWord_456538) baseStart_456538 baseEnd_456538 := by
    simpa [prefixWord, tailWord_456538, baseEnd_456538] using wordTrace_append hprefix tailTrace_456538
  have hstable : (prefixWord ++ tailWord_456538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456538).length < 2 ^ (prefixWord ++ tailWord_456538).sum := by decide
  have hdescent : baseEnd_456538 < baseStart_456538 := by decide
  rcases family_descends (prefixWord ++ tailWord_456538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456596 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_456596 : Nat := 118140960795 + 456596 * 2 ^ 59
def prefixEnd_456596 : Nat := 4983230072969 + 3 ^ 40 * 456596 * 2
def baseEnd_456596 : Nat := 208402855929245155333475

theorem tailTrace_456596 : CollatzResearch.WordTrace tailWord_456596 prefixEnd_456596 208402855929245155333475 := by
  unfold tailWord_456596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8326712126919073616786821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11102282835892098155715761 8326712126919073616786821)
  ·
    refine ⟨1561258523797326303147529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8326712126919073616786821 1561258523797326303147529)
    ·
      refine ⟨1170943892847994727360647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1561258523797326303147529 1170943892847994727360647)
      ·
        refine ⟨1756415839271992091040971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170943892847994727360647 1756415839271992091040971)
        ·
          refine ⟨2634623758907988136561457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1756415839271992091040971 2634623758907988136561457)
          ·
            refine ⟨1975967819180991102421093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2634623758907988136561457 1975967819180991102421093)
            ·
              refine ⟨370493966096435831703955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1975967819180991102421093 370493966096435831703955)
              ·
                refine ⟨555740949144653747555933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370493966096435831703955 555740949144653747555933)
                ·
                  refine ⟨208402855929245155333475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555740949144653747555933 208402855929245155333475)
                  ·
                    rfl

theorem cell20_456596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_456596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456596 prefixEnd_456596 := by exact prefixLift 456596
  have htrace : WordTrace (prefixWord ++ tailWord_456596) baseStart_456596 baseEnd_456596 := by
    simpa [prefixWord, tailWord_456596, baseEnd_456596] using wordTrace_append hprefix tailTrace_456596
  have hstable : (prefixWord ++ tailWord_456596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456596).length < 2 ^ (prefixWord ++ tailWord_456596).sum := by decide
  have hdescent : baseEnd_456596 < baseStart_456596 := by decide
  rcases family_descends (prefixWord ++ tailWord_456596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456700 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 2]
def baseStart_456700 : Nat := 118140960795 + 456700 * 2 ^ 59
def prefixEnd_456700 : Nat := 4983230072969 + 3 ^ 40 * 456700 * 2
def baseEnd_456700 : Nat := 208450324363083015866383

theorem tailTrace_456700 : CollatzResearch.WordTrace tailWord_456700 prefixEnd_456700 208450324363083015866383 := by
  unfold tailWord_456700
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328608722730686497679777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11104811630307581996906369 8328608722730686497679777)
  ·
    refine ⟨6246456542048014873259833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8328608722730686497679777 6246456542048014873259833)
    ·
      refine ⟨4684842406536011154944875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6246456542048014873259833 4684842406536011154944875)
      ·
        refine ⟨7027263609804016732417313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684842406536011154944875 7027263609804016732417313)
        ·
          refine ⟨5270447707353012549312985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7027263609804016732417313 5270447707353012549312985)
          ·
            refine ⟨3952835780514759411984739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5270447707353012549312985 3952835780514759411984739)
            ·
              refine ⟨5929253670772139117977109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952835780514759411984739 5929253670772139117977109)
              ·
                refine ⟨277933765817444021155177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5929253670772139117977109 277933765817444021155177)
                ·
                  refine ⟨208450324363083015866383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277933765817444021155177 208450324363083015866383)
                  ·
                    rfl

theorem cell20_456700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_456700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456700 prefixEnd_456700 := by exact prefixLift 456700
  have htrace : WordTrace (prefixWord ++ tailWord_456700) baseStart_456700 baseEnd_456700 := by
    simpa [prefixWord, tailWord_456700, baseEnd_456700] using wordTrace_append hprefix tailTrace_456700
  have hstable : (prefixWord ++ tailWord_456700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456700).length < 2 ^ (prefixWord ++ tailWord_456700).sum := by decide
  have hdescent : baseEnd_456700 < baseStart_456700 := by decide
  rcases family_descends (prefixWord ++ tailWord_456700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456728 : List Nat := [2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_456728 : Nat := 118140960795 + 456728 * 2 ^ 59
def prefixEnd_456728 : Nat := 4983230072969 + 3 ^ 40 * 456728 * 2
def baseEnd_456728 : Nat := 69487701442013120977645

theorem tailTrace_456728 : CollatzResearch.WordTrace tailWord_456728 prefixEnd_456728 69487701442013120977645 := by
  unfold tailWord_456728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329119344679966888689419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11105492459573289184919225 8329119344679966888689419)
  ·
    refine ⟨12493679017019950333034129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8329119344679966888689419 12493679017019950333034129)
    ·
      refine ⟨9370259262764962749775597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12493679017019950333034129 9370259262764962749775597)
      ·
        refine ⟨3513847223536861031165849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9370259262764962749775597 3513847223536861031165849)
        ·
          refine ⟨2635385417652645773374387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3513847223536861031165849 2635385417652645773374387)
          ·
            refine ⟨3953078126478968660061581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635385417652645773374387 3953078126478968660061581)
            ·
              refine ⟨1482404297429613247523093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3953078126478968660061581 1482404297429613247523093)
              ·
                refine ⟨69487701442013120977645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1482404297429613247523093 69487701442013120977645)
                ·
                  rfl

theorem cell20_456728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_456728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456728 prefixEnd_456728 := by exact prefixLift 456728
  have htrace : WordTrace (prefixWord ++ tailWord_456728) baseStart_456728 baseEnd_456728 := by
    simpa [prefixWord, tailWord_456728, baseEnd_456728] using wordTrace_append hprefix tailTrace_456728
  have hstable : (prefixWord ++ tailWord_456728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456728).length < 2 ^ (prefixWord ++ tailWord_456728).sum := by decide
  have hdescent : baseEnd_456728 < baseStart_456728 := by decide
  rcases family_descends (prefixWord ++ tailWord_456728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456735 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_456735 : Nat := 118140960795 + 456735 * 2 ^ 59
def prefixEnd_456735 : Nat := 4983230072969 + 3 ^ 40 * 456735 * 2
def baseEnd_456735 : Nat := 208466299316778449699573

theorem tailTrace_456735 : CollatzResearch.WordTrace tailWord_456735 prefixEnd_456735 208466299316778449699573 := by
  unfold tailWord_456735
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658494000334573972883659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11105662666889715981922439 16658494000334573972883659)
  ·
    refine ⟨24987741000501860959325489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16658494000334573972883659 24987741000501860959325489)
    ·
      refine ⟨18740805750376395719494117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24987741000501860959325489 18740805750376395719494117)
      ·
        refine ⟨3513901078195574197405147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18740805750376395719494117 3513901078195574197405147)
        ·
          refine ⟨5270851617293361296107721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513901078195574197405147 5270851617293361296107721)
          ·
            refine ⟨3953138712970020972080791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5270851617293361296107721 3953138712970020972080791)
            ·
              refine ⟨5929708069455031458121187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953138712970020972080791 5929708069455031458121187)
              ·
                refine ⟨8894562104182547187181781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929708069455031458121187 8894562104182547187181781)
                ·
                  refine ⟨208466299316778449699573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8894562104182547187181781 208466299316778449699573)
                  ·
                    rfl

theorem cell20_456735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_456735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456735 prefixEnd_456735 := by exact prefixLift 456735
  have htrace : WordTrace (prefixWord ++ tailWord_456735) baseStart_456735 baseEnd_456735 := by
    simpa [prefixWord, tailWord_456735, baseEnd_456735] using wordTrace_append hprefix tailTrace_456735
  have hstable : (prefixWord ++ tailWord_456735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456735).length < 2 ^ (prefixWord ++ tailWord_456735).sum := by decide
  have hdescent : baseEnd_456735 < baseStart_456735 := by decide
  rcases family_descends (prefixWord ++ tailWord_456735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456759 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_456759 : Nat := 118140960795 + 456759 * 2 ^ 59
def prefixEnd_456759 : Nat := 4983230072969 + 3 ^ 40 * 456759 * 2
def baseEnd_456759 : Nat := 208477253570741032899475

theorem tailTrace_456759 : CollatzResearch.WordTrace tailWord_456759 prefixEnd_456759 208477253570741032899475 := by
  unfold tailWord_456759
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659369352247626071757331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11106246234831750714504887 16659369352247626071757331)
  ·
    refine ⟨24989054028371439107635997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16659369352247626071757331 24989054028371439107635997)
    ·
      refine ⟨9370895260639289665363499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24989054028371439107635997 9370895260639289665363499)
      ·
        refine ⟨14056342890958934498045249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370895260639289665363499 14056342890958934498045249)
        ·
          refine ⟨10542257168219200873533937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14056342890958934498045249 10542257168219200873533937)
          ·
            refine ⟨7906692876164400655150453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10542257168219200873533937 7906692876164400655150453)
            ·
              refine ⟨741252457140412561420355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7906692876164400655150453 741252457140412561420355)
              ·
                refine ⟨1111878685710618842130533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741252457140412561420355 1111878685710618842130533)
                ·
                  refine ⟨208477253570741032899475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111878685710618842130533 208477253570741032899475)
                  ·
                    rfl

theorem cell20_456759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_456759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456759 prefixEnd_456759 := by exact prefixLift 456759
  have htrace : WordTrace (prefixWord ++ tailWord_456759) baseStart_456759 baseEnd_456759 := by
    simpa [prefixWord, tailWord_456759, baseEnd_456759] using wordTrace_append hprefix tailTrace_456759
  have hstable : (prefixWord ++ tailWord_456759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456759).length < 2 ^ (prefixWord ++ tailWord_456759).sum := by decide
  have hdescent : baseEnd_456759 < baseStart_456759 := by decide
  rcases family_descends (prefixWord ++ tailWord_456759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456769 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_456769 : Nat := 118140960795 + 456769 * 2 ^ 59
def prefixEnd_456769 : Nat := 4983230072969 + 3 ^ 40 * 456769 * 2
def baseEnd_456769 : Nat := 208481817843225442566101

theorem tailTrace_456769 : CollatzResearch.WordTrace tailWord_456769 prefixEnd_456769 208481817843225442566101 := by
  unfold tailWord_456769
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659734082211397779621361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11106489388140931853080907 16659734082211397779621361)
  ·
    refine ⟨12494800561658548334716021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16659734082211397779621361 12494800561658548334716021)
    ·
      refine ⟨1171387552655488906379627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12494800561658548334716021 1171387552655488906379627)
      ·
        refine ⟨1757081328983233359569441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171387552655488906379627 1757081328983233359569441)
        ·
          refine ⟨1317810996737425019677081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1757081328983233359569441 1317810996737425019677081)
          ·
            refine ⟨988358247553068764757811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317810996737425019677081 988358247553068764757811)
            ·
              refine ⟨1482537371329603147136717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988358247553068764757811 1482537371329603147136717)
              ·
                refine ⟨555951514248601180176269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1482537371329603147136717 555951514248601180176269)
                ·
                  refine ⟨208481817843225442566101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 555951514248601180176269 208481817843225442566101)
                  ·
                    rfl

theorem cell20_456769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_456769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456769 prefixEnd_456769 := by exact prefixLift 456769
  have htrace : WordTrace (prefixWord ++ tailWord_456769) baseStart_456769 baseEnd_456769 := by
    simpa [prefixWord, tailWord_456769, baseEnd_456769] using wordTrace_append hprefix tailTrace_456769
  have hstable : (prefixWord ++ tailWord_456769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456769).length < 2 ^ (prefixWord ++ tailWord_456769).sum := by decide
  have hdescent : baseEnd_456769 < baseStart_456769 := by decide
  rcases family_descends (prefixWord ++ tailWord_456769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456828 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_456828 : Nat := 118140960795 + 456828 * 2 ^ 59
def prefixEnd_456828 : Nat := 4983230072969 + 3 ^ 40 * 456828 * 2
def baseEnd_456828 : Nat := 208508747050883459599193

theorem tailTrace_456828 : CollatzResearch.WordTrace tailWord_456828 prefixEnd_456828 208508747050883459599193 := by
  unfold tailWord_456828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8330942994498825428009569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11107923992665100570679425 8330942994498825428009569)
  ·
    refine ⟨6248207245874119071007177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8330942994498825428009569 6248207245874119071007177)
    ·
      refine ⟨4686155434405589303255383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6248207245874119071007177 4686155434405589303255383)
      ·
        refine ⟨7029233151608383954883075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686155434405589303255383 7029233151608383954883075)
        ·
          refine ⟨10543849727412575932324613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029233151608383954883075 10543849727412575932324613)
          ·
            refine ⟨1976971823889857987310865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10543849727412575932324613 1976971823889857987310865)
            ·
              refine ⟨1482728867917393490483149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976971823889857987310865 1482728867917393490483149)
              ·
                refine ⟨556023325469022558931181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1482728867917393490483149 556023325469022558931181)
                ·
                  refine ⟨208508747050883459599193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556023325469022558931181 208508747050883459599193)
                  ·
                    rfl

theorem cell20_456828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_456828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456828 prefixEnd_456828 := by exact prefixLift 456828
  have htrace : WordTrace (prefixWord ++ tailWord_456828) baseStart_456828 baseEnd_456828 := by
    simpa [prefixWord, tailWord_456828, baseEnd_456828] using wordTrace_append hprefix tailTrace_456828
  have hstable : (prefixWord ++ tailWord_456828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456828).length < 2 ^ (prefixWord ++ tailWord_456828).sum := by decide
  have hdescent : baseEnd_456828 < baseStart_456828 := by decide
  rcases family_descends (prefixWord ++ tailWord_456828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456835 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_456835 : Nat := 118140960795 + 456835 * 2 ^ 59
def prefixEnd_456835 : Nat := 4983230072969 + 3 ^ 40 * 456835 * 2
def baseEnd_456835 : Nat := 208511942041622546365831

theorem tailTrace_456835 : CollatzResearch.WordTrace tailWord_456835 prefixEnd_456835 208511942041622546365831 := by
  unfold tailWord_456835
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662141299972291051523959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11108094199981527367682639 16662141299972291051523959)
  ·
    refine ⟨24993211949958436577285939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16662141299972291051523959 24993211949958436577285939)
    ·
      refine ⟨37489817924937654865928909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24993211949958436577285939 37489817924937654865928909)
      ·
        refine ⟨14058681721851620574723341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37489817924937654865928909 14058681721851620574723341)
        ·
          refine ⟨5272005645694357715521253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14058681721851620574723341 5272005645694357715521253)
          ·
            refine ⟨988501058567692071660235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5272005645694357715521253 988501058567692071660235)
            ·
              refine ⟨1482751587851538107490353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988501058567692071660235 1482751587851538107490353)
              ·
                refine ⟨1112063690888653580617765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482751587851538107490353 1112063690888653580617765)
                ·
                  refine ⟨208511942041622546365831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112063690888653580617765 208511942041622546365831)
                  ·
                    rfl

theorem cell20_456835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_456835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456835 prefixEnd_456835 := by exact prefixLift 456835
  have htrace : WordTrace (prefixWord ++ tailWord_456835) baseStart_456835 baseEnd_456835 := by
    simpa [prefixWord, tailWord_456835, baseEnd_456835] using wordTrace_append hprefix tailTrace_456835
  have hstable : (prefixWord ++ tailWord_456835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456835).length < 2 ^ (prefixWord ++ tailWord_456835).sum := by decide
  have hdescent : baseEnd_456835 < baseStart_456835 := by decide
  rcases family_descends (prefixWord ++ tailWord_456835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456854 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_456854 : Nat := 118140960795 + 456854 * 2 ^ 59
def prefixEnd_456854 : Nat := 4983230072969 + 3 ^ 40 * 456854 * 2
def baseEnd_456854 : Nat := 208520614159342924732421

theorem tailTrace_456854 : CollatzResearch.WordTrace tailWord_456854 prefixEnd_456854 208520614159342924732421 := by
  unfold tailWord_456854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041427142931466081029101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11108556191268971530977077 1041427142931466081029101)
  ·
    refine ⟨390535178599299780385913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1041427142931466081029101 390535178599299780385913)
    ·
      refine ⟨292901383949474835289435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390535178599299780385913 292901383949474835289435)
      ·
        refine ⟨439352075924212252934153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292901383949474835289435 439352075924212252934153)
        ·
          refine ⟨329514056943159189700615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439352075924212252934153 329514056943159189700615)
          ·
            refine ⟨494271085414738784550923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329514056943159189700615 494271085414738784550923)
            ·
              refine ⟨741406628122108176826385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494271085414738784550923 741406628122108176826385)
              ·
                refine ⟨556054971091581132619789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741406628122108176826385 556054971091581132619789)
                ·
                  refine ⟨208520614159342924732421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556054971091581132619789 208520614159342924732421)
                  ·
                    rfl

theorem cell20_456854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_456854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456854 prefixEnd_456854 := by exact prefixLift 456854
  have htrace : WordTrace (prefixWord ++ tailWord_456854) baseStart_456854 baseEnd_456854 := by
    simpa [prefixWord, tailWord_456854, baseEnd_456854] using wordTrace_append hprefix tailTrace_456854
  have hstable : (prefixWord ++ tailWord_456854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456854).length < 2 ^ (prefixWord ++ tailWord_456854).sum := by decide
  have hdescent : baseEnd_456854 < baseStart_456854 := by decide
  rcases family_descends (prefixWord ++ tailWord_456854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456924 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_456924 : Nat := 118140960795 + 456924 * 2 ^ 59
def prefixEnd_456924 : Nat := 4983230072969 + 3 ^ 40 * 456924 * 2
def baseEnd_456924 : Nat := 208552564066733792398801

theorem tailTrace_456924 : CollatzResearch.WordTrace tailWord_456924 prefixEnd_456924 208552564066733792398801 := by
  unfold tailWord_456924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332693698324929625756913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11110258264433239501009217 8332693698324929625756913)
  ·
    refine ⟨6249520273743697219317685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8332693698324929625756913 6249520273743697219317685)
    ·
      refine ⟨585892525663471614311033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6249520273743697219317685 585892525663471614311033)
      ·
        refine ⟨439419394247603710733275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585892525663471614311033 439419394247603710733275)
        ·
          refine ⟨659129091371405566099913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439419394247603710733275 659129091371405566099913)
          ·
            refine ⟨494346818528554174574935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659129091371405566099913 494346818528554174574935)
            ·
              refine ⟨741520227792831261862403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494346818528554174574935 741520227792831261862403)
              ·
                refine ⟨1112280341689246892793605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741520227792831261862403 1112280341689246892793605)
                ·
                  refine ⟨208552564066733792398801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112280341689246892793605 208552564066733792398801)
                  ·
                    rfl

theorem cell20_456924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_456924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456924 prefixEnd_456924 := by exact prefixLift 456924
  have htrace : WordTrace (prefixWord ++ tailWord_456924) baseStart_456924 baseEnd_456924 := by
    simpa [prefixWord, tailWord_456924, baseEnd_456924] using wordTrace_append hprefix tailTrace_456924
  have hstable : (prefixWord ++ tailWord_456924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456924).length < 2 ^ (prefixWord ++ tailWord_456924).sum := by decide
  have hdescent : baseEnd_456924 < baseStart_456924 := by decide
  rcases family_descends (prefixWord ++ tailWord_456924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456935 : List Nat := [1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_456935 : Nat := 118140960795 + 456935 * 2 ^ 59
def prefixEnd_456935 : Nat := 4983230072969 + 3 ^ 40 * 456935 * 2
def baseEnd_456935 : Nat := 69519194922155547677363

theorem tailTrace_456935 : CollatzResearch.WordTrace tailWord_456935 prefixEnd_456935 69519194922155547677363 := by
  unfold tailWord_456935
  simp only [CollatzResearch.WordTrace]
  refine ⟨16665788599610008130164259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11110525733073338753442839 16665788599610008130164259)
  ·
    refine ⟨24998682899415012195246389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16665788599610008130164259 24998682899415012195246389)
    ·
      refine ⟨2343626521820157393304349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24998682899415012195246389 2343626521820157393304349)
      ·
        refine ⟨878859945682559022489131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2343626521820157393304349 878859945682559022489131)
        ·
          refine ⟨1318289918523838533733697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878859945682559022489131 1318289918523838533733697)
          ·
            refine ⟨988717438892878900300273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318289918523838533733697 988717438892878900300273)
            ·
              refine ⟨741538079169659175225205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988717438892878900300273 741538079169659175225205)
              ·
                refine ⟨69519194922155547677363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 741538079169659175225205 69519194922155547677363)
                ·
                  rfl

theorem cell20_456935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_456935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456935 prefixEnd_456935 := by exact prefixLift 456935
  have htrace : WordTrace (prefixWord ++ tailWord_456935) baseStart_456935 baseEnd_456935 := by
    simpa [prefixWord, tailWord_456935, baseEnd_456935] using wordTrace_append hprefix tailTrace_456935
  have hstable : (prefixWord ++ tailWord_456935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456935).length < 2 ^ (prefixWord ++ tailWord_456935).sum := by decide
  have hdescent : baseEnd_456935 < baseStart_456935 := by decide
  rcases family_descends (prefixWord ++ tailWord_456935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456956 : List Nat := [2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_456956 : Nat := 118140960795 + 456956 * 2 ^ 59
def prefixEnd_456956 : Nat := 4983230072969 + 3 ^ 40 * 456956 * 2
def baseEnd_456956 : Nat := 69522389912894634444001

theorem tailTrace_456956 : CollatzResearch.WordTrace tailWord_456956 prefixEnd_456956 69522389912894634444001 := by
  unfold tailWord_456956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333277266266964358339361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11111036355022619144452481 8333277266266964358339361)
  ·
    refine ⟨6249957949700223268754521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8333277266266964358339361 6249957949700223268754521)
    ·
      refine ⟨4687468462275167451565891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6249957949700223268754521 4687468462275167451565891)
      ·
        refine ⟨7031202693412751177348837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687468462275167451565891 7031202693412751177348837)
        ·
          refine ⟨1318350505014890845752907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7031202693412751177348837 1318350505014890845752907)
          ·
            refine ⟨1977525757522336268629361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318350505014890845752907 1977525757522336268629361)
            ·
              refine ⟨1483144318141752201472021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977525757522336268629361 1483144318141752201472021)
              ·
                refine ⟨69522389912894634444001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1483144318141752201472021 69522389912894634444001)
                ·
                  rfl

theorem cell20_456956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_456956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456956 prefixEnd_456956 := by exact prefixLift 456956
  have htrace : WordTrace (prefixWord ++ tailWord_456956) baseStart_456956 baseEnd_456956 := by
    simpa [prefixWord, tailWord_456956, baseEnd_456956] using wordTrace_append hprefix tailTrace_456956
  have hstable : (prefixWord ++ tailWord_456956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456956).length < 2 ^ (prefixWord ++ tailWord_456956).sum := by decide
  have hdescent : baseEnd_456956 < baseStart_456956 := by decide
  rcases family_descends (prefixWord ++ tailWord_456956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456977 : List Nat := [1, 2, 2, 1, 1, 13]
def baseStart_456977 : Nat := 118140960795 + 456977 * 2 ^ 59
def prefixEnd_456977 : Nat := 4983230072969 + 3 ^ 40 * 456977 * 2
def baseEnd_456977 : Nat := 7725064989292635690071

theorem tailTrace_456977 : CollatzResearch.WordTrace tailWord_456977 prefixEnd_456977 7725064989292635690071 := by
  unfold tailWord_456977
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667320465457849303193185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11111546976971899535462123 16667320465457849303193185)
  ·
    refine ⟨12500490349093386977394889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16667320465457849303193185 12500490349093386977394889)
    ·
      refine ⟨9375367761820040233046167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12500490349093386977394889 9375367761820040233046167)
      ·
        refine ⟨14063051642730060349569251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9375367761820040233046167 14063051642730060349569251)
        ·
          refine ⟨21094577464095090524353877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063051642730060349569251 21094577464095090524353877)
          ·
            refine ⟨7725064989292635690071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 21094577464095090524353877 7725064989292635690071)
            ·
              rfl

theorem cell20_456977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 13].length) (baseStart_456977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456977 prefixEnd_456977 := by exact prefixLift 456977
  have htrace : WordTrace (prefixWord ++ tailWord_456977) baseStart_456977 baseEnd_456977 := by
    simpa [prefixWord, tailWord_456977, baseEnd_456977] using wordTrace_append hprefix tailTrace_456977
  have hstable : (prefixWord ++ tailWord_456977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456977).length < 2 ^ (prefixWord ++ tailWord_456977).sum := by decide
  have hdescent : baseEnd_456977 < baseStart_456977 := by decide
  rcases family_descends (prefixWord ++ tailWord_456977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456983 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 2]
def baseStart_456983 : Nat := 118140960795 + 456983 * 2 ^ 59
def prefixEnd_456983 : Nat := 4983230072969 + 3 ^ 40 * 456983 * 2
def baseEnd_456983 : Nat := 208579493274391809431893

theorem tailTrace_456983 : CollatzResearch.WordTrace tailWord_456983 prefixEnd_456983 208579493274391809431893 := by
  unfold tailWord_456983
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667539303436112327911603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11111692868957408218607735 16667539303436112327911603)
  ·
    refine ⟨25001308955154168491867405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16667539303436112327911603 25001308955154168491867405)
    ·
      refine ⟨9375490858182813184450277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25001308955154168491867405 9375490858182813184450277)
      ·
        refine ⟨1757904535909277472084427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9375490858182813184450277 1757904535909277472084427)
        ·
          refine ⟨2636856803863916208126641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757904535909277472084427 2636856803863916208126641)
          ·
            refine ⟨1977642602897937156094981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2636856803863916208126641 1977642602897937156094981)
            ·
              refine ⟨370807988043363216767809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1977642602897937156094981 370807988043363216767809)
              ·
                refine ⟨278105991032522412575857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370807988043363216767809 278105991032522412575857)
                ·
                  refine ⟨208579493274391809431893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278105991032522412575857 208579493274391809431893)
                  ·
                    rfl

theorem cell20_456983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 2].length) (baseStart_456983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456983 prefixEnd_456983 := by exact prefixLift 456983
  have htrace : WordTrace (prefixWord ++ tailWord_456983) baseStart_456983 baseEnd_456983 := by
    simpa [prefixWord, tailWord_456983, baseEnd_456983] using wordTrace_append hprefix tailTrace_456983
  have hstable : (prefixWord ++ tailWord_456983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456983).length < 2 ^ (prefixWord ++ tailWord_456983).sum := by decide
  have hdescent : baseEnd_456983 < baseStart_456983 := by decide
  rcases family_descends (prefixWord ++ tailWord_456983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456990 : List Nat := [4, 3, 2, 1, 1, 1, 3, 5]
def baseStart_456990 : Nat := 118140960795 + 456990 * 2 ^ 59
def prefixEnd_456990 : Nat := 4983230072969 + 3 ^ 40 * 456990 * 2
def baseEnd_456990 : Nat := 69527562755043632066177

theorem tailTrace_456990 : CollatzResearch.WordTrace tailWord_456990 prefixEnd_456990 69527562755043632066177 := by
  unfold tailWord_456990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083474326801344065427053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11111863076273835015610949 2083474326801344065427053)
  ·
    refine ⟨781302872550504024535145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2083474326801344065427053 781302872550504024535145)
    ·
      refine ⟨585977154412878018401359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781302872550504024535145 585977154412878018401359)
      ·
        refine ⟨878965731619317027602039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585977154412878018401359 878965731619317027602039)
        ·
          refine ⟨1318448597428975541403059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878965731619317027602039 1318448597428975541403059)
          ·
            refine ⟨1977672896143463312104589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318448597428975541403059 1977672896143463312104589)
            ·
              refine ⟨741627336053798742039221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1977672896143463312104589 741627336053798742039221)
              ·
                refine ⟨69527562755043632066177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 741627336053798742039221 69527562755043632066177)
                ·
                  rfl

theorem cell20_456990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_456990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_456990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_456990 prefixEnd_456990 := by exact prefixLift 456990
  have htrace : WordTrace (prefixWord ++ tailWord_456990) baseStart_456990 baseEnd_456990 := by
    simpa [prefixWord, tailWord_456990, baseEnd_456990] using wordTrace_append hprefix tailTrace_456990
  have hstable : (prefixWord ++ tailWord_456990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456990).length < 2 ^ (prefixWord ++ tailWord_456990).sum := by decide
  have hdescent : baseEnd_456990 < baseStart_456990 := by decide
  rcases family_descends (prefixWord ++ tailWord_456990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457015 : List Nat := [1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_457015 : Nat := 118140960795 + 457015 * 2 ^ 59
def prefixEnd_457015 : Nat := 4983230072969 + 3 ^ 40 * 457015 * 2
def baseEnd_457015 : Nat := 69531366315447306788365

theorem tailTrace_457015 : CollatzResearch.WordTrace tailWord_457015 prefixEnd_457015 69531366315447306788365 := by
  unfold tailWord_457015
  simp only [CollatzResearch.WordTrace]
  refine ⟨16668706439320181793076499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11112470959546787862050999 16668706439320181793076499)
  ·
    refine ⟨25003059658980272689614749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16668706439320181793076499 25003059658980272689614749)
    ·
      refine ⟨9376147372117602258605531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25003059658980272689614749 9376147372117602258605531)
      ·
        refine ⟨14064221058176403387908297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9376147372117602258605531 14064221058176403387908297)
        ·
          refine ⟨10548165793632302540931223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14064221058176403387908297 10548165793632302540931223)
          ·
            refine ⟨15822248690448453811396835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10548165793632302540931223 15822248690448453811396835)
            ·
              refine ⟨23733373035672680717095253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15822248690448453811396835 23733373035672680717095253)
              ·
                refine ⟨69531366315447306788365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23733373035672680717095253 69531366315447306788365)
                ·
                  rfl

theorem cell20_457015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_457015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457015 prefixEnd_457015 := by exact prefixLift 457015
  have htrace : WordTrace (prefixWord ++ tailWord_457015) baseStart_457015 baseEnd_457015 := by
    simpa [prefixWord, tailWord_457015, baseEnd_457015] using wordTrace_append hprefix tailTrace_457015
  have hstable : (prefixWord ++ tailWord_457015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457015).length < 2 ^ (prefixWord ++ tailWord_457015).sum := by decide
  have hdescent : baseEnd_457015 < baseStart_457015 := by decide
  rcases family_descends (prefixWord ++ tailWord_457015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457039 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_457039 : Nat := 118140960795 + 457039 * 2 ^ 59
def prefixEnd_457039 : Nat := 4983230072969 + 3 ^ 40 * 457039 * 2
def baseEnd_457039 : Nat := 208605053200304503564997

theorem tailTrace_457039 : CollatzResearch.WordTrace tailWord_457039 prefixEnd_457039 208605053200304503564997 := by
  unfold tailWord_457039
  simp only [CollatzResearch.WordTrace]
  refine ⟨16669581791233233891950171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11113054527488822594633447 16669581791233233891950171)
  ·
    refine ⟨25004372686849850837925257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16669581791233233891950171 25004372686849850837925257)
    ·
      refine ⟨18753279515137388128443943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25004372686849850837925257 18753279515137388128443943)
      ·
        refine ⟨28129919272706082192665915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18753279515137388128443943 28129919272706082192665915)
        ·
          refine ⟨42194878909059123288998873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28129919272706082192665915 42194878909059123288998873)
          ·
            refine ⟨31646159181794342466749155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42194878909059123288998873 31646159181794342466749155)
            ·
              refine ⟨47469238772691513700123733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31646159181794342466749155 47469238772691513700123733)
              ·
                refine ⟨556280141867478676173325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47469238772691513700123733 556280141867478676173325)
                ·
                  refine ⟨208605053200304503564997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 556280141867478676173325 208605053200304503564997)
                  ·
                    rfl

theorem cell20_457039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_457039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457039 prefixEnd_457039 := by exact prefixLift 457039
  have htrace : WordTrace (prefixWord ++ tailWord_457039) baseStart_457039 baseEnd_457039 := by
    simpa [prefixWord, tailWord_457039, baseEnd_457039] using wordTrace_append hprefix tailTrace_457039
  have hstable : (prefixWord ++ tailWord_457039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457039).length < 2 ^ (prefixWord ++ tailWord_457039).sum := by decide
  have hdescent : baseEnd_457039 < baseStart_457039 := by decide
  rcases family_descends (prefixWord ++ tailWord_457039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457042 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_457042 : Nat := 118140960795 + 457042 * 2 ^ 59
def prefixEnd_457042 : Nat := 4983230072969 + 3 ^ 40 * 457042 * 2
def baseEnd_457042 : Nat := 208606422482049826464985

theorem tailTrace_457042 : CollatzResearch.WordTrace tailWord_457042 prefixEnd_457042 208606422482049826464985 := by
  unfold tailWord_457042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167422802555591351077345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11113127473481576936206253 4167422802555591351077345)
  ·
    refine ⟨3125567101916693513308009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4167422802555591351077345 3125567101916693513308009)
    ·
      refine ⟨2344175326437520134981007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3125567101916693513308009 2344175326437520134981007)
      ·
        refine ⟨3516262989656280202471511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344175326437520134981007 3516262989656280202471511)
        ·
          refine ⟨5274394484484420303707267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516262989656280202471511 5274394484484420303707267)
          ·
            refine ⟨7911591726726630455560901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274394484484420303707267 7911591726726630455560901)
            ·
              refine ⟨1483423448761243210417669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7911591726726630455560901 1483423448761243210417669)
              ·
                refine ⟨278141896642733101953313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1483423448761243210417669 278141896642733101953313)
                ·
                  refine ⟨208606422482049826464985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278141896642733101953313 208606422482049826464985)
                  ·
                    rfl

theorem cell20_457042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_457042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457042 prefixEnd_457042 := by exact prefixLift 457042
  have htrace : WordTrace (prefixWord ++ tailWord_457042) baseStart_457042 baseEnd_457042 := by
    simpa [prefixWord, tailWord_457042, baseEnd_457042] using wordTrace_append hprefix tailTrace_457042
  have hstable : (prefixWord ++ tailWord_457042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457042).length < 2 ^ (prefixWord ++ tailWord_457042).sum := by decide
  have hdescent : baseEnd_457042 < baseStart_457042 := by decide
  rcases family_descends (prefixWord ++ tailWord_457042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457063 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_457063 : Nat := 118140960795 + 457063 * 2 ^ 59
def prefixEnd_457063 : Nat := 4983230072969 + 3 ^ 40 * 457063 * 2
def baseEnd_457063 : Nat := 208616007454267086764899

theorem tailTrace_457063 : CollatzResearch.WordTrace tailWord_457063 prefixEnd_457063 208616007454267086764899 := by
  unfold tailWord_457063
  simp only [CollatzResearch.WordTrace]
  refine ⟨16670457143146285990823843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11113638095430857327215895 16670457143146285990823843)
  ·
    refine ⟨25005685714719428986235765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16670457143146285990823843 25005685714719428986235765)
    ·
      refine ⟨2344283035754946467459603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25005685714719428986235765 2344283035754946467459603)
      ·
        refine ⟨3516424553632419701189405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344283035754946467459603 3516424553632419701189405)
        ·
          refine ⟨1318659207612157387946027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3516424553632419701189405 1318659207612157387946027)
          ·
            refine ⟨1977988811418236081919041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318659207612157387946027 1977988811418236081919041)
            ·
              refine ⟨1483491608563677061439281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977988811418236081919041 1483491608563677061439281)
              ·
                refine ⟨1112618706422757796079461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483491608563677061439281 1112618706422757796079461)
                ·
                  refine ⟨208616007454267086764899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112618706422757796079461 208616007454267086764899)
                  ·
                    rfl

theorem cell20_457063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_457063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457063 prefixEnd_457063 := by exact prefixLift 457063
  have htrace : WordTrace (prefixWord ++ tailWord_457063) baseStart_457063 baseEnd_457063 := by
    simpa [prefixWord, tailWord_457063, baseEnd_457063] using wordTrace_append hprefix tailTrace_457063
  have hstable : (prefixWord ++ tailWord_457063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457063).length < 2 ^ (prefixWord ++ tailWord_457063).sum := by decide
  have hdescent : baseEnd_457063 < baseStart_457063 := by decide
  rcases family_descends (prefixWord ++ tailWord_457063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457066 : List Nat := [3, 1, 3, 3, 1, 3, 2, 4]
def baseStart_457066 : Nat := 118140960795 + 457066 * 2 ^ 59
def prefixEnd_457066 : Nat := 4983230072969 + 3 ^ 40 * 457066 * 2
def baseEnd_457066 : Nat := 69539125578670803221629

theorem tailTrace_457066 : CollatzResearch.WordTrace tailWord_457066 prefixEnd_457066 69539125578670803221629 := by
  unfold tailWord_457066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167641640533854375795763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11113711041423611668788701 4167641640533854375795763)
  ·
    refine ⟨6251462460800781563693645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4167641640533854375795763 6251462460800781563693645)
    ·
      refine ⟨2344298422800293086385117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6251462460800781563693645 2344298422800293086385117)
      ·
        refine ⟨879111908550109907394419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2344298422800293086385117 879111908550109907394419)
        ·
          refine ⟨1318667862825164861091629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879111908550109907394419 1318667862825164861091629)
          ·
            refine ⟨494500448559436822909361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1318667862825164861091629 494500448559436822909361)
            ·
              refine ⟨370875336419577617182021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494500448559436822909361 370875336419577617182021)
              ·
                refine ⟨69539125578670803221629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370875336419577617182021 69539125578670803221629)
                ·
                  rfl

theorem cell20_457066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_457066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457066 prefixEnd_457066 := by exact prefixLift 457066
  have htrace : WordTrace (prefixWord ++ tailWord_457066) baseStart_457066 baseEnd_457066 := by
    simpa [prefixWord, tailWord_457066, baseEnd_457066] using wordTrace_append hprefix tailTrace_457066
  have hstable : (prefixWord ++ tailWord_457066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457066).length < 2 ^ (prefixWord ++ tailWord_457066).sum := by decide
  have hdescent : baseEnd_457066 < baseStart_457066 := by decide
  rcases family_descends (prefixWord ++ tailWord_457066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457097 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 2]
def baseStart_457097 : Nat := 118140960795 + 457097 * 2 ^ 59
def prefixEnd_457097 : Nat := 4983230072969 + 3 ^ 40 * 457097 * 2
def baseEnd_457097 : Nat := 208631525980714079631427

theorem tailTrace_457097 : CollatzResearch.WordTrace tailWord_457097 prefixEnd_457097 208631525980714079631427 := by
  unfold tailWord_457097
  simp only [CollatzResearch.WordTrace]
  refine ⟨16671697225023109797561545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11114464816682073198374363 16671697225023109797561545)
  ·
    refine ⟨12503772918767332348171159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16671697225023109797561545 12503772918767332348171159)
    ·
      refine ⟨18755659378150998522256739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12503772918767332348171159 18755659378150998522256739)
      ·
        refine ⟨28133489067226497783385109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18755659378150998522256739 28133489067226497783385109)
        ·
          refine ⟨1318757300026242083596177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28133489067226497783385109 1318757300026242083596177)
          ·
            refine ⟨989067975019681562697133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318757300026242083596177 989067975019681562697133)
            ·
              refine ⟨370900490632380586011425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 989067975019681562697133 370900490632380586011425)
              ·
                refine ⟨278175367974285439508569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370900490632380586011425 278175367974285439508569)
                ·
                  refine ⟨208631525980714079631427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278175367974285439508569 208631525980714079631427)
                  ·
                    rfl

theorem cell20_457097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_457097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457097 prefixEnd_457097 := by exact prefixLift 457097
  have htrace : WordTrace (prefixWord ++ tailWord_457097) baseStart_457097 baseEnd_457097 := by
    simpa [prefixWord, tailWord_457097, baseEnd_457097] using wordTrace_append hprefix tailTrace_457097
  have hstable : (prefixWord ++ tailWord_457097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457097).length < 2 ^ (prefixWord ++ tailWord_457097).sum := by decide
  have hdescent : baseEnd_457097 < baseStart_457097 := by decide
  rcases family_descends (prefixWord ++ tailWord_457097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457184 : List Nat := [2, 1, 1, 3, 1, 1, 7, 4]
def baseStart_457184 : Nat := 118140960795 + 457184 * 2 ^ 59
def prefixEnd_457184 : Nat := 4983230072969 + 3 ^ 40 * 457184 * 2
def baseEnd_457184 : Nat := 69557078383776147910357

theorem tailTrace_457184 : CollatzResearch.WordTrace tailWord_457184 prefixEnd_457184 69557078383776147910357 := by
  unfold tailWord_457184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8337435187853961827989303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11116580250471949103985737 8337435187853961827989303)
  ·
    refine ⟨12506152781780942741983955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8337435187853961827989303 12506152781780942741983955)
    ·
      refine ⟨18759229172671414112975933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12506152781780942741983955 18759229172671414112975933)
      ·
        refine ⟨7034710939751780292365975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18759229172671414112975933 7034710939751780292365975)
        ·
          refine ⟨10552066409627670438548963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7034710939751780292365975 10552066409627670438548963)
          ·
            refine ⟨15828099614441505657823445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10552066409627670438548963 15828099614441505657823445)
            ·
              refine ⟨370971084713472788855237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15828099614441505657823445 370971084713472788855237)
              ·
                refine ⟨69557078383776147910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370971084713472788855237 69557078383776147910357)
                ·
                  rfl

theorem cell20_457184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_457184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457184 prefixEnd_457184 := by exact prefixLift 457184
  have htrace : WordTrace (prefixWord ++ tailWord_457184) baseStart_457184 baseEnd_457184 := by
    simpa [prefixWord, tailWord_457184, baseEnd_457184] using wordTrace_append hprefix tailTrace_457184
  have hstable : (prefixWord ++ tailWord_457184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457184).length < 2 ^ (prefixWord ++ tailWord_457184).sum := by decide
  have hdescent : baseEnd_457184 < baseStart_457184 := by decide
  rcases family_descends (prefixWord ++ tailWord_457184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457191 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_457191 : Nat := 118140960795 + 457191 * 2 ^ 59
def prefixEnd_457191 : Nat := 4983230072969 + 3 ^ 40 * 457191 * 2
def baseEnd_457191 : Nat := 208674430142067530497709

theorem tailTrace_457191 : CollatzResearch.WordTrace tailWord_457191 prefixEnd_457191 208674430142067530497709 := by
  unfold tailWord_457191
  simp only [CollatzResearch.WordTrace]
  refine ⟨16675125686682563851483427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11116750457788375900988951 16675125686682563851483427)
  ·
    refine ⟨25012688530023845777225141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16675125686682563851483427 25012688530023845777225141)
    ·
      refine ⟨2344939549689735541614857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25012688530023845777225141 2344939549689735541614857)
      ·
        refine ⟨1758704662267301656211143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2344939549689735541614857 1758704662267301656211143)
        ·
          refine ⟨2638056993400952484316715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758704662267301656211143 2638056993400952484316715)
          ·
            refine ⟨3957085490101428726475073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638056993400952484316715 3957085490101428726475073)
            ·
              refine ⟨2967814117576071544856305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3957085490101428726475073 2967814117576071544856305)
              ·
                refine ⟨2225860588182053658642229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967814117576071544856305 2225860588182053658642229)
                ·
                  refine ⟨208674430142067530497709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2225860588182053658642229 208674430142067530497709)
                  ·
                    rfl

theorem cell20_457191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_457191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457191 prefixEnd_457191 := by exact prefixLift 457191
  have htrace : WordTrace (prefixWord ++ tailWord_457191) baseStart_457191 baseEnd_457191 := by
    simpa [prefixWord, tailWord_457191, baseEnd_457191] using wordTrace_append hprefix tailTrace_457191
  have hstable : (prefixWord ++ tailWord_457191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457191).length < 2 ^ (prefixWord ++ tailWord_457191).sum := by decide
  have hdescent : baseEnd_457191 < baseStart_457191 := by decide
  rcases family_descends (prefixWord ++ tailWord_457191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457194 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_457194 : Nat := 118140960795 + 457194 * 2 ^ 59
def prefixEnd_457194 : Nat := 4983230072969 + 3 ^ 40 * 457194 * 2
def baseEnd_457194 : Nat := 208675799423812853397697

theorem tailTrace_457194 : CollatzResearch.WordTrace tailWord_457194 prefixEnd_457194 208675799423812853397697 := by
  unfold tailWord_457194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168808776417923840960659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11116823403781130242561757 4168808776417923840960659)
  ·
    refine ⟨6253213164626885761440989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4168808776417923840960659 6253213164626885761440989)
    ·
      refine ⟨2344954936735082160540371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6253213164626885761440989 2344954936735082160540371)
      ·
        refine ⟨3517432405102623240810557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344954936735082160540371 3517432405102623240810557)
        ·
          refine ⟨1319037151913483715303959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3517432405102623240810557 1319037151913483715303959)
          ·
            refine ⟨1978555727870225572955939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319037151913483715303959 1978555727870225572955939)
            ·
              refine ⟨2967833591805338359433909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978555727870225572955939 2967833591805338359433909)
              ·
                refine ⟨278234399231750471196929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2967833591805338359433909 278234399231750471196929)
                ·
                  refine ⟨208675799423812853397697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278234399231750471196929 208675799423812853397697)
                  ·
                    rfl

theorem cell20_457194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_457194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457194 prefixEnd_457194 := by exact prefixLift 457194
  have htrace : WordTrace (prefixWord ++ tailWord_457194) baseStart_457194 baseEnd_457194 := by
    simpa [prefixWord, tailWord_457194, baseEnd_457194] using wordTrace_append hprefix tailTrace_457194
  have hstable : (prefixWord ++ tailWord_457194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457194).length < 2 ^ (prefixWord ++ tailWord_457194).sum := by decide
  have hdescent : baseEnd_457194 < baseStart_457194 := by decide
  rcases family_descends (prefixWord ++ tailWord_457194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457215 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 2]
def baseStart_457215 : Nat := 118140960795 + 457215 * 2 ^ 59
def prefixEnd_457215 : Nat := 4983230072969 + 3 ^ 40 * 457215 * 2
def baseEnd_457215 : Nat := 208685384396030113697611

theorem tailTrace_457215 : CollatzResearch.WordTrace tailWord_457215 prefixEnd_457215 208685384396030113697611 := by
  unfold tailWord_457215
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676001038595615950357099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11117334025730410633571399 16676001038595615950357099)
  ·
    refine ⟨25014001557893423925535649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676001038595615950357099 25014001557893423925535649)
    ·
      refine ⟨18760501168420067944151737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25014001557893423925535649 18760501168420067944151737)
      ·
        refine ⟨14070375876315050958113803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18760501168420067944151737 14070375876315050958113803)
        ·
          refine ⟨21105563814472576437170705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070375876315050958113803 21105563814472576437170705)
          ·
            refine ⟨15829172860854432327878029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21105563814472576437170705 15829172860854432327878029)
            ·
              refine ⟨5935939822820412122954261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15829172860854432327878029 5935939822820412122954261)
              ·
                refine ⟨278247179194706818263481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5935939822820412122954261 278247179194706818263481)
                ·
                  refine ⟨208685384396030113697611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278247179194706818263481 208685384396030113697611)
                  ·
                    rfl

theorem cell20_457215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 2].length) (baseStart_457215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457215 prefixEnd_457215 := by exact prefixLift 457215
  have htrace : WordTrace (prefixWord ++ tailWord_457215) baseStart_457215 baseEnd_457215 := by
    simpa [prefixWord, tailWord_457215, baseEnd_457215] using wordTrace_append hprefix tailTrace_457215
  have hstable : (prefixWord ++ tailWord_457215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457215).length < 2 ^ (prefixWord ++ tailWord_457215).sum := by decide
  have hdescent : baseEnd_457215 < baseStart_457215 := by decide
  rcases family_descends (prefixWord ++ tailWord_457215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457239 : List Nat := [1, 1, 3, 6, 1, 1, 1, 6]
def baseStart_457239 : Nat := 118140960795 + 457239 * 2 ^ 59
def prefixEnd_457239 : Nat := 4983230072969 + 3 ^ 40 * 457239 * 2
def baseEnd_457239 : Nat := 69565446216664232299171

theorem tailTrace_457239 : CollatzResearch.WordTrace tailWord_457239 prefixEnd_457239 69565446216664232299171 := by
  unfold tailWord_457239
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676876390508668049230771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11117917593672445366153847 16676876390508668049230771)
  ·
    refine ⟨25015314585763002073846157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676876390508668049230771 25015314585763002073846157)
    ·
      refine ⟨9380742969661125777692309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25015314585763002073846157 9380742969661125777692309)
      ·
        refine ⟨439722326702865270829327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9380742969661125777692309 439722326702865270829327)
        ·
          refine ⟨659583490054297906243991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439722326702865270829327 659583490054297906243991)
          ·
            refine ⟨989375235081446859365987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659583490054297906243991 989375235081446859365987)
            ·
              refine ⟨1484062852622170289048981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989375235081446859365987 1484062852622170289048981)
              ·
                refine ⟨69565446216664232299171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1484062852622170289048981 69565446216664232299171)
                ·
                  rfl

theorem cell20_457239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_457239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_457239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_457239 prefixEnd_457239 := by exact prefixLift 457239
  have htrace : WordTrace (prefixWord ++ tailWord_457239) baseStart_457239 baseEnd_457239 := by
    simpa [prefixWord, tailWord_457239, baseEnd_457239] using wordTrace_append hprefix tailTrace_457239
  have hstable : (prefixWord ++ tailWord_457239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457239).length < 2 ^ (prefixWord ++ tailWord_457239).sum := by decide
  have hdescent : baseEnd_457239 < baseStart_457239 := by decide
  rcases family_descends (prefixWord ++ tailWord_457239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
