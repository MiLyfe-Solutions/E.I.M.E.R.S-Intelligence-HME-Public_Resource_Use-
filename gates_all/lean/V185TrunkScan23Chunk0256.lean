import V185TrunkScan23Chunk0255

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1515015 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_1515015 : Nat := 118140960795 + 1515015 * 2 ^ 59
def prefixEnd_1515015 : Nat := 4983230072969 + 3 ^ 40 * 1515015 * 2
def baseEnd_1515015 : Nat := 777930893771495230545079

theorem tailTrace_1515015 : CollatzResearch.WordTrace tailWord_1515015 prefixEnd_1515015 777930893771495230545079 := by
  unfold tailWord_1515015
  simp only [CollatzResearch.WordTrace]
  refine ⟨55257136606366873807450499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36838091070911249204966999 55257136606366873807450499)
  ·
    refine ⟨82885704909550310711175749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55257136606366873807450499 82885704909550310711175749)
    ·
      refine ⟨15541069670540683258345453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82885704909550310711175749 15541069670540683258345453)
      ·
        refine ⟨5827901126452756221879545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15541069670540683258345453 5827901126452756221879545)
        ·
          refine ⟨4370925844839567166409659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5827901126452756221879545 4370925844839567166409659)
          ·
            refine ⟨6556388767259350749614489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370925844839567166409659 6556388767259350749614489)
            ·
              refine ⟨4917291575444513062210867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6556388767259350749614489 4917291575444513062210867)
              ·
                refine ⟨7375937363166769593316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917291575444513062210867 7375937363166769593316301)
                ·
                  refine ⟨2765976511187538597493613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7375937363166769593316301 2765976511187538597493613)
                  ·
                    refine ⟨1037241191695326974060105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765976511187538597493613 1037241191695326974060105)
                    ·
                      refine ⟨777930893771495230545079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037241191695326974060105 777930893771495230545079)
                      ·
                        rfl

theorem cell23_1515015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_1515015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515015 prefixEnd_1515015 := by exact prefixLift 1515015
  have htrace : WordTrace (prefixWord ++ tailWord_1515015) baseStart_1515015 baseEnd_1515015 := by
    simpa [prefixWord, tailWord_1515015, baseEnd_1515015] using wordTrace_append hprefix tailTrace_1515015
  have hstable : (prefixWord ++ tailWord_1515015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515015).length < 2 ^ (prefixWord ++ tailWord_1515015).sum := by decide
  have hdescent : baseEnd_1515015 < baseStart_1515015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515032 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 1, 3, 2]
def baseStart_1515032 : Nat := 118140960795 + 1515032 * 2 ^ 59
def prefixEnd_1515032 : Nat := 4983230072969 + 3 ^ 40 * 1515032 * 2
def baseEnd_1515032 : Nat := 777939622942621664032501

theorem tailTrace_1515032 : CollatzResearch.WordTrace tailWord_1515032 prefixEnd_1515032 777939622942621664032501 := by
  unfold tailWord_1515032
  simp only [CollatzResearch.WordTrace]
  refine ⟨27628878323652642855409675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36838504431536857140546233 27628878323652642855409675)
  ·
    refine ⟨41443317485478964283114513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27628878323652642855409675 41443317485478964283114513)
    ·
      refine ⟨31082488114109223212335885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41443317485478964283114513 31082488114109223212335885)
      ·
        refine ⟨11655933042790958704625957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31082488114109223212335885 11655933042790958704625957)
        ·
          refine ⟨2185487445523304757117367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11655933042790958704625957 2185487445523304757117367)
          ·
            refine ⟨3278231168284957135676051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185487445523304757117367 3278231168284957135676051)
            ·
              refine ⟨4917346752427435703514077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278231168284957135676051 4917346752427435703514077)
              ·
                refine ⟨1844005032160288388817779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4917346752427435703514077 1844005032160288388817779)
                ·
                  refine ⟨2766007548240432583226669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844005032160288388817779 2766007548240432583226669)
                  ·
                    refine ⟨1037252830590162218710001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766007548240432583226669 1037252830590162218710001)
                    ·
                      refine ⟨777939622942621664032501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037252830590162218710001 777939622942621664032501)
                      ·
                        rfl

theorem cell23_1515032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_1515032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515032 prefixEnd_1515032 := by exact prefixLift 1515032
  have htrace : WordTrace (prefixWord ++ tailWord_1515032) baseStart_1515032 baseEnd_1515032 := by
    simpa [prefixWord, tailWord_1515032, baseEnd_1515032] using wordTrace_append hprefix tailTrace_1515032
  have hstable : (prefixWord ++ tailWord_1515032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515032).length < 2 ^ (prefixWord ++ tailWord_1515032).sum := by decide
  have hdescent : baseEnd_1515032 < baseStart_1515032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515081 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_1515081 : Nat := 118140960795 + 1515081 * 2 ^ 59
def prefixEnd_1515081 : Nat := 4983230072969 + 3 ^ 40 * 1515081 * 2
def baseEnd_1515081 : Nat := 259321594498230657439925

theorem tailTrace_1515081 : CollatzResearch.WordTrace tailWord_1515081 prefixEnd_1515081 259321594498230657439925 := by
  unfold tailWord_1515081
  simp only [CollatzResearch.WordTrace]
  refine ⟨55259543824127767079353097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36839695882751844719568731 55259543824127767079353097)
  ·
    refine ⟨41444657868095825309514823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55259543824127767079353097 41444657868095825309514823)
    ·
      refine ⟨62166986802143737964272235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41444657868095825309514823 62166986802143737964272235)
      ·
        refine ⟨93250480203215606946408353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62166986802143737964272235 93250480203215606946408353)
        ·
          refine ⟨69937860152411705209806265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93250480203215606946408353 69937860152411705209806265)
          ·
            refine ⟨52453395114308778907354699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69937860152411705209806265 52453395114308778907354699)
            ·
              refine ⟨78680092671463168361032049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52453395114308778907354699 78680092671463168361032049)
              ·
                refine ⟨59010069503597376270774037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78680092671463168361032049 59010069503597376270774037)
                ·
                  refine ⟨2766097007981127012692533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59010069503597376270774037 2766097007981127012692533)
                  ·
                    refine ⟨259321594498230657439925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2766097007981127012692533 259321594498230657439925)
                    ·
                      rfl

theorem cell23_1515081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_1515081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515081 prefixEnd_1515081 := by exact prefixLift 1515081
  have htrace : WordTrace (prefixWord ++ tailWord_1515081) baseStart_1515081 baseEnd_1515081 := by
    simpa [prefixWord, tailWord_1515081, baseEnd_1515081] using wordTrace_append hprefix tailTrace_1515081
  have hstable : (prefixWord ++ tailWord_1515081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515081).length < 2 ^ (prefixWord ++ tailWord_1515081).sum := by decide
  have hdescent : baseEnd_1515081 < baseStart_1515081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515108 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_1515108 : Nat := 118140960795 + 1515108 * 2 ^ 59
def prefixEnd_1515108 : Nat := 4983230072969 + 3 ^ 40 * 1515108 * 2
def baseEnd_1515108 : Nat := 777978647472363366682151

theorem tailTrace_1515108 : CollatzResearch.WordTrace tailWord_1515108 prefixEnd_1515108 777978647472363366682151 := by
  unfold tailWord_1515108
  simp only [CollatzResearch.WordTrace]
  refine ⟨27630264297514975345292989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36840352396686633793723985 27630264297514975345292989)
  ·
    refine ⟨10361349111568115754484871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27630264297514975345292989 10361349111568115754484871)
    ·
      refine ⟨15542023667352173631727307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10361349111568115754484871 15542023667352173631727307)
      ·
        refine ⟨23313035501028260447590961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15542023667352173631727307 23313035501028260447590961)
        ·
          refine ⟨17484776625771195335693221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23313035501028260447590961 17484776625771195335693221)
          ·
            refine ⟨3278395617332099125442479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17484776625771195335693221 3278395617332099125442479)
            ·
              refine ⟨4917593425998148688163719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278395617332099125442479 4917593425998148688163719)
              ·
                refine ⟨7376390138997223032245579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917593425998148688163719 7376390138997223032245579)
                ·
                  refine ⟨11064585208495834548368369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7376390138997223032245579 11064585208495834548368369)
                  ·
                    refine ⟨8298438906371875911276277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11064585208495834548368369 8298438906371875911276277)
                    ·
                      refine ⟨777978647472363366682151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8298438906371875911276277 777978647472363366682151)
                      ·
                        rfl

theorem cell23_1515108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_1515108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515108 prefixEnd_1515108 := by exact prefixLift 1515108
  have htrace : WordTrace (prefixWord ++ tailWord_1515108) baseStart_1515108 baseEnd_1515108 := by
    simpa [prefixWord, tailWord_1515108, baseEnd_1515108] using wordTrace_append hprefix tailTrace_1515108
  have hstable : (prefixWord ++ tailWord_1515108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515108).length < 2 ^ (prefixWord ++ tailWord_1515108).sum := by decide
  have hdescent : baseEnd_1515108 < baseStart_1515108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515121 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1515121 : Nat := 118140960795 + 1515121 * 2 ^ 59
def prefixEnd_1515121 : Nat := 4983230072969 + 3 ^ 40 * 1515121 * 2
def baseEnd_1515121 : Nat := 777985322720871815819591

theorem tailTrace_1515121 : CollatzResearch.WordTrace tailWord_1515121 prefixEnd_1515121 777985322720871815819591 := by
  unfold tailWord_1515121
  simp only [CollatzResearch.WordTrace]
  refine ⟨55261002743982853910809217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36840668495988569273872811 55261002743982853910809217)
  ·
    refine ⟨41445752057987140433106913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55261002743982853910809217 41445752057987140433106913)
    ·
      refine ⟨31084314043490355324830185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41445752057987140433106913 31084314043490355324830185)
      ·
        refine ⟨23313235532617766493622639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31084314043490355324830185 23313235532617766493622639)
        ·
          refine ⟨34969853298926649740433959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23313235532617766493622639 34969853298926649740433959)
          ·
            refine ⟨52454779948389974610650939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34969853298926649740433959 52454779948389974610650939)
            ·
              refine ⟨78682169922584961915976409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52454779948389974610650939 78682169922584961915976409)
              ·
                refine ⟨59011627441938721436982307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78682169922584961915976409 59011627441938721436982307)
                ·
                  refine ⟨88517441162908082155473461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59011627441938721436982307 88517441162908082155473461)
                  ·
                    refine ⟨8298510109022632702075637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88517441162908082155473461 8298510109022632702075637)
                    ·
                      refine ⟨777985322720871815819591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8298510109022632702075637 777985322720871815819591)
                      ·
                        rfl

theorem cell23_1515121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1515121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515121 prefixEnd_1515121 := by exact prefixLift 1515121
  have htrace : WordTrace (prefixWord ++ tailWord_1515121) baseStart_1515121 baseEnd_1515121 := by
    simpa [prefixWord, tailWord_1515121, baseEnd_1515121] using wordTrace_append hprefix tailTrace_1515121
  have hstable : (prefixWord ++ tailWord_1515121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515121).length < 2 ^ (prefixWord ++ tailWord_1515121).sum := by decide
  have hdescent : baseEnd_1515121 < baseStart_1515121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515189 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1515189 : Nat := 118140960795 + 1515189 * 2 ^ 59
def prefixEnd_1515189 : Nat := 4983230072969 + 3 ^ 40 * 1515189 * 2
def baseEnd_1515189 : Nat := 778020239405377549769279

theorem tailTrace_1515189 : CollatzResearch.WordTrace tailWord_1515189 prefixEnd_1515189 778020239405377549769279 := by
  unfold tailWord_1515189
  simp only [CollatzResearch.WordTrace]
  refine ⟨55263482907736501524284621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36842321938491001016189747 55263482907736501524284621)
  ·
    refine ⟨20723806090401188071606733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55263482907736501524284621 20723806090401188071606733)
    ·
      refine ⟨7771427283900445526852525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20723806090401188071606733 7771427283900445526852525)
      ·
        refine ⟨2914285231462667072569697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7771427283900445526852525 2914285231462667072569697)
        ·
          refine ⟨2185713923597000304427273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2914285231462667072569697 2185713923597000304427273)
          ·
            refine ⟨1639285442697750228320455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2185713923597000304427273 1639285442697750228320455)
            ·
              refine ⟨2458928164046625342480683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639285442697750228320455 2458928164046625342480683)
              ·
                refine ⟨3688392246069938013721025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458928164046625342480683 3688392246069938013721025)
                ·
                  refine ⟨2766294184552453510290769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688392246069938013721025 2766294184552453510290769)
                  ·
                    refine ⟨2074720638414340132718077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2766294184552453510290769 2074720638414340132718077)
                    ·
                      refine ⟨778020239405377549769279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2074720638414340132718077 778020239405377549769279)
                      ·
                        rfl

theorem cell23_1515189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1515189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515189 prefixEnd_1515189 := by exact prefixLift 1515189
  have htrace : WordTrace (prefixWord ++ tailWord_1515189) baseStart_1515189 baseEnd_1515189 := by
    simpa [prefixWord, tailWord_1515189, baseEnd_1515189] using wordTrace_append hprefix tailTrace_1515189
  have hstable : (prefixWord ++ tailWord_1515189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515189).length < 2 ^ (prefixWord ++ tailWord_1515189).sum := by decide
  have hdescent : baseEnd_1515189 < baseStart_1515189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515239 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1515239 : Nat := 118140960795 + 1515239 * 2 ^ 59
def prefixEnd_1515239 : Nat := 4983230072969 + 3 ^ 40 * 1515239 * 2
def baseEnd_1515239 : Nat := 259348637812700784714683

theorem tailTrace_1515239 : CollatzResearch.WordTrace tailWord_1515239 prefixEnd_1515239 259348637812700784714683 := by
  unfold tailWord_1515239
  simp only [CollatzResearch.WordTrace]
  refine ⟨55265306557555360063604771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36843537705036906709069847 55265306557555360063604771)
  ·
    refine ⟨82897959836333040095407157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55265306557555360063604771 82897959836333040095407157)
    ·
      refine ⟨7771683734656222508944421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82897959836333040095407157 7771683734656222508944421)
      ·
        refine ⟨1457190700248041720427079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7771683734656222508944421 1457190700248041720427079)
        ·
          refine ⟨2185786050372062580640619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457190700248041720427079 2185786050372062580640619)
          ·
            refine ⟨3278679075558093870960929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185786050372062580640619 3278679075558093870960929)
            ·
              refine ⟨2459009306668570403220697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278679075558093870960929 2459009306668570403220697)
              ·
                refine ⟨1844256980001427802415523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459009306668570403220697 1844256980001427802415523)
                ·
                  refine ⟨2766385470002141703623285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844256980001427802415523 2766385470002141703623285)
                  ·
                    refine ⟨259348637812700784714683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2766385470002141703623285 259348637812700784714683)
                    ·
                      rfl

theorem cell23_1515239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1515239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515239 prefixEnd_1515239 := by exact prefixLift 1515239
  have htrace : WordTrace (prefixWord ++ tailWord_1515239) baseStart_1515239 baseEnd_1515239 := by
    simpa [prefixWord, tailWord_1515239, baseEnd_1515239] using wordTrace_append hprefix tailTrace_1515239
  have hstable : (prefixWord ++ tailWord_1515239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515239).length < 2 ^ (prefixWord ++ tailWord_1515239).sum := by decide
  have hdescent : baseEnd_1515239 < baseStart_1515239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515259 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 1, 2, 2]
def baseStart_1515259 : Nat := 118140960795 + 1515259 * 2 ^ 59
def prefixEnd_1515259 : Nat := 4983230072969 + 3 ^ 40 * 1515259 * 2
def baseEnd_1515259 : Nat := 778056183051192275893957

theorem tailTrace_1515259 : CollatzResearch.WordTrace tailWord_1515259 prefixEnd_1515259 778056183051192275893957 := by
  unfold tailWord_1515259
  simp only [CollatzResearch.WordTrace]
  refine ⟨55266036017482903479332831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36844024011655268986221887 55266036017482903479332831)
  ·
    refine ⟨82899054026224355218999247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55266036017482903479332831 82899054026224355218999247)
    ·
      refine ⟨124348581039336532828498871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82899054026224355218999247 124348581039336532828498871)
      ·
        refine ⟨186522871559004799242748307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124348581039336532828498871 186522871559004799242748307)
        ·
          refine ⟨279784307338507198864122461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186522871559004799242748307 279784307338507198864122461)
          ·
            refine ⟨104919115251940199574045923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279784307338507198864122461 104919115251940199574045923)
            ·
              refine ⟨157378672877910299361068885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104919115251940199574045923 157378672877910299361068885)
              ·
                refine ⟨922140661394005660318763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 157378672877910299361068885 922140661394005660318763)
                ·
                  refine ⟨1383210992091008490478145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922140661394005660318763 1383210992091008490478145)
                  ·
                    refine ⟨1037408244068256367858609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1383210992091008490478145 1037408244068256367858609)
                    ·
                      refine ⟨778056183051192275893957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037408244068256367858609 778056183051192275893957)
                      ·
                        rfl

theorem cell23_1515259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 2, 2].length) (baseStart_1515259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515259 prefixEnd_1515259 := by exact prefixLift 1515259
  have htrace : WordTrace (prefixWord ++ tailWord_1515259) baseStart_1515259 baseEnd_1515259 := by
    simpa [prefixWord, tailWord_1515259, baseEnd_1515259] using wordTrace_append hprefix tailTrace_1515259
  have hstable : (prefixWord ++ tailWord_1515259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515259).length < 2 ^ (prefixWord ++ tailWord_1515259).sum := by decide
  have hdescent : baseEnd_1515259 < baseStart_1515259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515282 : List Nat := [3, 2, 4, 1, 1, 2, 2, 8]
def baseStart_1515282 : Nat := 118140960795 + 1515282 * 2 ^ 59
def prefixEnd_1515282 : Nat := 4983230072969 + 3 ^ 40 * 1515282 * 2
def baseEnd_1515282 : Nat := 28817333078009099478013

theorem tailTrace_1515282 : CollatzResearch.WordTrace tailWord_1515282 prefixEnd_1515282 28817333078009099478013 := by
  unfold tailWord_1515282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13816718724099894601855025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36844583264266385604946733 13816718724099894601855025)
  ·
    refine ⟨10362539043074920951391269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13816718724099894601855025 10362539043074920951391269)
    ·
      refine ⟨1942976070576547678385863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10362539043074920951391269 1942976070576547678385863)
      ·
        refine ⟨2914464105864821517578795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1942976070576547678385863 2914464105864821517578795)
        ·
          refine ⟨4371696158797232276368193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914464105864821517578795 4371696158797232276368193)
          ·
            refine ⟨3278772119097924207276145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4371696158797232276368193 3278772119097924207276145)
            ·
              refine ⟨2459079089323443155457109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278772119097924207276145 2459079089323443155457109)
              ·
                refine ⟨28817333078009099478013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2459079089323443155457109 28817333078009099478013)
                ·
                  rfl

theorem cell23_1515282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_1515282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515282 prefixEnd_1515282 := by exact prefixLift 1515282
  have htrace : WordTrace (prefixWord ++ tailWord_1515282) baseStart_1515282 baseEnd_1515282 := by
    simpa [prefixWord, tailWord_1515282, baseEnd_1515282] using wordTrace_append hprefix tailTrace_1515282
  have hstable : (prefixWord ++ tailWord_1515282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515282).length < 2 ^ (prefixWord ++ tailWord_1515282).sum := by decide
  have hdescent : baseEnd_1515282 < baseStart_1515282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515326 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1515326 : Nat := 118140960795 + 1515326 * 2 ^ 59
def prefixEnd_1515326 : Nat := 4983230072969 + 3 ^ 40 * 1515326 * 2
def baseEnd_1515326 : Nat := 778090586255043513756149

theorem tailTrace_1515326 : CollatzResearch.WordTrace tailWord_1515326 prefixEnd_1515326 778090586255043513756149 := by
  unfold tailWord_1515326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908559963530021740252729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36845653138826782614681221 6908559963530021740252729)
  ·
    refine ⟨5181419972647516305189547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6908559963530021740252729 5181419972647516305189547)
    ·
      refine ⟨7772129958971274457784321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5181419972647516305189547 7772129958971274457784321)
      ·
        refine ⟨5829097469228455843338241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7772129958971274457784321 5829097469228455843338241)
        ·
          refine ⟨4371823101921341882503681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5829097469228455843338241 4371823101921341882503681)
          ·
            refine ⟨3278867326441006411877761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4371823101921341882503681 3278867326441006411877761)
            ·
              refine ⟨2459150494830754808908321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278867326441006411877761 2459150494830754808908321)
              ·
                refine ⟨1844362871123066106681241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459150494830754808908321 1844362871123066106681241)
                ·
                  refine ⟨1383272153342299580010931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1844362871123066106681241 1383272153342299580010931)
                  ·
                    refine ⟨2074908230013449370016397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383272153342299580010931 2074908230013449370016397)
                    ·
                      refine ⟨778090586255043513756149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2074908230013449370016397 778090586255043513756149)
                      ·
                        rfl

theorem cell23_1515326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1515326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515326 prefixEnd_1515326 := by exact prefixLift 1515326
  have htrace : WordTrace (prefixWord ++ tailWord_1515326) baseStart_1515326 baseEnd_1515326 := by
    simpa [prefixWord, tailWord_1515326, baseEnd_1515326] using wordTrace_append hprefix tailTrace_1515326
  have hstable : (prefixWord ++ tailWord_1515326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515326).length < 2 ^ (prefixWord ++ tailWord_1515326).sum := by decide
  have hdescent : baseEnd_1515326 < baseStart_1515326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515328 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_1515328 : Nat := 118140960795 + 1515328 * 2 ^ 59
def prefixEnd_1515328 : Nat := 4983230072969 + 3 ^ 40 * 1515328 * 2
def baseEnd_1515328 : Nat := 778091613216352505931139

theorem tailTrace_1515328 : CollatzResearch.WordTrace tailWord_1515328 prefixEnd_1515328 778091613216352505931139 := by
  unfold tailWord_1515328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27634276327116464131797319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36845701769488618842396425 27634276327116464131797319)
  ·
    refine ⟨41451414490674696197695979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27634276327116464131797319 41451414490674696197695979)
    ·
      refine ⟨62177121736012044296543969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41451414490674696197695979 62177121736012044296543969)
      ·
        refine ⟨46632841302009033222407977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62177121736012044296543969 46632841302009033222407977)
        ·
          refine ⟨34974630976506774916805983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46632841302009033222407977 34974630976506774916805983)
          ·
            refine ⟨52461946464760162375208975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34974630976506774916805983 52461946464760162375208975)
            ·
              refine ⟨78692919697140243562813463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52461946464760162375208975 78692919697140243562813463)
              ·
                refine ⟨118039379545710365344220195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78692919697140243562813463 118039379545710365344220195)
                ·
                  refine ⟨177059069318565548016330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118039379545710365344220195 177059069318565548016330293)
                  ·
                    refine ⟨16599287748615520126530965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177059069318565548016330293 16599287748615520126530965)
                    ·
                      refine ⟨778091613216352505931139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16599287748615520126530965 778091613216352505931139)
                      ·
                        rfl

theorem cell23_1515328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_1515328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515328 prefixEnd_1515328 := by exact prefixLift 1515328
  have htrace : WordTrace (prefixWord ++ tailWord_1515328) baseStart_1515328 baseEnd_1515328 := by
    simpa [prefixWord, tailWord_1515328, baseEnd_1515328] using wordTrace_append hprefix tailTrace_1515328
  have hstable : (prefixWord ++ tailWord_1515328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515328).length < 2 ^ (prefixWord ++ tailWord_1515328).sum := by decide
  have hdescent : baseEnd_1515328 < baseStart_1515328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515335 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_1515335 : Nat := 118140960795 + 1515335 * 2 ^ 59
def prefixEnd_1515335 : Nat := 4983230072969 + 3 ^ 40 * 1515335 * 2
def baseEnd_1515335 : Nat := 778095207580933978543607

theorem tailTrace_1515335 : CollatzResearch.WordTrace tailWord_1515335 prefixEnd_1515335 778095207580933978543607 := by
  unfold tailWord_1515335
  simp only [CollatzResearch.WordTrace]
  refine ⟨55268807965207568459099459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36845871976805045639399639 55268807965207568459099459)
  ·
    refine ⟨82903211947811352688649189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55268807965207568459099459 82903211947811352688649189)
    ·
      refine ⟨15544352240214628629121723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82903211947811352688649189 15544352240214628629121723)
      ·
        refine ⟨23316528360321942943682585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15544352240214628629121723 23316528360321942943682585)
        ·
          refine ⟨17487396270241457207761939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23316528360321942943682585 17487396270241457207761939)
          ·
            refine ⟨26231094405362185811642909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17487396270241457207761939 26231094405362185811642909)
            ·
              refine ⟨9836660402010819679366091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26231094405362185811642909 9836660402010819679366091)
              ·
                refine ⟨14754990603016229519049137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9836660402010819679366091 14754990603016229519049137)
                ·
                  refine ⟨11066242952262172139286853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14754990603016229519049137 11066242952262172139286853)
                  ·
                    refine ⟨2074920553549157276116285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11066242952262172139286853 2074920553549157276116285)
                    ·
                      refine ⟨778095207580933978543607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2074920553549157276116285 778095207580933978543607)
                      ·
                        rfl

theorem cell23_1515335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_1515335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515335 prefixEnd_1515335 := by exact prefixLift 1515335
  have htrace : WordTrace (prefixWord ++ tailWord_1515335) baseStart_1515335 baseEnd_1515335 := by
    simpa [prefixWord, tailWord_1515335, baseEnd_1515335] using wordTrace_append hprefix tailTrace_1515335
  have hstable : (prefixWord ++ tailWord_1515335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515335).length < 2 ^ (prefixWord ++ tailWord_1515335).sum := by decide
  have hdescent : baseEnd_1515335 < baseStart_1515335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515345 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_1515345 : Nat := 118140960795 + 1515345 * 2 ^ 59
def prefixEnd_1515345 : Nat := 4983230072969 + 3 ^ 40 * 1515345 * 2
def baseEnd_1515345 : Nat := 778100342387478939418561

theorem tailTrace_1515345 : CollatzResearch.WordTrace tailWord_1515345 prefixEnd_1515345 778100342387478939418561 := by
  unfold tailWord_1515345
  simp only [CollatzResearch.WordTrace]
  refine ⟨55269172695171340166963489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36846115130114226777975659 55269172695171340166963489)
  ·
    refine ⟨41451879521378505125222617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55269172695171340166963489 41451879521378505125222617)
    ·
      refine ⟨31088909641033878843916963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41451879521378505125222617 31088909641033878843916963)
      ·
        refine ⟨46633364461550818265875445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31088909641033878843916963 46633364461550818265875445)
        ·
          refine ⟨4371877918270389212425823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46633364461550818265875445 4371877918270389212425823)
          ·
            refine ⟨6557816877405583818638735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4371877918270389212425823 6557816877405583818638735)
            ·
              refine ⟨9836725316108375727958103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6557816877405583818638735 9836725316108375727958103)
              ·
                refine ⟨14755087974162563591937155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9836725316108375727958103 14755087974162563591937155)
                ·
                  refine ⟨22132631961243845387905733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14755087974162563591937155 22132631961243845387905733)
                  ·
                    refine ⟨4149868492733221010232325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22132631961243845387905733 4149868492733221010232325)
                    ·
                      refine ⟨778100342387478939418561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4149868492733221010232325 778100342387478939418561)
                      ·
                        rfl

theorem cell23_1515345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_1515345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515345 prefixEnd_1515345 := by exact prefixLift 1515345
  have htrace : WordTrace (prefixWord ++ tailWord_1515345) baseStart_1515345 baseEnd_1515345 := by
    simpa [prefixWord, tailWord_1515345, baseEnd_1515345] using wordTrace_append hprefix tailTrace_1515345
  have hstable : (prefixWord ++ tailWord_1515345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515345).length < 2 ^ (prefixWord ++ tailWord_1515345).sum := by decide
  have hdescent : baseEnd_1515345 < baseStart_1515345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515349 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_1515349 : Nat := 118140960795 + 1515349 * 2 ^ 59
def prefixEnd_1515349 : Nat := 4983230072969 + 3 ^ 40 * 1515349 * 2
def baseEnd_1515349 : Nat := 778102396310096923768543

theorem tailTrace_1515349 : CollatzResearch.WordTrace tailWord_1515349 prefixEnd_1515349 778102396310096923768543 := by
  unfold tailWord_1515349
  simp only [CollatzResearch.WordTrace]
  refine ⟨55269318587156848850109101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36846212391437899233406067 55269318587156848850109101)
  ·
    refine ⟨20725994470183818318790913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55269318587156848850109101 20725994470183818318790913)
    ·
      refine ⟨15544495852637863739093185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20725994470183818318790913 15544495852637863739093185)
      ·
        refine ⟨11658371889478397804319889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15544495852637863739093185 11658371889478397804319889)
        ·
          refine ⟨8743778917108798353239917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11658371889478397804319889 8743778917108798353239917)
          ·
            refine ⟨3278917093915799382464969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8743778917108798353239917 3278917093915799382464969)
            ·
              refine ⟨2459187820436849536848727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278917093915799382464969 2459187820436849536848727)
              ·
                refine ⟨3688781730655274305273091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459187820436849536848727 3688781730655274305273091)
                ·
                  refine ⟨5533172595982911457909637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688781730655274305273091 5533172595982911457909637)
                  ·
                    refine ⟨1037469861746795898358057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533172595982911457909637 1037469861746795898358057)
                    ·
                      refine ⟨778102396310096923768543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037469861746795898358057 778102396310096923768543)
                      ·
                        rfl

theorem cell23_1515349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_1515349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515349 prefixEnd_1515349 := by exact prefixLift 1515349
  have htrace : WordTrace (prefixWord ++ tailWord_1515349) baseStart_1515349 baseEnd_1515349 := by
    simpa [prefixWord, tailWord_1515349, baseEnd_1515349] using wordTrace_append hprefix tailTrace_1515349
  have hstable : (prefixWord ++ tailWord_1515349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515349).length < 2 ^ (prefixWord ++ tailWord_1515349).sum := by decide
  have hdescent : baseEnd_1515349 < baseStart_1515349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515365 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1515365 : Nat := 118140960795 + 1515365 * 2 ^ 59
def prefixEnd_1515365 : Nat := 4983230072969 + 3 ^ 40 * 1515365 * 2
def baseEnd_1515365 : Nat := 778110612000568861168469

theorem tailTrace_1515365 : CollatzResearch.WordTrace tailWord_1515365 prefixEnd_1515365 778110612000568861168469 := by
  unfold tailWord_1515365
  simp only [CollatzResearch.WordTrace]
  refine ⟨55269902155098883582691549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36846601436732589055127699 55269902155098883582691549)
  ·
    refine ⟨20726213308162081343509331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55269902155098883582691549 20726213308162081343509331)
    ·
      refine ⟨31089319962243122015263997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20726213308162081343509331 31089319962243122015263997)
      ·
        refine ⟨11658494985841170755723999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31089319962243122015263997 11658494985841170755723999)
        ·
          refine ⟨17487742478761756133585999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11658494985841170755723999 17487742478761756133585999)
          ·
            refine ⟨26231613718142634200378999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17487742478761756133585999 26231613718142634200378999)
            ·
              refine ⟨39347420577213951300568499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26231613718142634200378999 39347420577213951300568499)
              ·
                refine ⟨59021130865820926950852749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39347420577213951300568499 59021130865820926950852749)
                ·
                  refine ⟨22132924074682847606569781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59021130865820926950852749 22132924074682847606569781)
                  ·
                    refine ⟨2074961632001516963115917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22132924074682847606569781 2074961632001516963115917)
                    ·
                      refine ⟨778110612000568861168469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2074961632001516963115917 778110612000568861168469)
                      ·
                        rfl

theorem cell23_1515365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1515365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515365 prefixEnd_1515365 := by exact prefixLift 1515365
  have htrace : WordTrace (prefixWord ++ tailWord_1515365) baseStart_1515365 baseEnd_1515365 := by
    simpa [prefixWord, tailWord_1515365, baseEnd_1515365] using wordTrace_append hprefix tailTrace_1515365
  have hstable : (prefixWord ++ tailWord_1515365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515365).length < 2 ^ (prefixWord ++ tailWord_1515365).sum := by decide
  have hdescent : baseEnd_1515365 < baseStart_1515365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515370 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1515370 : Nat := 118140960795 + 1515370 * 2 ^ 59
def prefixEnd_1515370 : Nat := 4983230072969 + 3 ^ 40 * 1515370 * 2
def baseEnd_1515370 : Nat := 778113179403841341605947

theorem tailTrace_1515370 : CollatzResearch.WordTrace tailWord_1515370 prefixEnd_1515370 778113179403841341605947 := by
  unfold tailWord_1515370
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817521130020192359155891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36846723013387179624415709 13817521130020192359155891)
  ·
    refine ⟨20726281695030288538733837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13817521130020192359155891 20726281695030288538733837)
    ·
      refine ⟨7772355635636358202025189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20726281695030288538733837 7772355635636358202025189)
      ·
        refine ⟨1457316681681817162879723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7772355635636358202025189 1457316681681817162879723)
        ·
          refine ⟨2185975022522725744319585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457316681681817162879723 2185975022522725744319585)
          ·
            refine ⟨1639481266892044308239689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2185975022522725744319585 1639481266892044308239689)
            ·
              refine ⟨1229610950169033231179767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639481266892044308239689 1229610950169033231179767)
              ·
                refine ⟨1844416425253549846769651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229610950169033231179767 1844416425253549846769651)
                ·
                  refine ⟨2766624637880324770154477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844416425253549846769651 2766624637880324770154477)
                  ·
                    refine ⟨1037484239205121788807929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2766624637880324770154477 1037484239205121788807929)
                    ·
                      refine ⟨778113179403841341605947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037484239205121788807929 778113179403841341605947)
                      ·
                        rfl

theorem cell23_1515370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1515370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515370 prefixEnd_1515370 := by exact prefixLift 1515370
  have htrace : WordTrace (prefixWord ++ tailWord_1515370) baseStart_1515370 baseEnd_1515370 := by
    simpa [prefixWord, tailWord_1515370, baseEnd_1515370] using wordTrace_append hprefix tailTrace_1515370
  have hstable : (prefixWord ++ tailWord_1515370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515370).length < 2 ^ (prefixWord ++ tailWord_1515370).sum := by decide
  have hdescent : baseEnd_1515370 < baseStart_1515370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515372 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 5]
def baseStart_1515372 : Nat := 118140960795 + 1515372 * 2 ^ 59
def prefixEnd_1515372 : Nat := 4983230072969 + 3 ^ 40 * 1515372 * 2
def baseEnd_1515372 : Nat := 86457134040572259308993

theorem tailTrace_1515372 : CollatzResearch.WordTrace tailWord_1515372 prefixEnd_1515372 86457134040572259308993 := by
  unfold tailWord_1515372
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635078733036761889098185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36846771644049015852130913 27635078733036761889098185)
  ·
    refine ⟨20726309049777571416823639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27635078733036761889098185 20726309049777571416823639)
    ·
      refine ⟨31089463574666357125235459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20726309049777571416823639 31089463574666357125235459)
      ·
        refine ⟨46634195361999535687853189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31089463574666357125235459 46634195361999535687853189)
        ·
          refine ⟨8743911630374912941472473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46634195361999535687853189 8743911630374912941472473)
          ·
            refine ⟨6557933722781184706104355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8743911630374912941472473 6557933722781184706104355)
            ·
              refine ⟨9836900584171777059156533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6557933722781184706104355 9836900584171777059156533)
              ·
                refine ⟨922209429766104099295925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9836900584171777059156533 922209429766104099295925)
                ·
                  refine ⟨86457134040572259308993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 922209429766104099295925 86457134040572259308993)
                  ·
                    rfl

theorem cell23_1515372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_1515372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515372 prefixEnd_1515372 := by exact prefixLift 1515372
  have htrace : WordTrace (prefixWord ++ tailWord_1515372) baseStart_1515372 baseEnd_1515372 := by
    simpa [prefixWord, tailWord_1515372, baseEnd_1515372] using wordTrace_append hprefix tailTrace_1515372
  have hstable : (prefixWord ++ tailWord_1515372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515372).length < 2 ^ (prefixWord ++ tailWord_1515372).sum := by decide
  have hdescent : baseEnd_1515372 < baseStart_1515372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515385 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_1515385 : Nat := 118140960795 + 1515385 * 2 ^ 59
def prefixEnd_1515385 : Nat := 4983230072969 + 3 ^ 40 * 1515385 * 2
def baseEnd_1515385 : Nat := 259373627204552927639459

theorem tailTrace_1515385 : CollatzResearch.WordTrace tailWord_1515385 prefixEnd_1515385 259373627204552927639459 := by
  unfold tailWord_1515385
  simp only [CollatzResearch.WordTrace]
  refine ⟨55270631615026426998419609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36847087743350951332279739 55270631615026426998419609)
  ·
    refine ⟨41452973711269820248814707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55270631615026426998419609 41452973711269820248814707)
    ·
      refine ⟨62179460566904730373222061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41452973711269820248814707 62179460566904730373222061)
      ·
        refine ⟨23317297712589273889958273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62179460566904730373222061 23317297712589273889958273)
        ·
          refine ⟨17487973284441955417468705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23317297712589273889958273 17487973284441955417468705)
          ·
            refine ⟨13115979963331466563101529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17487973284441955417468705 13115979963331466563101529)
            ·
              refine ⟨9836984972498599922326147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13115979963331466563101529 9836984972498599922326147)
              ·
                refine ⟨14755477458747899883489221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9836984972498599922326147 14755477458747899883489221)
                ·
                  refine ⟨2766652023515231228154229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14755477458747899883489221 2766652023515231228154229)
                  ·
                    refine ⟨259373627204552927639459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2766652023515231228154229 259373627204552927639459)
                    ·
                      rfl

theorem cell23_1515385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_1515385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515385 prefixEnd_1515385 := by exact prefixLift 1515385
  have htrace : WordTrace (prefixWord ++ tailWord_1515385) baseStart_1515385 baseEnd_1515385 := by
    simpa [prefixWord, tailWord_1515385, baseEnd_1515385] using wordTrace_append hprefix tailTrace_1515385
  have hstable : (prefixWord ++ tailWord_1515385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515385).length < 2 ^ (prefixWord ++ tailWord_1515385).sum := by decide
  have hdescent : baseEnd_1515385 < baseStart_1515385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515512 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_1515512 : Nat := 118140960795 + 1515512 * 2 ^ 59
def prefixEnd_1515512 : Nat := 4983230072969 + 3 ^ 40 * 1515512 * 2
def baseEnd_1515512 : Nat := 778186093656779786030293

theorem tailTrace_1515512 : CollatzResearch.WordTrace tailWord_1515512 prefixEnd_1515512 778186093656779786030293 := by
  unfold tailWord_1515512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27637631842783163844146395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36850175790377551792195193 27637631842783163844146395)
  ·
    refine ⟨41456447764174745766219593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27637631842783163844146395 41456447764174745766219593)
    ·
      refine ⟨31092335823131059324664695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41456447764174745766219593 31092335823131059324664695)
      ·
        refine ⟨46638503734696588986997043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31092335823131059324664695 46638503734696588986997043)
        ·
          refine ⟨69957755602044883480495565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46638503734696588986997043 69957755602044883480495565)
          ·
            refine ⟨26234158350766831305185837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69957755602044883480495565 26234158350766831305185837)
            ·
              refine ⟨9837809381537561739444689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26234158350766831305185837 9837809381537561739444689)
              ·
                refine ⟨7378357036153171304583517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9837809381537561739444689 7378357036153171304583517)
                ·
                  refine ⟨2766883888557439239218819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7378357036153171304583517 2766883888557439239218819)
                  ·
                    refine ⟨4150325832836158858828229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766883888557439239218819 4150325832836158858828229)
                    ·
                      refine ⟨778186093656779786030293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4150325832836158858828229 778186093656779786030293)
                      ·
                        rfl

theorem cell23_1515512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_1515512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515512 prefixEnd_1515512 := by exact prefixLift 1515512
  have htrace : WordTrace (prefixWord ++ tailWord_1515512) baseStart_1515512 baseEnd_1515512 := by
    simpa [prefixWord, tailWord_1515512, baseEnd_1515512] using wordTrace_append hprefix tailTrace_1515512
  have hstable : (prefixWord ++ tailWord_1515512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515512).length < 2 ^ (prefixWord ++ tailWord_1515512).sum := by decide
  have hdescent : baseEnd_1515512 < baseStart_1515512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515543 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 1, 5]
def baseStart_1515543 : Nat := 118140960795 + 1515543 * 2 ^ 59
def prefixEnd_1515543 : Nat := 4983230072969 + 3 ^ 40 * 1515543 * 2
def baseEnd_1515543 : Nat := 259400670519023054914217

theorem tailTrace_1515543 : CollatzResearch.WordTrace tailWord_1515543 prefixEnd_1515543 259400670519023054914217 := by
  unfold tailWord_1515543
  simp only [CollatzResearch.WordTrace]
  refine ⟨55276394348454019982671283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36850929565636013321780855 55276394348454019982671283)
  ·
    refine ⟨82914591522681029974006925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55276394348454019982671283 82914591522681029974006925)
    ·
      refine ⟨31092971821005386240252597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82914591522681029974006925 31092971821005386240252597)
      ·
        refine ⟨2914966108219254960023681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31092971821005386240252597 2914966108219254960023681)
        ·
          refine ⟨2186224581164441220017761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2914966108219254960023681 2186224581164441220017761)
          ·
            refine ⟨1639668435873330915013321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186224581164441220017761 1639668435873330915013321)
            ·
              refine ⟨1229751326904998186259991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639668435873330915013321 1229751326904998186259991)
              ·
                refine ⟨1844626990357497279389987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229751326904998186259991 1844626990357497279389987)
                ·
                  refine ⟨2766940485536245919084981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844626990357497279389987 2766940485536245919084981)
                  ·
                    refine ⟨259400670519023054914217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2766940485536245919084981 259400670519023054914217)
                    ·
                      rfl

theorem cell23_1515543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_1515543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515543 prefixEnd_1515543 := by exact prefixLift 1515543
  have htrace : WordTrace (prefixWord ++ tailWord_1515543) baseStart_1515543 baseEnd_1515543 := by
    simpa [prefixWord, tailWord_1515543, baseEnd_1515543] using wordTrace_append hprefix tailTrace_1515543
  have hstable : (prefixWord ++ tailWord_1515543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515543).length < 2 ^ (prefixWord ++ tailWord_1515543).sum := by decide
  have hdescent : baseEnd_1515543 < baseStart_1515543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515546 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4]
def baseStart_1515546 : Nat := 118140960795 + 1515546 * 2 ^ 59
def prefixEnd_1515546 : Nat := 4983230072969 + 3 ^ 40 * 1515546 * 2
def baseEnd_1515546 : Nat := 778203551999032653005137

theorem tailTrace_1515546 : CollatzResearch.WordTrace tailWord_1515546 prefixEnd_1515546 778203551999032653005137 := by
  unfold tailWord_1515546
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819125941860787873757623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36851002511628767663353661 13819125941860787873757623)
  ·
    refine ⟨20728688912791181810636435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13819125941860787873757623 20728688912791181810636435)
    ·
      refine ⟨31093033369186772715954653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20728688912791181810636435 31093033369186772715954653)
      ·
        refine ⟨11659887513445039768482995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31093033369186772715954653 11659887513445039768482995)
        ·
          refine ⟨17489831270167559652724493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11659887513445039768482995 17489831270167559652724493)
          ·
            refine ⟨6558686726312834869771685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17489831270167559652724493 6558686726312834869771685)
            ·
              refine ⟨1229753761183656538082191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6558686726312834869771685 1229753761183656538082191)
              ·
                refine ⟨1844630641775484807123287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229753761183656538082191 1844630641775484807123287)
                ·
                  refine ⟨2766945962663227210684931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844630641775484807123287 2766945962663227210684931)
                  ·
                    refine ⟨4150418943994840816027397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766945962663227210684931 4150418943994840816027397)
                    ·
                      refine ⟨778203551999032653005137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4150418943994840816027397 778203551999032653005137)
                      ·
                        rfl

theorem cell23_1515546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_1515546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515546 prefixEnd_1515546 := by exact prefixLift 1515546
  have htrace : WordTrace (prefixWord ++ tailWord_1515546) baseStart_1515546 baseEnd_1515546 := by
    simpa [prefixWord, tailWord_1515546, baseEnd_1515546] using wordTrace_append hprefix tailTrace_1515546
  have hstable : (prefixWord ++ tailWord_1515546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515546).length < 2 ^ (prefixWord ++ tailWord_1515546).sum := by decide
  have hdescent : baseEnd_1515546 < baseStart_1515546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515556 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1515556 : Nat := 118140960795 + 1515556 * 2 ^ 59
def prefixEnd_1515556 : Nat := 4983230072969 + 3 ^ 40 * 1515556 * 2
def baseEnd_1515556 : Nat := 259402895601859204626697

theorem tailTrace_1515556 : CollatzResearch.WordTrace tailWord_1515556 prefixEnd_1515556 259402895601859204626697 := by
  unfold tailWord_1515556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27638434248703461601447261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36851245664937948801929681 27638434248703461601447261)
  ·
    refine ⟨10364412843263798100542723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27638434248703461601447261 10364412843263798100542723)
    ·
      refine ⟨15546619264895697150814085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10364412843263798100542723 15546619264895697150814085)
      ·
        refine ⟨2914991112167943215777641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15546619264895697150814085 2914991112167943215777641)
        ·
          refine ⟨2186243334125957411833231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2914991112167943215777641 2186243334125957411833231)
          ·
            refine ⟨3279365001188936117749847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186243334125957411833231 3279365001188936117749847)
            ·
              refine ⟨4919047501783404176624771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279365001188936117749847 4919047501783404176624771)
              ·
                refine ⟨7378571252675106264937157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919047501783404176624771 7378571252675106264937157)
                ·
                  refine ⟨1383482109876582424675717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7378571252675106264937157 1383482109876582424675717)
                  ·
                    refine ⟨259402895601859204626697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383482109876582424675717 259402895601859204626697)
                    ·
                      rfl

theorem cell23_1515556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1515556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515556 prefixEnd_1515556 := by exact prefixLift 1515556
  have htrace : WordTrace (prefixWord ++ tailWord_1515556) baseStart_1515556 baseEnd_1515556 := by
    simpa [prefixWord, tailWord_1515556, baseEnd_1515556] using wordTrace_append hprefix tailTrace_1515556
  have hstable : (prefixWord ++ tailWord_1515556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515556).length < 2 ^ (prefixWord ++ tailWord_1515556).sum := by decide
  have hdescent : baseEnd_1515556 < baseStart_1515556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515576 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_1515576 : Nat := 118140960795 + 1515576 * 2 ^ 59
def prefixEnd_1515576 : Nat := 4983230072969 + 3 ^ 40 * 1515576 * 2
def baseEnd_1515576 : Nat := 778218956418667535629999

theorem tailTrace_1515576 : CollatzResearch.WordTrace tailWord_1515576 prefixEnd_1515576 778218956418667535629999 := by
  unfold tailWord_1515576
  simp only [CollatzResearch.WordTrace]
  refine ⟨27638798978667233309311291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36851731971556311079081721 27638798978667233309311291)
  ·
    refine ⟨41458198468000849963966937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27638798978667233309311291 41458198468000849963966937)
    ·
      refine ⟨31093648851000637472975203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41458198468000849963966937 31093648851000637472975203)
      ·
        refine ⟨46640473276500956209462805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31093648851000637472975203 46640473276500956209462805)
        ·
          refine ⟨2186272184835982322318569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46640473276500956209462805 2186272184835982322318569)
          ·
            refine ⟨1639704138626986741738927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186272184835982322318569 1639704138626986741738927)
            ·
              refine ⟨2459556207940480112608391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639704138626986741738927 2459556207940480112608391)
              ·
                refine ⟨3689334311910720168912587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459556207940480112608391 3689334311910720168912587)
                ·
                  refine ⟨5534001467866080253368881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689334311910720168912587 5534001467866080253368881)
                  ·
                    refine ⟨4150501100899560190026661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5534001467866080253368881 4150501100899560190026661)
                    ·
                      refine ⟨778218956418667535629999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4150501100899560190026661 778218956418667535629999)
                      ·
                        rfl

theorem cell23_1515576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_1515576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515576 prefixEnd_1515576 := by exact prefixLift 1515576
  have htrace : WordTrace (prefixWord ++ tailWord_1515576) baseStart_1515576 baseEnd_1515576 := by
    simpa [prefixWord, tailWord_1515576, baseEnd_1515576] using wordTrace_append hprefix tailTrace_1515576
  have hstable : (prefixWord ++ tailWord_1515576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515576).length < 2 ^ (prefixWord ++ tailWord_1515576).sum := by decide
  have hdescent : baseEnd_1515576 < baseStart_1515576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515613 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1515613 : Nat := 118140960795 + 1515613 * 2 ^ 59
def prefixEnd_1515613 : Nat := 4983230072969 + 3 ^ 40 * 1515613 * 2
def baseEnd_1515613 : Nat := 778237955202883890867329

theorem tailTrace_1515613 : CollatzResearch.WordTrace tailWord_1515613 prefixEnd_1515613 778237955202883890867329 := by
  unfold tailWord_1515613
  simp only [CollatzResearch.WordTrace]
  refine ⟨55278947458200421937719493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36852631638800281291812995 55278947458200421937719493)
  ·
    refine ⟨10364802648412579113322405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55278947458200421937719493 10364802648412579113322405)
    ·
      refine ⟨1943400496577358583747951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10364802648412579113322405 1943400496577358583747951)
      ·
        refine ⟨2915100744866037875621927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943400496577358583747951 2915100744866037875621927)
        ·
          refine ⟨4372651117299056813432891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915100744866037875621927 4372651117299056813432891)
          ·
            refine ⟨6558976675948585220149337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372651117299056813432891 6558976675948585220149337)
            ·
              refine ⟨4919232506961438915112003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6558976675948585220149337 4919232506961438915112003)
              ·
                refine ⟨7378848760442158372668005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919232506961438915112003 7378848760442158372668005)
                ·
                  refine ⟨1383534142582904694875251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7378848760442158372668005 1383534142582904694875251)
                  ·
                    refine ⟨2075301213874357042312877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383534142582904694875251 2075301213874357042312877)
                    ·
                      refine ⟨778237955202883890867329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2075301213874357042312877 778237955202883890867329)
                      ·
                        rfl

theorem cell23_1515613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1515613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515613 prefixEnd_1515613 := by exact prefixLift 1515613
  have htrace : WordTrace (prefixWord ++ tailWord_1515613) baseStart_1515613 baseEnd_1515613 := by
    simpa [prefixWord, tailWord_1515613, baseEnd_1515613] using wordTrace_append hprefix tailTrace_1515613
  have hstable : (prefixWord ++ tailWord_1515613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515613).length < 2 ^ (prefixWord ++ tailWord_1515613).sum := by decide
  have hdescent : baseEnd_1515613 < baseStart_1515613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515614 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1515614 : Nat := 118140960795 + 1515614 * 2 ^ 59
def prefixEnd_1515614 : Nat := 4983230072969 + 3 ^ 40 * 1515614 * 2
def baseEnd_1515614 : Nat := 778238468683538386954825

theorem tailTrace_1515614 : CollatzResearch.WordTrace tailWord_1515614 prefixEnd_1515614 778238468683538386954825 := by
  unfold tailWord_1515614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6909872991399599888563237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36852655954131199405670597 6909872991399599888563237)
  ·
    refine ⟨1295601185887424979105607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6909872991399599888563237 1295601185887424979105607)
    ·
      refine ⟨1943401778831137468658411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295601185887424979105607 1943401778831137468658411)
      ·
        refine ⟨2915102668246706202987617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943401778831137468658411 2915102668246706202987617)
        ·
          refine ⟨2186327001185029652240713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2915102668246706202987617 2186327001185029652240713)
          ·
            refine ⟨1639745250888772239180535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186327001185029652240713 1639745250888772239180535)
            ·
              refine ⟨2459617876333158358770803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639745250888772239180535 2459617876333158358770803)
              ·
                refine ⟨3689426814499737538156205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459617876333158358770803 3689426814499737538156205)
                ·
                  refine ⟨1383535055437401576808577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3689426814499737538156205 1383535055437401576808577)
                  ·
                    refine ⟨1037651291578051182606433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1383535055437401576808577 1037651291578051182606433)
                    ·
                      refine ⟨778238468683538386954825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037651291578051182606433 778238468683538386954825)
                      ·
                        rfl

theorem cell23_1515614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1515614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515614 prefixEnd_1515614 := by exact prefixLift 1515614
  have htrace : WordTrace (prefixWord ++ tailWord_1515614) baseStart_1515614 baseEnd_1515614 := by
    simpa [prefixWord, tailWord_1515614, baseEnd_1515614] using wordTrace_append hprefix tailTrace_1515614
  have hstable : (prefixWord ++ tailWord_1515614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515614).length < 2 ^ (prefixWord ++ tailWord_1515614).sum := by decide
  have hdescent : baseEnd_1515614 < baseStart_1515614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515669 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_1515669 : Nat := 118140960795 + 1515669 * 2 ^ 59
def prefixEnd_1515669 : Nat := 4983230072969 + 3 ^ 40 * 1515669 * 2
def baseEnd_1515669 : Nat := 778266710119535671767071

theorem tailTrace_1515669 : CollatzResearch.WordTrace tailWord_1515669 prefixEnd_1515669 778266710119535671767071 := by
  unfold tailWord_1515669
  simp only [CollatzResearch.WordTrace]
  refine ⟨55280989945997543501758061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36853993297331695667838707 55280989945997543501758061)
  ·
    refine ⟨20730371229749078813159273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55280989945997543501758061 20730371229749078813159273)
    ·
      refine ⟨15547778422311809109869455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20730371229749078813159273 15547778422311809109869455)
      ·
        refine ⟨23321667633467713664804183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15547778422311809109869455 23321667633467713664804183)
        ·
          refine ⟨34982501450201570497206275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23321667633467713664804183 34982501450201570497206275)
          ·
            refine ⟨52473752175302355745809413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34982501450201570497206275 52473752175302355745809413)
            ·
              refine ⟨9838828532869191702339265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52473752175302355745809413 9838828532869191702339265)
              ·
                refine ⟨7379121399651893776754449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9838828532869191702339265 7379121399651893776754449)
                ·
                  refine ⟨5534341049738920332565837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7379121399651893776754449 5534341049738920332565837)
                  ·
                    refine ⟨2075377893652095124712189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5534341049738920332565837 2075377893652095124712189)
                    ·
                      refine ⟨778266710119535671767071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2075377893652095124712189 778266710119535671767071)
                      ·
                        rfl

theorem cell23_1515669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_1515669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515669 prefixEnd_1515669 := by exact prefixLift 1515669
  have htrace : WordTrace (prefixWord ++ tailWord_1515669) baseStart_1515669 baseEnd_1515669 := by
    simpa [prefixWord, tailWord_1515669, baseEnd_1515669] using wordTrace_append hprefix tailTrace_1515669
  have hstable : (prefixWord ++ tailWord_1515669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515669).length < 2 ^ (prefixWord ++ tailWord_1515669).sum := by decide
  have hdescent : baseEnd_1515669 < baseStart_1515669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515676 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 5]
def baseStart_1515676 : Nat := 118140960795 + 1515676 * 2 ^ 59
def prefixEnd_1515676 : Nat := 4983230072969 + 3 ^ 40 * 1515676 * 2
def baseEnd_1515676 : Nat := 86474478276013016042171

theorem tailTrace_1515676 : CollatzResearch.WordTrace tailWord_1515676 prefixEnd_1515676 86474478276013016042171 := by
  unfold tailWord_1515676
  simp only [CollatzResearch.WordTrace]
  refine ⟨27640622628486091848631441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36854163504648122464841921 27640622628486091848631441)
  ·
    refine ⟨20730466971364568886473581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27640622628486091848631441 20730466971364568886473581)
    ·
      refine ⟨7773925114261713332427593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20730466971364568886473581 7773925114261713332427593)
      ·
        refine ⟨5830443835696284999320695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7773925114261713332427593 5830443835696284999320695)
        ·
          refine ⟨8745665753544427498981043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5830443835696284999320695 8745665753544427498981043)
          ·
            refine ⟨13118498630316641248471565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8745665753544427498981043 13118498630316641248471565)
            ·
              refine ⟨4919436986368740468176837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13118498630316641248471565 4919436986368740468176837)
              ·
                refine ⟨922394434944138837783157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4919436986368740468176837 922394434944138837783157)
                ·
                  refine ⟨86474478276013016042171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 922394434944138837783157 86474478276013016042171)
                  ·
                    rfl

theorem cell23_1515676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_1515676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515676 prefixEnd_1515676 := by exact prefixLift 1515676
  have htrace : WordTrace (prefixWord ++ tailWord_1515676) baseStart_1515676 baseEnd_1515676 := by
    simpa [prefixWord, tailWord_1515676, baseEnd_1515676] using wordTrace_append hprefix tailTrace_1515676
  have hstable : (prefixWord ++ tailWord_1515676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515676).length < 2 ^ (prefixWord ++ tailWord_1515676).sum := by decide
  have hdescent : baseEnd_1515676 < baseStart_1515676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515736 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 3, 4]
def baseStart_1515736 : Nat := 118140960795 + 1515736 * 2 ^ 59
def prefixEnd_1515736 : Nat := 4983230072969 + 3 ^ 40 * 1515736 * 2
def baseEnd_1515736 : Nat := 259433704441128969876421

theorem tailTrace_1515736 : CollatzResearch.WordTrace tailWord_1515736 prefixEnd_1515736 259433704441128969876421 := by
  unfold tailWord_1515736
  simp only [CollatzResearch.WordTrace]
  refine ⟨27641716818377406972223531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36855622424503209296298041 27641716818377406972223531)
  ·
    refine ⟨41462575227566110458335297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27641716818377406972223531 41462575227566110458335297)
    ·
      refine ⟨31096931420674582843751473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41462575227566110458335297 31096931420674582843751473)
      ·
        refine ⟨23322698565505937132813605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31096931420674582843751473 23322698565505937132813605)
        ·
          refine ⟨4373005981032363212402551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23322698565505937132813605 4373005981032363212402551)
          ·
            refine ⟨6559508971548544818603827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373005981032363212402551 6559508971548544818603827)
            ·
              refine ⟨9839263457322817227905741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6559508971548544818603827 9839263457322817227905741)
              ·
                refine ⟨3689723796496056460464653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9839263457322817227905741 3689723796496056460464653)
                ·
                  refine ⟨1383646423686021172674245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3689723796496056460464653 1383646423686021172674245)
                  ·
                    refine ⟨259433704441128969876421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383646423686021172674245 259433704441128969876421)
                    ·
                      rfl

theorem cell23_1515736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_1515736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515736 prefixEnd_1515736 := by exact prefixLift 1515736
  have htrace : WordTrace (prefixWord ++ tailWord_1515736) baseStart_1515736 baseEnd_1515736 := by
    simpa [prefixWord, tailWord_1515736, baseEnd_1515736] using wordTrace_append hprefix tailTrace_1515736
  have hstable : (prefixWord ++ tailWord_1515736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515736).length < 2 ^ (prefixWord ++ tailWord_1515736).sum := by decide
  have hdescent : baseEnd_1515736 < baseStart_1515736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515770 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_1515770 : Nat := 118140960795 + 1515770 * 2 ^ 59
def prefixEnd_1515770 : Nat := 4983230072969 + 3 ^ 40 * 1515770 * 2
def baseEnd_1515770 : Nat := 259439523888546592201369

theorem tailTrace_1515770 : CollatzResearch.WordTrace tailWord_1515770 prefixEnd_1515770 259439523888546592201369 := by
  unfold tailWord_1515770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13821168429657909437796191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36856449145754425167456509 13821168429657909437796191)
  ·
    refine ⟨20731752644486864156694287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13821168429657909437796191 20731752644486864156694287)
    ·
      refine ⟨31097628966730296235041431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20731752644486864156694287 31097628966730296235041431)
      ·
        refine ⟨46646443450095444352562147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31097628966730296235041431 46646443450095444352562147)
        ·
          refine ⟨69969665175143166528843221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46646443450095444352562147 69969665175143166528843221)
          ·
            refine ⟨1639914027542417965519763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69969665175143166528843221 1639914027542417965519763)
            ·
              refine ⟨2459871041313626948279645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639914027542417965519763 2459871041313626948279645)
              ·
                refine ⟨922451640492610105604867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2459871041313626948279645 922451640492610105604867)
                ·
                  refine ⟨1383677460738915158407301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922451640492610105604867 1383677460738915158407301)
                  ·
                    refine ⟨259439523888546592201369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383677460738915158407301 259439523888546592201369)
                    ·
                      rfl

theorem cell23_1515770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_1515770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515770 prefixEnd_1515770 := by exact prefixLift 1515770
  have htrace : WordTrace (prefixWord ++ tailWord_1515770) baseStart_1515770 baseEnd_1515770 := by
    simpa [prefixWord, tailWord_1515770, baseEnd_1515770] using wordTrace_append hprefix tailTrace_1515770
  have hstable : (prefixWord ++ tailWord_1515770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515770).length < 2 ^ (prefixWord ++ tailWord_1515770).sum := by decide
  have hdescent : baseEnd_1515770 < baseStart_1515770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515776 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 5, 1, 3]
def baseStart_1515776 : Nat := 118140960795 + 1515776 * 2 ^ 59
def prefixEnd_1515776 : Nat := 4983230072969 + 3 ^ 40 * 1515776 * 2
def baseEnd_1515776 : Nat := 778321652549566753129079

theorem tailTrace_1515776 : CollatzResearch.WordTrace tailWord_1515776 prefixEnd_1515776 778321652549566753129079 := by
  unfold tailWord_1515776
  simp only [CollatzResearch.WordTrace]
  refine ⟨27642446278304950387951591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36856595037739933850602121 27642446278304950387951591)
  ·
    refine ⟨41463669417457425581927387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27642446278304950387951591 41463669417457425581927387)
    ·
      refine ⟨62195504126186138372891081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41463669417457425581927387 62195504126186138372891081)
      ·
        refine ⟨46646628094639603779668311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62195504126186138372891081 46646628094639603779668311)
        ·
          refine ⟨69969942141959405669502467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46646628094639603779668311 69969942141959405669502467)
          ·
            refine ⟨104954913212939108504253701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69969942141959405669502467 104954913212939108504253701)
            ·
              refine ⟨19679046227426082844547569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104954913212939108504253701 19679046227426082844547569)
              ·
                refine ⟨14759284670569562133410677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19679046227426082844547569 14759284670569562133410677)
                ·
                  refine ⟨1383682937865896450007251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14759284670569562133410677 1383682937865896450007251)
                  ·
                    refine ⟨2075524406798844675010877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383682937865896450007251 2075524406798844675010877)
                    ·
                      refine ⟨778321652549566753129079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2075524406798844675010877 778321652549566753129079)
                      ·
                        rfl

theorem cell23_1515776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_1515776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515776 prefixEnd_1515776 := by exact prefixLift 1515776
  have htrace : WordTrace (prefixWord ++ tailWord_1515776) baseStart_1515776 baseEnd_1515776 := by
    simpa [prefixWord, tailWord_1515776, baseEnd_1515776] using wordTrace_append hprefix tailTrace_1515776
  have hstable : (prefixWord ++ tailWord_1515776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515776).length < 2 ^ (prefixWord ++ tailWord_1515776).sum := by decide
  have hdescent : baseEnd_1515776 < baseStart_1515776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515793 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_1515793 : Nat := 118140960795 + 1515793 * 2 ^ 59
def prefixEnd_1515793 : Nat := 4983230072969 + 3 ^ 40 * 1515793 * 2
def baseEnd_1515793 : Nat := 778330381720693186616501

theorem tailTrace_1515793 : CollatzResearch.WordTrace tailWord_1515793 prefixEnd_1515793 778330381720693186616501 := by
  unfold tailWord_1515793
  simp only [CollatzResearch.WordTrace]
  refine ⟨55285512597548312679272033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36857008398365541786181355 55285512597548312679272033)
  ·
    refine ⟨41464134448161234509454025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55285512597548312679272033 41464134448161234509454025)
    ·
      refine ⟨31098100836120925882090519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41464134448161234509454025 31098100836120925882090519)
      ·
        refine ⟨46647151254181388823135779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31098100836120925882090519 46647151254181388823135779)
        ·
          refine ⟨69970726881272083234703669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46647151254181388823135779 69970726881272083234703669)
          ·
            refine ⟨6559755645119257803253469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69970726881272083234703669 6559755645119257803253469)
            ·
              refine ⟨2459908366919721676220051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6559755645119257803253469 2459908366919721676220051)
              ·
                refine ⟨3689862550379582514330077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459908366919721676220051 3689862550379582514330077)
                ·
                  refine ⟨1383698456392343442873779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3689862550379582514330077 1383698456392343442873779)
                  ·
                    refine ⟨2075547684588515164310669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383698456392343442873779 2075547684588515164310669)
                    ·
                      refine ⟨778330381720693186616501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2075547684588515164310669 778330381720693186616501)
                      ·
                        rfl

theorem cell23_1515793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_1515793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515793 prefixEnd_1515793 := by exact prefixLift 1515793
  have htrace : WordTrace (prefixWord ++ tailWord_1515793) baseStart_1515793 baseEnd_1515793 := by
    simpa [prefixWord, tailWord_1515793, baseEnd_1515793] using wordTrace_append hprefix tailTrace_1515793
  have hstable : (prefixWord ++ tailWord_1515793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515793).length < 2 ^ (prefixWord ++ tailWord_1515793).sum := by decide
  have hdescent : baseEnd_1515793 < baseStart_1515793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515844 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1515844 : Nat := 118140960795 + 1515844 * 2 ^ 59
def prefixEnd_1515844 : Nat := 4983230072969 + 3 ^ 40 * 1515844 * 2
def baseEnd_1515844 : Nat := 778356569234072487078767

theorem tailTrace_1515844 : CollatzResearch.WordTrace tailWord_1515844 prefixEnd_1515844 778356569234072487078767 := by
  unfold tailWord_1515844
  simp only [CollatzResearch.WordTrace]
  refine ⟨27643686360181774194689293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36858248480242365592919057 27643686360181774194689293)
  ·
    refine ⟨10366382385068165323008485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27643686360181774194689293 10366382385068165323008485)
    ·
      refine ⟨1943696697200280998064091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10366382385068165323008485 1943696697200280998064091)
      ·
        refine ⟨2915545045800421497096137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943696697200280998064091 2915545045800421497096137)
        ·
          refine ⟨2186658784350316122822103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2915545045800421497096137 2186658784350316122822103)
          ·
            refine ⟨3279988176525474184233155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186658784350316122822103 3279988176525474184233155)
            ·
              refine ⟨4919982264788211276349733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279988176525474184233155 4919982264788211276349733)
              ·
                refine ⟨922496674647789614315575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4919982264788211276349733 922496674647789614315575)
                ·
                  refine ⟨1383745011971684421473363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922496674647789614315575 1383745011971684421473363)
                  ·
                    refine ⟨2075617517957526632210045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383745011971684421473363 2075617517957526632210045)
                    ·
                      refine ⟨778356569234072487078767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2075617517957526632210045 778356569234072487078767)
                      ·
                        rfl

theorem cell23_1515844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1515844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515844 prefixEnd_1515844 := by exact prefixLift 1515844
  have htrace : WordTrace (prefixWord ++ tailWord_1515844) baseStart_1515844 baseEnd_1515844 := by
    simpa [prefixWord, tailWord_1515844, baseEnd_1515844] using wordTrace_append hprefix tailTrace_1515844
  have hstable : (prefixWord ++ tailWord_1515844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515844).length < 2 ^ (prefixWord ++ tailWord_1515844).sum := by decide
  have hdescent : baseEnd_1515844 < baseStart_1515844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515856 : List Nat := [2, 1, 1, 1, 1, 8, 1, 8]
def baseStart_1515856 : Nat := 118140960795 + 1515856 * 2 ^ 59
def prefixEnd_1515856 : Nat := 4983230072969 + 3 ^ 40 * 1515856 * 2
def baseEnd_1515856 : Nat := 28828249296367645930693

theorem tailTrace_1515856 : CollatzResearch.WordTrace tailWord_1515856 prefixEnd_1515856 28828249296367645930693 := by
  unfold tailWord_1515856
  simp only [CollatzResearch.WordTrace]
  refine ⟨27643905198160037219407711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36858540264213382959210281 27643905198160037219407711)
  ·
    refine ⟨41465857797240055829111567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27643905198160037219407711 41465857797240055829111567)
    ·
      refine ⟨62198786695860083743667351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41465857797240055829111567 62198786695860083743667351)
      ·
        refine ⟨93298180043790125615501027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62198786695860083743667351 93298180043790125615501027)
        ·
          refine ⟨139947270065685188423251541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93298180043790125615501027 139947270065685188423251541)
          ·
            refine ⟨1640007071082248301834979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 139947270065685188423251541 1640007071082248301834979)
            ·
              refine ⟨2460010606623372452752469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640007071082248301834979 2460010606623372452752469)
              ·
                refine ⟨28828249296367645930693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2460010606623372452752469 28828249296367645930693)
                ·
                  rfl

theorem cell23_1515856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 8].length) (baseStart_1515856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515856 prefixEnd_1515856 := by exact prefixLift 1515856
  have htrace : WordTrace (prefixWord ++ tailWord_1515856) baseStart_1515856 baseEnd_1515856 := by
    simpa [prefixWord, tailWord_1515856, baseEnd_1515856] using wordTrace_append hprefix tailTrace_1515856
  have hstable : (prefixWord ++ tailWord_1515856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515856).length < 2 ^ (prefixWord ++ tailWord_1515856).sum := by decide
  have hdescent : baseEnd_1515856 < baseStart_1515856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515884 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 1, 2, 2]
def baseStart_1515884 : Nat := 118140960795 + 1515884 * 2 ^ 59
def prefixEnd_1515884 : Nat := 4983230072969 + 3 ^ 40 * 1515884 * 2
def baseEnd_1515884 : Nat := 778377108460252330578583

theorem tailTrace_1515884 : CollatzResearch.WordTrace tailWord_1515884 prefixEnd_1515884 778377108460252330578583 := by
  unfold tailWord_1515884
  simp only [CollatzResearch.WordTrace]
  refine ⟨27644415820109317610417353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36859221093479090147223137 27644415820109317610417353)
  ·
    refine ⟨20733311865081988207813015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27644415820109317610417353 20733311865081988207813015)
    ·
      refine ⟨31099967797622982311719523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20733311865081988207813015 31099967797622982311719523)
      ·
        refine ⟨46649951696434473467579285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31099967797622982311719523 46649951696434473467579285)
        ·
          refine ⟨2186716485770365943792779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46649951696434473467579285 2186716485770365943792779)
          ·
            refine ⟨3280074728655548915689169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186716485770365943792779 3280074728655548915689169)
            ·
              refine ⟨2460056046491661686766877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3280074728655548915689169 2460056046491661686766877)
              ·
                refine ⟨922521017434373132537579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2460056046491661686766877 922521017434373132537579)
                ·
                  refine ⟨1383781526151559698806369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922521017434373132537579 1383781526151559698806369)
                  ·
                    refine ⟨1037836144613669774104777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1383781526151559698806369 1037836144613669774104777)
                    ·
                      refine ⟨778377108460252330578583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037836144613669774104777 778377108460252330578583)
                      ·
                        rfl

theorem cell23_1515884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_1515884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515884 prefixEnd_1515884 := by exact prefixLift 1515884
  have htrace : WordTrace (prefixWord ++ tailWord_1515884) baseStart_1515884 baseEnd_1515884 := by
    simpa [prefixWord, tailWord_1515884, baseEnd_1515884] using wordTrace_append hprefix tailTrace_1515884
  have hstable : (prefixWord ++ tailWord_1515884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515884).length < 2 ^ (prefixWord ++ tailWord_1515884).sum := by decide
  have hdescent : baseEnd_1515884 < baseStart_1515884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515894 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1515894 : Nat := 118140960795 + 1515894 * 2 ^ 59
def prefixEnd_1515894 : Nat := 4983230072969 + 3 ^ 40 * 1515894 * 2
def baseEnd_1515894 : Nat := 259460747755599097151179

theorem tailTrace_1515894 : CollatzResearch.WordTrace tailWord_1515894 prefixEnd_1515894 259460747755599097151179 := by
  unfold tailWord_1515894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455574773136400433043671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36859464246788271285799157 3455574773136400433043671)
  ·
    refine ⟨5183362159704600649565507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3455574773136400433043671 5183362159704600649565507)
    ·
      refine ⟨7775043239556900974348261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183362159704600649565507 7775043239556900974348261)
      ·
        refine ⟨1457820607416918932690299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7775043239556900974348261 1457820607416918932690299)
        ·
          refine ⟨2186730911125378399035449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457820607416918932690299 2186730911125378399035449)
          ·
            refine ⟨1640048183344033799276587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186730911125378399035449 1640048183344033799276587)
            ·
              refine ⟨2460072275016050698914881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640048183344033799276587 2460072275016050698914881)
              ·
                refine ⟨1845054206262038024186161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460072275016050698914881 1845054206262038024186161)
                ·
                  refine ⟨1383790654696528518139621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845054206262038024186161 1383790654696528518139621)
                  ·
                    refine ⟨259460747755599097151179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383790654696528518139621 259460747755599097151179)
                    ·
                      rfl

theorem cell23_1515894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1515894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515894 prefixEnd_1515894 := by exact prefixLift 1515894
  have htrace : WordTrace (prefixWord ++ tailWord_1515894) baseStart_1515894 baseEnd_1515894 := by
    simpa [prefixWord, tailWord_1515894, baseEnd_1515894] using wordTrace_append hprefix tailTrace_1515894
  have hstable : (prefixWord ++ tailWord_1515894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515894).length < 2 ^ (prefixWord ++ tailWord_1515894).sum := by decide
  have hdescent : baseEnd_1515894 < baseStart_1515894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515916 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_1515916 : Nat := 118140960795 + 1515916 * 2 ^ 59
def prefixEnd_1515916 : Nat := 4983230072969 + 3 ^ 40 * 1515916 * 2
def baseEnd_1515916 : Nat := 259464513280398735126145

theorem tailTrace_1515916 : CollatzResearch.WordTrace tailWord_1515916 prefixEnd_1515916 259464513280398735126145 := by
  unfold tailWord_1515916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27644999388051352342999801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36859999184068469790666401 27644999388051352342999801)
  ·
    refine ⟨20733749541038514257249851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27644999388051352342999801 20733749541038514257249851)
    ·
      refine ⟨31100624311557771385874777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20733749541038514257249851 31100624311557771385874777)
      ·
        refine ⟨23325468233668328539406083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31100624311557771385874777 23325468233668328539406083)
        ·
          refine ⟨34988202350502492809109125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23325468233668328539406083 34988202350502492809109125)
          ·
            refine ⟨6560287940719217401707961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34988202350502492809109125 6560287940719217401707961)
            ·
              refine ⟨4920215955539413051280971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560287940719217401707961 4920215955539413051280971)
              ·
                refine ⟨7380323933309119576921457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920215955539413051280971 7380323933309119576921457)
                ·
                  refine ⟨5535242949981839682691093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7380323933309119576921457 5535242949981839682691093)
                  ·
                    refine ⟨259464513280398735126145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5535242949981839682691093 259464513280398735126145)
                    ·
                      rfl

theorem cell23_1515916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_1515916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515916 prefixEnd_1515916 := by exact prefixLift 1515916
  have htrace : WordTrace (prefixWord ++ tailWord_1515916) baseStart_1515916 baseEnd_1515916 := by
    simpa [prefixWord, tailWord_1515916, baseEnd_1515916] using wordTrace_append hprefix tailTrace_1515916
  have hstable : (prefixWord ++ tailWord_1515916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515916).length < 2 ^ (prefixWord ++ tailWord_1515916).sum := by decide
  have hdescent : baseEnd_1515916 < baseStart_1515916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515919 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_1515919 : Nat := 118140960795 + 1515919 * 2 ^ 59
def prefixEnd_1515919 : Nat := 4983230072969 + 3 ^ 40 * 1515919 * 2
def baseEnd_1515919 : Nat := 778395080283159693640921

theorem tailTrace_1515919 : CollatzResearch.WordTrace tailWord_1515919 prefixEnd_1515919 778395080283159693640921 := by
  unfold tailWord_1515919
  simp only [CollatzResearch.WordTrace]
  refine ⟨55290108195091836198358811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36860072130061224132239207 55290108195091836198358811)
  ·
    refine ⟨82935162292637754297538217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55290108195091836198358811 82935162292637754297538217)
    ·
      refine ⟨62201371719478315723153663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82935162292637754297538217 62201371719478315723153663)
      ·
        refine ⟨93302057579217473584730495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62201371719478315723153663 93302057579217473584730495)
        ·
          refine ⟨139953086368826210377095743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93302057579217473584730495 139953086368826210377095743)
          ·
            refine ⟨209929629553239315565643615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139953086368826210377095743 209929629553239315565643615)
            ·
              refine ⟨314894444329858973348465423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209929629553239315565643615 314894444329858973348465423)
              ·
                refine ⟨472341666494788460022698135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314894444329858973348465423 472341666494788460022698135)
                ·
                  refine ⟨708512499742182690034047203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472341666494788460022698135 708512499742182690034047203)
                  ·
                    refine ⟨1062768749613274035051070805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708512499742182690034047203 1062768749613274035051070805)
                    ·
                      refine ⟨778395080283159693640921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 1062768749613274035051070805 778395080283159693640921)
                      ·
                        rfl

theorem cell23_1515919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_1515919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515919 prefixEnd_1515919 := by exact prefixLift 1515919
  have htrace : WordTrace (prefixWord ++ tailWord_1515919) baseStart_1515919 baseEnd_1515919 := by
    simpa [prefixWord, tailWord_1515919, baseEnd_1515919] using wordTrace_append hprefix tailTrace_1515919
  have hstable : (prefixWord ++ tailWord_1515919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515919).length < 2 ^ (prefixWord ++ tailWord_1515919).sum := by decide
  have hdescent : baseEnd_1515919 < baseStart_1515919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515940 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_1515940 : Nat := 118140960795 + 1515940 * 2 ^ 59
def prefixEnd_1515940 : Nat := 4983230072969 + 3 ^ 40 * 1515940 * 2
def baseEnd_1515940 : Nat := 778405863376904111478325

theorem tailTrace_1515940 : CollatzResearch.WordTrace tailWord_1515940 prefixEnd_1515940 778405863376904111478325 := by
  unfold tailWord_1515940
  simp only [CollatzResearch.WordTrace]
  refine ⟨27645437064007878392436637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36860582752010504523248849 27645437064007878392436637)
  ·
    refine ⟨10367038899002954397163739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27645437064007878392436637 10367038899002954397163739)
    ·
      refine ⟨15550558348504431595745609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10367038899002954397163739 15550558348504431595745609)
      ·
        refine ⟨11662918761378323696809207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15550558348504431595745609 11662918761378323696809207)
        ·
          refine ⟨17494378142067485545213811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11662918761378323696809207 17494378142067485545213811)
          ·
            refine ⟨26241567213101228317820717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17494378142067485545213811 26241567213101228317820717)
            ·
              refine ⟨9840587704912960619182769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26241567213101228317820717 9840587704912960619182769)
              ·
                refine ⟨7380440778684720464387077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9840587704912960619182769 7380440778684720464387077)
                ·
                  refine ⟨1383832646003385087072577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7380440778684720464387077 1383832646003385087072577)
                  ·
                    refine ⟨1037874484502538815304433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1383832646003385087072577 1037874484502538815304433)
                    ·
                      refine ⟨778405863376904111478325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037874484502538815304433 778405863376904111478325)
                      ·
                        rfl

theorem cell23_1515940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_1515940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515940 prefixEnd_1515940 := by exact prefixLift 1515940
  have htrace : WordTrace (prefixWord ++ tailWord_1515940) baseStart_1515940 baseEnd_1515940 := by
    simpa [prefixWord, tailWord_1515940, baseEnd_1515940] using wordTrace_append hprefix tailTrace_1515940
  have hstable : (prefixWord ++ tailWord_1515940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515940).length < 2 ^ (prefixWord ++ tailWord_1515940).sum := by decide
  have hdescent : baseEnd_1515940 < baseStart_1515940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515943 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1515943 : Nat := 118140960795 + 1515943 * 2 ^ 59
def prefixEnd_1515943 : Nat := 4983230072969 + 3 ^ 40 * 1515943 * 2
def baseEnd_1515943 : Nat := 778407403818867599740811

theorem tailTrace_1515943 : CollatzResearch.WordTrace tailWord_1515943 prefixEnd_1515943 778407403818867599740811 := by
  unfold tailWord_1515943
  simp only [CollatzResearch.WordTrace]
  refine ⟨55290983547004888297232483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36860655698003258864821655 55290983547004888297232483)
  ·
    refine ⟨82936475320507332445848725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55290983547004888297232483 82936475320507332445848725)
    ·
      refine ⟨3887647280648781208399159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82936475320507332445848725 3887647280648781208399159)
      ·
        refine ⟨5831470920973171812598739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3887647280648781208399159 5831470920973171812598739)
        ·
          refine ⟨8747206381459757718898109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831470920973171812598739 8747206381459757718898109)
          ·
            refine ⟨3280202393047409144586791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8747206381459757718898109 3280202393047409144586791)
            ·
              refine ⟨4920303589571113716880187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280202393047409144586791 4920303589571113716880187)
              ·
                refine ⟨7380455384356670575320281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920303589571113716880187 7380455384356670575320281)
                ·
                  refine ⟨5535341538267502931490211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7380455384356670575320281 5535341538267502931490211)
                  ·
                    refine ⟨8303012307401254397235317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5535341538267502931490211 8303012307401254397235317)
                    ·
                      refine ⟨778407403818867599740811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8303012307401254397235317 778407403818867599740811)
                      ·
                        rfl

theorem cell23_1515943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1515943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515943 prefixEnd_1515943 := by exact prefixLift 1515943
  have htrace : WordTrace (prefixWord ++ tailWord_1515943) baseStart_1515943 baseEnd_1515943 := by
    simpa [prefixWord, tailWord_1515943, baseEnd_1515943] using wordTrace_append hprefix tailTrace_1515943
  have hstable : (prefixWord ++ tailWord_1515943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515943).length < 2 ^ (prefixWord ++ tailWord_1515943).sum := by decide
  have hdescent : baseEnd_1515943 < baseStart_1515943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515993 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 2, 5]
def baseStart_1515993 : Nat := 118140960795 + 1515993 * 2 ^ 59
def prefixEnd_1515993 : Nat := 4983230072969 + 3 ^ 40 * 1515993 * 2
def baseEnd_1515993 : Nat := 259477692617197468038527

theorem tailTrace_1515993 : CollatzResearch.WordTrace tailWord_1515993 prefixEnd_1515993 259477692617197468038527 := by
  unfold tailWord_1515993
  simp only [CollatzResearch.WordTrace]
  refine ⟨55292807196823746836552633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36861871464549164557701755 55292807196823746836552633)
  ·
    refine ⟨41469605397617810127414475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55292807196823746836552633 41469605397617810127414475)
    ·
      refine ⟨62204408096426715191121713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41469605397617810127414475 62204408096426715191121713)
      ·
        refine ⟨46653306072320036393341285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62204408096426715191121713 46653306072320036393341285)
        ·
          refine ⟨8747494888560006823751491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46653306072320036393341285 8747494888560006823751491)
          ·
            refine ⟨13121242332840010235627237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8747494888560006823751491 13121242332840010235627237)
            ·
              refine ⟨2460232937407501919180107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13121242332840010235627237 2460232937407501919180107)
              ·
                refine ⟨3690349406111252878770161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460232937407501919180107 3690349406111252878770161)
                ·
                  refine ⟨2767762054583439659077621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3690349406111252878770161 2767762054583439659077621)
                  ·
                    refine ⟨259477692617197468038527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2767762054583439659077621 259477692617197468038527)
                    ·
                      rfl

theorem cell23_1515993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_1515993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515993 prefixEnd_1515993 := by exact prefixLift 1515993
  have htrace : WordTrace (prefixWord ++ tailWord_1515993) baseStart_1515993 baseEnd_1515993 := by
    simpa [prefixWord, tailWord_1515993, baseEnd_1515993] using wordTrace_append hprefix tailTrace_1515993
  have hstable : (prefixWord ++ tailWord_1515993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515993).length < 2 ^ (prefixWord ++ tailWord_1515993).sum := by decide
  have hdescent : baseEnd_1515993 < baseStart_1515993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516016 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_1516016 : Nat := 118140960795 + 1516016 * 2 ^ 59
def prefixEnd_1516016 : Nat := 4983230072969 + 3 ^ 40 * 1516016 * 2
def baseEnd_1516016 : Nat := 778444887906645814127975

theorem tailTrace_1516016 : CollatzResearch.WordTrace tailWord_1516016 prefixEnd_1516016 778444887906645814127975 := by
  unfold tailWord_1516016
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646823037870210882319951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36862430717160281176426601 27646823037870210882319951)
  ·
    refine ⟨41470234556805316323479927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27646823037870210882319951 41470234556805316323479927)
    ·
      refine ⟨62205351835207974485219891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41470234556805316323479927 62205351835207974485219891)
      ·
        refine ⟨93308027752811961727829837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62205351835207974485219891 93308027752811961727829837)
        ·
          refine ⟨34990510407304485647936189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93308027752811961727829837 34990510407304485647936189)
          ·
            refine ⟨13121441402739182117976071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34990510407304485647936189 13121441402739182117976071)
            ·
              refine ⟨19682162104108773176964107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13121441402739182117976071 19682162104108773176964107)
              ·
                refine ⟨29523243156163159765446161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19682162104108773176964107 29523243156163159765446161)
                ·
                  refine ⟨22142432367122369824084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29523243156163159765446161 22142432367122369824084621)
                  ·
                    refine ⟨8303412137670888684031733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22142432367122369824084621 8303412137670888684031733)
                    ·
                      refine ⟨778444887906645814127975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8303412137670888684031733 778444887906645814127975)
                      ·
                        rfl

theorem cell23_1516016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_1516016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516016 prefixEnd_1516016 := by exact prefixLift 1516016
  have htrace : WordTrace (prefixWord ++ tailWord_1516016) baseStart_1516016 baseEnd_1516016 := by
    simpa [prefixWord, tailWord_1516016, baseEnd_1516016] using wordTrace_append hprefix tailTrace_1516016
  have hstable : (prefixWord ++ tailWord_1516016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516016).length < 2 ^ (prefixWord ++ tailWord_1516016).sum := by decide
  have hdescent : baseEnd_1516016 < baseStart_1516016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516026 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_1516026 : Nat := 118140960795 + 1516026 * 2 ^ 59
def prefixEnd_1516026 : Nat := 4983230072969 + 3 ^ 40 * 1516026 * 2
def baseEnd_1516026 : Nat := 778450022713190775002929

theorem tailTrace_1516026 : CollatzResearch.WordTrace tailWord_1516026 prefixEnd_1516026 778450022713190775002929 := by
  unfold tailWord_1516026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823502701426048368125983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36862673870469462315002621 13823502701426048368125983)
  ·
    refine ⟨20735254052139072552188975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13823502701426048368125983 20735254052139072552188975)
    ·
      refine ⟨31102881078208608828283463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20735254052139072552188975 31102881078208608828283463)
      ·
        refine ⟨46654321617312913242425195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31102881078208608828283463 46654321617312913242425195)
        ·
          refine ⟨69981482425969369863637793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46654321617312913242425195 69981482425969369863637793)
          ·
            refine ⟨52486111819477027397728345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69981482425969369863637793 52486111819477027397728345)
            ·
              refine ⟨39364583864607770548296259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52486111819477027397728345 39364583864607770548296259)
              ·
                refine ⟨59046875796911655822444389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39364583864607770548296259 59046875796911655822444389)
                ·
                  refine ⟨11071289211920935466708323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59046875796911655822444389 11071289211920935466708323)
                  ·
                    refine ⟨16606933817881403200062485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11071289211920935466708323 16606933817881403200062485)
                    ·
                      refine ⟨778450022713190775002929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16606933817881403200062485 778450022713190775002929)
                      ·
                        rfl

theorem cell23_1516026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_1516026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516026 prefixEnd_1516026 := by exact prefixLift 1516026
  have htrace : WordTrace (prefixWord ++ tailWord_1516026) baseStart_1516026 baseEnd_1516026 := by
    simpa [prefixWord, tailWord_1516026, baseEnd_1516026] using wordTrace_append hprefix tailTrace_1516026
  have hstable : (prefixWord ++ tailWord_1516026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516026).length < 2 ^ (prefixWord ++ tailWord_1516026).sum := by decide
  have hdescent : baseEnd_1516026 < baseStart_1516026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516080 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 3, 1, 3]
def baseStart_1516080 : Nat := 118140960795 + 1516080 * 2 ^ 59
def prefixEnd_1516080 : Nat := 4983230072969 + 3 ^ 40 * 1516080 * 2
def baseEnd_1516080 : Nat := 778477750668533563727681

theorem tailTrace_1516080 : CollatzResearch.WordTrace tailWord_1516080 prefixEnd_1516080 778477750668533563727681 := by
  unfold tailWord_1516080
  simp only [CollatzResearch.WordTrace]
  refine ⟨27647990173754280347484847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36863986898339040463313129 27647990173754280347484847)
  ·
    refine ⟨41471985260631420521227271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27647990173754280347484847 41471985260631420521227271)
    ·
      refine ⟨62207977890947130781840907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41471985260631420521227271 62207977890947130781840907)
      ·
        refine ⟨93311966836420696172761361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62207977890947130781840907 93311966836420696172761361)
        ·
          refine ⟨69983975127315522129571021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93311966836420696172761361 69983975127315522129571021)
          ·
            refine ⟨26243990672743320798589133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69983975127315522129571021 26243990672743320798589133)
            ·
              refine ⟨9841496502278745299470925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26243990672743320798589133 9841496502278745299470925)
              ·
                refine ⟨3690561188354529487301597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9841496502278745299470925 3690561188354529487301597)
                ·
                  refine ⟨1383960445632948557738099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3690561188354529487301597 1383960445632948557738099)
                  ·
                    refine ⟨2075940668449422836607149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383960445632948557738099 2075940668449422836607149)
                    ·
                      refine ⟨778477750668533563727681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2075940668449422836607149 778477750668533563727681)
                      ·
                        rfl

theorem cell23_1516080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_1516080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516080 prefixEnd_1516080 := by exact prefixLift 1516080
  have htrace : WordTrace (prefixWord ++ tailWord_1516080) baseStart_1516080 baseEnd_1516080 := by
    simpa [prefixWord, tailWord_1516080, baseEnd_1516080] using wordTrace_append hprefix tailTrace_1516080
  have hstable : (prefixWord ++ tailWord_1516080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516080).length < 2 ^ (prefixWord ++ tailWord_1516080).sum := by decide
  have hdescent : baseEnd_1516080 < baseStart_1516080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516090 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2]
def baseStart_1516090 : Nat := 118140960795 + 1516090 * 2 ^ 59
def prefixEnd_1516090 : Nat := 4983230072969 + 3 ^ 40 * 1516090 * 2
def baseEnd_1516090 : Nat := 778482885475078524602635

theorem tailTrace_1516090 : CollatzResearch.WordTrace tailWord_1516090 prefixEnd_1516090 778482885475078524602635 := by
  unfold tailWord_1516090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13824086269368083100708431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36864230051648221601889149 13824086269368083100708431)
  ·
    refine ⟨20736129404052124651062647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13824086269368083100708431 20736129404052124651062647)
    ·
      refine ⟨31104194106078186976593971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20736129404052124651062647 31104194106078186976593971)
      ·
        refine ⟨46656291159117280464890957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31104194106078186976593971 46656291159117280464890957)
        ·
          refine ⟨17496109184668980174334109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46656291159117280464890957 17496109184668980174334109)
          ·
            refine ⟨6561040944250867565375291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17496109184668980174334109 6561040944250867565375291)
            ·
              refine ⟨9841561416376301348062937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6561040944250867565375291 9841561416376301348062937)
              ·
                refine ⟨7381171062282226011047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9841561416376301348062937 7381171062282226011047203)
                ·
                  refine ⟨11071756593423339016570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7381171062282226011047203 11071756593423339016570805)
                  ·
                    refine ⟨1037977180633438032803513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11071756593423339016570805 1037977180633438032803513)
                    ·
                      refine ⟨778482885475078524602635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037977180633438032803513 778482885475078524602635)
                      ·
                        rfl

theorem cell23_1516090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_1516090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516090 prefixEnd_1516090 := by exact prefixLift 1516090
  have htrace : WordTrace (prefixWord ++ tailWord_1516090) baseStart_1516090 baseEnd_1516090 := by
    simpa [prefixWord, tailWord_1516090, baseEnd_1516090] using wordTrace_append hprefix tailTrace_1516090
  have hstable : (prefixWord ++ tailWord_1516090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516090).length < 2 ^ (prefixWord ++ tailWord_1516090).sum := by decide
  have hdescent : baseEnd_1516090 < baseStart_1516090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516097 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1516097 : Nat := 118140960795 + 1516097 * 2 ^ 59
def prefixEnd_1516097 : Nat := 4983230072969 + 3 ^ 40 * 1516097 * 2
def baseEnd_1516097 : Nat := 778486479839659997215103

theorem tailTrace_1516097 : CollatzResearch.WordTrace tailWord_1516097 prefixEnd_1516097 778486479839659997215103 := by
  unfold tailWord_1516097
  simp only [CollatzResearch.WordTrace]
  refine ⟨55296600388446972598338545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36864400258964648398892363 55296600388446972598338545)
  ·
    refine ⟨41472450291335229448753909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55296600388446972598338545 41472450291335229448753909)
    ·
      refine ⟨3888042214812677760820679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41472450291335229448753909 3888042214812677760820679)
      ·
        refine ⟨5832063322219016641231019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888042214812677760820679 5832063322219016641231019)
        ·
          refine ⟨8748094983328524961846529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832063322219016641231019 8748094983328524961846529)
          ·
            refine ⟨6561071237496393721384897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8748094983328524961846529 6561071237496393721384897)
            ·
              refine ⟨4920803428122295291038673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6561071237496393721384897 4920803428122295291038673)
              ·
                refine ⟨3690602571091721468279005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920803428122295291038673 3690602571091721468279005)
                ·
                  refine ⟨1383975964159395550604627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3690602571091721468279005 1383975964159395550604627)
                  ·
                    refine ⟨2075963946239093325906941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383975964159395550604627 2075963946239093325906941)
                    ·
                      refine ⟨778486479839659997215103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2075963946239093325906941 778486479839659997215103)
                      ·
                        rfl

theorem cell23_1516097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1516097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516097 prefixEnd_1516097 := by exact prefixLift 1516097
  have htrace : WordTrace (prefixWord ++ tailWord_1516097) baseStart_1516097 baseEnd_1516097 := by
    simpa [prefixWord, tailWord_1516097, baseEnd_1516097] using wordTrace_append hprefix tailTrace_1516097
  have hstable : (prefixWord ++ tailWord_1516097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516097).length < 2 ^ (prefixWord ++ tailWord_1516097).sum := by decide
  have hdescent : baseEnd_1516097 < baseStart_1516097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516120 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1516120 : Nat := 118140960795 + 1516120 * 2 ^ 59
def prefixEnd_1516120 : Nat := 4983230072969 + 3 ^ 40 * 1516120 * 2
def baseEnd_1516120 : Nat := 778498289894713407227497

theorem tailTrace_1516120 : CollatzResearch.WordTrace tailWord_1516120 prefixEnd_1516120 778498289894713407227497 := by
  unfold tailWord_1516120
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648719633681823763212907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36864959511575765017617209 27648719633681823763212907)
  ·
    refine ⟨41473079450522735644819361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27648719633681823763212907 41473079450522735644819361)
    ·
      refine ⟨31104809587892051733614521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41473079450522735644819361 31104809587892051733614521)
      ·
        refine ⟨23328607190919038800210891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31104809587892051733614521 23328607190919038800210891)
        ·
          refine ⟨34992910786378558200316337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23328607190919038800210891 34992910786378558200316337)
          ·
            refine ⟨26244683089783918650237253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34992910786378558200316337 26244683089783918650237253)
            ·
              refine ⟨4920878079334484746919485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26244683089783918650237253 4920878079334484746919485)
              ·
                refine ⟨1845329279750431780094807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4920878079334484746919485 1845329279750431780094807)
                ·
                  refine ⟨2767993919625647670142211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845329279750431780094807 2767993919625647670142211)
                  ·
                    refine ⟨4151990879438471505213317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2767993919625647670142211 4151990879438471505213317)
                    ·
                      refine ⟨778498289894713407227497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4151990879438471505213317 778498289894713407227497)
                      ·
                        rfl

theorem cell23_1516120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1516120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516120 prefixEnd_1516120 := by exact prefixLift 1516120
  have htrace : WordTrace (prefixWord ++ tailWord_1516120) baseStart_1516120 baseEnd_1516120 := by
    simpa [prefixWord, tailWord_1516120, baseEnd_1516120] using wordTrace_append hprefix tailTrace_1516120
  have hstable : (prefixWord ++ tailWord_1516120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516120).length < 2 ^ (prefixWord ++ tailWord_1516120).sum := by decide
  have hdescent : baseEnd_1516120 < baseStart_1516120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516124 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_1516124 : Nat := 118140960795 + 1516124 * 2 ^ 59
def prefixEnd_1516124 : Nat := 4983230072969 + 3 ^ 40 * 1516124 * 2
def baseEnd_1516124 : Nat := 778500343817331391577479

theorem tailTrace_1516124 : CollatzResearch.WordTrace tailWord_1516124 prefixEnd_1516124 778500343817331391577479 := by
  unfold tailWord_1516124
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648792579674578104785713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36865056772899437473047617 27648792579674578104785713)
  ·
    refine ⟨20736594434755933578589285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27648792579674578104785713 20736594434755933578589285)
    ·
      refine ⟨3888111456516737545985491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20736594434755933578589285 3888111456516737545985491)
      ·
        refine ⟨5832167184775106318978237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888111456516737545985491 5832167184775106318978237)
        ·
          refine ⟨2187062694290664869616839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5832167184775106318978237 2187062694290664869616839)
          ·
            refine ⟨3280594041435997304425259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187062694290664869616839 3280594041435997304425259)
            ·
              refine ⟨4920891062153995956637889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280594041435997304425259 4920891062153995956637889)
              ·
                refine ⟨3690668296615496967478417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920891062153995956637889 3690668296615496967478417)
                ·
                  refine ⟨2768001222461622725608813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3690668296615496967478417 2768001222461622725608813)
                  ·
                    refine ⟨1038000458423108522103305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2768001222461622725608813 1038000458423108522103305)
                    ·
                      refine ⟨778500343817331391577479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038000458423108522103305 778500343817331391577479)
                      ·
                        rfl

theorem cell23_1516124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_1516124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516124 prefixEnd_1516124 := by exact prefixLift 1516124
  have htrace : WordTrace (prefixWord ++ tailWord_1516124) baseStart_1516124 baseEnd_1516124 := by
    simpa [prefixWord, tailWord_1516124, baseEnd_1516124] using wordTrace_append hprefix tailTrace_1516124
  have hstable : (prefixWord ++ tailWord_1516124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516124).length < 2 ^ (prefixWord ++ tailWord_1516124).sum := by decide
  have hdescent : baseEnd_1516124 < baseStart_1516124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516157 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1516157 : Nat := 118140960795 + 1516157 * 2 ^ 59
def prefixEnd_1516157 : Nat := 4983230072969 + 3 ^ 40 * 1516157 * 2
def baseEnd_1516157 : Nat := 778517288678929762464827

theorem tailTrace_1516157 : CollatzResearch.WordTrace tailWord_1516157 prefixEnd_1516157 778517288678929762464827 := by
  unfold tailWord_1516157
  simp only [CollatzResearch.WordTrace]
  refine ⟨55298788768229602845522725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36865859178819735230348483 55298788768229602845522725)
  ·
    refine ⟨10368522894043050533535511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55298788768229602845522725 10368522894043050533535511)
    ·
      refine ⟨15552784341064575800303267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10368522894043050533535511 15552784341064575800303267)
      ·
        refine ⟨23329176511596863700454901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15552784341064575800303267 23329176511596863700454901)
        ·
          refine ⟨2187110297962205971917647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23329176511596863700454901 2187110297962205971917647)
          ·
            refine ⟨3280665446943308957876471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187110297962205971917647 3280665446943308957876471)
            ·
              refine ⟨4920998170414963436814707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280665446943308957876471 4920998170414963436814707)
              ·
                refine ⟨7381497255622445155222061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920998170414963436814707 7381497255622445155222061)
                ·
                  refine ⟨2768061470858416933208273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7381497255622445155222061 2768061470858416933208273)
                  ·
                    refine ⟨2076046103143812699906205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768061470858416933208273 2076046103143812699906205)
                    ·
                      refine ⟨778517288678929762464827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076046103143812699906205 778517288678929762464827)
                      ·
                        rfl

theorem cell23_1516157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1516157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516157 prefixEnd_1516157 := by exact prefixLift 1516157
  have htrace : WordTrace (prefixWord ++ tailWord_1516157) baseStart_1516157 baseEnd_1516157 := by
    simpa [prefixWord, tailWord_1516157, baseEnd_1516157] using wordTrace_append hprefix tailTrace_1516157
  have hstable : (prefixWord ++ tailWord_1516157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516157).length < 2 ^ (prefixWord ++ tailWord_1516157).sum := by decide
  have hdescent : baseEnd_1516157 < baseStart_1516157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516174 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1516174 : Nat := 118140960795 + 1516174 * 2 ^ 59
def prefixEnd_1516174 : Nat := 4983230072969 + 3 ^ 40 * 1516174 * 2
def baseEnd_1516174 : Nat := 778526017850056195952249

theorem tailTrace_1516174 : CollatzResearch.WordTrace tailWord_1516174 prefixEnd_1516174 778526017850056195952249 := by
  unfold tailWord_1516174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6912426101146001843611447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36866272539445343165927717 6912426101146001843611447)
  ·
    refine ⟨10368639151719002765417171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6912426101146001843611447 10368639151719002765417171)
    ·
      refine ⟨15552958727578504148125757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10368639151719002765417171 15552958727578504148125757)
      ·
        refine ⟨5832359522841939055547159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15552958727578504148125757 5832359522841939055547159)
        ·
          refine ⟨8748539284262908583320739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832359522841939055547159 8748539284262908583320739)
          ·
            refine ⟨13122808926394362874981109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748539284262908583320739 13122808926394362874981109)
            ·
              refine ⟨1230263336849471519529479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13122808926394362874981109 1230263336849471519529479)
              ·
                refine ⟨1845395005274207279294219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230263336849471519529479 1845395005274207279294219)
                ·
                  refine ⟨2768092507911310918941329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845395005274207279294219 2768092507911310918941329)
                  ·
                    refine ⟨2076069380933483189205997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768092507911310918941329 2076069380933483189205997)
                    ·
                      refine ⟨778526017850056195952249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076069380933483189205997 778526017850056195952249)
                      ·
                        rfl

theorem cell23_1516174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1516174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516174 prefixEnd_1516174 := by exact prefixLift 1516174
  have htrace : WordTrace (prefixWord ++ tailWord_1516174) baseStart_1516174 baseEnd_1516174 := by
    simpa [prefixWord, tailWord_1516174, baseEnd_1516174] using wordTrace_append hprefix tailTrace_1516174
  have hstable : (prefixWord ++ tailWord_1516174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516174).length < 2 ^ (prefixWord ++ tailWord_1516174).sum := by decide
  have hdescent : baseEnd_1516174 < baseStart_1516174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516188 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_1516188 : Nat := 118140960795 + 1516188 * 2 ^ 59
def prefixEnd_1516188 : Nat := 4983230072969 + 3 ^ 40 * 1516188 * 2
def baseEnd_1516188 : Nat := 778533206579219141177185

theorem tailTrace_1516188 : CollatzResearch.WordTrace tailWord_1516188 prefixEnd_1516188 778533206579219141177185 := by
  unfold tailWord_1516188
  simp only [CollatzResearch.WordTrace]
  refine ⟨27649959715558647569950609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36866612954078196759934145 27649959715558647569950609)
  ·
    refine ⟨20737469786668985677462957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27649959715558647569950609 20737469786668985677462957)
    ·
      refine ⟨7776551170000869629048609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20737469786668985677462957 7776551170000869629048609)
      ·
        refine ⟨5832413377500652221786457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7776551170000869629048609 5832413377500652221786457)
        ·
          refine ⟨4374310033125489166339843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5832413377500652221786457 4374310033125489166339843)
          ·
            refine ⟨6561465049688233749509765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374310033125489166339843 6561465049688233749509765)
            ·
              refine ⟨1230274696816543828033081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6561465049688233749509765 1230274696816543828033081)
              ·
                refine ⟨922706022612407871024811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1230274696816543828033081 922706022612407871024811)
                ·
                  refine ⟨1384059033918611806537217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922706022612407871024811 1384059033918611806537217)
                  ·
                    refine ⟨1038044275438958854902913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1384059033918611806537217 1038044275438958854902913)
                    ·
                      refine ⟨778533206579219141177185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038044275438958854902913 778533206579219141177185)
                      ·
                        rfl

theorem cell23_1516188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_1516188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516188 prefixEnd_1516188 := by exact prefixLift 1516188
  have htrace : WordTrace (prefixWord ++ tailWord_1516188) baseStart_1516188 baseEnd_1516188 := by
    simpa [prefixWord, tailWord_1516188, baseEnd_1516188] using wordTrace_append hprefix tailTrace_1516188
  have hstable : (prefixWord ++ tailWord_1516188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516188).length < 2 ^ (prefixWord ++ tailWord_1516188).sum := by decide
  have hdescent : baseEnd_1516188 < baseStart_1516188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516190 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1516190 : Nat := 118140960795 + 1516190 * 2 ^ 59
def prefixEnd_1516190 : Nat := 4983230072969 + 3 ^ 40 * 1516190 * 2
def baseEnd_1516190 : Nat := 259511411180176044450725

theorem tailTrace_1516190 : CollatzResearch.WordTrace tailWord_1516190 prefixEnd_1516190 259511411180176044450725 := by
  unfold tailWord_1516190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6912499047138756185184253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36866661584740032987649349 6912499047138756185184253)
  ·
    refine ⟨2592187142677033569444095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6912499047138756185184253 2592187142677033569444095)
    ·
      refine ⟨3888280714015550354166143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592187142677033569444095 3888280714015550354166143)
      ·
        refine ⟨5832421071023325531249215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888280714015550354166143 5832421071023325531249215)
        ·
          refine ⟨8748631606534988296873823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832421071023325531249215 8748631606534988296873823)
          ·
            refine ⟨13122947409802482445310735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748631606534988296873823 13122947409802482445310735)
            ·
              refine ⟨19684421114703723667966103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13122947409802482445310735 19684421114703723667966103)
              ·
                refine ⟨29526631672055585501949155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19684421114703723667966103 29526631672055585501949155)
                ·
                  refine ⟨44289947508083378252923733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29526631672055585501949155 44289947508083378252923733)
                  ·
                    refine ⟨259511411180176044450725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44289947508083378252923733 259511411180176044450725)
                    ·
                      rfl

theorem cell23_1516190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1516190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516190 prefixEnd_1516190 := by exact prefixLift 1516190
  have htrace : WordTrace (prefixWord ++ tailWord_1516190) baseStart_1516190 baseEnd_1516190 := by
    simpa [prefixWord, tailWord_1516190, baseEnd_1516190] using wordTrace_append hprefix tailTrace_1516190
  have hstable : (prefixWord ++ tailWord_1516190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516190).length < 2 ^ (prefixWord ++ tailWord_1516190).sum := by decide
  have hdescent : baseEnd_1516190 < baseStart_1516190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516225 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1516225 : Nat := 118140960795 + 1516225 * 2 ^ 59
def prefixEnd_1516225 : Nat := 4983230072969 + 3 ^ 40 * 1516225 * 2
def baseEnd_1516225 : Nat := 778552205363435496414515

theorem tailTrace_1516225 : CollatzResearch.WordTrace tailWord_1516225 prefixEnd_1516225 778552205363435496414515 := by
  unfold tailWord_1516225
  simp only [CollatzResearch.WordTrace]
  refine ⟨55301268931983250458998129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36867512621322166972665419 55301268931983250458998129)
  ·
    refine ⟨41475951698987437844248597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55301268931983250458998129 41475951698987437844248597)
    ·
      refine ⟨1944185235890036148949153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41475951698987437844248597 1944185235890036148949153)
      ·
        refine ⟨1458138926917527111711865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1944185235890036148949153 1458138926917527111711865)
        ·
          refine ⟨1093604195188145333783899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1458138926917527111711865 1093604195188145333783899)
          ·
            refine ⟨1640406292782218000675849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093604195188145333783899 1640406292782218000675849)
            ·
              refine ⟨1230304719586663500506887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640406292782218000675849 1230304719586663500506887)
              ·
                refine ⟨1845457079379995250760331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230304719586663500506887 1845457079379995250760331)
                ·
                  refine ⟨2768185619069992876140497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845457079379995250760331 2768185619069992876140497)
                  ·
                    refine ⟨2076139214302494657105373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768185619069992876140497 2076139214302494657105373)
                    ·
                      refine ⟨778552205363435496414515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076139214302494657105373 778552205363435496414515)
                      ·
                        rfl

theorem cell23_1516225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1516225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516225 prefixEnd_1516225 := by exact prefixLift 1516225
  have htrace : WordTrace (prefixWord ++ tailWord_1516225) baseStart_1516225 baseEnd_1516225 := by
    simpa [prefixWord, tailWord_1516225, baseEnd_1516225] using wordTrace_append hprefix tailTrace_1516225
  have hstable : (prefixWord ++ tailWord_1516225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516225).length < 2 ^ (prefixWord ++ tailWord_1516225).sum := by decide
  have hdescent : baseEnd_1516225 < baseStart_1516225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516250 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_1516250 : Nat := 118140960795 + 1516250 * 2 ^ 59
def prefixEnd_1516250 : Nat := 4983230072969 + 3 ^ 40 * 1516250 * 2
def baseEnd_1516250 : Nat := 86507226931088655400211

theorem tailTrace_1516250 : CollatzResearch.WordTrace tailWord_1516250 prefixEnd_1516250 86507226931088655400211 := by
  unfold tailWord_1516250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825545189223169932164551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36868120504595119819105469 13825545189223169932164551)
  ·
    refine ⟨20738317783834754898246827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13825545189223169932164551 20738317783834754898246827)
    ·
      refine ⟨31107476675752132347370241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20738317783834754898246827 31107476675752132347370241)
      ·
        refine ⟨23330607506814099260527681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31107476675752132347370241 23330607506814099260527681)
        ·
          refine ⟨17497955630110574445395761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23330607506814099260527681 17497955630110574445395761)
          ·
            refine ⟨13123466722582930834046821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17497955630110574445395761 13123466722582930834046821)
            ·
              refine ⟨2460650010484299531383779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13123466722582930834046821 2460650010484299531383779)
              ·
                refine ⟨3690975015726449297075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460650010484299531383779 3690975015726449297075669)
                ·
                  refine ⟨86507226931088655400211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3690975015726449297075669 86507226931088655400211)
                  ·
                    rfl

theorem cell23_1516250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_1516250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516250 prefixEnd_1516250 := by exact prefixLift 1516250
  have htrace : WordTrace (prefixWord ++ tailWord_1516250) baseStart_1516250 baseEnd_1516250 := by
    simpa [prefixWord, tailWord_1516250, baseEnd_1516250] using wordTrace_append hprefix tailTrace_1516250
  have hstable : (prefixWord ++ tailWord_1516250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516250).length < 2 ^ (prefixWord ++ tailWord_1516250).sum := by decide
  have hdescent : baseEnd_1516250 < baseStart_1516250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516280 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_1516280 : Nat := 118140960795 + 1516280 * 2 ^ 59
def prefixEnd_1516280 : Nat := 4983230072969 + 3 ^ 40 * 1516280 * 2
def baseEnd_1516280 : Nat := 259526815599810927075587

theorem tailTrace_1516280 : CollatzResearch.WordTrace tailWord_1516280 prefixEnd_1516280 259526815599810927075587 := by
  unfold tailWord_1516280
  simp only [CollatzResearch.WordTrace]
  refine ⟨27651637473391997426125147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36868849964522663234833529 27651637473391997426125147)
  ·
    refine ⟨41477456210087996139187721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27651637473391997426125147 41477456210087996139187721)
    ·
      refine ⟨31108092157565997104390791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41477456210087996139187721 31108092157565997104390791)
      ·
        refine ⟨46662138236348995656586187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31108092157565997104390791 46662138236348995656586187)
        ·
          refine ⟨69993207354523493484879281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46662138236348995656586187 69993207354523493484879281)
          ·
            refine ⟨52494905515892620113659461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69993207354523493484879281 52494905515892620113659461)
            ·
              refine ⟨9842794784229866271311149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52494905515892620113659461 9842794784229866271311149)
              ·
                refine ⟨3691048044086199851741681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9842794784229866271311149 3691048044086199851741681)
                ·
                  refine ⟨2768286033064649888806261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3691048044086199851741681 2768286033064649888806261)
                  ·
                    refine ⟨259526815599810927075587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2768286033064649888806261 259526815599810927075587)
                    ·
                      rfl

theorem cell23_1516280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_1516280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516280 prefixEnd_1516280 := by exact prefixLift 1516280
  have htrace : WordTrace (prefixWord ++ tailWord_1516280) baseStart_1516280 baseEnd_1516280 := by
    simpa [prefixWord, tailWord_1516280, baseEnd_1516280] using wordTrace_append hprefix tailTrace_1516280
  have hstable : (prefixWord ++ tailWord_1516280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516280).length < 2 ^ (prefixWord ++ tailWord_1516280).sum := by decide
  have hdescent : baseEnd_1516280 < baseStart_1516280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516283 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_1516283 : Nat := 118140960795 + 1516283 * 2 ^ 59
def prefixEnd_1516283 : Nat := 4983230072969 + 3 ^ 40 * 1516283 * 2
def baseEnd_1516283 : Nat := 778581987241396269489247

theorem tailTrace_1516283 : CollatzResearch.WordTrace tailWord_1516283 prefixEnd_1516283 778581987241396269489247 := by
  unfold tailWord_1516283
  simp only [CollatzResearch.WordTrace]
  refine ⟨55303384365773126364609503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36868922910515417576406335 55303384365773126364609503)
  ·
    refine ⟨82955076548659689546914255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55303384365773126364609503 82955076548659689546914255)
    ·
      refine ⟨124432614822989534320371383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82955076548659689546914255 124432614822989534320371383)
      ·
        refine ⟨186648922234484301480557075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124432614822989534320371383 186648922234484301480557075)
        ·
          refine ⟨279973383351726452220835613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186648922234484301480557075 279973383351726452220835613)
          ·
            refine ⟨104990018756897419582813355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279973383351726452220835613 104990018756897419582813355)
            ·
              refine ⟨157485028135346129374220033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104990018756897419582813355 157485028135346129374220033)
              ·
                refine ⟨118113771101509597030665025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157485028135346129374220033 118113771101509597030665025)
                ·
                  refine ⟨88585328326132197772998769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118113771101509597030665025 88585328326132197772998769)
                  ·
                    refine ⟨66438996244599148329749077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88585328326132197772998769 66438996244599148329749077)
                    ·
                      refine ⟨778581987241396269489247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66438996244599148329749077 778581987241396269489247)
                      ·
                        rfl

theorem cell23_1516283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_1516283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516283 prefixEnd_1516283 := by exact prefixLift 1516283
  have htrace : WordTrace (prefixWord ++ tailWord_1516283) baseStart_1516283 baseEnd_1516283 := by
    simpa [prefixWord, tailWord_1516283, baseEnd_1516283] using wordTrace_append hprefix tailTrace_1516283
  have hstable : (prefixWord ++ tailWord_1516283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516283).length < 2 ^ (prefixWord ++ tailWord_1516283).sum := by decide
  have hdescent : baseEnd_1516283 < baseStart_1516283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516284 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 5]
def baseStart_1516284 : Nat := 118140960795 + 1516284 * 2 ^ 59
def prefixEnd_1516284 : Nat := 4983230072969 + 3 ^ 40 * 1516284 * 2
def baseEnd_1516284 : Nat := 86509166746894529508527

theorem tailTrace_1516284 : CollatzResearch.WordTrace tailWord_1516284 prefixEnd_1516284 86509166746894529508527 := by
  unfold tailWord_1516284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27651710419384751767697953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36868947225846335690263937 27651710419384751767697953)
  ·
    refine ⟨20738782814538563825773465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27651710419384751767697953 20738782814538563825773465)
    ·
      refine ⟨15554087110903922869330099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20738782814538563825773465 15554087110903922869330099)
      ·
        refine ⟨23331130666355884303995149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15554087110903922869330099 23331130666355884303995149)
        ·
          refine ⟨8749173999883456613998181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23331130666355884303995149 8749173999883456613998181)
          ·
            refine ⟨1640470124978148115124659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8749173999883456613998181 1640470124978148115124659)
            ·
              refine ⟨2460705187467222172686989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640470124978148115124659 2460705187467222172686989)
              ·
                refine ⟨922764445300208314757621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2460705187467222172686989 922764445300208314757621)
                ·
                  refine ⟨86509166746894529508527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 922764445300208314757621 86509166746894529508527)
                  ·
                    rfl

theorem cell23_1516284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_1516284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516284 prefixEnd_1516284 := by exact prefixLift 1516284
  have htrace : WordTrace (prefixWord ++ tailWord_1516284) baseStart_1516284 baseEnd_1516284 := by
    simpa [prefixWord, tailWord_1516284, baseEnd_1516284] using wordTrace_append hprefix tailTrace_1516284
  have hstable : (prefixWord ++ tailWord_1516284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516284).length < 2 ^ (prefixWord ++ tailWord_1516284).sum := by decide
  have hdescent : baseEnd_1516284 < baseStart_1516284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516334 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1516334 : Nat := 118140960795 + 1516334 * 2 ^ 59
def prefixEnd_1516334 : Nat := 4983230072969 + 3 ^ 40 * 1516334 * 2
def baseEnd_1516334 : Nat := 778608174754775569951513

theorem tailTrace_1516334 : CollatzResearch.WordTrace tailWord_1516334 prefixEnd_1516334 778608174754775569951513 := by
  unfold tailWord_1516334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913155561073545259339507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36870162992392241383144037 6913155561073545259339507)
  ·
    refine ⟨10369733341610317889009261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6913155561073545259339507 10369733341610317889009261)
    ·
      refine ⟨3888650003103869208378473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10369733341610317889009261 3888650003103869208378473)
      ·
        refine ⟨2916487502327901906283855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3888650003103869208378473 2916487502327901906283855)
        ·
          refine ⟨4374731253491852859425783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916487502327901906283855 4374731253491852859425783)
          ·
            refine ⟨6562096880237779289138675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374731253491852859425783 6562096880237779289138675)
            ·
              refine ⟨9843145320356668933708013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562096880237779289138675 9843145320356668933708013)
              ·
                refine ⟨3691179495133750850140505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9843145320356668933708013 3691179495133750850140505)
                ·
                  refine ⟨2768384621350313137605379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3691179495133750850140505 2768384621350313137605379)
                  ·
                    refine ⟨4152576932025469706408069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2768384621350313137605379 4152576932025469706408069)
                    ·
                      refine ⟨778608174754775569951513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4152576932025469706408069 778608174754775569951513)
                      ·
                        rfl

theorem cell23_1516334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1516334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516334 prefixEnd_1516334 := by exact prefixLift 1516334
  have htrace : WordTrace (prefixWord ++ tailWord_1516334) baseStart_1516334 baseEnd_1516334 := by
    simpa [prefixWord, tailWord_1516334, baseEnd_1516334] using wordTrace_append hprefix tailTrace_1516334
  have hstable : (prefixWord ++ tailWord_1516334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516334).length < 2 ^ (prefixWord ++ tailWord_1516334).sum := by decide
  have hdescent : baseEnd_1516334 < baseStart_1516334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516344 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 1, 4]
def baseStart_1516344 : Nat := 118140960795 + 1516344 * 2 ^ 59
def prefixEnd_1516344 : Nat := 4983230072969 + 3 ^ 40 * 1516344 * 2
def baseEnd_1516344 : Nat := 259537769853773510275489

theorem tailTrace_1516344 : CollatzResearch.WordTrace tailWord_1516344 prefixEnd_1516344 259537769853773510275489 := by
  unfold tailWord_1516344
  simp only [CollatzResearch.WordTrace]
  refine ⟨27652804609276066891290043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36870406145701422521720057 27652804609276066891290043)
  ·
    refine ⟨41479206913914100336935065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27652804609276066891290043 41479206913914100336935065)
    ·
      refine ⟨31109405185435575252701299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41479206913914100336935065 31109405185435575252701299)
      ·
        refine ⟨46664107778153362879051949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31109405185435575252701299 46664107778153362879051949)
        ·
          refine ⟨17499040416807511079644481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46664107778153362879051949 17499040416807511079644481)
          ·
            refine ⟨13124280312605633309733361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17499040416807511079644481 13124280312605633309733361)
            ·
              refine ⟨9843210234454224982300021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13124280312605633309733361 9843210234454224982300021)
              ·
                refine ⟨922800959480083592090627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9843210234454224982300021 922800959480083592090627)
                ·
                  refine ⟨1384201439220125388135941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922800959480083592090627 1384201439220125388135941)
                  ·
                    refine ⟨259537769853773510275489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1384201439220125388135941 259537769853773510275489)
                    ·
                      rfl

theorem cell23_1516344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_1516344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516344 prefixEnd_1516344 := by exact prefixLift 1516344
  have htrace : WordTrace (prefixWord ++ tailWord_1516344) baseStart_1516344 baseEnd_1516344 := by
    simpa [prefixWord, tailWord_1516344, baseEnd_1516344] using wordTrace_append hprefix tailTrace_1516344
  have hstable : (prefixWord ++ tailWord_1516344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516344).length < 2 ^ (prefixWord ++ tailWord_1516344).sum := by decide
  have hdescent : baseEnd_1516344 < baseStart_1516344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516360 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1516360 : Nat := 118140960795 + 1516360 * 2 ^ 59
def prefixEnd_1516360 : Nat := 4983230072969 + 3 ^ 40 * 1516360 * 2
def baseEnd_1516360 : Nat := 778621525251792468226393

theorem tailTrace_1516360 : CollatzResearch.WordTrace tailWord_1516360 prefixEnd_1516360 778621525251792468226393 := by
  unfold tailWord_1516360
  simp only [CollatzResearch.WordTrace]
  refine ⟨27653096393247084257581267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36870795190996112343441689 27653096393247084257581267)
  ·
    refine ⟨41479644589870626386371901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27653096393247084257581267 41479644589870626386371901)
    ·
      refine ⟨15554866721201484894889463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41479644589870626386371901 15554866721201484894889463)
      ·
        refine ⟨23332300081802227342334195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15554866721201484894889463 23332300081802227342334195)
        ·
          refine ⟨34998450122703341013501293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23332300081802227342334195 34998450122703341013501293)
          ·
            refine ⟨13124418796013752880062985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34998450122703341013501293 13124418796013752880062985)
            ·
              refine ⟨9843314097010314660047239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13124418796013752880062985 9843314097010314660047239)
              ·
                refine ⟨14764971145515471990070859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843314097010314660047239 14764971145515471990070859)
                ·
                  refine ⟨22147456718273207985106289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14764971145515471990070859 22147456718273207985106289)
                  ·
                    refine ⟨16610592538704905988829717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22147456718273207985106289 16610592538704905988829717)
                    ·
                      refine ⟨778621525251792468226393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16610592538704905988829717 778621525251792468226393)
                      ·
                        rfl

theorem cell23_1516360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1516360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516360 prefixEnd_1516360 := by exact prefixLift 1516360
  have htrace : WordTrace (prefixWord ++ tailWord_1516360) baseStart_1516360 baseEnd_1516360 := by
    simpa [prefixWord, tailWord_1516360, baseEnd_1516360] using wordTrace_append hprefix tailTrace_1516360
  have hstable : (prefixWord ++ tailWord_1516360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516360).length < 2 ^ (prefixWord ++ tailWord_1516360).sum := by decide
  have hdescent : baseEnd_1516360 < baseStart_1516360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516361 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 1, 4]
def baseStart_1516361 : Nat := 118140960795 + 1516361 * 2 ^ 59
def prefixEnd_1516361 : Nat := 4983230072969 + 3 ^ 40 * 1516361 * 2
def baseEnd_1516361 : Nat := 259540679577482321437963

theorem tailTrace_1516361 : CollatzResearch.WordTrace tailWord_1516361 prefixEnd_1516361 259540679577482321437963 := by
  unfold tailWord_1516361
  simp only [CollatzResearch.WordTrace]
  refine ⟨55306229259490545685948937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36870819506327030457299291 55306229259490545685948937)
  ·
    refine ⟨41479671944617909264461703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55306229259490545685948937 41479671944617909264461703)
    ·
      refine ⟨62219507916926863896692555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41479671944617909264461703 62219507916926863896692555)
      ·
        refine ⟨93329261875390295845038833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62219507916926863896692555 93329261875390295845038833)
        ·
          refine ⟨69996946406542721883779125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93329261875390295845038833 69996946406542721883779125)
          ·
            refine ⟨6562213725613380176604293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69996946406542721883779125 6562213725613380176604293)
            ·
              refine ⟨1230415073552508783113305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6562213725613380176604293 1230415073552508783113305)
              ·
                refine ⟨922811305164381587334979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1230415073552508783113305 922811305164381587334979)
                ·
                  refine ⟨1384216957746572381002469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922811305164381587334979 1384216957746572381002469)
                  ·
                    refine ⟨259540679577482321437963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1384216957746572381002469 259540679577482321437963)
                    ·
                      rfl

theorem cell23_1516361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 4].length) (baseStart_1516361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516361 prefixEnd_1516361 := by exact prefixLift 1516361
  have htrace : WordTrace (prefixWord ++ tailWord_1516361) baseStart_1516361 baseEnd_1516361 := by
    simpa [prefixWord, tailWord_1516361, baseEnd_1516361] using wordTrace_append hprefix tailTrace_1516361
  have hstable : (prefixWord ++ tailWord_1516361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516361).length < 2 ^ (prefixWord ++ tailWord_1516361).sum := by decide
  have hdescent : baseEnd_1516361 < baseStart_1516361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516367 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 3]
def baseStart_1516367 : Nat := 118140960795 + 1516367 * 2 ^ 59
def prefixEnd_1516367 : Nat := 4983230072969 + 3 ^ 40 * 1516367 * 2
def baseEnd_1516367 : Nat := 778625119616373940838861

theorem tailTrace_1516367 : CollatzResearch.WordTrace tailWord_1516367 prefixEnd_1516367 778625119616373940838861 := by
  unfold tailWord_1516367
  simp only [CollatzResearch.WordTrace]
  refine ⟨55306448097468808710667355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36870965398312539140444903 55306448097468808710667355)
  ·
    refine ⟨82959672146203213066001033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55306448097468808710667355 82959672146203213066001033)
    ·
      refine ⟨62219754109652409799500775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82959672146203213066001033 62219754109652409799500775)
      ·
        refine ⟨93329631164478614699251163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62219754109652409799500775 93329631164478614699251163)
        ·
          refine ⟨139994446746717922048876745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93329631164478614699251163 139994446746717922048876745)
          ·
            refine ⟨104995835060038441536657559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139994446746717922048876745 104995835060038441536657559)
            ·
              refine ⟨157493752590057662304986339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104995835060038441536657559 157493752590057662304986339)
              ·
                refine ⟨236240628885086493457479509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157493752590057662304986339 236240628885086493457479509)
                ·
                  refine ⟨1384222434873553672602419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 236240628885086493457479509 1384222434873553672602419)
                  ·
                    refine ⟨2076333652310330508903629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384222434873553672602419 2076333652310330508903629)
                    ·
                      refine ⟨778625119616373940838861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076333652310330508903629 778625119616373940838861)
                      ·
                        rfl

theorem cell23_1516367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_1516367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516367 prefixEnd_1516367 := by exact prefixLift 1516367
  have htrace : WordTrace (prefixWord ++ tailWord_1516367) baseStart_1516367 baseEnd_1516367 := by
    simpa [prefixWord, tailWord_1516367, baseEnd_1516367] using wordTrace_append hprefix tailTrace_1516367
  have hstable : (prefixWord ++ tailWord_1516367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516367).length < 2 ^ (prefixWord ++ tailWord_1516367).sum := by decide
  have hdescent : baseEnd_1516367 < baseStart_1516367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516384 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 3, 1, 3]
def baseStart_1516384 : Nat := 118140960795 + 1516384 * 2 ^ 59
def prefixEnd_1516384 : Nat := 4983230072969 + 3 ^ 40 * 1516384 * 2
def baseEnd_1516384 : Nat := 778633848787500374326283

theorem tailTrace_1516384 : CollatzResearch.WordTrace tailWord_1516384 prefixEnd_1516384 778633848787500374326283 := by
  unfold tailWord_1516384
  simp only [CollatzResearch.WordTrace]
  refine ⟨27653534069203610307018103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36871378758938147076024137 27653534069203610307018103)
  ·
    refine ⟨41480301103805415460527155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27653534069203610307018103 41480301103805415460527155)
    ·
      refine ⟨62220451655708123190790733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41480301103805415460527155 62220451655708123190790733)
      ·
        refine ⟨23332669370890546196546525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62220451655708123190790733 23332669370890546196546525)
        ·
          refine ⟨8749751014083954823704947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23332669370890546196546525 8749751014083954823704947)
          ·
            refine ⟨13124626521125932235557421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8749751014083954823704947 13124626521125932235557421)
            ·
              refine ⟨4921734945422224588334033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13124626521125932235557421 4921734945422224588334033)
              ·
                refine ⟨3691301209066668441250525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4921734945422224588334033 3691301209066668441250525)
                ·
                  refine ⟨1384237953400000665468947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3691301209066668441250525 1384237953400000665468947)
                  ·
                    refine ⟨2076356930100000998203421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384237953400000665468947 2076356930100000998203421)
                    ·
                      refine ⟨778633848787500374326283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076356930100000998203421 778633848787500374326283)
                      ·
                        rfl

theorem cell23_1516384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_1516384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516384 prefixEnd_1516384 := by exact prefixLift 1516384
  have htrace : WordTrace (prefixWord ++ tailWord_1516384) baseStart_1516384 baseEnd_1516384 := by
    simpa [prefixWord, tailWord_1516384, baseEnd_1516384] using wordTrace_append hprefix tailTrace_1516384
  have hstable : (prefixWord ++ tailWord_1516384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516384).length < 2 ^ (prefixWord ++ tailWord_1516384).sum := by decide
  have hdescent : baseEnd_1516384 < baseStart_1516384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516387 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 3, 5]
def baseStart_1516387 : Nat := 118140960795 + 1516387 * 2 ^ 59
def prefixEnd_1516387 : Nat := 4983230072969 + 3 ^ 40 * 1516387 * 2
def baseEnd_1516387 : Nat := 259545129743154620862923

theorem tailTrace_1516387 : CollatzResearch.WordTrace tailWord_1516387 prefixEnd_1516387 259545129743154620862923 := by
  unfold tailWord_1516387
  simp only [CollatzResearch.WordTrace]
  refine ⟨55307177557396352126395415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36871451704930901417596943 55307177557396352126395415)
  ·
    refine ⟨82960766336094528189593123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55307177557396352126395415 82960766336094528189593123)
    ·
      refine ⟨124441149504141792284389685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82960766336094528189593123 124441149504141792284389685)
      ·
        refine ⟨11666357766013293026661533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124441149504141792284389685 11666357766013293026661533)
        ·
          refine ⟨4374884162254984884998075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11666357766013293026661533 4374884162254984884998075)
          ·
            refine ⟨6562326243382477327497113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374884162254984884998075 6562326243382477327497113)
            ·
              refine ⟨4921744682536857995622835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6562326243382477327497113 4921744682536857995622835)
              ·
                refine ⟨7382617023805286993434253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921744682536857995622835 7382617023805286993434253)
                ·
                  refine ⟨2768481383926982622537845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7382617023805286993434253 2768481383926982622537845)
                  ·
                    refine ⟨259545129743154620862923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2768481383926982622537845 259545129743154620862923)
                    ·
                      rfl

theorem cell23_1516387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 5].length) (baseStart_1516387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516387 prefixEnd_1516387 := by exact prefixLift 1516387
  have htrace : WordTrace (prefixWord ++ tailWord_1516387) baseStart_1516387 baseEnd_1516387 := by
    simpa [prefixWord, tailWord_1516387, baseEnd_1516387] using wordTrace_append hprefix tailTrace_1516387
  have hstable : (prefixWord ++ tailWord_1516387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516387).length < 2 ^ (prefixWord ++ tailWord_1516387).sum := by decide
  have hdescent : baseEnd_1516387 < baseStart_1516387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516401 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 1, 1, 3]
def baseStart_1516401 : Nat := 118140960795 + 1516401 * 2 ^ 59
def prefixEnd_1516401 : Nat := 4983230072969 + 3 ^ 40 * 1516401 * 2
def baseEnd_1516401 : Nat := 778642577958626807813705

theorem tailTrace_1516401 : CollatzResearch.WordTrace tailWord_1516401 prefixEnd_1516401 778642577958626807813705 := by
  unfold tailWord_1516401
  simp only [CollatzResearch.WordTrace]
  refine ⟨55307688179345632517405057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36871792119563755011603371 55307688179345632517405057)
  ·
    refine ⟨41480766134509224388053793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55307688179345632517405057 41480766134509224388053793)
    ·
      refine ⟨31110574600881918291040345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41480766134509224388053793 31110574600881918291040345)
      ·
        refine ⟨23332930950661438718280259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31110574600881918291040345 23332930950661438718280259)
        ·
          refine ⟨34999396425992158077420389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23332930950661438718280259 34999396425992158077420389)
          ·
            refine ⟨6562386829873529639516323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34999396425992158077420389 6562386829873529639516323)
            ·
              refine ⟨9843580244810294459274485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562386829873529639516323 9843580244810294459274485)
              ·
                refine ⟨922835647950965105556983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9843580244810294459274485 922835647950965105556983)
                ·
                  refine ⟨1384253471926447658335475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922835647950965105556983 1384253471926447658335475)
                  ·
                    refine ⟨2076380207889671487503213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384253471926447658335475 2076380207889671487503213)
                    ·
                      refine ⟨778642577958626807813705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076380207889671487503213 778642577958626807813705)
                      ·
                        rfl

theorem cell23_1516401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_1516401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516401 prefixEnd_1516401 := by exact prefixLift 1516401
  have htrace : WordTrace (prefixWord ++ tailWord_1516401) baseStart_1516401 baseEnd_1516401 := by
    simpa [prefixWord, tailWord_1516401, baseEnd_1516401] using wordTrace_append hprefix tailTrace_1516401
  have hstable : (prefixWord ++ tailWord_1516401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516401).length < 2 ^ (prefixWord ++ tailWord_1516401).sum := by decide
  have hdescent : baseEnd_1516401 < baseStart_1516401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516407 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 8, 2]
def baseStart_1516407 : Nat := 118140960795 + 1516407 * 2 ^ 59
def prefixEnd_1516407 : Nat := 4983230072969 + 3 ^ 40 * 1516407 * 2
def baseEnd_1516407 : Nat := 778645658842553784338677

theorem tailTrace_1516407 : CollatzResearch.WordTrace tailWord_1516407 prefixEnd_1516407 778645658842553784338677 := by
  unfold tailWord_1516407
  simp only [CollatzResearch.WordTrace]
  refine ⟨55307907017323895542123475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36871938011549263694748983 55307907017323895542123475)
  ·
    refine ⟨82961860525985843313185213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55307907017323895542123475 82961860525985843313185213)
    ·
      refine ⟨31110697697244691242444455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82961860525985843313185213 31110697697244691242444455)
      ·
        refine ⟨46666046545867036863666683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31110697697244691242444455 46666046545867036863666683)
        ·
          refine ⟨69999069818800555295500025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46666046545867036863666683 69999069818800555295500025)
          ·
            refine ⟨52499302364100416471625019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69999069818800555295500025 52499302364100416471625019)
            ·
              refine ⟨78748953546150624707437529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52499302364100416471625019 78748953546150624707437529)
              ·
                refine ⟨59061715159612968530578147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78748953546150624707437529 59061715159612968530578147)
                ·
                  refine ⟨88592572739419452795867221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59061715159612968530578147 88592572739419452795867221)
                  ·
                    refine ⟨1038194211790071712451569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88592572739419452795867221 1038194211790071712451569)
                    ·
                      refine ⟨778645658842553784338677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038194211790071712451569 778645658842553784338677)
                      ·
                        rfl

theorem cell23_1516407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_1516407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516407 prefixEnd_1516407 := by exact prefixLift 1516407
  have htrace : WordTrace (prefixWord ++ tailWord_1516407) baseStart_1516407 baseEnd_1516407 := by
    simpa [prefixWord, tailWord_1516407, baseEnd_1516407] using wordTrace_append hprefix tailTrace_1516407
  have hstable : (prefixWord ++ tailWord_1516407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516407).length < 2 ^ (prefixWord ++ tailWord_1516407).sum := by decide
  have hdescent : baseEnd_1516407 < baseStart_1516407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516427 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 3]
def baseStart_1516427 : Nat := 118140960795 + 1516427 * 2 ^ 59
def prefixEnd_1516427 : Nat := 4983230072969 + 3 ^ 40 * 1516427 * 2
def baseEnd_1516427 : Nat := 778655928455643706088585

theorem tailTrace_1516427 : CollatzResearch.WordTrace tailWord_1516427 prefixEnd_1516427 778655928455643706088585 := by
  unfold tailWord_1516427
  simp only [CollatzResearch.WordTrace]
  refine ⟨55308636477251438957851535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36872424318167625971901023 55308636477251438957851535)
  ·
    refine ⟨82962954715877158436777303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55308636477251438957851535 82962954715877158436777303)
    ·
      refine ⟨124444432073815737655165955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82962954715877158436777303 124444432073815737655165955)
      ·
        refine ⟨186666648110723606482748933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124444432073815737655165955 186666648110723606482748933)
        ·
          refine ⟨34999996520760676215515425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186666648110723606482748933 34999996520760676215515425)
          ·
            refine ⟨26249997390570507161636569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34999996520760676215515425 26249997390570507161636569)
            ·
              refine ⟨19687498042927880371227427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26249997390570507161636569 19687498042927880371227427)
              ·
                refine ⟨29531247064391820556841141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19687498042927880371227427 29531247064391820556841141)
                ·
                  refine ⟨2768554412286733177203857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29531247064391820556841141 2768554412286733177203857)
                  ·
                    refine ⟨2076415809215049882902893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768554412286733177203857 2076415809215049882902893)
                    ·
                      refine ⟨778655928455643706088585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076415809215049882902893 778655928455643706088585)
                      ·
                        rfl

theorem cell23_1516427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 3].length) (baseStart_1516427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516427 prefixEnd_1516427 := by exact prefixLift 1516427
  have htrace : WordTrace (prefixWord ++ tailWord_1516427) baseStart_1516427 baseEnd_1516427 := by
    simpa [prefixWord, tailWord_1516427, baseEnd_1516427] using wordTrace_append hprefix tailTrace_1516427
  have hstable : (prefixWord ++ tailWord_1516427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516427).length < 2 ^ (prefixWord ++ tailWord_1516427).sum := by decide
  have hdescent : baseEnd_1516427 < baseStart_1516427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516437 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_1516437 : Nat := 118140960795 + 1516437 * 2 ^ 59
def prefixEnd_1516437 : Nat := 4983230072969 + 3 ^ 40 * 1516437 * 2
def baseEnd_1516437 : Nat := 778661063262188666963539

theorem tailTrace_1516437 : CollatzResearch.WordTrace tailWord_1516437 prefixEnd_1516437 778661063262188666963539 := by
  unfold tailWord_1516437
  simp only [CollatzResearch.WordTrace]
  refine ⟨55309001207215210665715565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36872667471476807110477043 55309001207215210665715565)
  ·
    refine ⟨20740875452705703999643337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55309001207215210665715565 20740875452705703999643337)
    ·
      refine ⟨15555656589529277999732503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20740875452705703999643337 15555656589529277999732503)
      ·
        refine ⟨23333484884293916999598755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15555656589529277999732503 23333484884293916999598755)
        ·
          refine ⟨35000227326440875499398133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23333484884293916999598755 35000227326440875499398133)
          ·
            refine ⟨3281271311853832078068575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35000227326440875499398133 3281271311853832078068575)
            ·
              refine ⟨4921906967780748117102863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281271311853832078068575 4921906967780748117102863)
              ·
                refine ⟨7382860451671122175654295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921906967780748117102863 7382860451671122175654295)
                ·
                  refine ⟨11074290677506683263481443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7382860451671122175654295 11074290677506683263481443)
                  ·
                    refine ⟨16611436016260024895222165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11074290677506683263481443 16611436016260024895222165)
                    ·
                      refine ⟨778661063262188666963539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16611436016260024895222165 778661063262188666963539)
                      ·
                        rfl

theorem cell23_1516437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_1516437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516437 prefixEnd_1516437 := by exact prefixLift 1516437
  have htrace : WordTrace (prefixWord ++ tailWord_1516437) baseStart_1516437 baseEnd_1516437 := by
    simpa [prefixWord, tailWord_1516437, baseEnd_1516437] using wordTrace_append hprefix tailTrace_1516437
  have hstable : (prefixWord ++ tailWord_1516437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516437).length < 2 ^ (prefixWord ++ tailWord_1516437).sum := by decide
  have hdescent : baseEnd_1516437 < baseStart_1516437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516438 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1516438 : Nat := 118140960795 + 1516438 * 2 ^ 59
def prefixEnd_1516438 : Nat := 4983230072969 + 3 ^ 40 * 1516438 * 2
def baseEnd_1516438 : Nat := 259553858914281054350345

theorem tailTrace_1516438 : CollatzResearch.WordTrace tailWord_1516438 prefixEnd_1516438 259553858914281054350345 := by
  unfold tailWord_1516438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456814855013224239781373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36872691786807725224334645 3456814855013224239781373)
  ·
    refine ⟨1296305570629959089918015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3456814855013224239781373 1296305570629959089918015)
    ·
      refine ⟨1944458355944938634877023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296305570629959089918015 1944458355944938634877023)
      ·
        refine ⟨2916687533917407952315535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944458355944938634877023 2916687533917407952315535)
        ·
          refine ⟨4375031300876111928473303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916687533917407952315535 4375031300876111928473303)
          ·
            refine ⟨6562546951314167892709955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375031300876111928473303 6562546951314167892709955)
            ·
              refine ⟨9843820426971251839064933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562546951314167892709955 9843820426971251839064933)
              ·
                refine ⟨1845716330057109719824675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9843820426971251839064933 1845716330057109719824675)
                ·
                  refine ⟨2768574495085664579737013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845716330057109719824675 2768574495085664579737013)
                  ·
                    refine ⟨259553858914281054350345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2768574495085664579737013 259553858914281054350345)
                    ·
                      rfl

theorem cell23_1516438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1516438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516438 prefixEnd_1516438 := by exact prefixLift 1516438
  have htrace : WordTrace (prefixWord ++ tailWord_1516438) baseStart_1516438 baseEnd_1516438 := by
    simpa [prefixWord, tailWord_1516438, baseEnd_1516438] using wordTrace_append hprefix tailTrace_1516438
  have hstable : (prefixWord ++ tailWord_1516438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516438).length < 2 ^ (prefixWord ++ tailWord_1516438).sum := by decide
  have hdescent : baseEnd_1516438 < baseStart_1516438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516447 : List Nat := [1, 1, 2, 5, 2, 2, 1, 9]
def baseStart_1516447 : Nat := 118140960795 + 1516447 * 2 ^ 59
def prefixEnd_1516447 : Nat := 4983230072969 + 3 ^ 40 * 1516447 * 2
def baseEnd_1516447 : Nat := 28839488817360504734759

theorem tailTrace_1516447 : CollatzResearch.WordTrace tailWord_1516447 prefixEnd_1516447 28839488817360504734759 := by
  unfold tailWord_1516447
  simp only [CollatzResearch.WordTrace]
  refine ⟨55309365937178982373579595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36872910624785988249053063 55309365937178982373579595)
  ·
    refine ⟨82964048905768473560369393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55309365937178982373579595 82964048905768473560369393)
    ·
      refine ⟨62223036679326355170277045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82964048905768473560369393 62223036679326355170277045)
      ·
        refine ⟨5833409688686845797213473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62223036679326355170277045 5833409688686845797213473)
        ·
          refine ⟨4375057266515134347910105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5833409688686845797213473 4375057266515134347910105)
          ·
            refine ⟨3281292949886350760932579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4375057266515134347910105 3281292949886350760932579)
            ·
              refine ⟨4921939424829526141398869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281292949886350760932579 4921939424829526141398869)
              ·
                refine ⟨28839488817360504734759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4921939424829526141398869 28839488817360504734759)
                ·
                  rfl

theorem cell23_1516447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 9].length) (baseStart_1516447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516447 prefixEnd_1516447 := by exact prefixLift 1516447
  have htrace : WordTrace (prefixWord ++ tailWord_1516447) baseStart_1516447 baseEnd_1516447 := by
    simpa [prefixWord, tailWord_1516447, baseEnd_1516447] using wordTrace_append hprefix tailTrace_1516447
  have hstable : (prefixWord ++ tailWord_1516447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516447).length < 2 ^ (prefixWord ++ tailWord_1516447).sum := by decide
  have hdescent : baseEnd_1516447 < baseStart_1516447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516457 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_1516457 : Nat := 118140960795 + 1516457 * 2 ^ 59
def prefixEnd_1516457 : Nat := 4983230072969 + 3 ^ 40 * 1516457 * 2
def baseEnd_1516457 : Nat := 778671332875278588713447

theorem tailTrace_1516457 : CollatzResearch.WordTrace tailWord_1516457 prefixEnd_1516457 778671332875278588713447 := by
  unfold tailWord_1516457
  simp only [CollatzResearch.WordTrace]
  refine ⟨55309730667142754081443625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36873153778095169387629083 55309730667142754081443625)
  ·
    refine ⟨41482298000357065561082719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55309730667142754081443625 41482298000357065561082719)
    ·
      refine ⟨62223447000535598341624079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41482298000357065561082719 62223447000535598341624079)
      ·
        refine ⟨93335170500803397512436119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62223447000535598341624079 93335170500803397512436119)
        ·
          refine ⟨140002755751205096268654179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93335170500803397512436119 140002755751205096268654179)
          ·
            refine ⟨210004133626807644402981269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140002755751205096268654179 210004133626807644402981269)
            ·
              refine ⟨9843943763756608331389747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210004133626807644402981269 9843943763756608331389747)
              ·
                refine ⟨14765915645634912497084621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843943763756608331389747 14765915645634912497084621)
                ·
                  refine ⟨5537218367113092186406733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14765915645634912497084621 5537218367113092186406733)
                  ·
                    refine ⟨2076456887667409569902525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5537218367113092186406733 2076456887667409569902525)
                    ·
                      refine ⟨778671332875278588713447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076456887667409569902525 778671332875278588713447)
                      ·
                        rfl

theorem cell23_1516457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_1516457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516457 prefixEnd_1516457 := by exact prefixLift 1516457
  have htrace : WordTrace (prefixWord ++ tailWord_1516457) baseStart_1516457 baseEnd_1516457 := by
    simpa [prefixWord, tailWord_1516457, baseEnd_1516457] using wordTrace_append hprefix tailTrace_1516457
  have hstable : (prefixWord ++ tailWord_1516457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516457).length < 2 ^ (prefixWord ++ tailWord_1516457).sum := by decide
  have hdescent : baseEnd_1516457 < baseStart_1516457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516474 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_1516474 : Nat := 118140960795 + 1516474 * 2 ^ 59
def prefixEnd_1516474 : Nat := 4983230072969 + 3 ^ 40 * 1516474 * 2
def baseEnd_1516474 : Nat := 778680062046405022200869

theorem tailTrace_1516474 : CollatzResearch.WordTrace tailWord_1516474 prefixEnd_1516474 778680062046405022200869 := by
  unfold tailWord_1516474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827587677020291496203119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36873567138720777323208317 13827587677020291496203119)
  ·
    refine ⟨20741381515530437244304679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13827587677020291496203119 20741381515530437244304679)
    ·
      refine ⟨31112072273295655866457019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20741381515530437244304679 31112072273295655866457019)
      ·
        refine ⟨46668108409943483799685529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31112072273295655866457019 46668108409943483799685529)
        ·
          refine ⟨35001081307457612849764147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46668108409943483799685529 35001081307457612849764147)
          ·
            refine ⟨52501621961186419274646221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35001081307457612849764147 52501621961186419274646221)
            ·
              refine ⟨19688108235444907227992333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52501621961186419274646221 19688108235444907227992333)
              ·
                refine ⟨7383040588291840210497125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19688108235444907227992333 7383040588291840210497125)
                ·
                  refine ⟨1384320110304720039468211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7383040588291840210497125 1384320110304720039468211)
                  ·
                    refine ⟨2076480165457080059202317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384320110304720039468211 2076480165457080059202317)
                    ·
                      refine ⟨778680062046405022200869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076480165457080059202317 778680062046405022200869)
                      ·
                        rfl

theorem cell23_1516474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_1516474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516474 prefixEnd_1516474 := by exact prefixLift 1516474
  have htrace : WordTrace (prefixWord ++ tailWord_1516474) baseStart_1516474 baseEnd_1516474 := by
    simpa [prefixWord, tailWord_1516474, baseEnd_1516474] using wordTrace_append hprefix tailTrace_1516474
  have hstable : (prefixWord ++ tailWord_1516474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516474).length < 2 ^ (prefixWord ++ tailWord_1516474).sum := by decide
  have hdescent : baseEnd_1516474 < baseStart_1516474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516491 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 3]
def baseStart_1516491 : Nat := 118140960795 + 1516491 * 2 ^ 59
def prefixEnd_1516491 : Nat := 4983230072969 + 3 ^ 40 * 1516491 * 2
def baseEnd_1516491 : Nat := 778688791217531455688291

theorem tailTrace_1516491 : CollatzResearch.WordTrace tailWord_1516491 prefixEnd_1516491 778688791217531455688291 := by
  unfold tailWord_1516491
  simp only [CollatzResearch.WordTrace]
  refine ⟨55310970749019577888181327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36873980499346385258787551 55310970749019577888181327)
  ·
    refine ⟨82966456123529366832271991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55310970749019577888181327 82966456123529366832271991)
    ·
      refine ⟨124449684185294050248407987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82966456123529366832271991 124449684185294050248407987)
      ·
        refine ⟨186674526277941075372611981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124449684185294050248407987 186674526277941075372611981)
        ·
          refine ⟨70002947354227903264729493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186674526277941075372611981 70002947354227903264729493)
          ·
            refine ⟨3281388157229432965534195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70002947354227903264729493 3281388157229432965534195)
            ·
              refine ⟨4922082235844149448301293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281388157229432965534195 4922082235844149448301293)
              ·
                refine ⟨1845780838441556043112985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4922082235844149448301293 1845780838441556043112985)
                ·
                  refine ⟨1384335628831167032334739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845780838441556043112985 1384335628831167032334739)
                  ·
                    refine ⟨2076503443246750548502109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384335628831167032334739 2076503443246750548502109)
                    ·
                      refine ⟨778688791217531455688291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076503443246750548502109 778688791217531455688291)
                      ·
                        rfl

theorem cell23_1516491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 3].length) (baseStart_1516491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516491 prefixEnd_1516491 := by exact prefixLift 1516491
  have htrace : WordTrace (prefixWord ++ tailWord_1516491) baseStart_1516491 baseEnd_1516491 := by
    simpa [prefixWord, tailWord_1516491, baseEnd_1516491] using wordTrace_append hprefix tailTrace_1516491
  have hstable : (prefixWord ++ tailWord_1516491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516491).length < 2 ^ (prefixWord ++ tailWord_1516491).sum := by decide
  have hdescent : baseEnd_1516491 < baseStart_1516491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516532 : List Nat := [2, 6, 2, 1, 2, 1, 1, 8]
def baseStart_1516532 : Nat := 118140960795 + 1516532 * 2 ^ 59
def prefixEnd_1516532 : Nat := 4983230072969 + 3 ^ 40 * 1516532 * 2
def baseEnd_1516532 : Nat := 28841105330532066491689

theorem tailTrace_1516532 : CollatzResearch.WordTrace tailWord_1516532 prefixEnd_1516532 28841105330532066491689 := by
  unfold tailWord_1516532
  simp only [CollatzResearch.WordTrace]
  refine ⟨27656233070935520945211925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36874977427914027926949233 27656233070935520945211925)
  ·
    refine ⟨1296385925200102544306809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27656233070935520945211925 1296385925200102544306809)
    ·
      refine ⟨972289443900076908230107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296385925200102544306809 972289443900076908230107)
      ·
        refine ⟨1458434165850115362345161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972289443900076908230107 1458434165850115362345161)
        ·
          refine ⟨1093825624387586521758871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1458434165850115362345161 1093825624387586521758871)
          ·
            refine ⟨1640738436581379782638307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093825624387586521758871 1640738436581379782638307)
            ·
              refine ⟨2461107654872069673957461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640738436581379782638307 2461107654872069673957461)
              ·
                refine ⟨28841105330532066491689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2461107654872069673957461 28841105330532066491689)
                ·
                  rfl

theorem cell23_1516532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 8].length) (baseStart_1516532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516532 prefixEnd_1516532 := by exact prefixLift 1516532
  have htrace : WordTrace (prefixWord ++ tailWord_1516532) baseStart_1516532 baseEnd_1516532 := by
    simpa [prefixWord, tailWord_1516532, baseEnd_1516532] using wordTrace_append hprefix tailTrace_1516532
  have hstable : (prefixWord ++ tailWord_1516532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516532).length < 2 ^ (prefixWord ++ tailWord_1516532).sum := by decide
  have hdescent : baseEnd_1516532 < baseStart_1516532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516537 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 7]
def baseStart_1516537 : Nat := 118140960795 + 1516537 * 2 ^ 59
def prefixEnd_1516537 : Nat := 4983230072969 + 3 ^ 40 * 1516537 * 2
def baseEnd_1516537 : Nat := 86523601258626475079231

theorem tailTrace_1516537 : CollatzResearch.WordTrace tailWord_1516537 prefixEnd_1516537 86523601258626475079231 := by
  unfold tailWord_1516537
  simp only [CollatzResearch.WordTrace]
  refine ⟨55312648506852927744355865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36875099004568618496237243 55312648506852927744355865)
  ·
    refine ⟨41484486380139695808266899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55312648506852927744355865 41484486380139695808266899)
    ·
      refine ⟨62226729570209543712400349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41484486380139695808266899 62226729570209543712400349)
      ·
        refine ⟨23335023588828578892150131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62226729570209543712400349 23335023588828578892150131)
        ·
          refine ⟨35002535383242868338225197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23335023588828578892150131 35002535383242868338225197)
          ·
            refine ⟨13125950768716075626834449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35002535383242868338225197 13125950768716075626834449)
            ·
              refine ⟨9844463076537056720125837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13125950768716075626834449 9844463076537056720125837)
              ·
                refine ⟨3691673653701396270047189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9844463076537056720125837 3691673653701396270047189)
                ·
                  refine ⟨86523601258626475079231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3691673653701396270047189 86523601258626475079231)
                  ·
                    rfl

theorem cell23_1516537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_1516537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516537 prefixEnd_1516537 := by exact prefixLift 1516537
  have htrace : WordTrace (prefixWord ++ tailWord_1516537) baseStart_1516537 baseEnd_1516537 := by
    simpa [prefixWord, tailWord_1516537, baseEnd_1516537] using wordTrace_append hprefix tailTrace_1516537
  have hstable : (prefixWord ++ tailWord_1516537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516537).length < 2 ^ (prefixWord ++ tailWord_1516537).sum := by decide
  have hdescent : baseEnd_1516537 < baseStart_1516537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516554 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_1516554 : Nat := 118140960795 + 1516554 * 2 ^ 59
def prefixEnd_1516554 : Nat := 4983230072969 + 3 ^ 40 * 1516554 * 2
def baseEnd_1516554 : Nat := 86524571166529412133389

theorem tailTrace_1516554 : CollatzResearch.WordTrace tailWord_1516554 prefixEnd_1516554 86524571166529412133389 := by
  unfold tailWord_1516554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828317136947834911931179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36875512365194226431816477 13828317136947834911931179)
  ·
    refine ⟨20742475705421752367896769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13828317136947834911931179 20742475705421752367896769)
    ·
      refine ⟨15556856779066314275922577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20742475705421752367896769 15556856779066314275922577)
      ·
        refine ⟨11667642584299735706941933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15556856779066314275922577 11667642584299735706941933)
        ·
          refine ⟨4375365969112400890103225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11667642584299735706941933 4375365969112400890103225)
          ·
            refine ⟨3281524476834300667577419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4375365969112400890103225 3281524476834300667577419)
            ·
              refine ⟨4922286715251451001366129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281524476834300667577419 4922286715251451001366129)
              ·
                refine ⟨3691715036438588251024597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4922286715251451001366129 3691715036438588251024597)
                ·
                  refine ⟨86524571166529412133389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3691715036438588251024597 86524571166529412133389)
                  ·
                    rfl

theorem cell23_1516554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_1516554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516554 prefixEnd_1516554 := by exact prefixLift 1516554
  have htrace : WordTrace (prefixWord ++ tailWord_1516554) baseStart_1516554 baseEnd_1516554 := by
    simpa [prefixWord, tailWord_1516554, baseEnd_1516554] using wordTrace_append hprefix tailTrace_1516554
  have hstable : (prefixWord ++ tailWord_1516554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516554).length < 2 ^ (prefixWord ++ tailWord_1516554).sum := by decide
  have hdescent : baseEnd_1516554 < baseStart_1516554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516604 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1516604 : Nat := 118140960795 + 1516604 * 2 ^ 59
def prefixEnd_1516604 : Nat := 4983230072969 + 3 ^ 40 * 1516604 * 2
def baseEnd_1516604 : Nat := 778746814531489513575271

theorem tailTrace_1516604 : CollatzResearch.WordTrace tailWord_1516604 prefixEnd_1516604 778746814531489513575271 := by
  unfold tailWord_1516604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27657546098805099093522433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36876728131740132124696577 27657546098805099093522433)
  ·
    refine ⟨20743159574103824320141825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27657546098805099093522433 20743159574103824320141825)
    ·
      refine ⟨15557369680577868240106369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20743159574103824320141825 15557369680577868240106369)
      ·
        refine ⟨11668027260433401180079777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15557369680577868240106369 11668027260433401180079777)
        ·
          refine ⟨8751020445325050885059833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11668027260433401180079777 8751020445325050885059833)
          ·
            refine ⟨6563265333993788163794875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751020445325050885059833 6563265333993788163794875)
            ·
              refine ⟨9844898000990682245692313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563265333993788163794875 9844898000990682245692313)
              ·
                refine ⟨7383673500743011684269235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9844898000990682245692313 7383673500743011684269235)
                ·
                  refine ⟨11075510251114517526403853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7383673500743011684269235 11075510251114517526403853)
                  ·
                    refine ⟨4153316344167944072401445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11075510251114517526403853 4153316344167944072401445)
                    ·
                      refine ⟨778746814531489513575271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4153316344167944072401445 778746814531489513575271)
                      ·
                        rfl

theorem cell23_1516604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1516604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516604 prefixEnd_1516604 := by exact prefixLift 1516604
  have htrace : WordTrace (prefixWord ++ tailWord_1516604) baseStart_1516604 baseEnd_1516604 := by
    simpa [prefixWord, tailWord_1516604, baseEnd_1516604] using wordTrace_append hprefix tailTrace_1516604
  have hstable : (prefixWord ++ tailWord_1516604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516604).length < 2 ^ (prefixWord ++ tailWord_1516604).sum := by decide
  have hdescent : baseEnd_1516604 < baseStart_1516604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516617 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_1516617 : Nat := 118140960795 + 1516617 * 2 ^ 59
def prefixEnd_1516617 : Nat := 4983230072969 + 3 ^ 40 * 1516617 * 2
def baseEnd_1516617 : Nat := 778753489779997962712711

theorem tailTrace_1516617 : CollatzResearch.WordTrace tailWord_1516617 prefixEnd_1516617 778753489779997962712711 := by
  unfold tailWord_1516617
  simp only [CollatzResearch.WordTrace]
  refine ⟨55315566346563101407268105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36877044231042067604845403 55315566346563101407268105)
  ·
    refine ⟨41486674759922326055451079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55315566346563101407268105 41486674759922326055451079)
    ·
      refine ⟨62230012139883489083176619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41486674759922326055451079 62230012139883489083176619)
      ·
        refine ⟨93345018209825233624764929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62230012139883489083176619 93345018209825233624764929)
        ·
          refine ⟨70008763657368925218573697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93345018209825233624764929 70008763657368925218573697)
          ·
            refine ⟨52506572743026693913930273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70008763657368925218573697 52506572743026693913930273)
            ·
              refine ⟨39379929557270020435447705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52506572743026693913930273 39379929557270020435447705)
              ·
                refine ⟨29534947167952515326585779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39379929557270020435447705 29534947167952515326585779)
                ·
                  refine ⟨44302420751928772989878669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29534947167952515326585779 44302420751928772989878669)
                  ·
                    refine ⟨16613407781973289871204501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44302420751928772989878669 16613407781973289871204501)
                    ·
                      refine ⟨778753489779997962712711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16613407781973289871204501 778753489779997962712711)
                      ·
                        rfl

theorem cell23_1516617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_1516617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516617 prefixEnd_1516617 := by exact prefixLift 1516617
  have htrace : WordTrace (prefixWord ++ tailWord_1516617) baseStart_1516617 baseEnd_1516617 := by
    simpa [prefixWord, tailWord_1516617, baseEnd_1516617] using wordTrace_append hprefix tailTrace_1516617
  have hstable : (prefixWord ++ tailWord_1516617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516617).length < 2 ^ (prefixWord ++ tailWord_1516617).sum := by decide
  have hdescent : baseEnd_1516617 < baseStart_1516617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516621 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1516621 : Nat := 118140960795 + 1516621 * 2 ^ 59
def prefixEnd_1516621 : Nat := 4983230072969 + 3 ^ 40 * 1516621 * 2
def baseEnd_1516621 : Nat := 778755543702615947062693

theorem tailTrace_1516621 : CollatzResearch.WordTrace tailWord_1516621 prefixEnd_1516621 778755543702615947062693 := by
  unfold tailWord_1516621
  simp only [CollatzResearch.WordTrace]
  refine ⟨55315712238548610090413717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36877141492365740060275811 55315712238548610090413717)
  ·
    refine ⟨2592924011181966097988143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55315712238548610090413717 2592924011181966097988143)
    ·
      refine ⟨3889386016772949146982215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592924011181966097988143 3889386016772949146982215)
      ·
        refine ⟨5834079025159423720473323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889386016772949146982215 5834079025159423720473323)
        ·
          refine ⟨8751118537739135580709985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834079025159423720473323 8751118537739135580709985)
          ·
            refine ⟨6563338903304351685532489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751118537739135580709985 6563338903304351685532489)
            ·
              refine ⟨4922504177478263764149367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563338903304351685532489 4922504177478263764149367)
              ·
                refine ⟨7383756266217395646224051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922504177478263764149367 7383756266217395646224051)
                ·
                  refine ⟨11075634399326093469336077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7383756266217395646224051 11075634399326093469336077)
                  ·
                    refine ⟨4153362899747285051001029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11075634399326093469336077 4153362899747285051001029)
                    ·
                      refine ⟨778755543702615947062693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4153362899747285051001029 778755543702615947062693)
                      ·
                        rfl

theorem cell23_1516621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1516621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516621 prefixEnd_1516621 := by exact prefixLift 1516621
  have htrace : WordTrace (prefixWord ++ tailWord_1516621) baseStart_1516621 baseEnd_1516621 := by
    simpa [prefixWord, tailWord_1516621, baseEnd_1516621] using wordTrace_append hprefix tailTrace_1516621
  have hstable : (prefixWord ++ tailWord_1516621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516621).length < 2 ^ (prefixWord ++ tailWord_1516621).sum := by decide
  have hdescent : baseEnd_1516621 < baseStart_1516621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516624 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_1516624 : Nat := 118140960795 + 1516624 * 2 ^ 59
def prefixEnd_1516624 : Nat := 4983230072969 + 3 ^ 40 * 1516624 * 2
def baseEnd_1516624 : Nat := 778757084144579435325179

theorem tailTrace_1516624 : CollatzResearch.WordTrace tailWord_1516624 prefixEnd_1516624 778757084144579435325179 := by
  unfold tailWord_1516624
  simp only [CollatzResearch.WordTrace]
  refine ⟨27657910828768870801386463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36877214438358494401848617 27657910828768870801386463)
  ·
    refine ⟨41486866243153306202079695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27657910828768870801386463 41486866243153306202079695)
    ·
      refine ⟨62230299364729959303119543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41486866243153306202079695 62230299364729959303119543)
      ·
        refine ⟨93345449047094938954679315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62230299364729959303119543 93345449047094938954679315)
        ·
          refine ⟨140018173570642408432018973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93345449047094938954679315 140018173570642408432018973)
          ·
            refine ⟨52506815088990903162007115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140018173570642408432018973 52506815088990903162007115)
            ·
              refine ⟨78760222633486354743010673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52506815088990903162007115 78760222633486354743010673)
              ·
                refine ⟨59070166975114766057258005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78760222633486354743010673 59070166975114766057258005)
                ·
                  refine ⟨2768914076958504658933969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59070166975114766057258005 2768914076958504658933969)
                  ·
                    refine ⟨2076685557718878494200477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768914076958504658933969 2076685557718878494200477)
                    ·
                      refine ⟨778757084144579435325179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076685557718878494200477 778757084144579435325179)
                      ·
                        rfl

theorem cell23_1516624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_1516624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516624 prefixEnd_1516624 := by exact prefixLift 1516624
  have htrace : WordTrace (prefixWord ++ tailWord_1516624) baseStart_1516624 baseEnd_1516624 := by
    simpa [prefixWord, tailWord_1516624, baseEnd_1516624] using wordTrace_append hprefix tailTrace_1516624
  have hstable : (prefixWord ++ tailWord_1516624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516624).length < 2 ^ (prefixWord ++ tailWord_1516624).sum := by decide
  have hdescent : baseEnd_1516624 < baseStart_1516624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516627 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 8]
def baseStart_1516627 : Nat := 118140960795 + 1516627 * 2 ^ 59
def prefixEnd_1516627 : Nat := 4983230072969 + 3 ^ 40 * 1516627 * 2
def baseEnd_1516627 : Nat := 86528736065171435954185

theorem tailTrace_1516627 : CollatzResearch.WordTrace tailWord_1516627 prefixEnd_1516627 86528736065171435954185 := by
  unfold tailWord_1516627
  simp only [CollatzResearch.WordTrace]
  refine ⟨55315931076526873115132135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36877287384351248743421423 55315931076526873115132135)
  ·
    refine ⟨82973896614790309672698203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55315931076526873115132135 82973896614790309672698203)
    ·
      refine ⟨124460844922185464509047305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82973896614790309672698203 124460844922185464509047305)
      ·
        refine ⟨93345633691639098381785479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124460844922185464509047305 93345633691639098381785479)
        ·
          refine ⟨140018450537458647572678219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93345633691639098381785479 140018450537458647572678219)
          ·
            refine ⟨210027675806187971359017329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140018450537458647572678219 210027675806187971359017329)
            ·
              refine ⟨157520756854640978519262997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210027675806187971359017329 157520756854640978519262997)
              ·
                refine ⟨7383785477561295868090453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157520756854640978519262997 7383785477561295868090453)
                ·
                  refine ⟨86528736065171435954185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7383785477561295868090453 86528736065171435954185)
                  ·
                    rfl

theorem cell23_1516627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 8].length) (baseStart_1516627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516627 prefixEnd_1516627 := by exact prefixLift 1516627
  have htrace : WordTrace (prefixWord ++ tailWord_1516627) baseStart_1516627 baseEnd_1516627 := by
    simpa [prefixWord, tailWord_1516627, baseEnd_1516627] using wordTrace_append hprefix tailTrace_1516627
  have hstable : (prefixWord ++ tailWord_1516627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516627).length < 2 ^ (prefixWord ++ tailWord_1516627).sum := by decide
  have hdescent : baseEnd_1516627 < baseStart_1516627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516644 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 6]
def baseStart_1516644 : Nat := 118140960795 + 1516644 * 2 ^ 59
def prefixEnd_1516644 : Nat := 4983230072969 + 3 ^ 40 * 1516644 * 2
def baseEnd_1516644 : Nat := 86529705973074373008343

theorem tailTrace_1516644 : CollatzResearch.WordTrace tailWord_1516644 prefixEnd_1516644 86529705973074373008343 := by
  unfold tailWord_1516644
  simp only [CollatzResearch.WordTrace]
  refine ⟨27658275558732642509250493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36877700744976856679000657 27658275558732642509250493)
  ·
    refine ⟨10371853334524740940968935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27658275558732642509250493 10371853334524740940968935)
    ·
      refine ⟨15557780001787111411453403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10371853334524740940968935 15557780001787111411453403)
      ·
        refine ⟨23336670002680667117180105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15557780001787111411453403 23336670002680667117180105)
        ·
          refine ⟨17502502502010500337885079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23336670002680667117180105 17502502502010500337885079)
          ·
            refine ⟨26253753753015750506827619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17502502502010500337885079 26253753753015750506827619)
            ·
              refine ⟨39380630629523625760241429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26253753753015750506827619 39380630629523625760241429)
              ·
                refine ⟨1845967060758919957511317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39380630629523625760241429 1845967060758919957511317)
                ·
                  refine ⟨86529705973074373008343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1845967060758919957511317 86529705973074373008343)
                  ·
                    rfl

theorem cell23_1516644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_1516644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516644 prefixEnd_1516644 := by exact prefixLift 1516644
  have htrace : WordTrace (prefixWord ++ tailWord_1516644) baseStart_1516644 baseEnd_1516644 := by
    simpa [prefixWord, tailWord_1516644, baseEnd_1516644] using wordTrace_append hprefix tailTrace_1516644
  have hstable : (prefixWord ++ tailWord_1516644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516644).length < 2 ^ (prefixWord ++ tailWord_1516644).sum := by decide
  have hdescent : baseEnd_1516644 < baseStart_1516644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516704 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_1516704 : Nat := 118140960795 + 1516704 * 2 ^ 59
def prefixEnd_1516704 : Nat := 4983230072969 + 3 ^ 40 * 1516704 * 2
def baseEnd_1516704 : Nat := 259599387532313040774937

theorem tailTrace_1516704 : CollatzResearch.WordTrace tailWord_1516704 prefixEnd_1516704 259599387532313040774937 := by
  unfold tailWord_1516704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27659369748623957632842583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36879159664831943510456777 27659369748623957632842583)
  ·
    refine ⟨41489054622935936449263875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27659369748623957632842583 41489054622935936449263875)
    ·
      refine ⟨62233581934403904673895813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41489054622935936449263875 62233581934403904673895813)
      ·
        refine ⟨11668796612700732126355465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62233581934403904673895813 11668796612700732126355465)
        ·
          refine ⟨8751597459525549094766599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11668796612700732126355465 8751597459525549094766599)
          ·
            refine ⟨13127396189288323642149899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751597459525549094766599 13127396189288323642149899)
            ·
              refine ⟨19691094283932485463224849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13127396189288323642149899 19691094283932485463224849)
              ·
                refine ⟨14768320712949364097418637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19691094283932485463224849 14768320712949364097418637)
                ·
                  refine ⟨5538120267356011536531989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14768320712949364097418637 5538120267356011536531989)
                  ·
                    refine ⟨259599387532313040774937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5538120267356011536531989 259599387532313040774937)
                    ·
                      rfl

theorem cell23_1516704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_1516704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516704 prefixEnd_1516704 := by exact prefixLift 1516704
  have htrace : WordTrace (prefixWord ++ tailWord_1516704) baseStart_1516704 baseEnd_1516704 := by
    simpa [prefixWord, tailWord_1516704, baseEnd_1516704] using wordTrace_append hprefix tailTrace_1516704
  have hstable : (prefixWord ++ tailWord_1516704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516704).length < 2 ^ (prefixWord ++ tailWord_1516704).sum := by decide
  have hdescent : baseEnd_1516704 < baseStart_1516704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516705 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1516705 : Nat := 118140960795 + 1516705 * 2 ^ 59
def prefixEnd_1516705 : Nat := 4983230072969 + 3 ^ 40 * 1516705 * 2
def baseEnd_1516705 : Nat := 778798676077593618412307

theorem tailTrace_1516705 : CollatzResearch.WordTrace tailWord_1516705 prefixEnd_1516705 778798676077593618412307 := by
  unfold tailWord_1516705
  simp only [CollatzResearch.WordTrace]
  refine ⟨55318775970244292436471569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36879183980162861624314379 55318775970244292436471569)
  ·
    refine ⟨41489081977683219327353677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55318775970244292436471569 41489081977683219327353677)
    ·
      refine ⟨15558405741631207247757629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41489081977683219327353677 15558405741631207247757629)
      ·
        refine ⟨5834402153111702717909111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15558405741631207247757629 5834402153111702717909111)
        ·
          refine ⟨8751603229667554076863667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834402153111702717909111 8751603229667554076863667)
          ·
            refine ⟨13127404844501331115295501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751603229667554076863667 13127404844501331115295501)
            ·
              refine ⟨4922776816687999168235813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13127404844501331115295501 4922776816687999168235813)
              ·
                refine ⟨923020653128999844044215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4922776816687999168235813 923020653128999844044215)
                ·
                  refine ⟨1384530979693499766066323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923020653128999844044215 1384530979693499766066323)
                  ·
                    refine ⟨2076796469540249649099485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384530979693499766066323 2076796469540249649099485)
                    ·
                      refine ⟨778798676077593618412307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076796469540249649099485 778798676077593618412307)
                      ·
                        rfl

theorem cell23_1516705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1516705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516705 prefixEnd_1516705 := by exact prefixLift 1516705
  have htrace : WordTrace (prefixWord ++ tailWord_1516705) baseStart_1516705 baseEnd_1516705 := by
    simpa [prefixWord, tailWord_1516705, baseEnd_1516705] using wordTrace_append hprefix tailTrace_1516705
  have hstable : (prefixWord ++ tailWord_1516705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516705).length < 2 ^ (prefixWord ++ tailWord_1516705).sum := by decide
  have hdescent : baseEnd_1516705 < baseStart_1516705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516721 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_1516721 : Nat := 118140960795 + 1516721 * 2 ^ 59
def prefixEnd_1516721 : Nat := 4983230072969 + 3 ^ 40 * 1516721 * 2
def baseEnd_1516721 : Nat := 259602297256021851937411

theorem tailTrace_1516721 : CollatzResearch.WordTrace tailWord_1516721 prefixEnd_1516721 259602297256021851937411 := by
  unfold tailWord_1516721
  simp only [CollatzResearch.WordTrace]
  refine ⟨55319359538186327169054017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36879573025457551446036011 55319359538186327169054017)
  ·
    refine ⟨41489519653639745376790513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55319359538186327169054017 41489519653639745376790513)
    ·
      refine ⟨31117139740229809032592885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41489519653639745376790513 31117139740229809032592885)
      ·
        refine ⟨2917231850646544596805583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31117139740229809032592885 2917231850646544596805583)
        ·
          refine ⟨4375847775969816895208375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917231850646544596805583 4375847775969816895208375)
          ·
            refine ⟨6563771663954725342812563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375847775969816895208375 6563771663954725342812563)
            ·
              refine ⟨9845657495932088014218845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563771663954725342812563 9845657495932088014218845)
              ·
                refine ⟨3692121560974533005332067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9845657495932088014218845 3692121560974533005332067)
                ·
                  refine ⟨5538182341461799507998101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692121560974533005332067 5538182341461799507998101)
                  ·
                    refine ⟨259602297256021851937411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5538182341461799507998101 259602297256021851937411)
                    ·
                      rfl

theorem cell23_1516721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_1516721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516721 prefixEnd_1516721 := by exact prefixLift 1516721
  have htrace : WordTrace (prefixWord ++ tailWord_1516721) baseStart_1516721 baseEnd_1516721 := by
    simpa [prefixWord, tailWord_1516721, baseEnd_1516721] using wordTrace_append hprefix tailTrace_1516721
  have hstable : (prefixWord ++ tailWord_1516721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516721).length < 2 ^ (prefixWord ++ tailWord_1516721).sum := by decide
  have hdescent : baseEnd_1516721 < baseStart_1516721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516775 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1516775 : Nat := 118140960795 + 1516775 * 2 ^ 59
def prefixEnd_1516775 : Nat := 4983230072969 + 3 ^ 40 * 1516775 * 2
def baseEnd_1516775 : Nat := 778834619723408344536985

theorem tailTrace_1516775 : CollatzResearch.WordTrace tailWord_1516775 prefixEnd_1516775 778834619723408344536985 := by
  unfold tailWord_1516775
  simp only [CollatzResearch.WordTrace]
  refine ⟨55321329079990694391519779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36880886053327129594346519 55321329079990694391519779)
  ·
    refine ⟨82981993619986041587279669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55321329079990694391519779 82981993619986041587279669)
    ·
      refine ⟨7779561901873691398807469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82981993619986041587279669 7779561901873691398807469)
      ·
        refine ⟨2917335713202634274552801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7779561901873691398807469 2917335713202634274552801)
        ·
          refine ⟨2188001784901975705914601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917335713202634274552801 2188001784901975705914601)
          ·
            refine ⟨1641001338676481779435951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188001784901975705914601 1641001338676481779435951)
            ·
              refine ⟨2461502008014722669153927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641001338676481779435951 2461502008014722669153927)
              ·
                refine ⟨3692253012022084003730891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461502008014722669153927 3692253012022084003730891)
                ·
                  refine ⟨5538379518033126005596337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692253012022084003730891 5538379518033126005596337)
                  ·
                    refine ⟨4153784638524844504197253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538379518033126005596337 4153784638524844504197253)
                    ·
                      refine ⟨778834619723408344536985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4153784638524844504197253 778834619723408344536985)
                      ·
                        rfl

theorem cell23_1516775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1516775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516775 prefixEnd_1516775 := by exact prefixLift 1516775
  have htrace : WordTrace (prefixWord ++ tailWord_1516775) baseStart_1516775 baseEnd_1516775 := by
    simpa [prefixWord, tailWord_1516775, baseEnd_1516775] using wordTrace_append hprefix tailTrace_1516775
  have hstable : (prefixWord ++ tailWord_1516775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516775).length < 2 ^ (prefixWord ++ tailWord_1516775).sum := by decide
  have hdescent : baseEnd_1516775 < baseStart_1516775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516778 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1516778 : Nat := 118140960795 + 1516778 * 2 ^ 59
def prefixEnd_1516778 : Nat := 4983230072969 + 3 ^ 40 * 1516778 * 2
def baseEnd_1516778 : Nat := 778836160165371832799471

theorem tailTrace_1516778 : CollatzResearch.WordTrace tailWord_1516778 prefixEnd_1516778 778836160165371832799471 := by
  unfold tailWord_1516778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830359624744956475969747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36880958999319883935919325 13830359624744956475969747)
  ·
    refine ⟨20745539437117434713954621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13830359624744956475969747 20745539437117434713954621)
    ·
      refine ⟨7779577288919038017732983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20745539437117434713954621 7779577288919038017732983)
      ·
        refine ⟨11669365933378557026599475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779577288919038017732983 11669365933378557026599475)
        ·
          refine ⟨17504048900067835539899213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11669365933378557026599475 17504048900067835539899213)
          ·
            refine ⟨6564018337525438327462205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17504048900067835539899213 6564018337525438327462205)
            ·
              refine ⟨2461506876572039372798327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6564018337525438327462205 2461506876572039372798327)
              ·
                refine ⟨3692260314858059059197491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461506876572039372798327 3692260314858059059197491)
                ·
                  refine ⟨5538390472287088588796237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692260314858059059197491 5538390472287088588796237)
                  ·
                    refine ⟨2076896427107658220798589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5538390472287088588796237 2076896427107658220798589)
                    ·
                      refine ⟨778836160165371832799471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076896427107658220798589 778836160165371832799471)
                      ·
                        rfl

theorem cell23_1516778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1516778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516778 prefixEnd_1516778 := by exact prefixLift 1516778
  have htrace : WordTrace (prefixWord ++ tailWord_1516778) baseStart_1516778 baseEnd_1516778 := by
    simpa [prefixWord, tailWord_1516778, baseEnd_1516778] using wordTrace_append hprefix tailTrace_1516778
  have hstable : (prefixWord ++ tailWord_1516778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516778).length < 2 ^ (prefixWord ++ tailWord_1516778).sum := by decide
  have hdescent : baseEnd_1516778 < baseStart_1516778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516796 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_1516796 : Nat := 118140960795 + 1516796 * 2 ^ 59
def prefixEnd_1516796 : Nat := 4983230072969 + 3 ^ 40 * 1516796 * 2
def baseEnd_1516796 : Nat := 778845402817152762374389

theorem tailTrace_1516796 : CollatzResearch.WordTrace tailWord_1516796 prefixEnd_1516796 778845402817152762374389 := by
  unfold tailWord_1516796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27661047506457307489017121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36881396675276409985356161 27661047506457307489017121)
  ·
    refine ⟨20745785629842980616762841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27661047506457307489017121 20745785629842980616762841)
    ·
      refine ⟨15559339222382235462572131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20745785629842980616762841 15559339222382235462572131)
      ·
        refine ⟨23339008833573353193858197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15559339222382235462572131 23339008833573353193858197)
        ·
          refine ⟨1094016039073750930962103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23339008833573353193858197 1094016039073750930962103)
          ·
            refine ⟨1641024058610626396443155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094016039073750930962103 1641024058610626396443155)
            ·
              refine ⟨2461536087915939594664733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641024058610626396443155 2461536087915939594664733)
              ·
                refine ⟨923076032968477347999275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461536087915939594664733 923076032968477347999275)
                ·
                  refine ⟨1384614049452716021998913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923076032968477347999275 1384614049452716021998913)
                  ·
                    refine ⟨1038460537089537016499185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1384614049452716021998913 1038460537089537016499185)
                    ·
                      refine ⟨778845402817152762374389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038460537089537016499185 778845402817152762374389)
                      ·
                        rfl

theorem cell23_1516796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_1516796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516796 prefixEnd_1516796 := by exact prefixLift 1516796
  have htrace : WordTrace (prefixWord ++ tailWord_1516796) baseStart_1516796 baseEnd_1516796 := by
    simpa [prefixWord, tailWord_1516796, baseEnd_1516796] using wordTrace_append hprefix tailTrace_1516796
  have hstable : (prefixWord ++ tailWord_1516796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516796).length < 2 ^ (prefixWord ++ tailWord_1516796).sum := by decide
  have hdescent : baseEnd_1516796 < baseStart_1516796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516821 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_1516821 : Nat := 118140960795 + 1516821 * 2 ^ 59
def prefixEnd_1516821 : Nat := 4983230072969 + 3 ^ 40 * 1516821 * 2
def baseEnd_1516821 : Nat := 778858239833515164561773

theorem tailTrace_1516821 : CollatzResearch.WordTrace tailWord_1516821 prefixEnd_1516821 778858239833515164561773 := by
  unfold tailWord_1516821
  simp only [CollatzResearch.WordTrace]
  refine ⟨55323006837824044247694317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36882004558549362831796211 55323006837824044247694317)
  ·
    refine ⟨20746127564184016592885369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55323006837824044247694317 20746127564184016592885369)
    ·
      refine ⟨15559595673138012444664027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20746127564184016592885369 15559595673138012444664027)
      ·
        refine ⟨23339393509707018666996041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15559595673138012444664027 23339393509707018666996041)
        ·
          refine ⟨17504545132280264000247031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23339393509707018666996041 17504545132280264000247031)
          ·
            refine ⟨26256817698420396000370547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17504545132280264000247031 26256817698420396000370547)
            ·
              refine ⟨39385226547630594000555821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26256817698420396000370547 39385226547630594000555821)
              ·
                refine ⟨14769459955361472750208433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39385226547630594000555821 14769459955361472750208433)
                ·
                  refine ⟨11077094966521104562656325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14769459955361472750208433 11077094966521104562656325)
                  ·
                    refine ⟨2076955306222707105498061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11077094966521104562656325 2076955306222707105498061)
                    ·
                      refine ⟨778858239833515164561773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076955306222707105498061 778858239833515164561773)
                      ·
                        rfl

theorem cell23_1516821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_1516821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516821 prefixEnd_1516821 := by exact prefixLift 1516821
  have htrace : WordTrace (prefixWord ++ tailWord_1516821) baseStart_1516821 baseEnd_1516821 := by
    simpa [prefixWord, tailWord_1516821, baseEnd_1516821] using wordTrace_append hprefix tailTrace_1516821
  have hstable : (prefixWord ++ tailWord_1516821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516821).length < 2 ^ (prefixWord ++ tailWord_1516821).sum := by decide
  have hdescent : baseEnd_1516821 < baseStart_1516821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516829 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1516829 : Nat := 118140960795 + 1516829 * 2 ^ 59
def prefixEnd_1516829 : Nat := 4983230072969 + 3 ^ 40 * 1516829 * 2
def baseEnd_1516829 : Nat := 778862347678751133261737

theorem tailTrace_1516829 : CollatzResearch.WordTrace tailWord_1516829 prefixEnd_1516829 778862347678751133261737 := by
  unfold tailWord_1516829
  simp only [CollatzResearch.WordTrace]
  refine ⟨55323298621795061613985541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36882199081196707742657027 55323298621795061613985541)
  ·
    refine ⟨10373118491586574052622289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55323298621795061613985541 10373118491586574052622289)
    ·
      refine ⟨7779838868689930539466717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10373118491586574052622289 7779838868689930539466717)
      ·
        refine ⟨2917439575758723952300019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7779838868689930539466717 2917439575758723952300019)
        ·
          refine ⟨4376159363638085928450029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917439575758723952300019 4376159363638085928450029)
          ·
            refine ⟨1641059761364282223168761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4376159363638085928450029 1641059761364282223168761)
            ·
              refine ⟨1230794821023211667376571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641059761364282223168761 1230794821023211667376571)
              ·
                refine ⟨1846192231534817501064857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230794821023211667376571 1846192231534817501064857)
                ·
                  refine ⟨1384644173651113125798643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846192231534817501064857 1384644173651113125798643)
                  ·
                    refine ⟨2076966260476669688697965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384644173651113125798643 2076966260476669688697965)
                    ·
                      refine ⟨778862347678751133261737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2076966260476669688697965 778862347678751133261737)
                      ·
                        rfl

theorem cell23_1516829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1516829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516829 prefixEnd_1516829 := by exact prefixLift 1516829
  have htrace : WordTrace (prefixWord ++ tailWord_1516829) baseStart_1516829 baseEnd_1516829 := by
    simpa [prefixWord, tailWord_1516829, baseEnd_1516829] using wordTrace_append hprefix tailTrace_1516829
  have hstable : (prefixWord ++ tailWord_1516829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516829).length < 2 ^ (prefixWord ++ tailWord_1516829).sum := by decide
  have hdescent : baseEnd_1516829 < baseStart_1516829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516858 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_1516858 : Nat := 118140960795 + 1516858 * 2 ^ 59
def prefixEnd_1516858 : Nat := 4983230072969 + 3 ^ 40 * 1516858 * 2
def baseEnd_1516858 : Nat := 86541915401970168866567

theorem tailTrace_1516858 : CollatzResearch.WordTrace tailWord_1516858 prefixEnd_1516858 86541915401970168866567 := by
  unfold tailWord_1516858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13831089084672499891697807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36882904225793333044527485 13831089084672499891697807)
  ·
    refine ⟨20746633627008749837546711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13831089084672499891697807 20746633627008749837546711)
    ·
      refine ⟨31119950440513124756320067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20746633627008749837546711 31119950440513124756320067)
      ·
        refine ⟨46679925660769687134480101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31119950440513124756320067 46679925660769687134480101)
        ·
          refine ⟨8752486061394316337715019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46679925660769687134480101 8752486061394316337715019)
          ·
            refine ⟨13128729092091474506572529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8752486061394316337715019 13128729092091474506572529)
            ·
              refine ⟨9846546819068605879929397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13128729092091474506572529 9846546819068605879929397)
              ·
                refine ⟨923113764287681801243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9846546819068605879929397 923113764287681801243381)
                ·
                  refine ⟨86541915401970168866567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923113764287681801243381 86541915401970168866567)
                  ·
                    rfl

theorem cell23_1516858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_1516858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516858 prefixEnd_1516858 := by exact prefixLift 1516858
  have htrace : WordTrace (prefixWord ++ tailWord_1516858) baseStart_1516858 baseEnd_1516858 := by
    simpa [prefixWord, tailWord_1516858, baseEnd_1516858] using wordTrace_append hprefix tailTrace_1516858
  have hstable : (prefixWord ++ tailWord_1516858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516858).length < 2 ^ (prefixWord ++ tailWord_1516858).sum := by decide
  have hdescent : baseEnd_1516858 < baseStart_1516858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516878 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_1516878 : Nat := 118140960795 + 1516878 * 2 ^ 59
def prefixEnd_1516878 : Nat := 4983230072969 + 3 ^ 40 * 1516878 * 2
def baseEnd_1516878 : Nat := 778887508230821441549011

theorem tailTrace_1516878 : CollatzResearch.WordTrace tailWord_1516878 prefixEnd_1516878 778887508230821441549011 := by
  unfold tailWord_1516878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915635724827192872814911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36883390532411695321679525 6915635724827192872814911)
  ·
    refine ⟨10373453587240789309222367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915635724827192872814911 10373453587240789309222367)
    ·
      refine ⟨15560180380861183963833551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10373453587240789309222367 15560180380861183963833551)
      ·
        refine ⟨23340270571291775945750327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15560180380861183963833551 23340270571291775945750327)
        ·
          refine ⟨35010405856937663918625491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23340270571291775945750327 35010405856937663918625491)
          ·
            refine ⟨52515608785406495877938237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35010405856937663918625491 52515608785406495877938237)
            ·
              refine ⟨19693353294527435954226839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52515608785406495877938237 19693353294527435954226839)
              ·
                refine ⟨29540029941791153931340259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19693353294527435954226839 29540029941791153931340259)
                ·
                  refine ⟨44310044912686730897010389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29540029941791153931340259 44310044912686730897010389)
                  ·
                    refine ⟨1038516677641095255398681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44310044912686730897010389 1038516677641095255398681)
                    ·
                      refine ⟨778887508230821441549011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038516677641095255398681 778887508230821441549011)
                      ·
                        rfl

theorem cell23_1516878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_1516878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516878 prefixEnd_1516878 := by exact prefixLift 1516878
  have htrace : WordTrace (prefixWord ++ tailWord_1516878) baseStart_1516878 baseEnd_1516878 := by
    simpa [prefixWord, tailWord_1516878, baseEnd_1516878] using wordTrace_append hprefix tailTrace_1516878
  have hstable : (prefixWord ++ tailWord_1516878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516878).length < 2 ^ (prefixWord ++ tailWord_1516878).sum := by decide
  have hdescent : baseEnd_1516878 < baseStart_1516878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516881 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_1516881 : Nat := 118140960795 + 1516881 * 2 ^ 59
def prefixEnd_1516881 : Nat := 4983230072969 + 3 ^ 40 * 1516881 * 2
def baseEnd_1516881 : Nat := 778889048672784929811497

theorem tailTrace_1516881 : CollatzResearch.WordTrace tailWord_1516881 prefixEnd_1516881 778889048672784929811497 := by
  unfold tailWord_1516881
  simp only [CollatzResearch.WordTrace]
  refine ⟨55325195217606674494878497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36883463478404449663252331 55325195217606674494878497)
  ·
    refine ⟨41493896413205005871158873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55325195217606674494878497 41493896413205005871158873)
    ·
      refine ⟨31120422309903754403369155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41493896413205005871158873 31120422309903754403369155)
      ·
        refine ⟨46680633464855631605053733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31120422309903754403369155 46680633464855631605053733)
        ·
          refine ⟨8752618774660430925947575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46680633464855631605053733 8752618774660430925947575)
          ·
            refine ⟨13128928161990646388921363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8752618774660430925947575 13128928161990646388921363)
            ·
              refine ⟨19693392242985969583382045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13128928161990646388921363 19693392242985969583382045)
              ·
                refine ⟨7385022091119738593768267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19693392242985969583382045 7385022091119738593768267)
                ·
                  refine ⟨11077533136679607890652401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7385022091119738593768267 11077533136679607890652401)
                  ·
                    refine ⟨8308149852509705917989301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11077533136679607890652401 8308149852509705917989301)
                    ·
                      refine ⟨778889048672784929811497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8308149852509705917989301 778889048672784929811497)
                      ·
                        rfl

theorem cell23_1516881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_1516881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516881 prefixEnd_1516881 := by exact prefixLift 1516881
  have htrace : WordTrace (prefixWord ++ tailWord_1516881) baseStart_1516881 baseEnd_1516881 := by
    simpa [prefixWord, tailWord_1516881, baseEnd_1516881] using wordTrace_append hprefix tailTrace_1516881
  have hstable : (prefixWord ++ tailWord_1516881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516881).length < 2 ^ (prefixWord ++ tailWord_1516881).sum := by decide
  have hdescent : baseEnd_1516881 < baseStart_1516881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516908 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1516908 : Nat := 118140960795 + 1516908 * 2 ^ 59
def prefixEnd_1516908 : Nat := 4983230072969 + 3 ^ 40 * 1516908 * 2
def baseEnd_1516908 : Nat := 778902912650456324173873

theorem tailTrace_1516908 : CollatzResearch.WordTrace tailWord_1516908 prefixEnd_1516908 778902912650456324173873 := by
  unfold tailWord_1516908
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663089994254429053055689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36884119992339238737407585 27663089994254429053055689)
  ·
    refine ⟨20747317495690821789791767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27663089994254429053055689 20747317495690821789791767)
    ·
      refine ⟨31120976243536232684687651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20747317495690821789791767 31120976243536232684687651)
      ·
        refine ⟨46681464365304349027031477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31120976243536232684687651 46681464365304349027031477)
        ·
          refine ⟨4376387284247282721284201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46681464365304349027031477 4376387284247282721284201)
          ·
            refine ⟨3282290463185462040963151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376387284247282721284201 3282290463185462040963151)
            ·
              refine ⟨4923435694778193061444727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282290463185462040963151 4923435694778193061444727)
              ·
                refine ⟨7385153542167289592167091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923435694778193061444727 7385153542167289592167091)
                ·
                  refine ⟨11077730313250934388250637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7385153542167289592167091 11077730313250934388250637)
                  ·
                    refine ⟨4154148867469100395593989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11077730313250934388250637 4154148867469100395593989)
                    ·
                      refine ⟨778902912650456324173873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4154148867469100395593989 778902912650456324173873)
                      ·
                        rfl

theorem cell23_1516908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1516908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516908 prefixEnd_1516908 := by exact prefixLift 1516908
  have htrace : WordTrace (prefixWord ++ tailWord_1516908) baseStart_1516908 baseEnd_1516908 := by
    simpa [prefixWord, tailWord_1516908, baseEnd_1516908] using wordTrace_append hprefix tailTrace_1516908
  have hstable : (prefixWord ++ tailWord_1516908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516908).length < 2 ^ (prefixWord ++ tailWord_1516908).sum := by decide
  have hdescent : baseEnd_1516908 < baseStart_1516908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516921 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1516921 : Nat := 118140960795 + 1516921 * 2 ^ 59
def prefixEnd_1516921 : Nat := 4983230072969 + 3 ^ 40 * 1516921 * 2
def baseEnd_1516921 : Nat := 778909587898964773311313

theorem tailTrace_1516921 : CollatzResearch.WordTrace tailWord_1516921 prefixEnd_1516921 778909587898964773311313 := by
  unfold tailWord_1516921
  simp only [CollatzResearch.WordTrace]
  refine ⟨55326654137461761326334617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36884436091641174217556411 55326654137461761326334617)
  ·
    refine ⟨41494990603096320994750963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55326654137461761326334617 41494990603096320994750963)
    ·
      refine ⟨62242485904644481492126445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41494990603096320994750963 62242485904644481492126445)
      ·
        refine ⟨23340932214241680559547417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62242485904644481492126445 23340932214241680559547417)
        ·
          refine ⟨17505699160681260419660563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23340932214241680559547417 17505699160681260419660563)
          ·
            refine ⟨26258548741021890629490845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17505699160681260419660563 26258548741021890629490845)
            ·
              refine ⟨9846955777883208986059067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26258548741021890629490845 9846955777883208986059067)
              ·
                refine ⟨14770433666824813479088601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9846955777883208986059067 14770433666824813479088601)
                ·
                  refine ⟨11077825250118610109316451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14770433666824813479088601 11077825250118610109316451)
                  ·
                    refine ⟨16616737875177915163974677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11077825250118610109316451 16616737875177915163974677)
                    ·
                      refine ⟨778909587898964773311313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16616737875177915163974677 778909587898964773311313)
                      ·
                        rfl

theorem cell23_1516921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1516921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516921 prefixEnd_1516921 := by exact prefixLift 1516921
  have htrace : WordTrace (prefixWord ++ tailWord_1516921) baseStart_1516921 baseEnd_1516921 := by
    simpa [prefixWord, tailWord_1516921, baseEnd_1516921] using wordTrace_append hprefix tailTrace_1516921
  have hstable : (prefixWord ++ tailWord_1516921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516921).length < 2 ^ (prefixWord ++ tailWord_1516921).sum := by decide
  have hdescent : baseEnd_1516921 < baseStart_1516921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516928 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_1516928 : Nat := 118140960795 + 1516928 * 2 ^ 59
def prefixEnd_1516928 : Nat := 4983230072969 + 3 ^ 40 * 1516928 * 2
def baseEnd_1516928 : Nat := 778913182263546245923781

theorem tailTrace_1516928 : CollatzResearch.WordTrace tailWord_1516928 prefixEnd_1516928 778913182263546245923781 := by
  unfold tailWord_1516928
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663454724218200760919719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36884606298957601014559625 27663454724218200760919719)
  ·
    refine ⟨41495182086327301141379579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27663454724218200760919719 41495182086327301141379579)
    ·
      refine ⟨62242773129490951712069369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41495182086327301141379579 62242773129490951712069369)
      ·
        refine ⟨46682079847118213784052027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62242773129490951712069369 46682079847118213784052027)
        ·
          refine ⟨70023119770677320676078041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46682079847118213784052027 70023119770677320676078041)
          ·
            refine ⟨52517339828007990507058531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70023119770677320676078041 52517339828007990507058531)
            ·
              refine ⟨78776009742011985760587797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52517339828007990507058531 78776009742011985760587797)
              ·
                refine ⟨3692625456656811832527553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78776009742011985760587797 3692625456656811832527553)
                ·
                  refine ⟨2769469092492608874395665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692625456656811832527553 2769469092492608874395665)
                  ·
                    refine ⟨2077101819369456655796749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769469092492608874395665 2077101819369456655796749)
                    ·
                      refine ⟨778913182263546245923781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077101819369456655796749 778913182263546245923781)
                      ·
                        rfl

theorem cell23_1516928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_1516928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516928 prefixEnd_1516928 := by exact prefixLift 1516928
  have htrace : WordTrace (prefixWord ++ tailWord_1516928) baseStart_1516928 baseEnd_1516928 := by
    simpa [prefixWord, tailWord_1516928, baseEnd_1516928] using wordTrace_append hprefix tailTrace_1516928
  have hstable : (prefixWord ++ tailWord_1516928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516928).length < 2 ^ (prefixWord ++ tailWord_1516928).sum := by decide
  have hdescent : baseEnd_1516928 < baseStart_1516928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516935 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 3, 4]
def baseStart_1516935 : Nat := 118140960795 + 1516935 * 2 ^ 59
def prefixEnd_1516935 : Nat := 4983230072969 + 3 ^ 40 * 1516935 * 2
def baseEnd_1516935 : Nat := 259638925542709239512083

theorem tailTrace_1516935 : CollatzResearch.WordTrace tailWord_1516935 prefixEnd_1516935 259638925542709239512083 := by
  unfold tailWord_1516935
  simp only [CollatzResearch.WordTrace]
  refine ⟨55327164759411041717344259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36884776506274027811562839 55327164759411041717344259)
  ·
    refine ⟨82990747139116562576016389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55327164759411041717344259 82990747139116562576016389)
    ·
      refine ⟨15560765088584355483003073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82990747139116562576016389 15560765088584355483003073)
      ·
        refine ⟨11670573816438266612252305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15560765088584355483003073 11670573816438266612252305)
        ·
          refine ⟨8752930362328699959189229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11670573816438266612252305 8752930362328699959189229)
          ·
            refine ⟨3282348885873262484695961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8752930362328699959189229 3282348885873262484695961)
            ·
              refine ⟨2461761664404946863521971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282348885873262484695961 2461761664404946863521971)
              ·
                refine ⟨3692642496607420295282957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461761664404946863521971 3692642496607420295282957)
                ·
                  refine ⟨1384740936227782610731109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3692642496607420295282957 1384740936227782610731109)
                  ·
                    refine ⟨259638925542709239512083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1384740936227782610731109 259638925542709239512083)
                    ·
                      rfl

theorem cell23_1516935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_1516935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516935 prefixEnd_1516935 := by exact prefixLift 1516935
  have htrace : WordTrace (prefixWord ++ tailWord_1516935) baseStart_1516935 baseEnd_1516935 := by
    simpa [prefixWord, tailWord_1516935, baseEnd_1516935] using wordTrace_append hprefix tailTrace_1516935
  have hstable : (prefixWord ++ tailWord_1516935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516935).length < 2 ^ (prefixWord ++ tailWord_1516935).sum := by decide
  have hdescent : baseEnd_1516935 < baseStart_1516935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516951 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1516951 : Nat := 118140960795 + 1516951 * 2 ^ 59
def prefixEnd_1516951 : Nat := 4983230072969 + 3 ^ 40 * 1516951 * 2
def baseEnd_1516951 : Nat := 778924992318599655936175

theorem tailTrace_1516951 : CollatzResearch.WordTrace tailWord_1516951 prefixEnd_1516951 778924992318599655936175 := by
  unfold tailWord_1516951
  simp only [CollatzResearch.WordTrace]
  refine ⟨55327748327353076449926707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36885165551568717633284471 55327748327353076449926707)
  ·
    refine ⟨82991622491029614674890061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55327748327353076449926707 82991622491029614674890061)
    ·
      refine ⟨31121858434136105503083773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82991622491029614674890061 31121858434136105503083773)
      ·
        refine ⟨11670696912801039563656415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31121858434136105503083773 11670696912801039563656415)
        ·
          refine ⟨17506045369201559345484623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11670696912801039563656415 17506045369201559345484623)
          ·
            refine ⟨26259068053802339018226935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17506045369201559345484623 26259068053802339018226935)
            ·
              refine ⟨39388602080703508527340403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26259068053802339018226935 39388602080703508527340403)
              ·
                refine ⟨59082903121055262791010605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39388602080703508527340403 59082903121055262791010605)
                ·
                  refine ⟨22156088670395723546628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59082903121055262791010605 22156088670395723546628977)
                  ·
                    refine ⟨16617066502796792659971733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22156088670395723546628977 16617066502796792659971733)
                    ·
                      refine ⟨778924992318599655936175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16617066502796792659971733 778924992318599655936175)
                      ·
                        rfl

theorem cell23_1516951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1516951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516951 prefixEnd_1516951 := by exact prefixLift 1516951
  have htrace : WordTrace (prefixWord ++ tailWord_1516951) baseStart_1516951 baseEnd_1516951 := by
    simpa [prefixWord, tailWord_1516951, baseEnd_1516951] using wordTrace_append hprefix tailTrace_1516951
  have hstable : (prefixWord ++ tailWord_1516951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516951).length < 2 ^ (prefixWord ++ tailWord_1516951).sum := by decide
  have hdescent : baseEnd_1516951 < baseStart_1516951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516992 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 1, 1, 3]
def baseStart_1516992 : Nat := 118140960795 + 1516992 * 2 ^ 59
def prefixEnd_1516992 : Nat := 4983230072969 + 3 ^ 40 * 1516992 * 2
def baseEnd_1516992 : Nat := 778946045025433995523487

theorem tailTrace_1516992 : CollatzResearch.WordTrace tailWord_1516992 prefixEnd_1516992 778946045025433995523487 := by
  unfold tailWord_1516992
  simp only [CollatzResearch.WordTrace]
  refine ⟨27664621860102270226084615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36886162480136360301446153 27664621860102270226084615)
  ·
    refine ⟨41496932790153405339126923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27664621860102270226084615 41496932790153405339126923)
    ·
      refine ⟨62245399185230108008690385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41496932790153405339126923 62245399185230108008690385)
      ·
        refine ⟨46684049388922581006517789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62245399185230108008690385 46684049388922581006517789)
        ·
          refine ⟨17506518520845967877444171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46684049388922581006517789 17506518520845967877444171)
          ·
            refine ⟨26259777781268951816166257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17506518520845967877444171 26259777781268951816166257)
            ·
              refine ⟨19694833335951713862124693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26259777781268951816166257 19694833335951713862124693)
              ·
                refine ⟨923195312622736587287095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19694833335951713862124693 923195312622736587287095)
                ·
                  refine ⟨1384792968934104880930643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923195312622736587287095 1384792968934104880930643)
                  ·
                    refine ⟨2077189453401157321395965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384792968934104880930643 2077189453401157321395965)
                    ·
                      refine ⟨778946045025433995523487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077189453401157321395965 778946045025433995523487)
                      ·
                        rfl

theorem cell23_1516992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_1516992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1516992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1516992 prefixEnd_1516992 := by exact prefixLift 1516992
  have htrace : WordTrace (prefixWord ++ tailWord_1516992) baseStart_1516992 baseEnd_1516992 := by
    simpa [prefixWord, tailWord_1516992, baseEnd_1516992] using wordTrace_append hprefix tailTrace_1516992
  have hstable : (prefixWord ++ tailWord_1516992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516992).length < 2 ^ (prefixWord ++ tailWord_1516992).sum := by decide
  have hdescent : baseEnd_1516992 < baseStart_1516992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517032 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_1517032 : Nat := 118140960795 + 1517032 * 2 ^ 59
def prefixEnd_1517032 : Nat := 4983230072969 + 3 ^ 40 * 1517032 * 2
def baseEnd_1517032 : Nat := 778966584251613839023303

theorem tailTrace_1517032 : CollatzResearch.WordTrace tailWord_1517032 prefixEnd_1517032 778966584251613839023303 := by
  unfold tailWord_1517032
  simp only [CollatzResearch.WordTrace]
  refine ⟨27665351320029813641812675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36887135093373084855750233 27665351320029813641812675)
  ·
    refine ⟨41498026980044720462719013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27665351320029813641812675 41498026980044720462719013)
    ·
      refine ⟨7780880058758385086759815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41498026980044720462719013 7780880058758385086759815)
      ·
        refine ⟨11671320088137577630139723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780880058758385086759815 11671320088137577630139723)
        ·
          refine ⟨17506980132206366445209585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11671320088137577630139723 17506980132206366445209585)
          ·
            refine ⟨13130235099154774833907189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17506980132206366445209585 13130235099154774833907189)
            ·
              refine ⟨1230959540545760140678799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13130235099154774833907189 1230959540545760140678799)
              ·
                refine ⟨1846439310818640211018199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230959540545760140678799 1846439310818640211018199)
                ·
                  refine ⟨2769658966227960316527299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846439310818640211018199 2769658966227960316527299)
                  ·
                    refine ⟨4154488449341940474790949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2769658966227960316527299 4154488449341940474790949)
                    ·
                      refine ⟨778966584251613839023303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4154488449341940474790949 778966584251613839023303)
                      ·
                        rfl

theorem cell23_1517032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_1517032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517032 prefixEnd_1517032 := by exact prefixLift 1517032
  have htrace : WordTrace (prefixWord ++ tailWord_1517032) baseStart_1517032 baseEnd_1517032 := by
    simpa [prefixWord, tailWord_1517032, baseEnd_1517032] using wordTrace_append hprefix tailTrace_1517032
  have hstable : (prefixWord ++ tailWord_1517032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517032).length < 2 ^ (prefixWord ++ tailWord_1517032).sum := by decide
  have hdescent : baseEnd_1517032 < baseStart_1517032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517042 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_1517042 : Nat := 118140960795 + 1517042 * 2 ^ 59
def prefixEnd_1517042 : Nat := 4983230072969 + 3 ^ 40 * 1517042 * 2
def baseEnd_1517042 : Nat := 259657239686052933299419

theorem tailTrace_1517042 : CollatzResearch.WordTrace tailWord_1517042 prefixEnd_1517042 259657239686052933299419 := by
  unfold tailWord_1517042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13832766842505849747872345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36887378246682265994326253 13832766842505849747872345)
  ·
    refine ⟨10374575131879387310904259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13832766842505849747872345 10374575131879387310904259)
    ·
      refine ⟨15561862697819080966356389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10374575131879387310904259 15561862697819080966356389)
      ·
        refine ⟨2917849255841077681191823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15561862697819080966356389 2917849255841077681191823)
        ·
          refine ⟨4376773883761616521787735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917849255841077681191823 4376773883761616521787735)
          ·
            refine ⟨6565160825642424782681603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376773883761616521787735 6565160825642424782681603)
            ·
              refine ⟨9847741238463637174022405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565160825642424782681603 9847741238463637174022405)
              ·
                refine ⟨1846451482211931970129201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9847741238463637174022405 1846451482211931970129201)
                ·
                  refine ⟨1384838611658948977596901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846451482211931970129201 1384838611658948977596901)
                  ·
                    refine ⟨259657239686052933299419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1384838611658948977596901 259657239686052933299419)
                    ·
                      rfl

theorem cell23_1517042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_1517042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517042 prefixEnd_1517042 := by exact prefixLift 1517042
  have htrace : WordTrace (prefixWord ++ tailWord_1517042) baseStart_1517042 baseEnd_1517042 := by
    simpa [prefixWord, tailWord_1517042, baseEnd_1517042] using wordTrace_append hprefix tailTrace_1517042
  have hstable : (prefixWord ++ tailWord_1517042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517042).length < 2 ^ (prefixWord ++ tailWord_1517042).sum := by decide
  have hdescent : baseEnd_1517042 < baseStart_1517042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517065 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_1517065 : Nat := 118140960795 + 1517065 * 2 ^ 59
def prefixEnd_1517065 : Nat := 4983230072969 + 3 ^ 40 * 1517065 * 2
def baseEnd_1517065 : Nat := 778983529113212209910651

theorem tailTrace_1517065 : CollatzResearch.WordTrace tailWord_1517065 prefixEnd_1517065 778983529113212209910651 := by
  unfold tailWord_1517065
  simp only [CollatzResearch.WordTrace]
  refine ⟨55331906248940073919576649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36887937499293382613051099 55331906248940073919576649)
  ·
    refine ⟨41498929686705055439682487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55331906248940073919576649 41498929686705055439682487)
    ·
      refine ⟨62248394530057583159523731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41498929686705055439682487 62248394530057583159523731)
      ·
        refine ⟨93372591795086374739285597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62248394530057583159523731 93372591795086374739285597)
        ·
          refine ⟨35014721923157390527232099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93372591795086374739285597 35014721923157390527232099)
          ·
            refine ⟨52522082884736085790848149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35014721923157390527232099 52522082884736085790848149)
            ·
              refine ⟨2461972635222004021446007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52522082884736085790848149 2461972635222004021446007)
              ·
                refine ⟨3692958952833006032169011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461972635222004021446007 3692958952833006032169011)
                ·
                  refine ⟨5539438429249509048253517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692958952833006032169011 5539438429249509048253517)
                  ·
                    refine ⟨2077289410968565893095069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5539438429249509048253517 2077289410968565893095069)
                    ·
                      refine ⟨778983529113212209910651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077289410968565893095069 778983529113212209910651)
                      ·
                        rfl

theorem cell23_1517065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_1517065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517065 prefixEnd_1517065 := by exact prefixLift 1517065
  have htrace : WordTrace (prefixWord ++ tailWord_1517065) baseStart_1517065 baseEnd_1517065 := by
    simpa [prefixWord, tailWord_1517065, baseEnd_1517065] using wordTrace_append hprefix tailTrace_1517065
  have hstable : (prefixWord ++ tailWord_1517065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517065).length < 2 ^ (prefixWord ++ tailWord_1517065).sum := by decide
  have hdescent : baseEnd_1517065 < baseStart_1517065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517116 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_1517116 : Nat := 118140960795 + 1517116 * 2 ^ 59
def prefixEnd_1517116 : Nat := 4983230072969 + 3 ^ 40 * 1517116 * 2
def baseEnd_1517116 : Nat := 779009716626591510372917

theorem tailTrace_1517116 : CollatzResearch.WordTrace tailWord_1517116 prefixEnd_1517116 779009716626591510372917 := by
  unfold tailWord_1517116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27666883185877654814841601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36889177581170206419788801 27666883185877654814841601)
  ·
    refine ⟨20750162389408241111131201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27666883185877654814841601 20750162389408241111131201)
    ·
      refine ⟨15562621792056180833348401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20750162389408241111131201 15562621792056180833348401)
      ·
        refine ⟨11671966344042135625011301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15562621792056180833348401 11671966344042135625011301)
        ·
          refine ⟨2188493689507900429689619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11671966344042135625011301 2188493689507900429689619)
          ·
            refine ⟨3282740534261850644534429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188493689507900429689619 3282740534261850644534429)
            ·
              refine ⟨1231027700348193991700411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3282740534261850644534429 1231027700348193991700411)
              ·
                refine ⟨1846541550522290987550617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231027700348193991700411 1846541550522290987550617)
                ·
                  refine ⟨1384906162891718240662963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846541550522290987550617 1384906162891718240662963)
                  ·
                    refine ⟨2077359244337577360994445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1384906162891718240662963 2077359244337577360994445)
                    ·
                      refine ⟨779009716626591510372917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077359244337577360994445 779009716626591510372917)
                      ·
                        rfl

theorem cell23_1517116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_1517116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517116 prefixEnd_1517116 := by exact prefixLift 1517116
  have htrace : WordTrace (prefixWord ++ tailWord_1517116) baseStart_1517116 baseEnd_1517116 := by
    simpa [prefixWord, tailWord_1517116, baseEnd_1517116] using wordTrace_append hprefix tailTrace_1517116
  have hstable : (prefixWord ++ tailWord_1517116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517116).length < 2 ^ (prefixWord ++ tailWord_1517116).sum := by decide
  have hdescent : baseEnd_1517116 < baseStart_1517116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517162 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_1517162 : Nat := 118140960795 + 1517162 * 2 ^ 59
def prefixEnd_1517162 : Nat := 4983230072969 + 3 ^ 40 * 1517162 * 2
def baseEnd_1517162 : Nat := 86559259637410925599745

theorem tailTrace_1517162 : CollatzResearch.WordTrace tailWord_1517162 prefixEnd_1517162 86559259637410925599745 := by
  unfold tailWord_1517162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13833861032397164871464435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36890296086392439657238493 13833861032397164871464435)
  ·
    refine ⟨20750791548595747307196653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13833861032397164871464435 20750791548595747307196653)
    ·
      refine ⟨7781546830723405240198745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20750791548595747307196653 7781546830723405240198745)
      ·
        refine ⟨5836160123042553930149059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7781546830723405240198745 5836160123042553930149059)
        ·
          refine ⟨8754240184563830895223589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836160123042553930149059 8754240184563830895223589)
          ·
            refine ⟨1641420034605718292854423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8754240184563830895223589 1641420034605718292854423)
            ·
              refine ⟨2462130051908577439281635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641420034605718292854423 2462130051908577439281635)
              ·
                refine ⟨3693195077862866158922453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462130051908577439281635 3693195077862866158922453)
                ·
                  refine ⟨86559259637410925599745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3693195077862866158922453 86559259637410925599745)
                  ·
                    rfl

theorem cell23_1517162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_1517162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517162 prefixEnd_1517162 := by exact prefixLift 1517162
  have htrace : WordTrace (prefixWord ++ tailWord_1517162) baseStart_1517162 baseEnd_1517162 := by
    simpa [prefixWord, tailWord_1517162, baseEnd_1517162] using wordTrace_append hprefix tailTrace_1517162
  have hstable : (prefixWord ++ tailWord_1517162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517162).length < 2 ^ (prefixWord ++ tailWord_1517162).sum := by decide
  have hdescent : baseEnd_1517162 < baseStart_1517162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517173 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1517173 : Nat := 118140960795 + 1517173 * 2 ^ 59
def prefixEnd_1517173 : Nat := 4983230072969 + 3 ^ 40 * 1517173 * 2
def baseEnd_1517173 : Nat := 779038985023897787360155

theorem tailTrace_1517173 : CollatzResearch.WordTrace tailWord_1517173 prefixEnd_1517173 779038985023897787360155 := by
  unfold tailWord_1517173
  simp only [CollatzResearch.WordTrace]
  refine ⟨55335845332548808364508173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36890563555032538909672115 55335845332548808364508173)
  ·
    refine ⟨20750941999705803136690565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55335845332548808364508173 20750941999705803136690565)
    ·
      refine ⟨3890801624944838088129481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20750941999705803136690565 3890801624944838088129481)
      ·
        refine ⟨2918101218708628566097111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3890801624944838088129481 2918101218708628566097111)
        ·
          refine ⟨4377151828062942849145667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918101218708628566097111 4377151828062942849145667)
          ·
            refine ⟨6565727742094414273718501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377151828062942849145667 6565727742094414273718501)
            ·
              refine ⟨1231073951642702676322219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6565727742094414273718501 1231073951642702676322219)
              ·
                refine ⟨1846610927464054014483329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231073951642702676322219 1846610927464054014483329)
                ·
                  refine ⟨1384958195598040510862497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846610927464054014483329 1384958195598040510862497)
                  ·
                    refine ⟨1038718646698530383146873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1384958195598040510862497 1038718646698530383146873)
                    ·
                      refine ⟨779038985023897787360155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038718646698530383146873 779038985023897787360155)
                      ·
                        rfl

theorem cell23_1517173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1517173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517173 prefixEnd_1517173 := by exact prefixLift 1517173
  have htrace : WordTrace (prefixWord ++ tailWord_1517173) baseStart_1517173 baseEnd_1517173 := by
    simpa [prefixWord, tailWord_1517173, baseEnd_1517173] using wordTrace_append hprefix tailTrace_1517173
  have hstable : (prefixWord ++ tailWord_1517173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517173).length < 2 ^ (prefixWord ++ tailWord_1517173).sum := by decide
  have hdescent : baseEnd_1517173 < baseStart_1517173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517229 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_1517229 : Nat := 118140960795 + 1517229 * 2 ^ 59
def prefixEnd_1517229 : Nat := 4983230072969 + 3 ^ 40 * 1517229 * 2
def baseEnd_1517229 : Nat := 779067739940549568259897

theorem tailTrace_1517229 : CollatzResearch.WordTrace tailWord_1517229 prefixEnd_1517229 779067739940549568259897 := by
  unfold tailWord_1517229
  simp only [CollatzResearch.WordTrace]
  refine ⟨55337887820345929928546741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36891925213563953285697827 55337887820345929928546741)
  ·
    refine ⟨5187926983157430930801257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55337887820345929928546741 5187926983157430930801257)
    ·
      refine ⟨3890945237368073198100943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5187926983157430930801257 3890945237368073198100943)
      ·
        refine ⟨5836417856052109797151415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3890945237368073198100943 5836417856052109797151415)
        ·
          refine ⟨8754626784078164695727123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836417856052109797151415 8754626784078164695727123)
          ·
            refine ⟨13131940176117247043590685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8754626784078164695727123 13131940176117247043590685)
            ·
              refine ⟨4924477566043967641346507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13131940176117247043590685 4924477566043967641346507)
              ·
                refine ⟨7386716349065951462019761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924477566043967641346507 7386716349065951462019761)
                ·
                  refine ⟨5540037261799463596514821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7386716349065951462019761 5540037261799463596514821)
                  ·
                    refine ⟨1038756986587399424346529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5540037261799463596514821 1038756986587399424346529)
                    ·
                      refine ⟨779067739940549568259897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038756986587399424346529 779067739940549568259897)
                      ·
                        rfl

theorem cell23_1517229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_1517229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517229 prefixEnd_1517229 := by exact prefixLift 1517229
  have htrace : WordTrace (prefixWord ++ tailWord_1517229) baseStart_1517229 baseEnd_1517229 := by
    simpa [prefixWord, tailWord_1517229, baseEnd_1517229] using wordTrace_append hprefix tailTrace_1517229
  have hstable : (prefixWord ++ tailWord_1517229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517229).length < 2 ^ (prefixWord ++ tailWord_1517229).sum := by decide
  have hdescent : baseEnd_1517229 < baseStart_1517229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517235 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 6]
def baseStart_1517235 : Nat := 118140960795 + 1517235 * 2 ^ 59
def prefixEnd_1517235 : Nat := 4983230072969 + 3 ^ 40 * 1517235 * 2
def baseEnd_1517235 : Nat := 86563424536052949420541

theorem tailTrace_1517235 : CollatzResearch.WordTrace tailWord_1517235 prefixEnd_1517235 86563424536052949420541 := by
  unfold tailWord_1517235
  simp only [CollatzResearch.WordTrace]
  refine ⟨55338106658324192953265159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36892071105549461968843439 55338106658324192953265159)
  ·
    refine ⟨83007159987486289429897739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55338106658324192953265159 83007159987486289429897739)
    ·
      refine ⟨124510739981229434144846609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83007159987486289429897739 124510739981229434144846609)
      ·
        refine ⟨93383054985922075608634957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124510739981229434144846609 93383054985922075608634957)
        ·
          refine ⟨35018645619720778353238109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93383054985922075608634957 35018645619720778353238109)
          ·
            refine ⟨13131992107395291882464291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35018645619720778353238109 13131992107395291882464291)
            ·
              refine ⟨19697988161092937823696437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13131992107395291882464291 19697988161092937823696437)
              ·
                refine ⟨1846686390102462920971541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19697988161092937823696437 1846686390102462920971541)
                ·
                  refine ⟨86563424536052949420541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1846686390102462920971541 86563424536052949420541)
                  ·
                    rfl

theorem cell23_1517235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 6].length) (baseStart_1517235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517235 prefixEnd_1517235 := by exact prefixLift 1517235
  have htrace : WordTrace (prefixWord ++ tailWord_1517235) baseStart_1517235 baseEnd_1517235 := by
    simpa [prefixWord, tailWord_1517235, baseEnd_1517235] using wordTrace_append hprefix tailTrace_1517235
  have hstable : (prefixWord ++ tailWord_1517235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517235).length < 2 ^ (prefixWord ++ tailWord_1517235).sum := by decide
  have hdescent : baseEnd_1517235 < baseStart_1517235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517279 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 3]
def baseStart_1517279 : Nat := 118140960795 + 1517279 * 2 ^ 59
def prefixEnd_1517279 : Nat := 4983230072969 + 3 ^ 40 * 1517279 * 2
def baseEnd_1517279 : Nat := 779093413973274372634667

theorem tailTrace_1517279 : CollatzResearch.WordTrace tailWord_1517279 prefixEnd_1517279 779093413973274372634667 := by
  unfold tailWord_1517279
  simp only [CollatzResearch.WordTrace]
  refine ⟨55339711470164788467866891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36893140980109858978577927 55339711470164788467866891)
  ·
    refine ⟨83009567205247182701800337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55339711470164788467866891 83009567205247182701800337)
    ·
      refine ⟨62257175403935387026350253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83009567205247182701800337 62257175403935387026350253)
      ·
        refine ⟨23346440776475770134881345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62257175403935387026350253 23346440776475770134881345)
        ·
          refine ⟨17509830582356827601161009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23346440776475770134881345 17509830582356827601161009)
          ·
            refine ⟨13132372936767620700870757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17509830582356827601161009 13132372936767620700870757)
            ·
              refine ⟨2462319925643928881413267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13132372936767620700870757 2462319925643928881413267)
              ·
                refine ⟨3693479888465893322119901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462319925643928881413267 3693479888465893322119901)
                ·
                  refine ⟨1385054958174709995794963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3693479888465893322119901 1385054958174709995794963)
                  ·
                    refine ⟨2077582437262064993692445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385054958174709995794963 2077582437262064993692445)
                    ·
                      refine ⟨779093413973274372634667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077582437262064993692445 779093413973274372634667)
                      ·
                        rfl

theorem cell23_1517279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_1517279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517279 prefixEnd_1517279 := by exact prefixLift 1517279
  have htrace : WordTrace (prefixWord ++ tailWord_1517279) baseStart_1517279 baseEnd_1517279 := by
    simpa [prefixWord, tailWord_1517279, baseEnd_1517279] using wordTrace_append hprefix tailTrace_1517279
  have hstable : (prefixWord ++ tailWord_1517279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517279).length < 2 ^ (prefixWord ++ tailWord_1517279).sum := by decide
  have hdescent : baseEnd_1517279 < baseStart_1517279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517322 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1517322 : Nat := 118140960795 + 1517322 * 2 ^ 59
def prefixEnd_1517322 : Nat := 4983230072969 + 3 ^ 40 * 1517322 * 2
def baseEnd_1517322 : Nat := 779115493641417704396969

theorem tailTrace_1517322 : CollatzResearch.WordTrace tailWord_1517322 prefixEnd_1517322 779115493641417704396969 := by
  unfold tailWord_1517322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13835319952252251702920555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36894186539339337874454813 13835319952252251702920555)
  ·
    refine ⟨20752979928378377554380833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13835319952252251702920555 20752979928378377554380833)
    ·
      refine ⟨15564734946283783165785625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20752979928378377554380833 15564734946283783165785625)
      ·
        refine ⟨11673551209712837374339219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15564734946283783165785625 11673551209712837374339219)
        ·
          refine ⟨17510326814569256061508829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673551209712837374339219 17510326814569256061508829)
          ·
            refine ⟨6566372555463471023065811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17510326814569256061508829 6566372555463471023065811)
            ·
              refine ⟨9849558833195206534598717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566372555463471023065811 9849558833195206534598717)
              ·
                refine ⟨3693584562448202450474519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9849558833195206534598717 3693584562448202450474519)
                ·
                  refine ⟨5540376843672303675711779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693584562448202450474519 5540376843672303675711779)
                  ·
                    refine ⟨8310565265508455513567669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540376843672303675711779 8310565265508455513567669)
                    ·
                      refine ⟨779115493641417704396969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8310565265508455513567669 779115493641417704396969)
                      ·
                        rfl

theorem cell23_1517322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1517322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517322 prefixEnd_1517322 := by exact prefixLift 1517322
  have htrace : WordTrace (prefixWord ++ tailWord_1517322) baseStart_1517322 baseEnd_1517322 := by
    simpa [prefixWord, tailWord_1517322, baseEnd_1517322] using wordTrace_append hprefix tailTrace_1517322
  have hstable : (prefixWord ++ tailWord_1517322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517322).length < 2 ^ (prefixWord ++ tailWord_1517322).sum := by decide
  have hdescent : baseEnd_1517322 < baseStart_1517322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517336 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 3, 2, 2]
def baseStart_1517336 : Nat := 118140960795 + 1517336 * 2 ^ 59
def prefixEnd_1517336 : Nat := 4983230072969 + 3 ^ 40 * 1517336 * 2
def baseEnd_1517336 : Nat := 779122682370580649621905

theorem tailTrace_1517336 : CollatzResearch.WordTrace tailWord_1517336 prefixEnd_1517336 779122682370580649621905 := by
  unfold tailWord_1517336
  simp only [CollatzResearch.WordTrace]
  refine ⟨27670895215479143601345931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36894526953972191468461241 27670895215479143601345931)
  ·
    refine ⟨41506342823218715402018897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27670895215479143601345931 41506342823218715402018897)
    ·
      refine ⟨31129757117414036551514173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41506342823218715402018897 31129757117414036551514173)
      ·
        refine ⟨11673658919030263706817815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31129757117414036551514173 11673658919030263706817815)
        ·
          refine ⟨17510488378545395560226723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673658919030263706817815 17510488378545395560226723)
          ·
            refine ⟨26265732567818093340340085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17510488378545395560226723 26265732567818093340340085)
            ·
              refine ⟨2462412428232946250656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26265732567818093340340085 2462412428232946250656883)
              ·
                refine ⟨3693618642349419375985325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462412428232946250656883 3693618642349419375985325)
                ·
                  refine ⟨1385106990881032265994497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3693618642349419375985325 1385106990881032265994497)
                  ·
                    refine ⟨1038830243160774199495873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385106990881032265994497 1038830243160774199495873)
                    ·
                      refine ⟨779122682370580649621905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038830243160774199495873 779122682370580649621905)
                      ·
                        rfl

theorem cell23_1517336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_1517336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517336 prefixEnd_1517336 := by exact prefixLift 1517336
  have htrace : WordTrace (prefixWord ++ tailWord_1517336) baseStart_1517336 baseEnd_1517336 := by
    simpa [prefixWord, tailWord_1517336, baseEnd_1517336] using wordTrace_append hprefix tailTrace_1517336
  have hstable : (prefixWord ++ tailWord_1517336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517336).length < 2 ^ (prefixWord ++ tailWord_1517336).sum := by decide
  have hdescent : baseEnd_1517336 < baseStart_1517336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517356 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_1517356 : Nat := 118140960795 + 1517356 * 2 ^ 59
def prefixEnd_1517356 : Nat := 4983230072969 + 3 ^ 40 * 1517356 * 2
def baseEnd_1517356 : Nat := 779132951983670571371813

theorem tailTrace_1517356 : CollatzResearch.WordTrace tailWord_1517356 prefixEnd_1517356 779132951983670571371813 := by
  unfold tailWord_1517356
  simp only [CollatzResearch.WordTrace]
  refine ⟨27671259945442915309209961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36895013260590553745613281 27671259945442915309209961)
  ·
    refine ⟨20753444959082186481907471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27671259945442915309209961 20753444959082186481907471)
    ·
      refine ⟨31130167438623279722861207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20753444959082186481907471 31130167438623279722861207)
      ·
        refine ⟨46695251157934919584291811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31130167438623279722861207 46695251157934919584291811)
        ·
          refine ⟨70042876736902379376437717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46695251157934919584291811 70042876736902379376437717)
          ·
            refine ⟨1641629923521149516635259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70042876736902379376437717 1641629923521149516635259)
            ·
              refine ⟨2462444885281724274952889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641629923521149516635259 2462444885281724274952889)
              ·
                refine ⟨1846833663961293206214667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462444885281724274952889 1846833663961293206214667)
                ·
                  refine ⟨2770250495941939809322001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846833663961293206214667 2770250495941939809322001)
                  ·
                    refine ⟨2077687871956454856991501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2770250495941939809322001 2077687871956454856991501)
                    ·
                      refine ⟨779132951983670571371813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077687871956454856991501 779132951983670571371813)
                      ·
                        rfl

theorem cell23_1517356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_1517356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517356 prefixEnd_1517356 := by exact prefixLift 1517356
  have htrace : WordTrace (prefixWord ++ tailWord_1517356) baseStart_1517356 baseEnd_1517356 := by
    simpa [prefixWord, tailWord_1517356, baseEnd_1517356] using wordTrace_append hprefix tailTrace_1517356
  have hstable : (prefixWord ++ tailWord_1517356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517356).length < 2 ^ (prefixWord ++ tailWord_1517356).sum := by decide
  have hdescent : baseEnd_1517356 < baseStart_1517356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517366 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1517366 : Nat := 118140960795 + 1517366 * 2 ^ 59
def prefixEnd_1517366 : Nat := 4983230072969 + 3 ^ 40 * 1517366 * 2
def baseEnd_1517366 : Nat := 779138086790215532246767

theorem tailTrace_1517366 : CollatzResearch.WordTrace tailWord_1517366 prefixEnd_1517366 779138086790215532246767 := by
  unfold tailWord_1517366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458930288803100145392747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36895256413899734884189301 3458930288803100145392747)
  ·
    refine ⟨5188395433204650218089121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3458930288803100145392747 5188395433204650218089121)
    ·
      refine ⟨3891296574903487663566841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5188395433204650218089121 3891296574903487663566841)
      ·
        refine ⟨2918472431177615747675131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3891296574903487663566841 2918472431177615747675131)
        ·
          refine ⟨4377708646766423621512697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918472431177615747675131 4377708646766423621512697)
          ·
            refine ⟨3283281485074817716134523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377708646766423621512697 3283281485074817716134523)
            ·
              refine ⟨4924922227612226574201785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283281485074817716134523 4924922227612226574201785)
              ·
                refine ⟨3693691670709169930651339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924922227612226574201785 3693691670709169930651339)
                ·
                  refine ⟨5540537506063754895977009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693691670709169930651339 5540537506063754895977009)
                  ·
                    refine ⟨4155403129547816171982757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5540537506063754895977009 4155403129547816171982757)
                    ·
                      refine ⟨779138086790215532246767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4155403129547816171982757 779138086790215532246767)
                      ·
                        rfl

theorem cell23_1517366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1517366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517366 prefixEnd_1517366 := by exact prefixLift 1517366
  have htrace : WordTrace (prefixWord ++ tailWord_1517366) baseStart_1517366 baseEnd_1517366 := by
    simpa [prefixWord, tailWord_1517366, baseEnd_1517366] using wordTrace_append hprefix tailTrace_1517366
  have hstable : (prefixWord ++ tailWord_1517366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517366).length < 2 ^ (prefixWord ++ tailWord_1517366).sum := by decide
  have hdescent : baseEnd_1517366 < baseStart_1517366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517373 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1517373 : Nat := 118140960795 + 1517373 * 2 ^ 59
def prefixEnd_1517373 : Nat := 4983230072969 + 3 ^ 40 * 1517373 * 2
def baseEnd_1517373 : Nat := 779141681154797004859235

theorem tailTrace_1517373 : CollatzResearch.WordTrace tailWord_1517373 prefixEnd_1517373 779141681154797004859235 := by
  unfold tailWord_1517373
  simp only [CollatzResearch.WordTrace]
  refine ⟨55343139931824242521788773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36895426621216161681192515 55343139931824242521788773)
  ·
    refine ⟨10376838737217045472835395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55343139931824242521788773 10376838737217045472835395)
    ·
      refine ⟨15565258105825568209253093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10376838737217045472835395 15565258105825568209253093)
      ·
        refine ⟨2918485894842294039234955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15565258105825568209253093 2918485894842294039234955)
        ·
          refine ⟨4377728842263441058852433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918485894842294039234955 4377728842263441058852433)
          ·
            refine ⟨3283296631697580794139325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4377728842263441058852433 3283296631697580794139325)
            ·
              refine ⟨1231236236886592797802247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3283296631697580794139325 1231236236886592797802247)
              ·
                refine ⟨1846854355329889196703371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231236236886592797802247 1846854355329889196703371)
                ·
                  refine ⟨2770281532994833795055057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846854355329889196703371 2770281532994833795055057)
                  ·
                    refine ⟨2077711149746125346291293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2770281532994833795055057 2077711149746125346291293)
                    ·
                      refine ⟨779141681154797004859235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077711149746125346291293 779141681154797004859235)
                      ·
                        rfl

theorem cell23_1517373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1517373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517373 prefixEnd_1517373 := by exact prefixLift 1517373
  have htrace : WordTrace (prefixWord ++ tailWord_1517373) baseStart_1517373 baseEnd_1517373 := by
    simpa [prefixWord, tailWord_1517373, baseEnd_1517373] using wordTrace_append hprefix tailTrace_1517373
  have hstable : (prefixWord ++ tailWord_1517373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517373).length < 2 ^ (prefixWord ++ tailWord_1517373).sum := by decide
  have hdescent : baseEnd_1517373 < baseStart_1517373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517386 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_1517386 : Nat := 118140960795 + 1517386 * 2 ^ 59
def prefixEnd_1517386 : Nat := 4983230072969 + 3 ^ 40 * 1517386 * 2
def baseEnd_1517386 : Nat := 779148356403305453996675

theorem tailTrace_1517386 : CollatzResearch.WordTrace tailWord_1517386 prefixEnd_1517386 779148356403305453996675 := by
  unfold tailWord_1517386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13835903520194286435503003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36895742720518097161341341 13835903520194286435503003)
  ·
    refine ⟨20753855280291429653254505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13835903520194286435503003 20753855280291429653254505)
    ·
      refine ⟨15565391460218572239940879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20753855280291429653254505 15565391460218572239940879)
      ·
        refine ⟨23348087190327858359911319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15565391460218572239940879 23348087190327858359911319)
        ·
          refine ⟨35022130785491787539866979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23348087190327858359911319 35022130785491787539866979)
          ·
            refine ⟨52533196178237681309800469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35022130785491787539866979 52533196178237681309800469)
            ·
              refine ⟨2462493570854891311396897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52533196178237681309800469 2462493570854891311396897)
              ·
                refine ⟨1846870178141168483547673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462493570854891311396897 1846870178141168483547673)
                ·
                  refine ⟨1385152633605876362660755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846870178141168483547673 1385152633605876362660755)
                  ·
                    refine ⟨2077728950408814543991133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385152633605876362660755 2077728950408814543991133)
                    ·
                      refine ⟨779148356403305453996675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077728950408814543991133 779148356403305453996675)
                      ·
                        rfl

theorem cell23_1517386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_1517386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517386 prefixEnd_1517386 := by exact prefixLift 1517386
  have htrace : WordTrace (prefixWord ++ tailWord_1517386) baseStart_1517386 baseEnd_1517386 := by
    simpa [prefixWord, tailWord_1517386, baseEnd_1517386] using wordTrace_append hprefix tailTrace_1517386
  have hstable : (prefixWord ++ tailWord_1517386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517386).length < 2 ^ (prefixWord ++ tailWord_1517386).sum := by decide
  have hdescent : baseEnd_1517386 < baseStart_1517386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517389 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1517389 : Nat := 118140960795 + 1517389 * 2 ^ 59
def prefixEnd_1517389 : Nat := 4983230072969 + 3 ^ 40 * 1517389 * 2
def baseEnd_1517389 : Nat := 259716632281756314086387

theorem tailTrace_1517389 : CollatzResearch.WordTrace tailWord_1517389 prefixEnd_1517389 259716632281756314086387 := by
  unfold tailWord_1517389
  simp only [CollatzResearch.WordTrace]
  refine ⟨55343723499766277254371221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36895815666510851502914147 55343723499766277254371221)
  ·
    refine ⟨2594237039051544246298651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55343723499766277254371221 2594237039051544246298651)
    ·
      refine ⟨3891355558577316369447977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594237039051544246298651 3891355558577316369447977)
      ·
        refine ⟨2918516668932987277085983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3891355558577316369447977 2918516668932987277085983)
        ·
          refine ⟨4377775003399480915628975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918516668932987277085983 4377775003399480915628975)
          ·
            refine ⟨6566662505099221373443463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377775003399480915628975 6566662505099221373443463)
            ·
              refine ⟨9849993757648832060165195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566662505099221373443463 9849993757648832060165195)
              ·
                refine ⟨14774990636473248090247793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9849993757648832060165195 14774990636473248090247793)
                ·
                  refine ⟨11081242977354936067685845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14774990636473248090247793 11081242977354936067685845)
                  ·
                    refine ⟨259716632281756314086387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11081242977354936067685845 259716632281756314086387)
                    ·
                      rfl

theorem cell23_1517389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1517389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517389 prefixEnd_1517389 := by exact prefixLift 1517389
  have htrace : WordTrace (prefixWord ++ tailWord_1517389) baseStart_1517389 baseEnd_1517389 := by
    simpa [prefixWord, tailWord_1517389, baseEnd_1517389] using wordTrace_append hprefix tailTrace_1517389
  have hstable : (prefixWord ++ tailWord_1517389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517389).length < 2 ^ (prefixWord ++ tailWord_1517389).sum := by decide
  have hdescent : baseEnd_1517389 < baseStart_1517389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517396 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_1517396 : Nat := 118140960795 + 1517396 * 2 ^ 59
def prefixEnd_1517396 : Nat := 4983230072969 + 3 ^ 40 * 1517396 * 2
def baseEnd_1517396 : Nat := 779153491209850414871629

theorem tailTrace_1517396 : CollatzResearch.WordTrace tailWord_1517396 prefixEnd_1517396 779153491209850414871629 := by
  unfold tailWord_1517396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27671989405370458724938021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36895985873827278299917361 27671989405370458724938021)
  ·
    refine ⟨5188498013506961010925879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27671989405370458724938021 5188498013506961010925879)
    ·
      refine ⟨7782747020260441516388819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5188498013506961010925879 7782747020260441516388819)
      ·
        refine ⟨11674120530390662274583229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7782747020260441516388819 11674120530390662274583229)
        ·
          refine ⟨4377795198896498352968711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11674120530390662274583229 4377795198896498352968711)
          ·
            refine ⟨6566692798344747529453067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377795198896498352968711 6566692798344747529453067)
            ·
              refine ⟨9850039197517121294179601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566692798344747529453067 9850039197517121294179601)
              ·
                refine ⟨7387529398137840970634701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9850039197517121294179601 7387529398137840970634701)
                ·
                  refine ⟨2770323524301690363988013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7387529398137840970634701 2770323524301690363988013)
                  ·
                    refine ⟨1038871321613133886495505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2770323524301690363988013 1038871321613133886495505)
                    ·
                      refine ⟨779153491209850414871629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038871321613133886495505 779153491209850414871629)
                      ·
                        rfl

theorem cell23_1517396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_1517396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517396 prefixEnd_1517396 := by exact prefixLift 1517396
  have htrace : WordTrace (prefixWord ++ tailWord_1517396) baseStart_1517396 baseEnd_1517396 := by
    simpa [prefixWord, tailWord_1517396, baseEnd_1517396] using wordTrace_append hprefix tailTrace_1517396
  have hstable : (prefixWord ++ tailWord_1517396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517396).length < 2 ^ (prefixWord ++ tailWord_1517396).sum := by decide
  have hdescent : baseEnd_1517396 < baseStart_1517396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517402 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_1517402 : Nat := 118140960795 + 1517402 * 2 ^ 59
def prefixEnd_1517402 : Nat := 4983230072969 + 3 ^ 40 * 1517402 * 2
def baseEnd_1517402 : Nat := 259718857364592463798867

theorem tailTrace_1517402 : CollatzResearch.WordTrace tailWord_1517402 prefixEnd_1517402 259718857364592463798867 := by
  unfold tailWord_1517402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13836049412179795118648615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36896131765812786983062973 13836049412179795118648615)
  ·
    refine ⟨20754074118269692677972923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13836049412179795118648615 20754074118269692677972923)
    ·
      refine ⟨31131111177404539016959385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20754074118269692677972923 31131111177404539016959385)
      ·
        refine ⟨23348333383053404262719539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31131111177404539016959385 23348333383053404262719539)
        ·
          refine ⟨35022500074580106394079309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23348333383053404262719539 35022500074580106394079309)
          ·
            refine ⟨13133437527967539897779741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35022500074580106394079309 13133437527967539897779741)
            ·
              refine ⟨4925039072987827461667403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13133437527967539897779741 4925039072987827461667403)
              ·
                refine ⟨7387558609481741192501105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925039072987827461667403 7387558609481741192501105)
                ·
                  refine ⟨5540668957111305894375829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7387558609481741192501105 5540668957111305894375829)
                  ·
                    refine ⟨259718857364592463798867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5540668957111305894375829 259718857364592463798867)
                    ·
                      rfl

theorem cell23_1517402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_1517402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517402 prefixEnd_1517402 := by exact prefixLift 1517402
  have htrace : WordTrace (prefixWord ++ tailWord_1517402) baseStart_1517402 baseEnd_1517402 := by
    simpa [prefixWord, tailWord_1517402, baseEnd_1517402] using wordTrace_append hprefix tailTrace_1517402
  have hstable : (prefixWord ++ tailWord_1517402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517402).length < 2 ^ (prefixWord ++ tailWord_1517402).sum := by decide
  have hdescent : baseEnd_1517402 < baseStart_1517402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517426 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_1517426 : Nat := 118140960795 + 1517426 * 2 ^ 59
def prefixEnd_1517426 : Nat := 4983230072969 + 3 ^ 40 * 1517426 * 2
def baseEnd_1517426 : Nat := 779168895629485297496491

theorem tailTrace_1517426 : CollatzResearch.WordTrace tailWord_1517426 prefixEnd_1517426 779168895629485297496491 := by
  unfold tailWord_1517426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13836268250158058143367033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36896715333754821715645421 13836268250158058143367033)
  ·
    refine ⟨10377201187618543607525275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13836268250158058143367033 10377201187618543607525275)
    ·
      refine ⟨15565801781427815411287913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10377201187618543607525275 15565801781427815411287913)
      ·
        refine ⟨11674351336070861558465935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15565801781427815411287913 11674351336070861558465935)
        ·
          refine ⟨17511527004106292337698903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11674351336070861558465935 17511527004106292337698903)
          ·
            refine ⟨26267290506159438506548355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17511527004106292337698903 26267290506159438506548355)
            ·
              refine ⟨39400935759239157759822533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26267290506159438506548355 39400935759239157759822533)
              ·
                refine ⟨7387675454857342079966725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39400935759239157759822533 7387675454857342079966725)
                ·
                  refine ⟨1385189147785751639993761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7387675454857342079966725 1385189147785751639993761)
                  ·
                    refine ⟨1038891860839313729995321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385189147785751639993761 1038891860839313729995321)
                    ·
                      refine ⟨779168895629485297496491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038891860839313729995321 779168895629485297496491)
                      ·
                        rfl

theorem cell23_1517426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_1517426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517426 prefixEnd_1517426 := by exact prefixLift 1517426
  have htrace : WordTrace (prefixWord ++ tailWord_1517426) baseStart_1517426 baseEnd_1517426 := by
    simpa [prefixWord, tailWord_1517426, baseEnd_1517426] using wordTrace_append hprefix tailTrace_1517426
  have hstable : (prefixWord ++ tailWord_1517426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517426).length < 2 ^ (prefixWord ++ tailWord_1517426).sum := by decide
  have hdescent : baseEnd_1517426 < baseStart_1517426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517430 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1517430 : Nat := 118140960795 + 1517430 * 2 ^ 59
def prefixEnd_1517430 : Nat := 4983230072969 + 3 ^ 40 * 1517430 * 2
def baseEnd_1517430 : Nat := 779170949552103281846473

theorem tailTrace_1517430 : CollatzResearch.WordTrace tailWord_1517430 prefixEnd_1517430 779170949552103281846473 := by
  unfold tailWord_1517430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459076180788608828538359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36896812595078494171075829 3459076180788608828538359)
  ·
    refine ⟨5188614271182913242807539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3459076180788608828538359 5188614271182913242807539)
    ·
      refine ⟨7782921406774369864211309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5188614271182913242807539 7782921406774369864211309)
      ·
        refine ⟨2918595527540388699079241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7782921406774369864211309 2918595527540388699079241)
        ·
          refine ⟨2188946645655291524309431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2918595527540388699079241 2188946645655291524309431)
          ·
            refine ⟨3283419968482937286464147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188946645655291524309431 3283419968482937286464147)
            ·
              refine ⟨4925129952724405929696221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283419968482937286464147 4925129952724405929696221)
              ·
                refine ⟨1846923732271652223636083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4925129952724405929696221 1846923732271652223636083)
                ·
                  refine ⟨2770385598407478335454125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846923732271652223636083 2770385598407478335454125)
                  ·
                    refine ⟨1038894599402804375795297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2770385598407478335454125 1038894599402804375795297)
                    ·
                      refine ⟨779170949552103281846473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038894599402804375795297 779170949552103281846473)
                      ·
                        rfl

theorem cell23_1517430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1517430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517430 prefixEnd_1517430 := by exact prefixLift 1517430
  have htrace : WordTrace (prefixWord ++ tailWord_1517430) baseStart_1517430 baseEnd_1517430 := by
    simpa [prefixWord, tailWord_1517430, baseEnd_1517430] using wordTrace_append hprefix tailTrace_1517430
  have hstable : (prefixWord ++ tailWord_1517430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517430).length < 2 ^ (prefixWord ++ tailWord_1517430).sum := by decide
  have hdescent : baseEnd_1517430 < baseStart_1517430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517443 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 2, 2, 2]
def baseStart_1517443 : Nat := 118140960795 + 1517443 * 2 ^ 59
def prefixEnd_1517443 : Nat := 4983230072969 + 3 ^ 40 * 1517443 * 2
def baseEnd_1517443 : Nat := 779177624800611730983913

theorem tailTrace_1517443 : CollatzResearch.WordTrace tailWord_1517443 prefixEnd_1517443 779177624800611730983913 := by
  unfold tailWord_1517443
  simp only [CollatzResearch.WordTrace]
  refine ⟨55345693041570644476836983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36897128694380429651224655 55345693041570644476836983)
  ·
    refine ⟨83018539562355966715255475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55345693041570644476836983 83018539562355966715255475)
    ·
      refine ⟨124527809343533950072883213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83018539562355966715255475 124527809343533950072883213)
      ·
        refine ⟨46697928503825231277331205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124527809343533950072883213 46697928503825231277331205)
        ·
          refine ⟨8755861594467230864499601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46697928503825231277331205 8755861594467230864499601)
          ·
            refine ⟨6566896195850423148374701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8755861594467230864499601 6566896195850423148374701)
            ·
              refine ⟨2462586073443908680640513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6566896195850423148374701 2462586073443908680640513)
              ·
                refine ⟨1846939555082931510480385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462586073443908680640513 1846939555082931510480385)
                ·
                  refine ⟨1385204666312198632860289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846939555082931510480385 1385204666312198632860289)
                  ·
                    refine ⟨1038903499734148974645217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385204666312198632860289 1038903499734148974645217)
                    ·
                      refine ⟨779177624800611730983913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038903499734148974645217 779177624800611730983913)
                      ·
                        rfl

theorem cell23_1517443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_1517443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517443 prefixEnd_1517443 := by exact prefixLift 1517443
  have htrace : WordTrace (prefixWord ++ tailWord_1517443) baseStart_1517443 baseEnd_1517443 := by
    simpa [prefixWord, tailWord_1517443, baseEnd_1517443] using wordTrace_append hprefix tailTrace_1517443
  have hstable : (prefixWord ++ tailWord_1517443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517443).length < 2 ^ (prefixWord ++ tailWord_1517443).sum := by decide
  have hdescent : baseEnd_1517443 < baseStart_1517443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517449 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 5]
def baseStart_1517449 : Nat := 118140960795 + 1517449 * 2 ^ 59
def prefixEnd_1517449 : Nat := 4983230072969 + 3 ^ 40 * 1517449 * 2
def baseEnd_1517449 : Nat := 86575633964948745278765

theorem tailTrace_1517449 : CollatzResearch.WordTrace tailWord_1517449 prefixEnd_1517449 86575633964948745278765 := by
  unfold tailWord_1517449
  simp only [CollatzResearch.WordTrace]
  refine ⟨55345911879548907501555401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36897274586365938334370267 55345911879548907501555401)
  ·
    refine ⟨41509433909661680626166551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55345911879548907501555401 41509433909661680626166551)
    ·
      refine ⟨62264150864492520939249827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41509433909661680626166551 62264150864492520939249827)
      ·
        refine ⟨93396226296738781408874741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62264150864492520939249827 93396226296738781408874741)
        ·
          refine ⟨8755896215319260757082007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93396226296738781408874741 8755896215319260757082007)
          ·
            refine ⟨13133844322978891135623011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8755896215319260757082007 13133844322978891135623011)
            ·
              refine ⟨19700766484468336703434517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13133844322978891135623011 19700766484468336703434517)
              ·
                refine ⟨923473428959453282973493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19700766484468336703434517 923473428959453282973493)
                ·
                  refine ⟨86575633964948745278765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923473428959453282973493 86575633964948745278765)
                  ·
                    rfl

theorem cell23_1517449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 5].length) (baseStart_1517449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517449 prefixEnd_1517449 := by exact prefixLift 1517449
  have htrace : WordTrace (prefixWord ++ tailWord_1517449) baseStart_1517449 baseEnd_1517449 := by
    simpa [prefixWord, tailWord_1517449, baseEnd_1517449] using wordTrace_append hprefix tailTrace_1517449
  have hstable : (prefixWord ++ tailWord_1517449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517449).length < 2 ^ (prefixWord ++ tailWord_1517449).sum := by decide
  have hdescent : baseEnd_1517449 < baseStart_1517449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517472 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1517472 : Nat := 118140960795 + 1517472 * 2 ^ 59
def prefixEnd_1517472 : Nat := 4983230072969 + 3 ^ 40 * 1517472 * 2
def baseEnd_1517472 : Nat := 779192515739592117521279

theorem tailTrace_1517472 : CollatzResearch.WordTrace tailWord_1517472 prefixEnd_1517472 779192515739592117521279 := by
  unfold tailWord_1517472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673375379232791214821335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36897833838977054953095113 27673375379232791214821335)
  ·
    refine ⟨41510063068849186822232003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27673375379232791214821335 41510063068849186822232003)
    ·
      refine ⟨62265094603273780233348005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510063068849186822232003 62265094603273780233348005)
      ·
        refine ⟨11674705238113833793752751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62265094603273780233348005 11674705238113833793752751)
        ·
          refine ⟨17512057857170750690629127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11674705238113833793752751 17512057857170750690629127)
          ·
            refine ⟨26268086785756126035943691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17512057857170750690629127 26268086785756126035943691)
            ·
              refine ⟨39402130178634189053915537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26268086785756126035943691 39402130178634189053915537)
              ·
                refine ⟨29551597633975641790436653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39402130178634189053915537 29551597633975641790436653)
                ·
                  refine ⟨11081849112740865671413745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29551597633975641790436653 11081849112740865671413745)
                  ·
                    refine ⟨8311386834555649253560309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11081849112740865671413745 8311386834555649253560309)
                    ·
                      refine ⟨779192515739592117521279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8311386834555649253560309 779192515739592117521279)
                      ·
                        rfl

theorem cell23_1517472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1517472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517472 prefixEnd_1517472 := by exact prefixLift 1517472
  have htrace : WordTrace (prefixWord ++ tailWord_1517472) baseStart_1517472 baseEnd_1517472 := by
    simpa [prefixWord, tailWord_1517472, baseEnd_1517472] using wordTrace_append hprefix tailTrace_1517472
  have hstable : (prefixWord ++ tailWord_1517472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517472).length < 2 ^ (prefixWord ++ tailWord_1517472).sum := by decide
  have hdescent : baseEnd_1517472 < baseStart_1517472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517479 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1517479 : Nat := 118140960795 + 1517479 * 2 ^ 59
def prefixEnd_1517479 : Nat := 4983230072969 + 3 ^ 40 * 1517479 * 2
def baseEnd_1517479 : Nat := 259732036701391196711249

theorem tailTrace_1517479 : CollatzResearch.WordTrace tailWord_1517479 prefixEnd_1517479 259732036701391196711249 := by
  unfold tailWord_1517479
  simp only [CollatzResearch.WordTrace]
  refine ⟨55347006069440222625147491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36898004046293481750098327 55347006069440222625147491)
  ·
    refine ⟨83020509104160333937721237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55347006069440222625147491 83020509104160333937721237)
    ·
      refine ⟨3891586364257515653330683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83020509104160333937721237 3891586364257515653330683)
      ·
        refine ⟨5837379546386273479996025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891586364257515653330683 5837379546386273479996025)
        ·
          refine ⟨4378034659789705109997019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5837379546386273479996025 4378034659789705109997019)
          ·
            refine ⟨6567051989684557664995529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378034659789705109997019 6567051989684557664995529)
            ·
              refine ⟨4925288992263418248746647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6567051989684557664995529 4925288992263418248746647)
              ·
                refine ⟨7387933488395127373119971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925288992263418248746647 7387933488395127373119971)
                ·
                  refine ⟨11081900232592691059679957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387933488395127373119971 11081900232592691059679957)
                  ·
                    refine ⟨259732036701391196711249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11081900232592691059679957 259732036701391196711249)
                    ·
                      rfl

theorem cell23_1517479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1517479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517479 prefixEnd_1517479 := by exact prefixLift 1517479
  have htrace : WordTrace (prefixWord ++ tailWord_1517479) baseStart_1517479 baseEnd_1517479 := by
    simpa [prefixWord, tailWord_1517479, baseEnd_1517479] using wordTrace_append hprefix tailTrace_1517479
  have hstable : (prefixWord ++ tailWord_1517479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517479).length < 2 ^ (prefixWord ++ tailWord_1517479).sum := by decide
  have hdescent : baseEnd_1517479 < baseStart_1517479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517500 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 5]
def baseStart_1517500 : Nat := 118140960795 + 1517500 * 2 ^ 59
def prefixEnd_1517500 : Nat := 4983230072969 + 3 ^ 40 * 1517500 * 2
def baseEnd_1517500 : Nat := 86578543688657556441239

theorem tailTrace_1517500 : CollatzResearch.WordTrace tailWord_1517500 prefixEnd_1517500 86578543688657556441239 := by
  unfold tailWord_1517500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673886001182071605830977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36898514668242762141107969 27673886001182071605830977)
  ·
    refine ⟨20755414500886553704373233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27673886001182071605830977 20755414500886553704373233)
    ·
      refine ⟨15566560875664915278279925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20755414500886553704373233 15566560875664915278279925)
      ·
        refine ⟨1459365082093585807338743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15566560875664915278279925 1459365082093585807338743)
        ·
          refine ⟨2189047623140378711008115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459365082093585807338743 2189047623140378711008115)
          ·
            refine ⟨3283571434710568066512173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189047623140378711008115 3283571434710568066512173)
            ·
              refine ⟨1231339288016463024942065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3283571434710568066512173 1231339288016463024942065)
              ·
                refine ⟨923504466012347268706549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231339288016463024942065 923504466012347268706549)
                ·
                  refine ⟨86578543688657556441239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923504466012347268706549 86578543688657556441239)
                  ·
                    rfl

theorem cell23_1517500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_1517500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517500 prefixEnd_1517500 := by exact prefixLift 1517500
  have htrace : WordTrace (prefixWord ++ tailWord_1517500) baseStart_1517500 baseEnd_1517500 := by
    simpa [prefixWord, tailWord_1517500, baseEnd_1517500] using wordTrace_append hprefix tailTrace_1517500
  have hstable : (prefixWord ++ tailWord_1517500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517500).length < 2 ^ (prefixWord ++ tailWord_1517500).sum := by decide
  have hdescent : baseEnd_1517500 < baseStart_1517500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517509 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_1517509 : Nat := 118140960795 + 1517509 * 2 ^ 59
def prefixEnd_1517509 : Nat := 4983230072969 + 3 ^ 40 * 1517509 * 2
def baseEnd_1517509 : Nat := 259737171507936157586203

theorem tailTrace_1517509 : CollatzResearch.WordTrace tailWord_1517509 prefixEnd_1517509 259737171507936157586203 := by
  unfold tailWord_1517509
  simp only [CollatzResearch.WordTrace]
  refine ⟨55348100259331537748739581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36898733506221025165826387 55348100259331537748739581)
  ·
    refine ⟨20755537597249326655777343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55348100259331537748739581 20755537597249326655777343)
    ·
      refine ⟨31133306395873989983666015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20755537597249326655777343 31133306395873989983666015)
      ·
        refine ⟨46699959593810984975499023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31133306395873989983666015 46699959593810984975499023)
        ·
          refine ⟨70049939390716477463248535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46699959593810984975499023 70049939390716477463248535)
          ·
            refine ⟨105074909086074716194872803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70049939390716477463248535 105074909086074716194872803)
            ·
              refine ⟨157612363629112074292309205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105074909086074716194872803 157612363629112074292309205)
              ·
                refine ⟨3694039772557314241225997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157612363629112074292309205 3694039772557314241225997)
                ·
                  refine ⟨1385264914708992840459749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3694039772557314241225997 1385264914708992840459749)
                  ·
                    refine ⟨259737171507936157586203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385264914708992840459749 259737171507936157586203)
                    ·
                      rfl

theorem cell23_1517509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_1517509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517509 prefixEnd_1517509 := by exact prefixLift 1517509
  have htrace : WordTrace (prefixWord ++ tailWord_1517509) baseStart_1517509 baseEnd_1517509 := by
    simpa [prefixWord, tailWord_1517509, baseEnd_1517509] using wordTrace_append hprefix tailTrace_1517509
  have hstable : (prefixWord ++ tailWord_1517509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517509).length < 2 ^ (prefixWord ++ tailWord_1517509).sum := by decide
  have hdescent : baseEnd_1517509 < baseStart_1517509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517519 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_1517519 : Nat := 118140960795 + 1517519 * 2 ^ 59
def prefixEnd_1517519 : Nat := 4983230072969 + 3 ^ 40 * 1517519 * 2
def baseEnd_1517519 : Nat := 779216649330353433633563

theorem tailTrace_1517519 : CollatzResearch.WordTrace tailWord_1517519 prefixEnd_1517519 779216649330353433633563 := by
  unfold tailWord_1517519
  simp only [CollatzResearch.WordTrace]
  refine ⟨55348464989295309456603611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36898976659530206304402407 55348464989295309456603611)
  ·
    refine ⟨83022697483942964184905417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55348464989295309456603611 83022697483942964184905417)
    ·
      refine ⟨62267023112957223138679063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83022697483942964184905417 62267023112957223138679063)
      ·
        refine ⟨93400534669435834708018595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62267023112957223138679063 93400534669435834708018595)
        ·
          refine ⟨140100802004153752062027893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93400534669435834708018595 140100802004153752062027893)
          ·
            refine ⟨13134450187889414255815115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140100802004153752062027893 13134450187889414255815115)
            ·
              refine ⟨19701675281834121383722673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134450187889414255815115 19701675281834121383722673)
              ·
                refine ⟨14776256461375591037792005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19701675281834121383722673 14776256461375591037792005)
                ·
                  refine ⟨2770548086507923319586001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14776256461375591037792005 2770548086507923319586001)
                  ·
                    refine ⟨2077911064880942489689501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2770548086507923319586001 2077911064880942489689501)
                    ·
                      refine ⟨779216649330353433633563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2077911064880942489689501 779216649330353433633563)
                      ·
                        rfl

theorem cell23_1517519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_1517519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517519 prefixEnd_1517519 := by exact prefixLift 1517519
  have htrace : WordTrace (prefixWord ++ tailWord_1517519) baseStart_1517519 baseEnd_1517519 := by
    simpa [prefixWord, tailWord_1517519, baseEnd_1517519] using wordTrace_append hprefix tailTrace_1517519
  have hstable : (prefixWord ++ tailWord_1517519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517519).length < 2 ^ (prefixWord ++ tailWord_1517519).sum := by decide
  have hdescent : baseEnd_1517519 < baseStart_1517519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517533 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1517533 : Nat := 118140960795 + 1517533 * 2 ^ 59
def prefixEnd_1517533 : Nat := 4983230072969 + 3 ^ 40 * 1517533 * 2
def baseEnd_1517533 : Nat := 779223838059516378858499

theorem tailTrace_1517533 : CollatzResearch.WordTrace tailWord_1517533 prefixEnd_1517533 779223838059516378858499 := by
  unfold tailWord_1517533
  simp only [CollatzResearch.WordTrace]
  refine ⟨55348975611244589847613253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36899317074163059898408835 55348975611244589847613253)
  ·
    refine ⟨10377932927108360596427485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55348975611244589847613253 10377932927108360596427485)
    ·
      refine ⟨3891724847665635223660307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10377932927108360596427485 3891724847665635223660307)
      ·
        refine ⟨5837587271498452835490461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891724847665635223660307 5837587271498452835490461)
        ·
          refine ⟨2189095226811919813308923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5837587271498452835490461 2189095226811919813308923)
          ·
            refine ⟨3283642840217879719963385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189095226811919813308923 3283642840217879719963385)
            ·
              refine ⟨2462732130163409789972539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283642840217879719963385 2462732130163409789972539)
              ·
                refine ⟨3694098195245114684958809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462732130163409789972539 3694098195245114684958809)
                ·
                  refine ⟨2770573646433836013719107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694098195245114684958809 2770573646433836013719107)
                  ·
                    refine ⟨4155860469650754020578661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2770573646433836013719107 4155860469650754020578661)
                    ·
                      refine ⟨779223838059516378858499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4155860469650754020578661 779223838059516378858499)
                      ·
                        rfl

theorem cell23_1517533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1517533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517533 prefixEnd_1517533 := by exact prefixLift 1517533
  have htrace : WordTrace (prefixWord ++ tailWord_1517533) baseStart_1517533 baseEnd_1517533 := by
    simpa [prefixWord, tailWord_1517533, baseEnd_1517533] using wordTrace_append hprefix tailTrace_1517533
  have hstable : (prefixWord ++ tailWord_1517533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517533).length < 2 ^ (prefixWord ++ tailWord_1517533).sum := by decide
  have hdescent : baseEnd_1517533 < baseStart_1517533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517569 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1517569 : Nat := 118140960795 + 1517569 * 2 ^ 59
def prefixEnd_1517569 : Nat := 4983230072969 + 3 ^ 40 * 1517569 * 2
def baseEnd_1517569 : Nat := 259747441121026079336111

theorem tailTrace_1517569 : CollatzResearch.WordTrace tailWord_1517569 prefixEnd_1517569 259747441121026079336111 := by
  unfold tailWord_1517569
  simp only [CollatzResearch.WordTrace]
  refine ⟨55350288639114167995923761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36900192426076111997282507 55350288639114167995923761)
  ·
    refine ⟨41512716479335625996942821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55350288639114167995923761 41512716479335625996942821)
    ·
      refine ⟨7783634339875429874426779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41512716479335625996942821 7783634339875429874426779)
      ·
        refine ⟨11675451509813144811640169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7783634339875429874426779 11675451509813144811640169)
        ·
          refine ⟨8756588632359858608730127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11675451509813144811640169 8756588632359858608730127)
          ·
            refine ⟨13134882948539787913095191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8756588632359858608730127 13134882948539787913095191)
            ·
              refine ⟨19702324422809681869642787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134882948539787913095191 19702324422809681869642787)
              ·
                refine ⟨29553486634214522804464181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19702324422809681869642787 29553486634214522804464181)
                ·
                  refine ⟨2770639371957611512918517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29553486634214522804464181 2770639371957611512918517)
                  ·
                    refine ⟨259747441121026079336111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2770639371957611512918517 259747441121026079336111)
                    ·
                      rfl

theorem cell23_1517569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1517569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517569 prefixEnd_1517569 := by exact prefixLift 1517569
  have htrace : WordTrace (prefixWord ++ tailWord_1517569) baseStart_1517569 baseEnd_1517569 := by
    simpa [prefixWord, tailWord_1517569, baseEnd_1517569] using wordTrace_append hprefix tailTrace_1517569
  have hstable : (prefixWord ++ tailWord_1517569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517569).length < 2 ^ (prefixWord ++ tailWord_1517569).sum := by decide
  have hdescent : baseEnd_1517569 < baseStart_1517569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517576 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_1517576 : Nat := 118140960795 + 1517576 * 2 ^ 59
def prefixEnd_1517576 : Nat := 4983230072969 + 3 ^ 40 * 1517576 * 2
def baseEnd_1517576 : Nat := 779245917727659710620801

theorem tailTrace_1517576 : CollatzResearch.WordTrace tailWord_1517576 prefixEnd_1517576 779245917727659710620801 := by
  unfold tailWord_1517576
  simp only [CollatzResearch.WordTrace]
  refine ⟨27675271975044404095714291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36900362633392538794285721 27675271975044404095714291)
  ·
    refine ⟨41512907962566606143571437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27675271975044404095714291 41512907962566606143571437)
    ·
      refine ⟨15567340485962477303839289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41512907962566606143571437 15567340485962477303839289)
      ·
        refine ⟨11675505364471857977879467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15567340485962477303839289 11675505364471857977879467)
        ·
          refine ⟨17513258046707786966819201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11675505364471857977879467 17513258046707786966819201)
          ·
            refine ⟨13134943535030840225114401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17513258046707786966819201 13134943535030840225114401)
            ·
              refine ⟨9851207651273130168835801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13134943535030840225114401 9851207651273130168835801)
              ·
                refine ⟨7388405738454847626626851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9851207651273130168835801 7388405738454847626626851)
                ·
                  refine ⟨11082608607682271439940277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7388405738454847626626851 11082608607682271439940277)
                  ·
                    refine ⟨1038994556970212947494401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11082608607682271439940277 1038994556970212947494401)
                    ·
                      refine ⟨779245917727659710620801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1038994556970212947494401 779245917727659710620801)
                      ·
                        rfl

theorem cell23_1517576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_1517576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517576 prefixEnd_1517576 := by exact prefixLift 1517576
  have htrace : WordTrace (prefixWord ++ tailWord_1517576) baseStart_1517576 baseEnd_1517576 := by
    simpa [prefixWord, tailWord_1517576, baseEnd_1517576] using wordTrace_append hprefix tailTrace_1517576
  have hstable : (prefixWord ++ tailWord_1517576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517576).length < 2 ^ (prefixWord ++ tailWord_1517576).sum := by decide
  have hdescent : baseEnd_1517576 < baseStart_1517576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517599 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 1, 6]
def baseStart_1517599 : Nat := 118140960795 + 1517599 * 2 ^ 59
def prefixEnd_1517599 : Nat := 4983230072969 + 3 ^ 40 * 1517599 * 2
def baseEnd_1517599 : Nat := 259752575927571040211065

theorem tailTrace_1517599 : CollatzResearch.WordTrace tailWord_1517599 prefixEnd_1517599 259752575927571040211065 := by
  unfold tailWord_1517599
  simp only [CollatzResearch.WordTrace]
  refine ⟨55351382829005483119515851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36900921886003655413010567 55351382829005483119515851)
  ·
    refine ⟨83027074243508224679273777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55351382829005483119515851 83027074243508224679273777)
    ·
      refine ⟨62270305682631168509455333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83027074243508224679273777 62270305682631168509455333)
      ·
        refine ⟨11675682315493344095522875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62270305682631168509455333 11675682315493344095522875)
        ·
          refine ⟨17513523473240016143284313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11675682315493344095522875 17513523473240016143284313)
          ·
            refine ⟨13135142604930012107463235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17513523473240016143284313 13135142604930012107463235)
            ·
              refine ⟨19702713907395018161194853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13135142604930012107463235 19702713907395018161194853)
              ·
                refine ⟨3694258857636565905224035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19702713907395018161194853 3694258857636565905224035)
                ·
                  refine ⟨5541388286454848857836053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694258857636565905224035 5541388286454848857836053)
                  ·
                    refine ⟨259752575927571040211065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5541388286454848857836053 259752575927571040211065)
                    ·
                      rfl

theorem cell23_1517599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_1517599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517599 prefixEnd_1517599 := by exact prefixLift 1517599
  have htrace : WordTrace (prefixWord ++ tailWord_1517599) baseStart_1517599 baseEnd_1517599 := by
    simpa [prefixWord, tailWord_1517599, baseEnd_1517599] using wordTrace_append hprefix tailTrace_1517599
  have hstable : (prefixWord ++ tailWord_1517599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517599).length < 2 ^ (prefixWord ++ tailWord_1517599).sum := by decide
  have hdescent : baseEnd_1517599 < baseStart_1517599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517616 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 4, 4]
def baseStart_1517616 : Nat := 118140960795 + 1517616 * 2 ^ 59
def prefixEnd_1517616 : Nat := 4983230072969 + 3 ^ 40 * 1517616 * 2
def baseEnd_1517616 : Nat := 259755485651279851373539

theorem tailTrace_1517616 : CollatzResearch.WordTrace tailWord_1517616 prefixEnd_1517616 259755485651279851373539 := by
  unfold tailWord_1517616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676001434971947511442351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36901335246629263348589801 27676001434971947511442351)
  ·
    refine ⟨41514002152457921267163527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27676001434971947511442351 41514002152457921267163527)
    ·
      refine ⟨62271003228686881900745291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41514002152457921267163527 62271003228686881900745291)
      ·
        refine ⟨93406504843030322851117937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62271003228686881900745291 93406504843030322851117937)
        ·
          refine ⟨70054878632272742138338453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93406504843030322851117937 70054878632272742138338453)
          ·
            refine ⟨3283822435887784787734615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70054878632272742138338453 3283822435887784787734615)
            ·
              refine ⟨4925733653831677181601923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283822435887784787734615 4925733653831677181601923)
              ·
                refine ⟨7388600480747515772402885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925733653831677181601923 7388600480747515772402885)
                ·
                  refine ⟨1385362590140159207325541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7388600480747515772402885 1385362590140159207325541)
                  ·
                    refine ⟨259755485651279851373539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385362590140159207325541 259755485651279851373539)
                    ·
                      rfl

theorem cell23_1517616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_1517616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517616 prefixEnd_1517616 := by exact prefixLift 1517616
  have htrace : WordTrace (prefixWord ++ tailWord_1517616) baseStart_1517616 baseEnd_1517616 := by
    simpa [prefixWord, tailWord_1517616, baseEnd_1517616] using wordTrace_append hprefix tailTrace_1517616
  have hstable : (prefixWord ++ tailWord_1517616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517616).length < 2 ^ (prefixWord ++ tailWord_1517616).sum := by decide
  have hdescent : baseEnd_1517616 < baseStart_1517616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517619 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4]
def baseStart_1517619 : Nat := 118140960795 + 1517619 * 2 ^ 59
def prefixEnd_1517619 : Nat := 4983230072969 + 3 ^ 40 * 1517619 * 2
def baseEnd_1517619 : Nat := 779267997395803042383103

theorem tailTrace_1517619 : CollatzResearch.WordTrace tailWord_1517619 prefixEnd_1517619 779267997395803042383103 := by
  unfold tailWord_1517619
  simp only [CollatzResearch.WordTrace]
  refine ⟨55352112288933026535243911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36901408192622017690162607 55352112288933026535243911)
  ·
    refine ⟨83028168433399539802865867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55352112288933026535243911 83028168433399539802865867)
    ·
      refine ⟨124542252650099309704298801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83028168433399539802865867 124542252650099309704298801)
      ·
        refine ⟨93406689487574482278224101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124542252650099309704298801 93406689487574482278224101)
        ·
          refine ⟨17513754278920215427167019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93406689487574482278224101 17513754278920215427167019)
          ·
            refine ⟨26270631418380323140750529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17513754278920215427167019 26270631418380323140750529)
            ·
              refine ⟨19702973563785242355562897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26270631418380323140750529 19702973563785242355562897)
              ·
                refine ⟨14777230172838931766672173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19702973563785242355562897 14777230172838931766672173)
                ·
                  refine ⟨5541461314814599412502065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14777230172838931766672173 5541461314814599412502065)
                  ·
                    refine ⟨4156095986110949559376549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5541461314814599412502065 4156095986110949559376549)
                    ·
                      refine ⟨779267997395803042383103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4156095986110949559376549 779267997395803042383103)
                      ·
                        rfl

theorem cell23_1517619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_1517619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517619 prefixEnd_1517619 := by exact prefixLift 1517619
  have htrace : WordTrace (prefixWord ++ tailWord_1517619) baseStart_1517619 baseEnd_1517619 := by
    simpa [prefixWord, tailWord_1517619, baseEnd_1517619] using wordTrace_append hprefix tailTrace_1517619
  have hstable : (prefixWord ++ tailWord_1517619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517619).length < 2 ^ (prefixWord ++ tailWord_1517619).sum := by decide
  have hdescent : baseEnd_1517619 < baseStart_1517619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517623 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 3, 2, 2]
def baseStart_1517623 : Nat := 118140960795 + 1517623 * 2 ^ 59
def prefixEnd_1517623 : Nat := 4983230072969 + 3 ^ 40 * 1517623 * 2
def baseEnd_1517623 : Nat := 779270051318421026733085

theorem tailTrace_1517623 : CollatzResearch.WordTrace tailWord_1517623 prefixEnd_1517623 779270051318421026733085 := by
  unfold tailWord_1517623
  simp only [CollatzResearch.WordTrace]
  refine ⟨55352258180918535218389523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36901505453945690145593015 55352258180918535218389523)
  ·
    refine ⟨83028387271377802827584285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55352258180918535218389523 83028387271377802827584285)
    ·
      refine ⟨31135645226766676060344107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83028387271377802827584285 31135645226766676060344107)
      ·
        refine ⟨46703467840150014090516161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31135645226766676060344107 46703467840150014090516161)
        ·
          refine ⟨35027600880112510567887121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46703467840150014090516161 35027600880112510567887121)
          ·
            refine ⟨26270700660084382925915341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35027600880112510567887121 26270700660084382925915341)
            ·
              refine ⟨9851512747531643597218253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26270700660084382925915341 9851512747531643597218253)
              ·
                refine ⟨3694317280324366348956845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9851512747531643597218253 3694317280324366348956845)
                ·
                  refine ⟨1385368980121637380858817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3694317280324366348956845 1385368980121637380858817)
                  ·
                    refine ⟨1039026735091228035644113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385368980121637380858817 1039026735091228035644113)
                    ·
                      refine ⟨779270051318421026733085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039026735091228035644113 779270051318421026733085)
                      ·
                        rfl

theorem cell23_1517623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_1517623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517623 prefixEnd_1517623 := by exact prefixLift 1517623
  have htrace : WordTrace (prefixWord ++ tailWord_1517623) baseStart_1517623 baseEnd_1517623 := by
    simpa [prefixWord, tailWord_1517623, baseEnd_1517623] using wordTrace_append hprefix tailTrace_1517623
  have hstable : (prefixWord ++ tailWord_1517623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517623).length < 2 ^ (prefixWord ++ tailWord_1517623).sum := by decide
  have hdescent : baseEnd_1517623 < baseStart_1517623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517629 : List Nat := [1, 4, 1, 3, 1, 1, 2, 10]
def baseStart_1517629 : Nat := 118140960795 + 1517629 * 2 ^ 59
def prefixEnd_1517629 : Nat := 4983230072969 + 3 ^ 40 * 1517629 * 2
def baseEnd_1517629 : Nat := 28861967859346222342891

theorem tailTrace_1517629 : CollatzResearch.WordTrace tailWord_1517629 prefixEnd_1517629 28861967859346222342891 := by
  unfold tailWord_1517629
  simp only [CollatzResearch.WordTrace]
  refine ⟨55352477018896798243107941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36901651345931198828738627 55352477018896798243107941)
  ·
    refine ⟨10378589441043149670582739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55352477018896798243107941 10378589441043149670582739)
    ·
      refine ⟨15567884161564724505874109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10378589441043149670582739 15567884161564724505874109)
      ·
        refine ⟨5837956560586771689702791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15567884161564724505874109 5837956560586771689702791)
        ·
          refine ⟨8756934840880157534554187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5837956560586771689702791 8756934840880157534554187)
          ·
            refine ⟨13135402261320236301831281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8756934840880157534554187 13135402261320236301831281)
            ·
              refine ⟨9851551695990177226373461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13135402261320236301831281 9851551695990177226373461)
              ·
                refine ⟨28861967859346222342891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9851551695990177226373461 28861967859346222342891)
                ·
                  rfl

theorem cell23_1517629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 10].length) (baseStart_1517629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517629 prefixEnd_1517629 := by exact prefixLift 1517629
  have htrace : WordTrace (prefixWord ++ tailWord_1517629) baseStart_1517629 baseEnd_1517629 := by
    simpa [prefixWord, tailWord_1517629, baseEnd_1517629] using wordTrace_append hprefix tailTrace_1517629
  have hstable : (prefixWord ++ tailWord_1517629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517629).length < 2 ^ (prefixWord ++ tailWord_1517629).sum := by decide
  have hdescent : baseEnd_1517629 < baseStart_1517629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517633 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1517633 : Nat := 118140960795 + 1517633 * 2 ^ 59
def prefixEnd_1517633 : Nat := 4983230072969 + 3 ^ 40 * 1517633 * 2
def baseEnd_1517633 : Nat := 259758395374988662536013

theorem tailTrace_1517633 : CollatzResearch.WordTrace tailWord_1517633 prefixEnd_1517633 259758395374988662536013 := by
  unfold tailWord_1517633
  simp only [CollatzResearch.WordTrace]
  refine ⟨55352622910882306926253553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36901748607254871284169035 55352622910882306926253553)
  ·
    refine ⟨41514467183161730194690165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55352622910882306926253553 41514467183161730194690165)
    ·
      refine ⟨3891981298421412205752203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41514467183161730194690165 3891981298421412205752203)
      ·
        refine ⟨5837971947632118308628305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891981298421412205752203 5837971947632118308628305)
        ·
          refine ⟨4378478960724088731471229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5837971947632118308628305 4378478960724088731471229)
          ·
            refine ⟨1641929610271533274301711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4378478960724088731471229 1641929610271533274301711)
            ·
              refine ⟨2462894415407299911452567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641929610271533274301711 2462894415407299911452567)
              ·
                refine ⟨3694341623110949867178851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462894415407299911452567 3694341623110949867178851)
                ·
                  refine ⟨5541512434666424800768277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694341623110949867178851 5541512434666424800768277)
                  ·
                    refine ⟨259758395374988662536013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5541512434666424800768277 259758395374988662536013)
                    ·
                      rfl

theorem cell23_1517633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1517633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517633 prefixEnd_1517633 := by exact prefixLift 1517633
  have htrace : WordTrace (prefixWord ++ tailWord_1517633) baseStart_1517633 baseEnd_1517633 := by
    simpa [prefixWord, tailWord_1517633, baseEnd_1517633] using wordTrace_append hprefix tailTrace_1517633
  have hstable : (prefixWord ++ tailWord_1517633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517633).length < 2 ^ (prefixWord ++ tailWord_1517633).sum := by decide
  have hdescent : baseEnd_1517633 < baseStart_1517633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517646 : List Nat := [4, 1, 1, 1, 1, 4, 4, 7]
def baseStart_1517646 : Nat := 118140960795 + 1517646 * 2 ^ 59
def prefixEnd_1517646 : Nat := 4983230072969 + 3 ^ 40 * 1517646 * 2
def baseEnd_1517646 : Nat := 28862291161980534694277

theorem tailTrace_1517646 : CollatzResearch.WordTrace tailWord_1517646 prefixEnd_1517646 28862291161980534694277 := by
  unfold tailWord_1517646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919137132479401268309599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36902064706556806764317861 6919137132479401268309599)
  ·
    refine ⟨10378705698719101902464399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919137132479401268309599 10378705698719101902464399)
    ·
      refine ⟨15568058548078652853696599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10378705698719101902464399 15568058548078652853696599)
      ·
        refine ⟨23352087822117979280544899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15568058548078652853696599 23352087822117979280544899)
        ·
          refine ⟨35028131733176968920817349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23352087822117979280544899 35028131733176968920817349)
          ·
            refine ⟨6567774699970681672653253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35028131733176968920817349 6567774699970681672653253)
            ·
              refine ⟨1231457756244502813622485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6567774699970681672653253 1231457756244502813622485)
              ·
                refine ⟨28862291161980534694277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1231457756244502813622485 28862291161980534694277)
                ·
                  rfl

theorem cell23_1517646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_1517646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517646 prefixEnd_1517646 := by exact prefixLift 1517646
  have htrace : WordTrace (prefixWord ++ tailWord_1517646) baseStart_1517646 baseEnd_1517646 := by
    simpa [prefixWord, tailWord_1517646, baseEnd_1517646] using wordTrace_append hprefix tailTrace_1517646
  have hstable : (prefixWord ++ tailWord_1517646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517646).length < 2 ^ (prefixWord ++ tailWord_1517646).sum := by decide
  have hdescent : baseEnd_1517646 < baseStart_1517646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517673 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 3]
def baseStart_1517673 : Nat := 118140960795 + 1517673 * 2 ^ 59
def prefixEnd_1517673 : Nat := 4983230072969 + 3 ^ 40 * 1517673 * 2
def baseEnd_1517673 : Nat := 779295725351145831107855

theorem tailTrace_1517673 : CollatzResearch.WordTrace tailWord_1517673 prefixEnd_1517673 779295725351145831107855 := by
  unfold tailWord_1517673
  simp only [CollatzResearch.WordTrace]
  refine ⟨55354081830737393757709673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36902721220491595838473115 55354081830737393757709673)
  ·
    refine ⟨41515561373053045318282255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55354081830737393757709673 41515561373053045318282255)
    ·
      refine ⟨62273342059579567977423383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41515561373053045318282255 62273342059579567977423383)
      ·
        refine ⟨93410013089369351966135075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62273342059579567977423383 93410013089369351966135075)
        ·
          refine ⟨140115019634054027949202613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93410013089369351966135075 140115019634054027949202613)
          ·
            refine ⟨13135783090692565120237745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140115019634054027949202613 13135783090692565120237745)
            ·
              refine ⟨9851837318019423840178309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13135783090692565120237745 9851837318019423840178309)
              ·
                refine ⟨1847219497128641970033433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9851837318019423840178309 1847219497128641970033433)
                ·
                  refine ⟨1385414622846481477525075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847219497128641970033433 1385414622846481477525075)
                  ·
                    refine ⟨2078121934269722216287613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385414622846481477525075 2078121934269722216287613)
                    ·
                      refine ⟨779295725351145831107855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078121934269722216287613 779295725351145831107855)
                      ·
                        rfl

theorem cell23_1517673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_1517673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517673 prefixEnd_1517673 := by exact prefixLift 1517673
  have htrace : WordTrace (prefixWord ++ tailWord_1517673) baseStart_1517673 baseEnd_1517673 := by
    simpa [prefixWord, tailWord_1517673, baseEnd_1517673] using wordTrace_append hprefix tailTrace_1517673
  have hstable : (prefixWord ++ tailWord_1517673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517673).length < 2 ^ (prefixWord ++ tailWord_1517673).sum := by decide
  have hdescent : baseEnd_1517673 < baseStart_1517673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517674 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_1517674 : Nat := 118140960795 + 1517674 * 2 ^ 59
def prefixEnd_1517674 : Nat := 4983230072969 + 3 ^ 40 * 1517674 * 2
def baseEnd_1517674 : Nat := 779296238831800327195351

theorem tailTrace_1517674 : CollatzResearch.WordTrace tailWord_1517674 prefixEnd_1517674 779296238831800327195351 := by
  unfold tailWord_1517674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13838529575933442732124019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36902745535822513952330717 13838529575933442732124019)
  ·
    refine ⟨20757794363900164098186029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13838529575933442732124019 20757794363900164098186029)
    ·
      refine ⟨7784172886462561536819761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20757794363900164098186029 7784172886462561536819761)
      ·
        refine ⟨5838129664846921152614821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7784172886462561536819761 5838129664846921152614821)
        ·
          refine ⟨1094649312158797716115279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5838129664846921152614821 1094649312158797716115279)
          ·
            refine ⟨1641973968238196574172919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094649312158797716115279 1641973968238196574172919)
            ·
              refine ⟨2462960952357294861259379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641973968238196574172919 2462960952357294861259379)
              ·
                refine ⟨3694441428535942291889069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462960952357294861259379 3694441428535942291889069)
                ·
                  refine ⟨1385415535700978359458401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3694441428535942291889069 1385415535700978359458401)
                  ·
                    refine ⟨1039061651775733769593801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385415535700978359458401 1039061651775733769593801)
                    ·
                      refine ⟨779296238831800327195351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039061651775733769593801 779296238831800327195351)
                      ·
                        rfl

theorem cell23_1517674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_1517674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517674 prefixEnd_1517674 := by exact prefixLift 1517674
  have htrace : WordTrace (prefixWord ++ tailWord_1517674) baseStart_1517674 baseEnd_1517674 := by
    simpa [prefixWord, tailWord_1517674, baseEnd_1517674] using wordTrace_append hprefix tailTrace_1517674
  have hstable : (prefixWord ++ tailWord_1517674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517674).length < 2 ^ (prefixWord ++ tailWord_1517674).sum := by decide
  have hdescent : baseEnd_1517674 < baseStart_1517674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517781 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1517781 : Nat := 118140960795 + 1517781 * 2 ^ 59
def prefixEnd_1517781 : Nat := 4983230072969 + 3 ^ 40 * 1517781 * 2
def baseEnd_1517781 : Nat := 779351181261831408557359

theorem tailTrace_1517781 : CollatzResearch.WordTrace tailWord_1517781 prefixEnd_1517781 779351181261831408557359 := by
  unfold tailWord_1517781
  simp only [CollatzResearch.WordTrace]
  refine ⟨55358020914346128202641197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36905347276230752135094131 55358020914346128202641197)
  ·
    refine ⟨20759257842879798075990449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55358020914346128202641197 20759257842879798075990449)
    ·
      refine ⟨15569443382159848556992837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20759257842879798075990449 15569443382159848556992837)
      ·
        refine ⟨2919270634154971604436157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15569443382159848556992837 2919270634154971604436157)
        ·
          refine ⟨1094726487808114351663559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2919270634154971604436157 1094726487808114351663559)
          ·
            refine ⟨1642089731712171527495339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094726487808114351663559 1642089731712171527495339)
            ·
              refine ⟨2463134597568257291243009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642089731712171527495339 2463134597568257291243009)
              ·
                refine ⟨1847350948176192968432257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463134597568257291243009 1847350948176192968432257)
                ·
                  refine ⟨1385513211132144726324193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847350948176192968432257 1385513211132144726324193)
                  ·
                    refine ⟨1039134908349108544743145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385513211132144726324193 1039134908349108544743145)
                    ·
                      refine ⟨779351181261831408557359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039134908349108544743145 779351181261831408557359)
                      ·
                        rfl

theorem cell23_1517781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1517781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517781 prefixEnd_1517781 := by exact prefixLift 1517781
  have htrace : WordTrace (prefixWord ++ tailWord_1517781) baseStart_1517781 baseEnd_1517781 := by
    simpa [prefixWord, tailWord_1517781, baseEnd_1517781] using wordTrace_append hprefix tailTrace_1517781
  have hstable : (prefixWord ++ tailWord_1517781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517781).length < 2 ^ (prefixWord ++ tailWord_1517781).sum := by decide
  have hdescent : baseEnd_1517781 < baseStart_1517781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517803 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 2, 4, 2]
def baseStart_1517803 : Nat := 118140960795 + 1517803 * 2 ^ 59
def prefixEnd_1517803 : Nat := 4983230072969 + 3 ^ 40 * 1517803 * 2
def baseEnd_1517803 : Nat := 779362477836230322482257

theorem tailTrace_1517803 : CollatzResearch.WordTrace tailWord_1517803 prefixEnd_1517803 779362477836230322482257 := by
  unfold tailWord_1517803
  simp only [CollatzResearch.WordTrace]
  refine ⟨55358823320266425959942063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36905882213510950639961375 55358823320266425959942063)
  ·
    refine ⟨83038234980399638939913095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55358823320266425959942063 83038234980399638939913095)
    ·
      refine ⟨124557352470599458409869643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83038234980399638939913095 124557352470599458409869643)
      ·
        refine ⟨186836028705899187614804465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124557352470599458409869643 186836028705899187614804465)
        ·
          refine ⟨140127021529424390711103349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186836028705899187614804465 140127021529424390711103349)
          ·
            refine ⟨13136908268383536629165939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140127021529424390711103349 13136908268383536629165939)
            ·
              refine ⟨19705362402575304943748909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13136908268383536629165939 19705362402575304943748909)
              ·
                refine ⟨7389510900965739353905841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19705362402575304943748909 7389510900965739353905841)
                ·
                  refine ⟨5542133175724304515429381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389510900965739353905841 5542133175724304515429381)
                  ·
                    refine ⟨1039149970448307096643009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5542133175724304515429381 1039149970448307096643009)
                    ·
                      refine ⟨779362477836230322482257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039149970448307096643009 779362477836230322482257)
                      ·
                        rfl

theorem cell23_1517803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4, 2].length) (baseStart_1517803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517803 prefixEnd_1517803 := by exact prefixLift 1517803
  have htrace : WordTrace (prefixWord ++ tailWord_1517803) baseStart_1517803 baseEnd_1517803 := by
    simpa [prefixWord, tailWord_1517803, baseEnd_1517803] using wordTrace_append hprefix tailTrace_1517803
  have hstable : (prefixWord ++ tailWord_1517803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517803).length < 2 ^ (prefixWord ++ tailWord_1517803).sum := by decide
  have hdescent : baseEnd_1517803 < baseStart_1517803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517823 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_1517823 : Nat := 118140960795 + 1517823 * 2 ^ 59
def prefixEnd_1517823 : Nat := 4983230072969 + 3 ^ 40 * 1517823 * 2
def baseEnd_1517823 : Nat := 779372747449320244232165

theorem tailTrace_1517823 : CollatzResearch.WordTrace tailWord_1517823 prefixEnd_1517823 779372747449320244232165 := by
  unfold tailWord_1517823
  simp only [CollatzResearch.WordTrace]
  refine ⟨55359552780193969375670123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36906368520129312917113415 55359552780193969375670123)
  ·
    refine ⟨83039329170290954063505185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55359552780193969375670123 83039329170290954063505185)
    ·
      refine ⟨62279496877718215547628889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83039329170290954063505185 62279496877718215547628889)
      ·
        refine ⟨46709622658288661660721667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62279496877718215547628889 46709622658288661660721667)
        ·
          refine ⟨70064433987432992491082501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46709622658288661660721667 70064433987432992491082501)
          ·
            refine ⟨13137081372643686092077969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70064433987432992491082501 13137081372643686092077969)
            ·
              refine ⟨9852811029482764569058477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13137081372643686092077969 9852811029482764569058477)
              ·
                refine ⟨3694804136056036713396929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9852811029482764569058477 3694804136056036713396929)
                ·
                  refine ⟨2771103102042027535047697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694804136056036713396929 2771103102042027535047697)
                  ·
                    refine ⟨2078327326531520651285773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2771103102042027535047697 2078327326531520651285773)
                    ·
                      refine ⟨779372747449320244232165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078327326531520651285773 779372747449320244232165)
                      ·
                        rfl

theorem cell23_1517823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_1517823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517823 prefixEnd_1517823 := by exact prefixLift 1517823
  have htrace : WordTrace (prefixWord ++ tailWord_1517823) baseStart_1517823 baseEnd_1517823 := by
    simpa [prefixWord, tailWord_1517823, baseEnd_1517823] using wordTrace_append hprefix tailTrace_1517823
  have hstable : (prefixWord ++ tailWord_1517823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517823).length < 2 ^ (prefixWord ++ tailWord_1517823).sum := by decide
  have hdescent : baseEnd_1517823 < baseStart_1517823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517860 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 6]
def baseStart_1517860 : Nat := 118140960795 + 1517860 * 2 ^ 59
def prefixEnd_1517860 : Nat := 4983230072969 + 3 ^ 40 * 1517860 * 2
def baseEnd_1517860 : Nat := 86599082914837399941055

theorem tailTrace_1517860 : CollatzResearch.WordTrace tailWord_1517860 prefixEnd_1517860 86599082914837399941055 := by
  unfold tailWord_1517860
  simp only [CollatzResearch.WordTrace]
  refine ⟨27680451140529962347383517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36907268187373283129844689 27680451140529962347383517)
  ·
    refine ⟨10380169177698735880268819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27680451140529962347383517 10380169177698735880268819)
    ·
      refine ⟨15570253766548103820403229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10380169177698735880268819 15570253766548103820403229)
      ·
        refine ⟨5838845162455538932651211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15570253766548103820403229 5838845162455538932651211)
        ·
          refine ⟨8758267743683308398976817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5838845162455538932651211 8758267743683308398976817)
          ·
            refine ⟨6568700807762481299232613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8758267743683308398976817 6568700807762481299232613)
            ·
              refine ⟨1231631401455465243606115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6568700807762481299232613 1231631401455465243606115)
              ·
                refine ⟨1847447102183197865409173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231631401455465243606115 1847447102183197865409173)
                ·
                  refine ⟨86599082914837399941055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1847447102183197865409173 86599082914837399941055)
                  ·
                    rfl

theorem cell23_1517860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_1517860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517860 prefixEnd_1517860 := by exact prefixLift 1517860
  have htrace : WordTrace (prefixWord ++ tailWord_1517860) baseStart_1517860 baseEnd_1517860 := by
    simpa [prefixWord, tailWord_1517860, baseEnd_1517860] using wordTrace_append hprefix tailTrace_1517860
  have hstable : (prefixWord ++ tailWord_1517860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517860).length < 2 ^ (prefixWord ++ tailWord_1517860).sum := by decide
  have hdescent : baseEnd_1517860 < baseStart_1517860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517880 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 2, 3, 2]
def baseStart_1517880 : Nat := 118140960795 + 1517880 * 2 ^ 59
def prefixEnd_1517880 : Nat := 4983230072969 + 3 ^ 40 * 1517880 * 2
def baseEnd_1517880 : Nat := 779402015846626521219403

theorem tailTrace_1517880 : CollatzResearch.WordTrace tailWord_1517880 prefixEnd_1517880 779402015846626521219403 := by
  unfold tailWord_1517880
  simp only [CollatzResearch.WordTrace]
  refine ⟨27680815870493734055247547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36907754493991645406996729 27680815870493734055247547)
  ·
    refine ⟨41521223805740601082871321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27680815870493734055247547 41521223805740601082871321)
    ·
      refine ⟨31140917854305450812153491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41521223805740601082871321 31140917854305450812153491)
      ·
        refine ⟨46711376781458176218230237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31140917854305450812153491 46711376781458176218230237)
        ·
          refine ⟨17516766293046816081836339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46711376781458176218230237 17516766293046816081836339)
          ·
            refine ⟨26275149439570224122754509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17516766293046816081836339 26275149439570224122754509)
            ·
              refine ⟨9853181039838834046032941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26275149439570224122754509 9853181039838834046032941)
              ·
                refine ⟨3694942889939562767262353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9853181039838834046032941 3694942889939562767262353)
                ·
                  refine ⟨2771207167454672075446765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3694942889939562767262353 2771207167454672075446765)
                  ·
                    refine ⟨1039202687795502028292537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2771207167454672075446765 1039202687795502028292537)
                    ·
                      refine ⟨779402015846626521219403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039202687795502028292537 779402015846626521219403)
                      ·
                        rfl

theorem cell23_1517880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_1517880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517880 prefixEnd_1517880 := by exact prefixLift 1517880
  have htrace : WordTrace (prefixWord ++ tailWord_1517880) baseStart_1517880 baseEnd_1517880 := by
    simpa [prefixWord, tailWord_1517880, baseEnd_1517880] using wordTrace_append hprefix tailTrace_1517880
  have hstable : (prefixWord ++ tailWord_1517880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517880).length < 2 ^ (prefixWord ++ tailWord_1517880).sum := by decide
  have hdescent : baseEnd_1517880 < baseStart_1517880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517887 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 1, 1, 3]
def baseStart_1517887 : Nat := 118140960795 + 1517887 * 2 ^ 59
def prefixEnd_1517887 : Nat := 4983230072969 + 3 ^ 40 * 1517887 * 2
def baseEnd_1517887 : Nat := 779405610211207993831871

theorem tailTrace_1517887 : CollatzResearch.WordTrace tailWord_1517887 prefixEnd_1517887 779405610211207993831871 := by
  unfold tailWord_1517887
  simp only [CollatzResearch.WordTrace]
  refine ⟨55361887051962108305999915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36907924701308072203999943 55361887051962108305999915)
  ·
    refine ⟨83042830577943162458999873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55361887051962108305999915 83042830577943162458999873)
    ·
      refine ⟨62282122933457371844249905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83042830577943162458999873 62282122933457371844249905)
      ·
        refine ⟨46711592200093028883187429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62282122933457371844249905 46711592200093028883187429)
        ·
          refine ⟨8758423537517442915597643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46711592200093028883187429 8758423537517442915597643)
          ·
            refine ⟨13137635306276164373396465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758423537517442915597643 13137635306276164373396465)
            ·
              refine ⟨9853226479707123280047349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13137635306276164373396465 9853226479707123280047349)
              ·
                refine ⟨923739982472542807504439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9853226479707123280047349 923739982472542807504439)
                ·
                  refine ⟨1385609973708814211256659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923739982472542807504439 1385609973708814211256659)
                  ·
                    refine ⟨2078414960563221316884989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385609973708814211256659 2078414960563221316884989)
                    ·
                      refine ⟨779405610211207993831871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078414960563221316884989 779405610211207993831871)
                      ·
                        rfl

theorem cell23_1517887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_1517887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517887 prefixEnd_1517887 := by exact prefixLift 1517887
  have htrace : WordTrace (prefixWord ++ tailWord_1517887) baseStart_1517887 baseEnd_1517887 := by
    simpa [prefixWord, tailWord_1517887, baseEnd_1517887] using wordTrace_append hprefix tailTrace_1517887
  have hstable : (prefixWord ++ tailWord_1517887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517887).length < 2 ^ (prefixWord ++ tailWord_1517887).sum := by decide
  have hdescent : baseEnd_1517887 < baseStart_1517887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517904 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 1, 1, 3]
def baseStart_1517904 : Nat := 118140960795 + 1517904 * 2 ^ 59
def prefixEnd_1517904 : Nat := 4983230072969 + 3 ^ 40 * 1517904 * 2
def baseEnd_1517904 : Nat := 779414339382334427319293

theorem tailTrace_1517904 : CollatzResearch.WordTrace tailWord_1517904 prefixEnd_1517904 779414339382334427319293 := by
  unfold tailWord_1517904
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681253546450260104684383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36908338061933680139579177 27681253546450260104684383)
  ·
    refine ⟨41521880319675390157026575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27681253546450260104684383 41521880319675390157026575)
    ·
      refine ⟨62282820479513085235539863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41521880319675390157026575 62282820479513085235539863)
      ·
        refine ⟨93424230719269627853309795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62282820479513085235539863 93424230719269627853309795)
        ·
          refine ⟨140136346078904441779964693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93424230719269627853309795 140136346078904441779964693)
          ·
            refine ⟨6568891222448645708435845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140136346078904441779964693 6568891222448645708435845)
            ·
              refine ⟨1231667104209121070331721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6568891222448645708435845 1231667104209121070331721)
              ·
                refine ⟨923750328156840802748791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231667104209121070331721 923750328156840802748791)
                ·
                  refine ⟨1385625492235261204123187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923750328156840802748791 1385625492235261204123187)
                  ·
                    refine ⟨2078438238352891806184781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385625492235261204123187 2078438238352891806184781)
                    ·
                      refine ⟨779414339382334427319293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078438238352891806184781 779414339382334427319293)
                      ·
                        rfl

theorem cell23_1517904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 1, 3].length) (baseStart_1517904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517904 prefixEnd_1517904 := by exact prefixLift 1517904
  have htrace : WordTrace (prefixWord ++ tailWord_1517904) baseStart_1517904 baseEnd_1517904 := by
    simpa [prefixWord, tailWord_1517904, baseEnd_1517904] using wordTrace_append hprefix tailTrace_1517904
  have hstable : (prefixWord ++ tailWord_1517904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517904).length < 2 ^ (prefixWord ++ tailWord_1517904).sum := by decide
  have hdescent : baseEnd_1517904 < baseStart_1517904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517920 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 1, 6]
def baseStart_1517920 : Nat := 118140960795 + 1517920 * 2 ^ 59
def prefixEnd_1517920 : Nat := 4983230072969 + 3 ^ 40 * 1517920 * 2
def baseEnd_1517920 : Nat := 259807518357602121573073

theorem tailTrace_1517920 : CollatzResearch.WordTrace tailWord_1517920 prefixEnd_1517920 259807518357602121573073 := by
  unfold tailWord_1517920
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681545330421277470975607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36908727107228369961300809 27681545330421277470975607)
  ·
    refine ⟨41522317995631916206463411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27681545330421277470975607 41522317995631916206463411)
    ·
      refine ⟨62283476993447874309695117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41522317995631916206463411 62283476993447874309695117)
      ·
        refine ⟨23356303872542952866135669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62283476993447874309695117 23356303872542952866135669)
        ·
          refine ⟨2189653488050901831200219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23356303872542952866135669 2189653488050901831200219)
          ·
            refine ⟨3284480232076352746800329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189653488050901831200219 3284480232076352746800329)
            ·
              refine ⟨2463360174057264560100247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284480232076352746800329 2463360174057264560100247)
              ·
                refine ⟨3695040261085896840150371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463360174057264560100247 3695040261085896840150371)
                ·
                  refine ⟨5542560391628845260225557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695040261085896840150371 5542560391628845260225557)
                  ·
                    refine ⟨259807518357602121573073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5542560391628845260225557 259807518357602121573073)
                    ·
                      rfl

theorem cell23_1517920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_1517920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517920 prefixEnd_1517920 := by exact prefixLift 1517920
  have htrace : WordTrace (prefixWord ++ tailWord_1517920) baseStart_1517920 baseEnd_1517920 := by
    simpa [prefixWord, tailWord_1517920, baseEnd_1517920] using wordTrace_append hprefix tailTrace_1517920
  have hstable : (prefixWord ++ tailWord_1517920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517920).length < 2 ^ (prefixWord ++ tailWord_1517920).sum := by decide
  have hdescent : baseEnd_1517920 < baseStart_1517920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517927 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_1517927 : Nat := 118140960795 + 1517927 * 2 ^ 59
def prefixEnd_1517927 : Nat := 4983230072969 + 3 ^ 40 * 1517927 * 2
def baseEnd_1517927 : Nat := 779426149437387837331687

theorem tailTrace_1517927 : CollatzResearch.WordTrace tailWord_1517927 prefixEnd_1517927 779426149437387837331687 := by
  unfold tailWord_1517927
  simp only [CollatzResearch.WordTrace]
  refine ⟨55363345971817195137456035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36908897314544796758304023 55363345971817195137456035)
  ·
    refine ⟨83045018957725792706184053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55363345971817195137456035 83045018957725792706184053)
    ·
      refine ⟨7785470527286793066204755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83045018957725792706184053 7785470527286793066204755)
      ·
        refine ⟨11678205790930189599307133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785470527286793066204755 11678205790930189599307133)
        ·
          refine ⟨4379327171598821099740175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11678205790930189599307133 4379327171598821099740175)
          ·
            refine ⟨6568990757398231649610263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379327171598821099740175 6568990757398231649610263)
            ·
              refine ⟨9853486136097347474415395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568990757398231649610263 9853486136097347474415395)
              ·
                refine ⟨14780229204146021211623093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9853486136097347474415395 14780229204146021211623093)
                ·
                  refine ⟨1385646487888689488589665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14780229204146021211623093 1385646487888689488589665)
                  ·
                    refine ⟨1039234865916517116442249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1385646487888689488589665 1039234865916517116442249)
                    ·
                      refine ⟨779426149437387837331687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039234865916517116442249 779426149437387837331687)
                      ·
                        rfl

theorem cell23_1517927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_1517927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517927 prefixEnd_1517927 := by exact prefixLift 1517927
  have htrace : WordTrace (prefixWord ++ tailWord_1517927) baseStart_1517927 baseEnd_1517927 := by
    simpa [prefixWord, tailWord_1517927, baseEnd_1517927] using wordTrace_append hprefix tailTrace_1517927
  have hstable : (prefixWord ++ tailWord_1517927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517927).length < 2 ^ (prefixWord ++ tailWord_1517927).sum := by decide
  have hdescent : baseEnd_1517927 < baseStart_1517927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517943 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_1517943 : Nat := 118140960795 + 1517943 * 2 ^ 59
def prefixEnd_1517943 : Nat := 4983230072969 + 3 ^ 40 * 1517943 * 2
def baseEnd_1517943 : Nat := 779434365127859774731613

theorem tailTrace_1517943 : CollatzResearch.WordTrace tailWord_1517943 prefixEnd_1517943 779434365127859774731613 := by
  unfold tailWord_1517943
  simp only [CollatzResearch.WordTrace]
  refine ⟨55363929539759229870038483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36909286359839486580025655 55363929539759229870038483)
  ·
    refine ⟨83045894309638844805057725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55363929539759229870038483 83045894309638844805057725)
    ·
      refine ⟨31142210366114566801896647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83045894309638844805057725 31142210366114566801896647)
      ·
        refine ⟨46713315549171850202844971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31142210366114566801896647 46713315549171850202844971)
        ·
          refine ⟨70069973323757775304267457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46713315549171850202844971 70069973323757775304267457)
          ·
            refine ⟨52552479992818331478200593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70069973323757775304267457 52552479992818331478200593)
            ·
              refine ⟨39414359994613748608650445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52552479992818331478200593 39414359994613748608650445)
              ·
                refine ⟨14780384997980155728243917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39414359994613748608650445 14780384997980155728243917)
                ·
                  refine ⟨5542644374242558398091469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14780384997980155728243917 5542644374242558398091469)
                  ·
                    refine ⟨2078491640340959399284301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5542644374242558398091469 2078491640340959399284301)
                    ·
                      refine ⟨779434365127859774731613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078491640340959399284301 779434365127859774731613)
                      ·
                        rfl

theorem cell23_1517943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_1517943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517943 prefixEnd_1517943 := by exact prefixLift 1517943
  have htrace : WordTrace (prefixWord ++ tailWord_1517943) baseStart_1517943 baseEnd_1517943 := by
    simpa [prefixWord, tailWord_1517943, baseEnd_1517943] using wordTrace_append hprefix tailTrace_1517943
  have hstable : (prefixWord ++ tailWord_1517943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517943).length < 2 ^ (prefixWord ++ tailWord_1517943).sum := by decide
  have hdescent : baseEnd_1517943 < baseStart_1517943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517947 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 1, 2, 3]
def baseStart_1517947 : Nat := 118140960795 + 1517947 * 2 ^ 59
def prefixEnd_1517947 : Nat := 4983230072969 + 3 ^ 40 * 1517947 * 2
def baseEnd_1517947 : Nat := 779436419050477759081595

theorem tailTrace_1517947 : CollatzResearch.WordTrace tailWord_1517947 prefixEnd_1517947 779436419050477759081595 := by
  unfold tailWord_1517947
  simp only [CollatzResearch.WordTrace]
  refine ⟨55364075431744738553184095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36909383621163159035456063 55364075431744738553184095)
  ·
    refine ⟨83046113147617107829776143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55364075431744738553184095 83046113147617107829776143)
    ·
      refine ⟨124569169721425661744664215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83046113147617107829776143 124569169721425661744664215)
      ·
        refine ⟨186853754582138492616996323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124569169721425661744664215 186853754582138492616996323)
        ·
          refine ⟨280280631873207738925494485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186853754582138492616996323 280280631873207738925494485)
          ·
            refine ⟨6569077309528306381066277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 280280631873207738925494485 6569077309528306381066277)
            ·
              refine ⟨1231701995536557446449927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6569077309528306381066277 1231701995536557446449927)
              ·
                refine ⟨1847552993304836169674891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231701995536557446449927 1847552993304836169674891)
                ·
                  refine ⟨2771329489957254254512337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847552993304836169674891 2771329489957254254512337)
                  ·
                    refine ⟨2078497117467940690884253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2771329489957254254512337 2078497117467940690884253)
                    ·
                      refine ⟨779436419050477759081595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078497117467940690884253 779436419050477759081595)
                      ·
                        rfl

theorem cell23_1517947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 2, 3].length) (baseStart_1517947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517947 prefixEnd_1517947 := by exact prefixLift 1517947
  have htrace : WordTrace (prefixWord ++ tailWord_1517947) baseStart_1517947 baseEnd_1517947 := by
    simpa [prefixWord, tailWord_1517947, baseEnd_1517947] using wordTrace_append hprefix tailTrace_1517947
  have hstable : (prefixWord ++ tailWord_1517947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517947).length < 2 ^ (prefixWord ++ tailWord_1517947).sum := by decide
  have hdescent : baseEnd_1517947 < baseStart_1517947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517954 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1517954 : Nat := 118140960795 + 1517954 * 2 ^ 59
def prefixEnd_1517954 : Nat := 4983230072969 + 3 ^ 40 * 1517954 * 2
def baseEnd_1517954 : Nat := 259813337805019743898021

theorem tailTrace_1517954 : CollatzResearch.WordTrace tailWord_1517954 prefixEnd_1517954 259813337805019743898021 := by
  unfold tailWord_1517954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13841082685679844687172229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36909553828479585832459277 13841082685679844687172229)
  ·
    refine ⟨2595203003564970878844793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13841082685679844687172229 2595203003564970878844793)
    ·
      refine ⟨1946402252673728159133595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2595203003564970878844793 1946402252673728159133595)
      ·
        refine ⟨2919603379010592238700393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946402252673728159133595 2919603379010592238700393)
        ·
          refine ⟨2189702534257944179025295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2919603379010592238700393 2189702534257944179025295)
          ·
            refine ⟨3284553801386916268537943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189702534257944179025295 3284553801386916268537943)
            ·
              refine ⟨4926830702080374402806915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284553801386916268537943 4926830702080374402806915)
              ·
                refine ⟨7390246053120561604210373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926830702080374402806915 7390246053120561604210373)
                ·
                  refine ⟨1385671134960105300789445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7390246053120561604210373 1385671134960105300789445)
                  ·
                    refine ⟨259813337805019743898021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385671134960105300789445 259813337805019743898021)
                    ·
                      rfl

theorem cell23_1517954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1517954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517954 prefixEnd_1517954 := by exact prefixLift 1517954
  have htrace : WordTrace (prefixWord ++ tailWord_1517954) baseStart_1517954 baseEnd_1517954 := by
    simpa [prefixWord, tailWord_1517954, baseEnd_1517954] using wordTrace_append hprefix tailTrace_1517954
  have hstable : (prefixWord ++ tailWord_1517954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517954).length < 2 ^ (prefixWord ++ tailWord_1517954).sum := by decide
  have hdescent : baseEnd_1517954 < baseStart_1517954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517987 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 1, 3, 2]
def baseStart_1517987 : Nat := 118140960795 + 1517987 * 2 ^ 59
def prefixEnd_1517987 : Nat := 4983230072969 + 3 ^ 40 * 1517987 * 2
def baseEnd_1517987 : Nat := 779456958276657602581411

theorem tailTrace_1517987 : CollatzResearch.WordTrace tailWord_1517987 prefixEnd_1517987 779456958276657602581411 := by
  unfold tailWord_1517987
  simp only [CollatzResearch.WordTrace]
  refine ⟨55365534351599825384640215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36910356234399883589760143 55365534351599825384640215)
  ·
    refine ⟨83048301527399738076960323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55365534351599825384640215 83048301527399738076960323)
    ·
      refine ⟨124572452291099607115440485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83048301527399738076960323 124572452291099607115440485)
      ·
        refine ⟨23357334804581176334145091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124572452291099607115440485 23357334804581176334145091)
        ·
          refine ⟨35036002206871764501217637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23357334804581176334145091 35036002206871764501217637)
          ·
            refine ⟨6569250413788455843978307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35036002206871764501217637 6569250413788455843978307)
            ·
              refine ⟨9853875620682683765967461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6569250413788455843978307 9853875620682683765967461)
              ·
                refine ⟨1847601678878003206118899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9853875620682683765967461 1847601678878003206118899)
                ·
                  refine ⟨2771402518317004809178349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847601678878003206118899 2771402518317004809178349)
                  ·
                    refine ⟨1039275944368876803441881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2771402518317004809178349 1039275944368876803441881)
                    ·
                      refine ⟨779456958276657602581411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039275944368876803441881 779456958276657602581411)
                      ·
                        rfl

theorem cell23_1517987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_1517987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1517987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1517987 prefixEnd_1517987 := by exact prefixLift 1517987
  have htrace : WordTrace (prefixWord ++ tailWord_1517987) baseStart_1517987 baseEnd_1517987 := by
    simpa [prefixWord, tailWord_1517987, baseEnd_1517987] using wordTrace_append hprefix tailTrace_1517987
  have hstable : (prefixWord ++ tailWord_1517987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517987).length < 2 ^ (prefixWord ++ tailWord_1517987).sum := by decide
  have hdescent : baseEnd_1517987 < baseStart_1517987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518003 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 3]
def baseStart_1518003 : Nat := 118140960795 + 1518003 * 2 ^ 59
def prefixEnd_1518003 : Nat := 4983230072969 + 3 ^ 40 * 1518003 * 2
def baseEnd_1518003 : Nat := 779465173967129539981337

theorem tailTrace_1518003 : CollatzResearch.WordTrace tailWord_1518003 prefixEnd_1518003 779465173967129539981337 := by
  unfold tailWord_1518003
  simp only [CollatzResearch.WordTrace]
  refine ⟨55366117919541860117222663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36910745279694573411481775 55366117919541860117222663)
  ·
    refine ⟨83049176879312790175833995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55366117919541860117222663 83049176879312790175833995)
    ·
      refine ⟨124573765318969185263750993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83049176879312790175833995 124573765318969185263750993)
      ·
        refine ⟨93430323989226888947813245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124573765318969185263750993 93430323989226888947813245)
        ·
          refine ⟨35036371495960083355429967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93430323989226888947813245 35036371495960083355429967)
          ·
            refine ⟨52554557243940125033144951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35036371495960083355429967 52554557243940125033144951)
            ·
              refine ⟨78831835865910187549717427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52554557243940125033144951 78831835865910187549717427)
              ·
                refine ⟨118247753798865281324576141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78831835865910187549717427 118247753798865281324576141)
                ·
                  refine ⟨44342907674574480496716053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118247753798865281324576141 44342907674574480496716053)
                  ·
                    refine ⟨2078573797245678773283565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44342907674574480496716053 2078573797245678773283565)
                    ·
                      refine ⟨779465173967129539981337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078573797245678773283565 779465173967129539981337)
                      ·
                        rfl

theorem cell23_1518003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_1518003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518003 prefixEnd_1518003 := by exact prefixLift 1518003
  have htrace : WordTrace (prefixWord ++ tailWord_1518003) baseStart_1518003 baseEnd_1518003 := by
    simpa [prefixWord, tailWord_1518003, baseEnd_1518003] using wordTrace_append hprefix tailTrace_1518003
  have hstable : (prefixWord ++ tailWord_1518003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518003).length < 2 ^ (prefixWord ++ tailWord_1518003).sum := by decide
  have hdescent : baseEnd_1518003 < baseStart_1518003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518028 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1518028 : Nat := 118140960795 + 1518028 * 2 ^ 59
def prefixEnd_1518028 : Nat := 4983230072969 + 3 ^ 40 * 1518028 * 2
def baseEnd_1518028 : Nat := 779478010983491942168723

theorem tailTrace_1518028 : CollatzResearch.WordTrace tailWord_1518028 prefixEnd_1518028 779478010983491942168723 := by
  unfold tailWord_1518028
  simp only [CollatzResearch.WordTrace]
  refine ⟨27683514872225644693441369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36911353162967526257921825 27683514872225644693441369)
  ·
    refine ⟨20762636154169233520081027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27683514872225644693441369 20762636154169233520081027)
    ·
      refine ⟨31143954231253850280121541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20762636154169233520081027 31143954231253850280121541)
      ·
        refine ⟨5839491418360096927522789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31143954231253850280121541 5839491418360096927522789)
        ·
          refine ⟨1094904640942518173910523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5839491418360096927522789 1094904640942518173910523)
          ·
            refine ⟨1642356961413777260865785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094904640942518173910523 1642356961413777260865785)
            ·
              refine ⟨1231767721060332945649339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642356961413777260865785 1231767721060332945649339)
              ·
                refine ⟨1847651581590499418474009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231767721060332945649339 1847651581590499418474009)
                ·
                  refine ⟨1385738686192874563855507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847651581590499418474009 1385738686192874563855507)
                  ·
                    refine ⟨2078608029289311845783261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385738686192874563855507 2078608029289311845783261)
                    ·
                      refine ⟨779478010983491942168723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2078608029289311845783261 779478010983491942168723)
                      ·
                        rfl

theorem cell23_1518028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1518028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518028 prefixEnd_1518028 := by exact prefixLift 1518028
  have htrace : WordTrace (prefixWord ++ tailWord_1518028) baseStart_1518028 baseEnd_1518028 := by
    simpa [prefixWord, tailWord_1518028, baseEnd_1518028] using wordTrace_append hprefix tailTrace_1518028
  have hstable : (prefixWord ++ tailWord_1518028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518028).length < 2 ^ (prefixWord ++ tailWord_1518028).sum := by decide
  have hdescent : baseEnd_1518028 < baseStart_1518028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518090 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1518090 : Nat := 118140960795 + 1518090 * 2 ^ 59
def prefixEnd_1518090 : Nat := 4983230072969 + 3 ^ 40 * 1518090 * 2
def baseEnd_1518090 : Nat := 779509846784070699593437

theorem tailTrace_1518090 : CollatzResearch.WordTrace tailWord_1518090 prefixEnd_1518090 779509846784070699593437 := by
  unfold tailWord_1518090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13842322767556668493909931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36912860713484449317093149 13842322767556668493909931)
  ·
    refine ⟨20763484151335002740864897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13842322767556668493909931 20763484151335002740864897)
    ·
      refine ⟨15572613113501252055648673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20763484151335002740864897 15572613113501252055648673)
      ·
        refine ⟨11679459835125939041736505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15572613113501252055648673 11679459835125939041736505)
        ·
          refine ⟨8759594876344454281302379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11679459835125939041736505 8759594876344454281302379)
          ·
            refine ⟨13139392314516681421953569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8759594876344454281302379 13139392314516681421953569)
            ·
              refine ⟨9854544235887511066465177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13139392314516681421953569 9854544235887511066465177)
              ·
                refine ⟨7390908176915633299848883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9854544235887511066465177 7390908176915633299848883)
                ·
                  refine ⟨11086362265373449949773325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7390908176915633299848883 11086362265373449949773325)
                  ·
                    refine ⟨4157385849515043731164997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11086362265373449949773325 4157385849515043731164997)
                    ·
                      refine ⟨779509846784070699593437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4157385849515043731164997 779509846784070699593437)
                      ·
                        rfl

theorem cell23_1518090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1518090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518090 prefixEnd_1518090 := by exact prefixLift 1518090
  have htrace : WordTrace (prefixWord ++ tailWord_1518090) baseStart_1518090 baseEnd_1518090 := by
    simpa [prefixWord, tailWord_1518090, baseEnd_1518090] using wordTrace_append hprefix tailTrace_1518090
  have hstable : (prefixWord ++ tailWord_1518090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518090).length < 2 ^ (prefixWord ++ tailWord_1518090).sum := by decide
  have hdescent : baseEnd_1518090 < baseStart_1518090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518134 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1518134 : Nat := 118140960795 + 1518134 * 2 ^ 59
def prefixEnd_1518134 : Nat := 4983230072969 + 3 ^ 40 * 1518134 * 2
def baseEnd_1518134 : Nat := 259844146644289509147745

theorem tailTrace_1518134 : CollatzResearch.WordTrace tailWord_1518134 prefixEnd_1518134 259844146644289509147745 := by
  unfold tailWord_1518134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460680992629204343140091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36913930588044846326827637 3460680992629204343140091)
  ·
    refine ⟨5191021488943806514710137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3460680992629204343140091 5191021488943806514710137)
    ·
      refine ⟨3893266116707854886032603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5191021488943806514710137 3893266116707854886032603)
      ·
        refine ⟨5839899175061782329048905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893266116707854886032603 5839899175061782329048905)
        ·
          refine ⟨4379924381296336746786679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5839899175061782329048905 4379924381296336746786679)
          ·
            refine ⟨6569886571944505120180019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379924381296336746786679 6569886571944505120180019)
            ·
              refine ⟨9854829857916757680270029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6569886571944505120180019 9854829857916757680270029)
              ·
                refine ⟨3695561196718784130101261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9854829857916757680270029 3695561196718784130101261)
                ·
                  refine ⟨1385835448769544048787973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3695561196718784130101261 1385835448769544048787973)
                  ·
                    refine ⟨259844146644289509147745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385835448769544048787973 259844146644289509147745)
                    ·
                      rfl

theorem cell23_1518134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1518134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518134 prefixEnd_1518134 := by exact prefixLift 1518134
  have htrace : WordTrace (prefixWord ++ tailWord_1518134) baseStart_1518134 baseEnd_1518134 := by
    simpa [prefixWord, tailWord_1518134, baseEnd_1518134] using wordTrace_append hprefix tailTrace_1518134
  have hstable : (prefixWord ++ tailWord_1518134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518134).length < 2 ^ (prefixWord ++ tailWord_1518134).sum := by decide
  have hdescent : baseEnd_1518134 < baseStart_1518134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518167 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 1, 5, 2]
def baseStart_1518167 : Nat := 118140960795 + 1518167 * 2 ^ 59
def prefixEnd_1518167 : Nat := 4983230072969 + 3 ^ 40 * 1518167 * 2
def baseEnd_1518167 : Nat := 779549384794466898330583

theorem tailTrace_1518167 : CollatzResearch.WordTrace tailWord_1518167 prefixEnd_1518167 779549384794466898330583 := by
  unfold tailWord_1518167
  simp only [CollatzResearch.WordTrace]
  refine ⟨55372099490947716126192755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36914732993965144084128503 55372099490947716126192755)
  ·
    refine ⟨83058149236421574189289133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55372099490947716126192755 83058149236421574189289133)
    ·
      refine ⟨31146805963658090320983425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83058149236421574189289133 31146805963658090320983425)
      ·
        refine ⟨23360104472743567740737569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31146805963658090320983425 23360104472743567740737569)
        ·
          refine ⟨17520078354557675805553177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23360104472743567740737569 17520078354557675805553177)
          ·
            refine ⟨13140058765918256854164883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17520078354557675805553177 13140058765918256854164883)
            ·
              refine ⟨19710088148877385281247325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13140058765918256854164883 19710088148877385281247325)
              ·
                refine ⟨7391283055829019480467747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19710088148877385281247325 7391283055829019480467747)
                ·
                  refine ⟨11086924583743529220701621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391283055829019480467747 11086924583743529220701621)
                  ·
                    refine ⟨1039399179725955864440777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11086924583743529220701621 1039399179725955864440777)
                    ·
                      refine ⟨779549384794466898330583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039399179725955864440777 779549384794466898330583)
                      ·
                        rfl

theorem cell23_1518167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_1518167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518167 prefixEnd_1518167 := by exact prefixLift 1518167
  have htrace : WordTrace (prefixWord ++ tailWord_1518167) baseStart_1518167 baseEnd_1518167 := by
    simpa [prefixWord, tailWord_1518167, baseEnd_1518167] using wordTrace_append hprefix tailTrace_1518167
  have hstable : (prefixWord ++ tailWord_1518167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518167).length < 2 ^ (prefixWord ++ tailWord_1518167).sum := by decide
  have hdescent : baseEnd_1518167 < baseStart_1518167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518177 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 1, 5]
def baseStart_1518177 : Nat := 118140960795 + 1518177 * 2 ^ 59
def prefixEnd_1518177 : Nat := 4983230072969 + 3 ^ 40 * 1518177 * 2
def baseEnd_1518177 : Nat := 259851506533670619735179

theorem tailTrace_1518177 : CollatzResearch.WordTrace tailWord_1518177 prefixEnd_1518177 259851506533670619735179 := by
  unfold tailWord_1518177
  simp only [CollatzResearch.WordTrace]
  refine ⟨55372464220911487834056785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36914976147274325222704523 55372464220911487834056785)
  ·
    refine ⟨41529348165683615875542589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55372464220911487834056785 41529348165683615875542589)
    ·
      refine ⟨15573505562131355953328471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41529348165683615875542589 15573505562131355953328471)
      ·
        refine ⟨23360258343197033929992707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15573505562131355953328471 23360258343197033929992707)
        ·
          refine ⟨35040387514795550894989061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23360258343197033929992707 35040387514795550894989061)
          ·
            refine ⟨6570072659024165792810449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35040387514795550894989061 6570072659024165792810449)
            ·
              refine ⟨4927554494268124344607837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570072659024165792810449 4927554494268124344607837)
              ·
                refine ⟨1847832935350546629227939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4927554494268124344607837 1847832935350546629227939)
                ·
                  refine ⟨2771749403025819943841909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1847832935350546629227939 2771749403025819943841909)
                  ·
                    refine ⟨259851506533670619735179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2771749403025819943841909 259851506533670619735179)
                    ·
                      rfl

theorem cell23_1518177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_1518177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518177 prefixEnd_1518177 := by exact prefixLift 1518177
  have htrace : WordTrace (prefixWord ++ tailWord_1518177) baseStart_1518177 baseEnd_1518177 := by
    simpa [prefixWord, tailWord_1518177, baseEnd_1518177] using wordTrace_append hprefix tailTrace_1518177
  have hstable : (prefixWord ++ tailWord_1518177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518177).length < 2 ^ (prefixWord ++ tailWord_1518177).sum := by decide
  have hdescent : baseEnd_1518177 < baseStart_1518177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518198 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1518198 : Nat := 118140960795 + 1518198 * 2 ^ 59
def prefixEnd_1518198 : Nat := 4983230072969 + 3 ^ 40 * 1518198 * 2
def baseEnd_1518198 : Nat := 86618366966084030782549

theorem tailTrace_1518198 : CollatzResearch.WordTrace tailWord_1518198 prefixEnd_1518198 86618366966084030782549 := by
  unfold tailWord_1518198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460826884614713026285703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36915486769223605613714165 3460826884614713026285703)
  ·
    refine ⟨5191240326922069539428555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3460826884614713026285703 5191240326922069539428555)
    ·
      refine ⟨7786860490383104309142833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191240326922069539428555 7786860490383104309142833)
      ·
        refine ⟨5840145367787328231857125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7786860490383104309142833 5840145367787328231857125)
        ·
          refine ⟨1095027256460124043473211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5840145367787328231857125 1095027256460124043473211)
          ·
            refine ⟨1642540884690186065209817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095027256460124043473211 1642540884690186065209817)
            ·
              refine ⟨1231905663517639548907363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642540884690186065209817 1231905663517639548907363)
              ·
                refine ⟨1847858495276459323361045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231905663517639548907363 1847858495276459323361045)
                ·
                  refine ⟨86618366966084030782549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1847858495276459323361045 86618366966084030782549)
                  ·
                    rfl

theorem cell23_1518198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1518198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518198 prefixEnd_1518198 := by exact prefixLift 1518198
  have htrace : WordTrace (prefixWord ++ tailWord_1518198) baseStart_1518198 baseEnd_1518198 := by
    simpa [prefixWord, tailWord_1518198, baseEnd_1518198] using wordTrace_append hprefix tailTrace_1518198
  have hstable : (prefixWord ++ tailWord_1518198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518198).length < 2 ^ (prefixWord ++ tailWord_1518198).sum := by decide
  have hdescent : baseEnd_1518198 < baseStart_1518198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518241 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 2, 4]
def baseStart_1518241 : Nat := 118140960795 + 1518241 * 2 ^ 59
def prefixEnd_1518241 : Nat := 4983230072969 + 3 ^ 40 * 1518241 * 2
def baseEnd_1518241 : Nat := 259862460787633202935081

theorem tailTrace_1518241 : CollatzResearch.WordTrace tailWord_1518241 prefixEnd_1518241 259862460787633202935081 := by
  unfold tailWord_1518241
  simp only [CollatzResearch.WordTrace]
  refine ⟨55374798492679626764386577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36916532328453084509591051 55374798492679626764386577)
  ·
    refine ⟨41531098869509720073289933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55374798492679626764386577 41531098869509720073289933)
    ·
      refine ⟨15574162076066145027483725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41531098869509720073289933 15574162076066145027483725)
      ·
        refine ⟨5840310778524804385306397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15574162076066145027483725 5840310778524804385306397)
        ·
          refine ⟨2190116541946801644489899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5840310778524804385306397 2190116541946801644489899)
          ·
            refine ⟨3285174812920202466734849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190116541946801644489899 3285174812920202466734849)
            ·
              refine ⟨2463881109690151850051137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285174812920202466734849 2463881109690151850051137)
              ·
                refine ⟨1847910832267613887538353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2463881109690151850051137 1847910832267613887538353)
                ·
                  refine ⟨1385933124200710415653765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847910832267613887538353 1385933124200710415653765)
                  ·
                    refine ⟨259862460787633202935081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385933124200710415653765 259862460787633202935081)
                    ·
                      rfl

theorem cell23_1518241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_1518241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518241 prefixEnd_1518241 := by exact prefixLift 1518241
  have htrace : WordTrace (prefixWord ++ tailWord_1518241) baseStart_1518241 baseEnd_1518241 := by
    simpa [prefixWord, tailWord_1518241, baseEnd_1518241] using wordTrace_append hprefix tailTrace_1518241
  have hstable : (prefixWord ++ tailWord_1518241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518241).length < 2 ^ (prefixWord ++ tailWord_1518241).sum := by decide
  have hdescent : baseEnd_1518241 < baseStart_1518241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518254 : List Nat := [4, 1, 4, 1, 1, 1, 3, 8]
def baseStart_1518254 : Nat := 118140960795 + 1518254 * 2 ^ 59
def prefixEnd_1518254 : Nat := 4983230072969 + 3 ^ 40 * 1518254 * 2
def baseEnd_1518254 : Nat := 28873853985607705849729

theorem tailTrace_1518254 : CollatzResearch.WordTrace tailWord_1518254 prefixEnd_1518254 28873853985607705849729 := by
  unfold tailWord_1518254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921909080204066248076227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36916848427755019989739877 6921909080204066248076227)
  ·
    refine ⟨10382863620306099372114341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6921909080204066248076227 10382863620306099372114341)
    ·
      refine ⟨1946786928807393632271439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10382863620306099372114341 1946786928807393632271439)
      ·
        refine ⟨2920180393211090448407159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946786928807393632271439 2920180393211090448407159)
        ·
          refine ⟨4380270589816635672610739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920180393211090448407159 4380270589816635672610739)
          ·
            refine ⟨6570405884724953508916109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380270589816635672610739 6570405884724953508916109)
            ·
              refine ⟨2463902206771857565843541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6570405884724953508916109 2463902206771857565843541)
              ·
                refine ⟨28873853985607705849729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2463902206771857565843541 28873853985607705849729)
                ·
                  rfl

theorem cell23_1518254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_1518254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518254 prefixEnd_1518254 := by exact prefixLift 1518254
  have htrace : WordTrace (prefixWord ++ tailWord_1518254) baseStart_1518254 baseEnd_1518254 := by
    simpa [prefixWord, tailWord_1518254, baseEnd_1518254] using wordTrace_append hprefix tailTrace_1518254
  have hstable : (prefixWord ++ tailWord_1518254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518254).length < 2 ^ (prefixWord ++ tailWord_1518254).sum := by decide
  have hdescent : baseEnd_1518254 < baseStart_1518254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518338 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_1518338 : Nat := 118140960795 + 1518338 * 2 ^ 59
def prefixEnd_1518338 : Nat := 4983230072969 + 3 ^ 40 * 1518338 * 2
def baseEnd_1518338 : Nat := 779637189986385729292297

theorem tailTrace_1518338 : CollatzResearch.WordTrace tailWord_1518338 prefixEnd_1518338 779637189986385729292297 := by
  unfold tailWord_1518338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844584093332053082666917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36918890915552141553778445 13844584093332053082666917)
  ·
    refine ⟨2595859517499759953000047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13844584093332053082666917 2595859517499759953000047)
    ·
      refine ⟨3893789276249639929500071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595859517499759953000047 3893789276249639929500071)
      ·
        refine ⟨5840683914374459894250107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893789276249639929500071 5840683914374459894250107)
        ·
          refine ⟨8761025871561689841375161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840683914374459894250107 8761025871561689841375161)
          ·
            refine ⟨6570769403671267381031371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8761025871561689841375161 6570769403671267381031371)
            ·
              refine ⟨9856154105506901071547057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570769403671267381031371 9856154105506901071547057)
              ·
                refine ⟨7392115579130175803660293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9856154105506901071547057 7392115579130175803660293)
                ·
                  refine ⟨1386021671086907963186305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7392115579130175803660293 1386021671086907963186305)
                  ·
                    refine ⟨1039516253315180972389729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386021671086907963186305 1039516253315180972389729)
                    ·
                      refine ⟨779637189986385729292297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039516253315180972389729 779637189986385729292297)
                      ·
                        rfl

theorem cell23_1518338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_1518338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518338 prefixEnd_1518338 := by exact prefixLift 1518338
  have htrace : WordTrace (prefixWord ++ tailWord_1518338) baseStart_1518338 baseEnd_1518338 := by
    simpa [prefixWord, tailWord_1518338, baseEnd_1518338] using wordTrace_append hprefix tailTrace_1518338
  have hstable : (prefixWord ++ tailWord_1518338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518338).length < 2 ^ (prefixWord ++ tailWord_1518338).sum := by decide
  have hdescent : baseEnd_1518338 < baseStart_1518338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518367 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1518367 : Nat := 118140960795 + 1518367 * 2 ^ 59
def prefixEnd_1518367 : Nat := 4983230072969 + 3 ^ 40 * 1518367 * 2
def baseEnd_1518367 : Nat := 779652080925366115829663

theorem tailTrace_1518367 : CollatzResearch.WordTrace tailWord_1518367 prefixEnd_1518367 779652080925366115829663 := by
  unfold tailWord_1518367
  simp only [CollatzResearch.WordTrace]
  refine ⟨55379394090223150283473355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36919596060148766855648903 55379394090223150283473355)
  ·
    refine ⟨83069091135334725425210033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55379394090223150283473355 83069091135334725425210033)
    ·
      refine ⟨62301818351501044068907525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83069091135334725425210033 62301818351501044068907525)
      ·
        refine ⟨11681590940906445762920161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62301818351501044068907525 11681590940906445762920161)
        ·
          refine ⟨8761193205679834322190121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11681590940906445762920161 8761193205679834322190121)
          ·
            refine ⟨6570894904259875741642591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8761193205679834322190121 6570894904259875741642591)
            ·
              refine ⟨9856342356389813612463887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570894904259875741642591 9856342356389813612463887)
              ·
                refine ⟨14784513534584720418695831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856342356389813612463887 14784513534584720418695831)
                ·
                  refine ⟨22176770301877080628043747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14784513534584720418695831 22176770301877080628043747)
                  ·
                    refine ⟨33265155452815620942065621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22176770301877080628043747 33265155452815620942065621)
                    ·
                      refine ⟨779652080925366115829663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33265155452815620942065621 779652080925366115829663)
                      ·
                        rfl

theorem cell23_1518367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1518367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518367 prefixEnd_1518367 := by exact prefixLift 1518367
  have htrace : WordTrace (prefixWord ++ tailWord_1518367) baseStart_1518367 baseEnd_1518367 := by
    simpa [prefixWord, tailWord_1518367, baseEnd_1518367] using wordTrace_append hprefix tailTrace_1518367
  have hstable : (prefixWord ++ tailWord_1518367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518367).length < 2 ^ (prefixWord ++ tailWord_1518367).sum := by decide
  have hdescent : baseEnd_1518367 < baseStart_1518367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518372 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_1518372 : Nat := 118140960795 + 1518372 * 2 ^ 59
def prefixEnd_1518372 : Nat := 4983230072969 + 3 ^ 40 * 1518372 * 2
def baseEnd_1518372 : Nat := 779654648328638596267141

theorem tailTrace_1518372 : CollatzResearch.WordTrace tailWord_1518372 prefixEnd_1518372 779654648328638596267141 := by
  unfold tailWord_1518372
  simp only [CollatzResearch.WordTrace]
  refine ⟨27689788227602518068702685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36919717636803357424936913 27689788227602518068702685)
  ·
    refine ⟨10383670585350944275763507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27689788227602518068702685 10383670585350944275763507)
    ·
      refine ⟨15575505878026416413645261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10383670585350944275763507 15575505878026416413645261)
      ·
        refine ⟨5840814704259906155116973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15575505878026416413645261 5840814704259906155116973)
        ·
          refine ⟨2190305514097464808168865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5840814704259906155116973 2190305514097464808168865)
          ·
            refine ⟨1642729135573098606126649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190305514097464808168865 1642729135573098606126649)
            ·
              refine ⟨1232046851679823954594987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642729135573098606126649 1232046851679823954594987)
              ·
                refine ⟨1848070277519735931892481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232046851679823954594987 1848070277519735931892481)
                ·
                  refine ⟨1386052708139801948919361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848070277519735931892481 1386052708139801948919361)
                  ·
                    refine ⟨1039539531104851461689521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386052708139801948919361 1039539531104851461689521)
                    ·
                      refine ⟨779654648328638596267141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039539531104851461689521 779654648328638596267141)
                      ·
                        rfl

theorem cell23_1518372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_1518372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518372 prefixEnd_1518372 := by exact prefixLift 1518372
  have htrace : WordTrace (prefixWord ++ tailWord_1518372) baseStart_1518372 baseEnd_1518372 := by
    simpa [prefixWord, tailWord_1518372, baseEnd_1518372] using wordTrace_append hprefix tailTrace_1518372
  have hstable : (prefixWord ++ tailWord_1518372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518372).length < 2 ^ (prefixWord ++ tailWord_1518372).sum := by decide
  have hdescent : baseEnd_1518372 < baseStart_1518372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518407 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1518407 : Nat := 118140960795 + 1518407 * 2 ^ 59
def prefixEnd_1518407 : Nat := 4983230072969 + 3 ^ 40 * 1518407 * 2
def baseEnd_1518407 : Nat := 779672620151545959329479

theorem tailTrace_1518407 : CollatzResearch.WordTrace tailWord_1518407 prefixEnd_1518407 779672620151545959329479 := by
  unfold tailWord_1518407
  simp only [CollatzResearch.WordTrace]
  refine ⟨55380853010078237114929475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36920568673385491409952983 55380853010078237114929475)
  ·
    refine ⟨83071279515117355672394213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55380853010078237114929475 83071279515117355672394213)
    ·
      refine ⟨15575864909084504188573915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83071279515117355672394213 15575864909084504188573915)
      ·
        refine ⟨23363797363626756282860873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15575864909084504188573915 23363797363626756282860873)
        ·
          refine ⟨17522848022720067212145655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23363797363626756282860873 17522848022720067212145655)
          ·
            refine ⟨26284272034080100818218483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17522848022720067212145655 26284272034080100818218483)
            ·
              refine ⟨39426408051120151227327725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26284272034080100818218483 39426408051120151227327725)
              ·
                refine ⟨14784903019170056710247897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39426408051120151227327725 14784903019170056710247897)
                ·
                  refine ⟨11088677264377542532685923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14784903019170056710247897 11088677264377542532685923)
                  ·
                    refine ⟨16633015896566313799028885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11088677264377542532685923 16633015896566313799028885)
                    ·
                      refine ⟨779672620151545959329479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16633015896566313799028885 779672620151545959329479)
                      ·
                        rfl

theorem cell23_1518407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1518407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518407 prefixEnd_1518407 := by exact prefixLift 1518407
  have htrace : WordTrace (prefixWord ++ tailWord_1518407) baseStart_1518407 baseEnd_1518407 := by
    simpa [prefixWord, tailWord_1518407, baseEnd_1518407] using wordTrace_append hprefix tailTrace_1518407
  have hstable : (prefixWord ++ tailWord_1518407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518407).length < 2 ^ (prefixWord ++ tailWord_1518407).sum := by decide
  have hdescent : baseEnd_1518407 < baseStart_1518407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518428 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1518428 : Nat := 118140960795 + 1518428 * 2 ^ 59
def prefixEnd_1518428 : Nat := 4983230072969 + 3 ^ 40 * 1518428 * 2
def baseEnd_1518428 : Nat := 779683403245290377166883

theorem tailTrace_1518428 : CollatzResearch.WordTrace tailWord_1518428 prefixEnd_1518428 779683403245290377166883 := by
  unfold tailWord_1518428
  simp only [CollatzResearch.WordTrace]
  refine ⟨27690809471501078850721969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36921079295334771800962625 27690809471501078850721969)
  ·
    refine ⟨20768107103625809138041477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27690809471501078850721969 20768107103625809138041477)
    ·
      refine ⟨3894020081929839213382777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20768107103625809138041477 3894020081929839213382777)
      ·
        refine ⟨2920515061447379410037083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3894020081929839213382777 2920515061447379410037083)
        ·
          refine ⟨4380772592171069115055625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920515061447379410037083 4380772592171069115055625)
          ·
            refine ⟨3285579444128301836291719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380772592171069115055625 3285579444128301836291719)
            ·
              refine ⟨4928369166192452754437579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285579444128301836291719 4928369166192452754437579)
              ·
                refine ⟨7392553749288679131656369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928369166192452754437579 7392553749288679131656369)
                ·
                  refine ⟨5544415311966509348742277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392553749288679131656369 5544415311966509348742277)
                  ·
                    refine ⟨1039577870993720502889177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544415311966509348742277 1039577870993720502889177)
                    ·
                      refine ⟨779683403245290377166883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039577870993720502889177 779683403245290377166883)
                      ·
                        rfl

theorem cell23_1518428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1518428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518428 prefixEnd_1518428 := by exact prefixLift 1518428
  have htrace : WordTrace (prefixWord ++ tailWord_1518428) baseStart_1518428 baseEnd_1518428 := by
    simpa [prefixWord, tailWord_1518428, baseEnd_1518428] using wordTrace_append hprefix tailTrace_1518428
  have hstable : (prefixWord ++ tailWord_1518428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518428).length < 2 ^ (prefixWord ++ tailWord_1518428).sum := by decide
  have hdescent : baseEnd_1518428 < baseStart_1518428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518498 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1518498 : Nat := 118140960795 + 1518498 * 2 ^ 59
def prefixEnd_1518498 : Nat := 4983230072969 + 3 ^ 40 * 1518498 * 2
def baseEnd_1518498 : Nat := 259906448963701701097187

theorem tailTrace_1518498 : CollatzResearch.WordTrace tailWord_1518498 prefixEnd_1518498 259906448963701701097187 := by
  unfold tailWord_1518498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13846043013187139914123037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36922781368499039770994765 13846043013187139914123037)
  ·
    refine ⟨5192266129945177467796139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13846043013187139914123037 5192266129945177467796139)
    ·
      refine ⟨7788399194917766201694209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192266129945177467796139 7788399194917766201694209)
      ·
        refine ⟨5841299396188324651270657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7788399194917766201694209 5841299396188324651270657)
        ·
          refine ⟨4380974547141243488452993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841299396188324651270657 4380974547141243488452993)
          ·
            refine ⟨3285730910355932616339745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380974547141243488452993 3285730910355932616339745)
            ·
              refine ⟨2464298182766949462254809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285730910355932616339745 2464298182766949462254809)
              ·
                refine ⟨1848223637075212096691107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464298182766949462254809 1848223637075212096691107)
                ·
                  refine ⟨2772335455612818145036661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848223637075212096691107 2772335455612818145036661)
                  ·
                    refine ⟨259906448963701701097187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2772335455612818145036661 259906448963701701097187)
                    ·
                      rfl

theorem cell23_1518498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1518498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518498 prefixEnd_1518498 := by exact prefixLift 1518498
  have htrace : WordTrace (prefixWord ++ tailWord_1518498) baseStart_1518498 baseEnd_1518498 := by
    simpa [prefixWord, tailWord_1518498, baseEnd_1518498] using wordTrace_append hprefix tailTrace_1518498
  have hstable : (prefixWord ++ tailWord_1518498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518498).length < 2 ^ (prefixWord ++ tailWord_1518498).sum := by decide
  have hdescent : baseEnd_1518498 < baseStart_1518498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518507 : List Nat := [1, 1, 1, 1, 2, 1, 1, 15]
def baseStart_1518507 : Nat := 118140960795 + 1518507 * 2 ^ 59
def prefixEnd_1518507 : Nat := 4983230072969 + 3 ^ 40 * 1518507 * 2
def baseEnd_1518507 : Nat := 28878665489518354373297

theorem tailTrace_1518507 : CollatzResearch.WordTrace tailWord_1518507 prefixEnd_1518507 28878665489518354373297 := by
  unfold tailWord_1518507
  simp only [CollatzResearch.WordTrace]
  refine ⟨55384500309715954193569775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36923000206477302795713183 55384500309715954193569775)
  ·
    refine ⟨83076750464573931290354663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55384500309715954193569775 83076750464573931290354663)
    ·
      refine ⟨124615125696860896935531995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83076750464573931290354663 124615125696860896935531995)
      ·
        refine ⟨186922688545291345403297993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124615125696860896935531995 186922688545291345403297993)
        ·
          refine ⟨140192016408968509052473495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186922688545291345403297993 140192016408968509052473495)
          ·
            refine ⟨210288024613452763578710243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140192016408968509052473495 210288024613452763578710243)
            ·
              refine ⟨315432036920179145368065365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210288024613452763578710243 315432036920179145368065365)
              ·
                refine ⟨28878665489518354373297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 315432036920179145368065365 28878665489518354373297)
                ·
                  rfl

theorem cell23_1518507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 15].length) (baseStart_1518507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518507 prefixEnd_1518507 := by exact prefixLift 1518507
  have htrace : WordTrace (prefixWord ++ tailWord_1518507) baseStart_1518507 baseEnd_1518507 := by
    simpa [prefixWord, tailWord_1518507, baseEnd_1518507] using wordTrace_append hprefix tailTrace_1518507
  have hstable : (prefixWord ++ tailWord_1518507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518507).length < 2 ^ (prefixWord ++ tailWord_1518507).sum := by decide
  have hdescent : baseEnd_1518507 < baseStart_1518507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518521 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1518521 : Nat := 118140960795 + 1518521 * 2 ^ 59
def prefixEnd_1518521 : Nat := 4983230072969 + 3 ^ 40 * 1518521 * 2
def baseEnd_1518521 : Nat := 779731156946158513303955

theorem tailTrace_1518521 : CollatzResearch.WordTrace tailWord_1518521 prefixEnd_1518521 779731156946158513303955 := by
  unfold tailWord_1518521
  simp only [CollatzResearch.WordTrace]
  refine ⟨55385010931665234584579417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36923340621110156389719611 55385010931665234584579417)
  ·
    refine ⟨41538758198748925938434563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55385010931665234584579417 41538758198748925938434563)
    ·
      refine ⟨62308137298123388907651845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41538758198748925938434563 62308137298123388907651845)
      ·
        refine ⟨11682775743398135420184721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62308137298123388907651845 11682775743398135420184721)
        ·
          refine ⟨8762081807548601565138541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11682775743398135420184721 8762081807548601565138541)
          ·
            refine ⟨3285780677830725586926953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8762081807548601565138541 3285780677830725586926953)
            ·
              refine ⟨2464335508373044190195215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285780677830725586926953 2464335508373044190195215)
              ·
                refine ⟨3696503262559566285292823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464335508373044190195215 3696503262559566285292823)
                ·
                  refine ⟨5544754893839349427939235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696503262559566285292823 5544754893839349427939235)
                  ·
                    refine ⟨8317132340759024141908853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5544754893839349427939235 8317132340759024141908853)
                    ·
                      refine ⟨779731156946158513303955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8317132340759024141908853 779731156946158513303955)
                      ·
                        rfl

theorem cell23_1518521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1518521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518521 prefixEnd_1518521 := by exact prefixLift 1518521
  have htrace : WordTrace (prefixWord ++ tailWord_1518521) baseStart_1518521 baseEnd_1518521 := by
    simpa [prefixWord, tailWord_1518521, baseEnd_1518521] using wordTrace_append hprefix tailTrace_1518521
  have hstable : (prefixWord ++ tailWord_1518521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518521).length < 2 ^ (prefixWord ++ tailWord_1518521).sum := by decide
  have hdescent : baseEnd_1518521 < baseStart_1518521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518535 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_1518535 : Nat := 118140960795 + 1518535 * 2 ^ 59
def prefixEnd_1518535 : Nat := 4983230072969 + 3 ^ 40 * 1518535 * 2
def baseEnd_1518535 : Nat := 779738345675321458528891

theorem tailTrace_1518535 : CollatzResearch.WordTrace tailWord_1518535 prefixEnd_1518535 779738345675321458528891 := by
  unfold tailWord_1518535
  simp only [CollatzResearch.WordTrace]
  refine ⟨55385521553614514975589059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36923681035743009983726039 55385521553614514975589059)
  ·
    refine ⟨83078282330421772463383589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55385521553614514975589059 83078282330421772463383589)
    ·
      refine ⟨15577177936954082336884423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83078282330421772463383589 15577177936954082336884423)
      ·
        refine ⟨23365766905431123505326635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15577177936954082336884423 23365766905431123505326635)
        ·
          refine ⟨35048650358146685257989953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23365766905431123505326635 35048650358146685257989953)
          ·
            refine ⟨26286487768610013943492465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35048650358146685257989953 26286487768610013943492465)
            ·
              refine ⟨19714865826457510457619349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26286487768610013943492465 19714865826457510457619349)
              ·
                refine ⟨924134335615195802700907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19714865826457510457619349 924134335615195802700907)
                ·
                  refine ⟨1386201503422793704051361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924134335615195802700907 1386201503422793704051361)
                  ·
                    refine ⟨1039651127567095278038521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386201503422793704051361 1039651127567095278038521)
                    ·
                      refine ⟨779738345675321458528891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039651127567095278038521 779738345675321458528891)
                      ·
                        rfl

theorem cell23_1518535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_1518535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518535 prefixEnd_1518535 := by exact prefixLift 1518535
  have htrace : WordTrace (prefixWord ++ tailWord_1518535) baseStart_1518535 baseEnd_1518535 := by
    simpa [prefixWord, tailWord_1518535, baseEnd_1518535] using wordTrace_append hprefix tailTrace_1518535
  have hstable : (prefixWord ++ tailWord_1518535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518535).length < 2 ^ (prefixWord ++ tailWord_1518535).sum := by decide
  have hdescent : baseEnd_1518535 < baseStart_1518535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518551 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_1518551 : Nat := 118140960795 + 1518551 * 2 ^ 59
def prefixEnd_1518551 : Nat := 4983230072969 + 3 ^ 40 * 1518551 * 2
def baseEnd_1518551 : Nat := 779746561365793395928817

theorem tailTrace_1518551 : CollatzResearch.WordTrace tailWord_1518551 prefixEnd_1518551 779746561365793395928817 := by
  unfold tailWord_1518551
  simp only [CollatzResearch.WordTrace]
  refine ⟨55386105121556549708171507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36924070081037699805447671 55386105121556549708171507)
  ·
    refine ⟨83079157682334824562257261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55386105121556549708171507 83079157682334824562257261)
    ·
      refine ⟨31154684130875559210846473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83079157682334824562257261 31154684130875559210846473)
      ·
        refine ⟨23366013098156669408134855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31154684130875559210846473 23366013098156669408134855)
        ·
          refine ⟨35049019647235004112202283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23366013098156669408134855 35049019647235004112202283)
          ·
            refine ⟨52573529470852506168303425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35049019647235004112202283 52573529470852506168303425)
            ·
              refine ⟨39430147103139379626227569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52573529470852506168303425 39430147103139379626227569)
              ·
                refine ⟨29572610327354534719670677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39430147103139379626227569 29572610327354534719670677)
                ·
                  refine ⟨1386216109094743814984563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29572610327354534719670677 1386216109094743814984563)
                  ·
                    refine ⟨2079324163642115722476845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1386216109094743814984563 2079324163642115722476845)
                    ·
                      refine ⟨779746561365793395928817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2079324163642115722476845 779746561365793395928817)
                      ·
                        rfl

theorem cell23_1518551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_1518551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518551 prefixEnd_1518551 := by exact prefixLift 1518551
  have htrace : WordTrace (prefixWord ++ tailWord_1518551) baseStart_1518551 baseEnd_1518551 := by
    simpa [prefixWord, tailWord_1518551, baseEnd_1518551] using wordTrace_append hprefix tailTrace_1518551
  have hstable : (prefixWord ++ tailWord_1518551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518551).length < 2 ^ (prefixWord ++ tailWord_1518551).sum := by decide
  have hdescent : baseEnd_1518551 < baseStart_1518551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518564 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_1518564 : Nat := 118140960795 + 1518564 * 2 ^ 59
def prefixEnd_1518564 : Nat := 4983230072969 + 3 ^ 40 * 1518564 * 2
def baseEnd_1518564 : Nat := 779753236614301845066257

theorem tailTrace_1518564 : CollatzResearch.WordTrace tailWord_1518564 prefixEnd_1518564 779753236614301845066257 := by
  unfold tailWord_1518564
  simp only [CollatzResearch.WordTrace]
  refine ⟨27693289635254726464197373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36924386180339635285596497 27693289635254726464197373)
  ·
    refine ⟨10384983613220522424074015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27693289635254726464197373 10384983613220522424074015)
    ·
      refine ⟨15577475419830783636111023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10384983613220522424074015 15577475419830783636111023)
      ·
        refine ⟨23366213129746175454166535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15577475419830783636111023 23366213129746175454166535)
        ·
          refine ⟨35049319694619263181249803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23366213129746175454166535 35049319694619263181249803)
          ·
            refine ⟨52573979541928894771874705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35049319694619263181249803 52573979541928894771874705)
            ·
              refine ⟨39430484656446671078906029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52573979541928894771874705 39430484656446671078906029)
              ·
                refine ⟨14786431746167501654589761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39430484656446671078906029 14786431746167501654589761)
                ·
                  refine ⟨11089823809625626240942321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14786431746167501654589761 11089823809625626240942321)
                  ·
                    refine ⟨8317367857219219680706741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11089823809625626240942321 8317367857219219680706741)
                    ·
                      refine ⟨779753236614301845066257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8317367857219219680706741 779753236614301845066257)
                      ·
                        rfl

theorem cell23_1518564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_1518564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518564 prefixEnd_1518564 := by exact prefixLift 1518564
  have htrace : WordTrace (prefixWord ++ tailWord_1518564) baseStart_1518564 baseEnd_1518564 := by
    simpa [prefixWord, tailWord_1518564, baseEnd_1518564] using wordTrace_append hprefix tailTrace_1518564
  have hstable : (prefixWord ++ tailWord_1518564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518564).length < 2 ^ (prefixWord ++ tailWord_1518564).sum := by decide
  have hdescent : baseEnd_1518564 < baseStart_1518564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518580 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1518580 : Nat := 118140960795 + 1518580 * 2 ^ 59
def prefixEnd_1518580 : Nat := 4983230072969 + 3 ^ 40 * 1518580 * 2
def baseEnd_1518580 : Nat := 779761452304773782466185

theorem tailTrace_1518580 : CollatzResearch.WordTrace tailWord_1518580 prefixEnd_1518580 779761452304773782466185 := by
  unfold tailWord_1518580
  simp only [CollatzResearch.WordTrace]
  refine ⟨27693581419225743830488597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36924775225634325107318129 27693581419225743830488597)
  ·
    refine ⟨1298136629026206742054153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27693581419225743830488597 1298136629026206742054153)
    ·
      refine ⟨973602471769655056540615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298136629026206742054153 973602471769655056540615)
      ·
        refine ⟨1460403707654482584810923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973602471769655056540615 1460403707654482584810923)
        ·
          refine ⟨2190605561481723877216385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460403707654482584810923 2190605561481723877216385)
          ·
            refine ⟨1642954171111292907912289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190605561481723877216385 1642954171111292907912289)
            ·
              refine ⟨1232215628333469680934217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642954171111292907912289 1232215628333469680934217)
              ·
                refine ⟨924161721250102260700663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232215628333469680934217 924161721250102260700663)
                ·
                  refine ⟨1386242581875153391050995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924161721250102260700663 1386242581875153391050995)
                  ·
                    refine ⟨2079363872812730086576493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1386242581875153391050995 2079363872812730086576493)
                    ·
                      refine ⟨779761452304773782466185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2079363872812730086576493 779761452304773782466185)
                      ·
                        rfl

theorem cell23_1518580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1518580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518580 prefixEnd_1518580 := by exact prefixLift 1518580
  have htrace : WordTrace (prefixWord ++ tailWord_1518580) baseStart_1518580 baseEnd_1518580 := by
    simpa [prefixWord, tailWord_1518580, baseEnd_1518580] using wordTrace_append hprefix tailTrace_1518580
  have hstable : (prefixWord ++ tailWord_1518580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518580).length < 2 ^ (prefixWord ++ tailWord_1518580).sum := by decide
  have hdescent : baseEnd_1518580 < baseStart_1518580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518584 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_1518584 : Nat := 118140960795 + 1518584 * 2 ^ 59
def prefixEnd_1518584 : Nat := 4983230072969 + 3 ^ 40 * 1518584 * 2
def baseEnd_1518584 : Nat := 259921168742463922272055

theorem tailTrace_1518584 : CollatzResearch.WordTrace tailWord_1518584 prefixEnd_1518584 259921168742463922272055 := by
  unfold tailWord_1518584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27693654365218498172061403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36924872486957997562748537 27693654365218498172061403)
  ·
    refine ⟨41540481547827747258092105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27693654365218498172061403 41540481547827747258092105)
    ·
      refine ⟨31155361160870810443569079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41540481547827747258092105 31155361160870810443569079)
      ·
        refine ⟨46733041741306215665353619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31155361160870810443569079 46733041741306215665353619)
        ·
          refine ⟨70099562611959323498030429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46733041741306215665353619 70099562611959323498030429)
          ·
            refine ⟨26287335979484746311761411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70099562611959323498030429 26287335979484746311761411)
            ·
              refine ⟨39431003969227119467642117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26287335979484746311761411 39431003969227119467642117)
              ·
                refine ⟨7393313244230084900182897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39431003969227119467642117 7393313244230084900182897)
                ·
                  refine ⟨5544984933172563675137173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7393313244230084900182897 5544984933172563675137173)
                  ·
                    refine ⟨259921168742463922272055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5544984933172563675137173 259921168742463922272055)
                    ·
                      rfl

theorem cell23_1518584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_1518584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518584 prefixEnd_1518584 := by exact prefixLift 1518584
  have htrace : WordTrace (prefixWord ++ tailWord_1518584) baseStart_1518584 baseEnd_1518584 := by
    simpa [prefixWord, tailWord_1518584, baseEnd_1518584] using wordTrace_append hprefix tailTrace_1518584
  have hstable : (prefixWord ++ tailWord_1518584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518584).length < 2 ^ (prefixWord ++ tailWord_1518584).sum := by decide
  have hdescent : baseEnd_1518584 < baseStart_1518584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518641 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1518641 : Nat := 118140960795 + 1518641 * 2 ^ 59
def prefixEnd_1518641 : Nat := 4983230072969 + 3 ^ 40 * 1518641 * 2
def baseEnd_1518641 : Nat := 779792774624698043803403

theorem tailTrace_1518641 : CollatzResearch.WordTrace tailWord_1518641 prefixEnd_1518641 779792774624698043803403 := by
  unfold tailWord_1518641
  simp only [CollatzResearch.WordTrace]
  refine ⟨55389387691230495078947777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36926258460820330052631851 55389387691230495078947777)
  ·
    refine ⟨41542040768422871309210833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55389387691230495078947777 41542040768422871309210833)
    ·
      refine ⟨31156530576317153481908125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41542040768422871309210833 31156530576317153481908125)
      ·
        refine ⟨11683698966118932555715547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31156530576317153481908125 11683698966118932555715547)
        ·
          refine ⟨17525548449178398833573321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11683698966118932555715547 17525548449178398833573321)
          ·
            refine ⟨13144161336883799125179991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17525548449178398833573321 13144161336883799125179991)
            ·
              refine ⟨19716242005325698687769987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13144161336883799125179991 19716242005325698687769987)
              ·
                refine ⟨29574363007988548031654981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19716242005325698687769987 29574363007988548031654981)
                ·
                  refine ⟨5545193063997852755935309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29574363007988548031654981 5545193063997852755935309)
                  ·
                    refine ⟨2079447398999194783475741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5545193063997852755935309 2079447398999194783475741)
                    ·
                      refine ⟨779792774624698043803403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2079447398999194783475741 779792774624698043803403)
                      ·
                        rfl

theorem cell23_1518641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1518641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518641 prefixEnd_1518641 := by exact prefixLift 1518641
  have htrace : WordTrace (prefixWord ++ tailWord_1518641) baseStart_1518641 baseEnd_1518641 := by
    simpa [prefixWord, tailWord_1518641, baseEnd_1518641] using wordTrace_append hprefix tailTrace_1518641
  have hstable : (prefixWord ++ tailWord_1518641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518641).length < 2 ^ (prefixWord ++ tailWord_1518641).sum := by decide
  have hdescent : baseEnd_1518641 < baseStart_1518641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518648 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 5]
def baseStart_1518648 : Nat := 118140960795 + 1518648 * 2 ^ 59
def prefixEnd_1518648 : Nat := 4983230072969 + 3 ^ 40 * 1518648 * 2
def baseEnd_1518648 : Nat := 86644040998808835157319

theorem tailTrace_1518648 : CollatzResearch.WordTrace tailWord_1518648 prefixEnd_1518648 86644040998808835157319 := by
  unfold tailWord_1518648
  simp only [CollatzResearch.WordTrace]
  refine ⟨27694821501102567637226299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36926428668136756849635065 27694821501102567637226299)
  ·
    refine ⟨41542232251653851455839449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27694821501102567637226299 41542232251653851455839449)
    ·
      refine ⟨31156674188740388591879587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41542232251653851455839449 31156674188740388591879587)
      ·
        refine ⟨46735011283110582887819381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31156674188740388591879587 46735011283110582887819381)
        ·
          refine ⟨4381407307791617145733067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46735011283110582887819381 4381407307791617145733067)
          ·
            refine ⟨6572110961687425718599601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381407307791617145733067 6572110961687425718599601)
            ·
              refine ⟨4929083221265569288949701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572110961687425718599601 4929083221265569288949701)
              ·
                refine ⟨924203103987294241678069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4929083221265569288949701 924203103987294241678069)
                ·
                  refine ⟨86644040998808835157319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 924203103987294241678069 86644040998808835157319)
                  ·
                    rfl

theorem cell23_1518648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 5].length) (baseStart_1518648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518648 prefixEnd_1518648 := by exact prefixLift 1518648
  have htrace : WordTrace (prefixWord ++ tailWord_1518648) baseStart_1518648 baseEnd_1518648 := by
    simpa [prefixWord, tailWord_1518648, baseEnd_1518648] using wordTrace_append hprefix tailTrace_1518648
  have hstable : (prefixWord ++ tailWord_1518648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518648).length < 2 ^ (prefixWord ++ tailWord_1518648).sum := by decide
  have hdescent : baseEnd_1518648 < baseStart_1518648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518698 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1518698 : Nat := 118140960795 + 1518698 * 2 ^ 59
def prefixEnd_1518698 : Nat := 4983230072969 + 3 ^ 40 * 1518698 * 2
def baseEnd_1518698 : Nat := 779822043022004320790641

theorem tailTrace_1518698 : CollatzResearch.WordTrace tailWord_1518698 prefixEnd_1518698 779822043022004320790641 := by
  unfold tailWord_1518698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13847866663005998453443187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36927644434682662542515165 13847866663005998453443187)
  ·
    refine ⟨20771799994508997680164781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13847866663005998453443187 20771799994508997680164781)
    ·
      refine ⟨7789424997940874130061793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20771799994508997680164781 7789424997940874130061793)
      ·
        refine ⟨5842068748455655597546345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7789424997940874130061793 5842068748455655597546345)
        ·
          refine ⟨4381551561341741698159759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5842068748455655597546345 4381551561341741698159759)
          ·
            refine ⟨6572327342012612547239639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381551561341741698159759 6572327342012612547239639)
            ·
              refine ⟨9858491013018918820859459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6572327342012612547239639 9858491013018918820859459)
              ·
                refine ⟨14787736519528378231289189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9858491013018918820859459 14787736519528378231289189)
                ·
                  refine ⟨2772700597411570918366723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14787736519528378231289189 2772700597411570918366723)
                  ·
                    refine ⟨4159050896117356377550085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2772700597411570918366723 4159050896117356377550085)
                    ·
                      refine ⟨779822043022004320790641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4159050896117356377550085 779822043022004320790641)
                      ·
                        rfl

theorem cell23_1518698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1518698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518698 prefixEnd_1518698 := by exact prefixLift 1518698
  have htrace : WordTrace (prefixWord ++ tailWord_1518698) baseStart_1518698 baseEnd_1518698 := by
    simpa [prefixWord, tailWord_1518698, baseEnd_1518698] using wordTrace_append hprefix tailTrace_1518698
  have hstable : (prefixWord ++ tailWord_1518698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518698).length < 2 ^ (prefixWord ++ tailWord_1518698).sum := by decide
  have hdescent : baseEnd_1518698 < baseStart_1518698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518731 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 3]
def baseStart_1518731 : Nat := 118140960795 + 1518731 * 2 ^ 59
def prefixEnd_1518731 : Nat := 4983230072969 + 3 ^ 40 * 1518731 * 2
def baseEnd_1518731 : Nat := 779838987883602691677989

theorem tailTrace_1518731 : CollatzResearch.WordTrace tailWord_1518731 prefixEnd_1518731 779838987883602691677989 := by
  unfold tailWord_1518731
  simp only [CollatzResearch.WordTrace]
  refine ⟨55392670260904440449724047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36928446840602960299816031 55392670260904440449724047)
  ·
    refine ⟨83089005391356660674586071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55392670260904440449724047 83089005391356660674586071)
    ·
      refine ⟨124633508087034991011879107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83089005391356660674586071 124633508087034991011879107)
      ·
        refine ⟨186950262130552486517818661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124633508087034991011879107 186950262130552486517818661)
        ·
          refine ⟨35053174149478591222090999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186950262130552486517818661 35053174149478591222090999)
          ·
            refine ⟨52579761224217886833136499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35053174149478591222090999 52579761224217886833136499)
            ·
              refine ⟨78869641836326830249704749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52579761224217886833136499 78869641836326830249704749)
              ·
                refine ⟨29576115688622561343639281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78869641836326830249704749 29576115688622561343639281)
                ·
                  refine ⟨22182086766466921007729461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29576115688622561343639281 22182086766466921007729461)
                  ·
                    refine ⟨2079570634356273844474637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22182086766466921007729461 2079570634356273844474637)
                    ·
                      refine ⟨779838987883602691677989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2079570634356273844474637 779838987883602691677989)
                      ·
                        rfl

theorem cell23_1518731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 3].length) (baseStart_1518731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518731 prefixEnd_1518731 := by exact prefixLift 1518731
  have htrace : WordTrace (prefixWord ++ tailWord_1518731) baseStart_1518731 baseEnd_1518731 := by
    simpa [prefixWord, tailWord_1518731, baseEnd_1518731] using wordTrace_append hprefix tailTrace_1518731
  have hstable : (prefixWord ++ tailWord_1518731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518731).length < 2 ^ (prefixWord ++ tailWord_1518731).sum := by decide
  have hdescent : baseEnd_1518731 < baseStart_1518731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518759 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1518759 : Nat := 118140960795 + 1518759 * 2 ^ 59
def prefixEnd_1518759 : Nat := 4983230072969 + 3 ^ 40 * 1518759 * 2
def baseEnd_1518759 : Nat := 259951121780642860709287

theorem tailTrace_1518759 : CollatzResearch.WordTrace tailWord_1518759 prefixEnd_1518759 259951121780642860709287 := by
  unfold tailWord_1518759
  simp only [CollatzResearch.WordTrace]
  refine ⟨55393691504803001231743331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36929127669868667487828887 55393691504803001231743331)
  ·
    refine ⟨83090537257204501847614997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55393691504803001231743331 83090537257204501847614997)
    ·
      refine ⟨3894868933931461024106953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83090537257204501847614997 3894868933931461024106953)
      ·
        refine ⟨2921151700448595768080215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3894868933931461024106953 2921151700448595768080215)
        ·
          refine ⟨4381727550672893652120323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921151700448595768080215 4381727550672893652120323)
          ·
            refine ⟨6572591326009340478180485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381727550672893652120323 6572591326009340478180485)
            ·
              refine ⟨1232360873626751339658841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6572591326009340478180485 1232360873626751339658841)
              ·
                refine ⟨924270655220063504744131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232360873626751339658841 924270655220063504744131)
                ·
                  refine ⟨1386405982830095257116197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924270655220063504744131 1386405982830095257116197)
                  ·
                    refine ⟨259951121780642860709287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1386405982830095257116197 259951121780642860709287)
                    ·
                      rfl

theorem cell23_1518759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1518759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518759 prefixEnd_1518759 := by exact prefixLift 1518759
  have htrace : WordTrace (prefixWord ++ tailWord_1518759) baseStart_1518759 baseEnd_1518759 := by
    simpa [prefixWord, tailWord_1518759, baseEnd_1518759] using wordTrace_append hprefix tailTrace_1518759
  have hstable : (prefixWord ++ tailWord_1518759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518759).length < 2 ^ (prefixWord ++ tailWord_1518759).sum := by decide
  have hdescent : baseEnd_1518759 < baseStart_1518759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518782 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_1518782 : Nat := 118140960795 + 1518782 * 2 ^ 59
def prefixEnd_1518782 : Nat := 4983230072969 + 3 ^ 40 * 1518782 * 2
def baseEnd_1518782 : Nat := 779865175396981992140255

theorem tailTrace_1518782 : CollatzResearch.WordTrace tailWord_1518782 prefixEnd_1518782 779865175396981992140255 := by
  unfold tailWord_1518782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6924316297964959519978825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36929686922479784106553733 6924316297964959519978825)
  ·
    refine ⟨5193237223473719639984119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6924316297964959519978825 5193237223473719639984119)
    ·
      refine ⟨7789855835210579459976179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5193237223473719639984119 7789855835210579459976179)
      ·
        refine ⟨11684783752815869189964269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7789855835210579459976179 11684783752815869189964269)
        ·
          refine ⟨4381793907305950946236601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11684783752815869189964269 4381793907305950946236601)
          ·
            refine ⟨3286345430479463209677451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381793907305950946236601 3286345430479463209677451)
            ·
              refine ⟨4929518145719194814516177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286345430479463209677451 4929518145719194814516177)
              ·
                refine ⟨3697138609289396110887133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929518145719194814516177 3697138609289396110887133)
                ·
                  refine ⟨1386426978483523541582675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3697138609289396110887133 1386426978483523541582675)
                  ·
                    refine ⟨2079640467725285312374013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1386426978483523541582675 2079640467725285312374013)
                    ·
                      refine ⟨779865175396981992140255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2079640467725285312374013 779865175396981992140255)
                      ·
                        rfl

theorem cell23_1518782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_1518782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518782 prefixEnd_1518782 := by exact prefixLift 1518782
  have htrace : WordTrace (prefixWord ++ tailWord_1518782) baseStart_1518782 baseEnd_1518782 := by
    simpa [prefixWord, tailWord_1518782, baseEnd_1518782] using wordTrace_append hprefix tailTrace_1518782
  have hstable : (prefixWord ++ tailWord_1518782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518782).length < 2 ^ (prefixWord ++ tailWord_1518782).sum := by decide
  have hdescent : baseEnd_1518782 < baseStart_1518782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518785 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1518785 : Nat := 118140960795 + 1518785 * 2 ^ 59
def prefixEnd_1518785 : Nat := 4983230072969 + 3 ^ 40 * 1518785 * 2
def baseEnd_1518785 : Nat := 259955571946315160134247

theorem tailTrace_1518785 : CollatzResearch.WordTrace tailWord_1518785 prefixEnd_1518785 259955571946315160134247 := by
  unfold tailWord_1518785
  simp only [CollatzResearch.WordTrace]
  refine ⟨55394639802708807672189809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36929759868472538448126539 55394639802708807672189809)
  ·
    refine ⟨41545979852031605754142357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55394639802708807672189809 41545979852031605754142357)
    ·
      refine ⟨1947467805563981519725423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41545979852031605754142357 1947467805563981519725423)
      ·
        refine ⟨2921201708345972279588135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947467805563981519725423 2921201708345972279588135)
        ·
          refine ⟨4381802562518958419382203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921201708345972279588135 4381802562518958419382203)
          ·
            refine ⟨6572703843778437629073305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4381802562518958419382203 6572703843778437629073305)
            ·
              refine ⟨4929527882833828221804979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6572703843778437629073305 4929527882833828221804979)
              ·
                refine ⟨7394291824250742332707469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4929527882833828221804979 7394291824250742332707469)
                ·
                  refine ⟨2772859434094028374765301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7394291824250742332707469 2772859434094028374765301)
                  ·
                    refine ⟨259955571946315160134247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2772859434094028374765301 259955571946315160134247)
                    ·
                      rfl

theorem cell23_1518785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1518785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518785 prefixEnd_1518785 := by exact prefixLift 1518785
  have htrace : WordTrace (prefixWord ++ tailWord_1518785) baseStart_1518785 baseEnd_1518785 := by
    simpa [prefixWord, tailWord_1518785, baseEnd_1518785] using wordTrace_append hprefix tailTrace_1518785
  have hstable : (prefixWord ++ tailWord_1518785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518785).length < 2 ^ (prefixWord ++ tailWord_1518785).sum := by decide
  have hdescent : baseEnd_1518785 < baseStart_1518785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518786 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1518786 : Nat := 118140960795 + 1518786 * 2 ^ 59
def prefixEnd_1518786 : Nat := 4983230072969 + 3 ^ 40 * 1518786 * 2
def baseEnd_1518786 : Nat := 779867229319599976490237

theorem tailTrace_1518786 : CollatzResearch.WordTrace tailWord_1518786 prefixEnd_1518786 779867229319599976490237 := by
  unfold tailWord_1518786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13848669068926296210744053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36929784183803456561984141 13848669068926296210744053)
  ·
    refine ⟨1298312725211840269757255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13848669068926296210744053 1298312725211840269757255)
    ·
      refine ⟨1947469087817760404635883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298312725211840269757255 1947469087817760404635883)
      ·
        refine ⟨2921203631726640606953825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947469087817760404635883 2921203631726640606953825)
        ·
          refine ⟨2190902723794980455215369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921203631726640606953825 2190902723794980455215369)
          ·
            refine ⟨1643177042846235341411527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190902723794980455215369 1643177042846235341411527)
            ·
              refine ⟨2464765564269353012117291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643177042846235341411527 2464765564269353012117291)
              ·
                refine ⟨3697148346404029518175937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464765564269353012117291 3697148346404029518175937)
                ·
                  refine ⟨2772861259803022138631953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697148346404029518175937 2772861259803022138631953)
                  ·
                    refine ⟨2079645944852266603973965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2772861259803022138631953 2079645944852266603973965)
                    ·
                      refine ⟨779867229319599976490237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2079645944852266603973965 779867229319599976490237)
                      ·
                        rfl

theorem cell23_1518786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1518786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518786 prefixEnd_1518786 := by exact prefixLift 1518786
  have htrace : WordTrace (prefixWord ++ tailWord_1518786) baseStart_1518786 baseEnd_1518786 := by
    simpa [prefixWord, tailWord_1518786, baseEnd_1518786] using wordTrace_append hprefix tailTrace_1518786
  have hstable : (prefixWord ++ tailWord_1518786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518786).length < 2 ^ (prefixWord ++ tailWord_1518786).sum := by decide
  have hdescent : baseEnd_1518786 < baseStart_1518786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518801 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_1518801 : Nat := 118140960795 + 1518801 * 2 ^ 59
def prefixEnd_1518801 : Nat := 4983230072969 + 3 ^ 40 * 1518801 * 2
def baseEnd_1518801 : Nat := 779874931529417417802667

theorem tailTrace_1518801 : CollatzResearch.WordTrace tailWord_1518801 prefixEnd_1518801 779874931529417417802667 := by
  unfold tailWord_1518801
  simp only [CollatzResearch.WordTrace]
  refine ⟨55395223370650842404772257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36930148913767228269848171 55395223370650842404772257)
  ·
    refine ⟨41546417527988131803579193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55395223370650842404772257 41546417527988131803579193)
    ·
      refine ⟨31159813145991098852684395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41546417527988131803579193 31159813145991098852684395)
      ·
        refine ⟨46739719718986648279026593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31159813145991098852684395 46739719718986648279026593)
        ·
          refine ⟨35054789789239986209269945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46739719718986648279026593 35054789789239986209269945)
          ·
            refine ⟨26291092341929989656952459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35054789789239986209269945 26291092341929989656952459)
            ·
              refine ⟨39436638512894984485428689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26291092341929989656952459 39436638512894984485428689)
              ·
                refine ⟨29577478884671238364071517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39436638512894984485428689 29577478884671238364071517)
                ·
                  refine ⟨11091554581751714386526819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29577478884671238364071517 11091554581751714386526819)
                  ·
                    refine ⟨16637331872627571579790229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11091554581751714386526819 16637331872627571579790229)
                    ·
                      refine ⟨779874931529417417802667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16637331872627571579790229 779874931529417417802667)
                      ·
                        rfl

theorem cell23_1518801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_1518801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518801 prefixEnd_1518801 := by exact prefixLift 1518801
  have htrace : WordTrace (prefixWord ++ tailWord_1518801) baseStart_1518801 baseEnd_1518801 := by
    simpa [prefixWord, tailWord_1518801, baseEnd_1518801] using wordTrace_append hprefix tailTrace_1518801
  have hstable : (prefixWord ++ tailWord_1518801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518801).length < 2 ^ (prefixWord ++ tailWord_1518801).sum := by decide
  have hdescent : baseEnd_1518801 < baseStart_1518801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518815 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 2, 4]
def baseStart_1518815 : Nat := 118140960795 + 1518815 * 2 ^ 59
def prefixEnd_1518815 : Nat := 4983230072969 + 3 ^ 40 * 1518815 * 2
def baseEnd_1518815 : Nat := 259960706752860121009201

theorem tailTrace_1518815 : CollatzResearch.WordTrace tailWord_1518815 prefixEnd_1518815 259960706752860121009201 := by
  unfold tailWord_1518815
  simp only [CollatzResearch.WordTrace]
  refine ⟨55395733992600122795781899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36930489328400081863854599 55395733992600122795781899)
  ·
    refine ⟨83093600988900184193672849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55395733992600122795781899 83093600988900184193672849)
    ·
      refine ⟨62320200741675138145254637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83093600988900184193672849 62320200741675138145254637)
      ·
        refine ⟨23370075278128176804470489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62320200741675138145254637 23370075278128176804470489)
        ·
          refine ⟨17527556458596132603352867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23370075278128176804470489 17527556458596132603352867)
          ·
            refine ⟨26291334687894198905029301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17527556458596132603352867 26291334687894198905029301)
            ·
              refine ⟨2464812626990081147346497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26291334687894198905029301 2464812626990081147346497)
              ·
                refine ⟨1848609470242560860509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464812626990081147346497 1848609470242560860509873)
                ·
                  refine ⟨1386457102681920645382405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848609470242560860509873 1386457102681920645382405)
                  ·
                    refine ⟨259960706752860121009201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1386457102681920645382405 259960706752860121009201)
                    ·
                      rfl

theorem cell23_1518815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_1518815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518815 prefixEnd_1518815 := by exact prefixLift 1518815
  have htrace : WordTrace (prefixWord ++ tailWord_1518815) baseStart_1518815 baseEnd_1518815 := by
    simpa [prefixWord, tailWord_1518815, baseEnd_1518815] using wordTrace_append hprefix tailTrace_1518815
  have hstable : (prefixWord ++ tailWord_1518815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518815).length < 2 ^ (prefixWord ++ tailWord_1518815).sum := by decide
  have hdescent : baseEnd_1518815 < baseStart_1518815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518835 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 4]
def baseStart_1518835 : Nat := 118140960795 + 1518835 * 2 ^ 59
def prefixEnd_1518835 : Nat := 4983230072969 + 3 ^ 40 * 1518835 * 2
def baseEnd_1518835 : Nat := 779892389871670284777511

theorem tailTrace_1518835 : CollatzResearch.WordTrace tailWord_1518835 prefixEnd_1518835 779892389871670284777511 := by
  unfold tailWord_1518835
  simp only [CollatzResearch.WordTrace]
  refine ⟨55396463452527666211509959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36930975635018444141006639 55396463452527666211509959)
  ·
    refine ⟨83094695178791499317264939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55396463452527666211509959 83094695178791499317264939)
    ·
      refine ⟨124642042768187248975897409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83094695178791499317264939 124642042768187248975897409)
      ·
        refine ⟨93481532076140436731923057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124642042768187248975897409 93481532076140436731923057)
        ·
          refine ⟨70111149057105327548942293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93481532076140436731923057 70111149057105327548942293)
          ·
            refine ⟨1643230056025906114428335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70111149057105327548942293 1643230056025906114428335)
            ·
              refine ⟨2464845084038859171642503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643230056025906114428335 2464845084038859171642503)
              ·
                refine ⟨3697267626058288757463755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2464845084038859171642503 3697267626058288757463755)
                ·
                  refine ⟨5545901439087433136195633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697267626058288757463755 5545901439087433136195633)
                  ·
                    refine ⟨4159426079315574852146725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5545901439087433136195633 4159426079315574852146725)
                    ·
                      refine ⟨779892389871670284777511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4159426079315574852146725 779892389871670284777511)
                      ·
                        rfl

theorem cell23_1518835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_1518835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518835 prefixEnd_1518835 := by exact prefixLift 1518835
  have htrace : WordTrace (prefixWord ++ tailWord_1518835) baseStart_1518835 baseEnd_1518835 := by
    simpa [prefixWord, tailWord_1518835, baseEnd_1518835] using wordTrace_append hprefix tailTrace_1518835
  have hstable : (prefixWord ++ tailWord_1518835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518835).length < 2 ^ (prefixWord ++ tailWord_1518835).sum := by decide
  have hdescent : baseEnd_1518835 < baseStart_1518835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518836 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1518836 : Nat := 118140960795 + 1518836 * 2 ^ 59
def prefixEnd_1518836 : Nat := 4983230072969 + 3 ^ 40 * 1518836 * 2
def baseEnd_1518836 : Nat := 259964301117441593621669

theorem tailTrace_1518836 : CollatzResearch.WordTrace tailWord_1518836 prefixEnd_1518836 259964301117441593621669 := by
  unfold tailWord_1518836
  simp only [CollatzResearch.WordTrace]
  refine ⟨27698249962762021691148181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36930999950349362254864241 27698249962762021691148181)
  ·
    refine ⟨1298355467004469766772571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27698249962762021691148181 1298355467004469766772571)
    ·
      refine ⟨1947533200506704650158857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298355467004469766772571 1947533200506704650158857)
      ·
        refine ⟨1460649900380028487619143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1947533200506704650158857 1460649900380028487619143)
        ·
          refine ⟨2190974850570042731428715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460649900380028487619143 2190974850570042731428715)
          ·
            refine ⟨3286462275855064097143073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190974850570042731428715 3286462275855064097143073)
            ·
              refine ⟨2464846706891298072857305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286462275855064097143073 2464846706891298072857305)
              ·
                refine ⟨1848635030168473554642979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464846706891298072857305 1848635030168473554642979)
                ·
                  refine ⟨2772952545252710331964469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848635030168473554642979 2772952545252710331964469)
                  ·
                    refine ⟨259964301117441593621669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2772952545252710331964469 259964301117441593621669)
                    ·
                      rfl

theorem cell23_1518836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1518836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518836 prefixEnd_1518836 := by exact prefixLift 1518836
  have htrace : WordTrace (prefixWord ++ tailWord_1518836) baseStart_1518836 baseEnd_1518836 := by
    simpa [prefixWord, tailWord_1518836, baseEnd_1518836] using wordTrace_append hprefix tailTrace_1518836
  have hstable : (prefixWord ++ tailWord_1518836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518836).length < 2 ^ (prefixWord ++ tailWord_1518836).sum := by decide
  have hdescent : baseEnd_1518836 < baseStart_1518836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518895 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 1, 4, 2]
def baseStart_1518895 : Nat := 118140960795 + 1518895 * 2 ^ 59
def prefixEnd_1518895 : Nat := 4983230072969 + 3 ^ 40 * 1518895 * 2
def baseEnd_1518895 : Nat := 779923198710940050027235

theorem tailTrace_1518895 : CollatzResearch.WordTrace tailWord_1518895 prefixEnd_1518895 779923198710940050027235 := by
  unfold tailWord_1518895
  simp only [CollatzResearch.WordTrace]
  refine ⟨55398651832310296458694139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36932434554873530972462759 55398651832310296458694139)
  ·
    refine ⟨83097977748465444688041209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55398651832310296458694139 83097977748465444688041209)
    ·
      refine ⟨62323483311349083516030907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83097977748465444688041209 62323483311349083516030907)
      ·
        refine ⟨93485224967023625274046361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62323483311349083516030907 93485224967023625274046361)
        ·
          refine ⟨70113918725267718955534771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93485224967023625274046361 70113918725267718955534771)
          ·
            refine ⟨105170878087901578433302157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70113918725267718955534771 105170878087901578433302157)
            ·
              refine ⟨39439079282963091912488309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105170878087901578433302157 39439079282963091912488309)
              ·
                refine ⟨3697413682777789866795779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39439079282963091912488309 3697413682777789866795779)
                ·
                  refine ⟨5546120524166684800193669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697413682777789866795779 5546120524166684800193669)
                  ·
                    refine ⟨1039897598281253400036313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546120524166684800193669 1039897598281253400036313)
                    ·
                      refine ⟨779923198710940050027235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039897598281253400036313 779923198710940050027235)
                      ·
                        rfl

theorem cell23_1518895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4, 2].length) (baseStart_1518895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518895 prefixEnd_1518895 := by exact prefixLift 1518895
  have htrace : WordTrace (prefixWord ++ tailWord_1518895) baseStart_1518895 baseEnd_1518895 := by
    simpa [prefixWord, tailWord_1518895, baseEnd_1518895] using wordTrace_append hprefix tailTrace_1518895
  have hstable : (prefixWord ++ tailWord_1518895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518895).length < 2 ^ (prefixWord ++ tailWord_1518895).sum := by decide
  have hdescent : baseEnd_1518895 < baseStart_1518895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518899 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 1, 3, 2]
def baseStart_1518899 : Nat := 118140960795 + 1518899 * 2 ^ 59
def prefixEnd_1518899 : Nat := 4983230072969 + 3 ^ 40 * 1518899 * 2
def baseEnd_1518899 : Nat := 779925252633558034377217

theorem tailTrace_1518899 : CollatzResearch.WordTrace tailWord_1518899 prefixEnd_1518899 779925252633558034377217 := by
  unfold tailWord_1518899
  simp only [CollatzResearch.WordTrace]
  refine ⟨55398797724295805141839751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36932531816197203427893167 55398797724295805141839751)
  ·
    refine ⟨83098196586443707712759627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55398797724295805141839751 83098196586443707712759627)
    ·
      refine ⟨124647294879665561569139441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83098196586443707712759627 124647294879665561569139441)
      ·
        refine ⟨93485471159749171176854581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124647294879665561569139441 93485471159749171176854581)
        ·
          refine ⟨8764262921226484797830117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93485471159749171176854581 8764262921226484797830117)
          ·
            refine ⟨1643299297729965899593147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8764262921226484797830117 1643299297729965899593147)
            ·
              refine ⟨2464948946594948849389721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643299297729965899593147 2464948946594948849389721)
              ·
                refine ⟨1848711709946211637042291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464948946594948849389721 1848711709946211637042291)
                ·
                  refine ⟨2773067564919317455563437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848711709946211637042291 2773067564919317455563437)
                  ·
                    refine ⟨1039900336844744045836289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773067564919317455563437 1039900336844744045836289)
                    ·
                      refine ⟨779925252633558034377217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039900336844744045836289 779925252633558034377217)
                      ·
                        rfl

theorem cell23_1518899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 3, 2].length) (baseStart_1518899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518899 prefixEnd_1518899 := by exact prefixLift 1518899
  have htrace : WordTrace (prefixWord ++ tailWord_1518899) baseStart_1518899 baseEnd_1518899 := by
    simpa [prefixWord, tailWord_1518899, baseEnd_1518899] using wordTrace_append hprefix tailTrace_1518899
  have hstable : (prefixWord ++ tailWord_1518899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518899).length < 2 ^ (prefixWord ++ tailWord_1518899).sum := by decide
  have hdescent : baseEnd_1518899 < baseStart_1518899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518929 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 2, 2, 2]
def baseStart_1518929 : Nat := 118140960795 + 1518929 * 2 ^ 59
def prefixEnd_1518929 : Nat := 4983230072969 + 3 ^ 40 * 1518929 * 2
def baseEnd_1518929 : Nat := 779940657053192917002079

theorem tailTrace_1518929 : CollatzResearch.WordTrace tailWord_1518929 prefixEnd_1518929 779940657053192917002079 := by
  unfold tailWord_1518929
  simp only [CollatzResearch.WordTrace]
  refine ⟨55399891914187120265431841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36933261276124746843621227 55399891914187120265431841)
  ·
    refine ⟨41549918935640340199073881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55399891914187120265431841 41549918935640340199073881)
    ·
      refine ⟨31162439201730255149305411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41549918935640340199073881 31162439201730255149305411)
      ·
        refine ⟨46743658802595382723958117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31162439201730255149305411 46743658802595382723958117)
        ·
          refine ⟨8764436025486634260742147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46743658802595382723958117 8764436025486634260742147)
          ·
            refine ⟨13146654038229951391113221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764436025486634260742147 13146654038229951391113221)
            ·
              refine ⟨2464997632168115885833729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13146654038229951391113221 2464997632168115885833729)
              ·
                refine ⟨1848748224126086914375297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464997632168115885833729 1848748224126086914375297)
                ·
                  refine ⟨1386561168094565185781473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848748224126086914375297 1386561168094565185781473)
                  ·
                    refine ⟨1039920876070923889336105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386561168094565185781473 1039920876070923889336105)
                    ·
                      refine ⟨779940657053192917002079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039920876070923889336105 779940657053192917002079)
                      ·
                        rfl

theorem cell23_1518929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_1518929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1518929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1518929 prefixEnd_1518929 := by exact prefixLift 1518929
  have htrace : WordTrace (prefixWord ++ tailWord_1518929) baseStart_1518929 baseEnd_1518929 := by
    simpa [prefixWord, tailWord_1518929, baseEnd_1518929] using wordTrace_append hprefix tailTrace_1518929
  have hstable : (prefixWord ++ tailWord_1518929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518929).length < 2 ^ (prefixWord ++ tailWord_1518929).sum := by decide
  have hdescent : baseEnd_1518929 < baseStart_1518929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519002 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2]
def baseStart_1519002 : Nat := 118140960795 + 1519002 * 2 ^ 59
def prefixEnd_1519002 : Nat := 4983230072969 + 3 ^ 40 * 1519002 * 2
def baseEnd_1519002 : Nat := 779978141140971131389243

theorem tailTrace_1519002 : CollatzResearch.WordTrace tailWord_1519002 prefixEnd_1519002 779978141140971131389243 := by
  unfold tailWord_1519002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850638610730663433209815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36935036295281769155226173 13850638610730663433209815)
  ·
    refine ⟨20775957916095995149814723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13850638610730663433209815 20775957916095995149814723)
    ·
      refine ⟨31163936874143992724722085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20775957916095995149814723 31163936874143992724722085)
      ·
        refine ⟨5843238163901998635885391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31163936874143992724722085 5843238163901998635885391)
        ·
          refine ⟨8764857245852997953828087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843238163901998635885391 8764857245852997953828087)
          ·
            refine ⟨13147285868779496930742131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764857245852997953828087 13147285868779496930742131)
            ·
              refine ⟨19720928803169245396113197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13147285868779496930742131 19720928803169245396113197)
              ·
                refine ⟨7395348301188467023542449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19720928803169245396113197 7395348301188467023542449)
                ·
                  refine ⟨5546511225891350267656837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7395348301188467023542449 5546511225891350267656837)
                  ·
                    refine ⟨1039970854854628175185657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5546511225891350267656837 1039970854854628175185657)
                    ·
                      refine ⟨779978141140971131389243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1039970854854628175185657 779978141140971131389243)
                      ·
                        rfl

theorem cell23_1519002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_1519002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519002 prefixEnd_1519002 := by exact prefixLift 1519002
  have htrace : WordTrace (prefixWord ++ tailWord_1519002) baseStart_1519002 baseEnd_1519002 := by
    simpa [prefixWord, tailWord_1519002, baseEnd_1519002] using wordTrace_append hprefix tailTrace_1519002
  have hstable : (prefixWord ++ tailWord_1519002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519002).length < 2 ^ (prefixWord ++ tailWord_1519002).sum := by decide
  have hdescent : baseEnd_1519002 < baseStart_1519002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519015 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1519015 : Nat := 118140960795 + 1519015 * 2 ^ 59
def prefixEnd_1519015 : Nat := 4983230072969 + 3 ^ 40 * 1519015 * 2
def baseEnd_1519015 : Nat := 779984816389479580526683

theorem tailTrace_1519015 : CollatzResearch.WordTrace tailWord_1519015 prefixEnd_1519015 779984816389479580526683 := by
  unfold tailWord_1519015
  simp only [CollatzResearch.WordTrace]
  refine ⟨55403028591875556953062499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36935352394583704635374999 55403028591875556953062499)
  ·
    refine ⟨83104542887813335429593749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55403028591875556953062499 83104542887813335429593749)
    ·
      refine ⟨3895525447866250098262207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83104542887813335429593749 3895525447866250098262207)
      ·
        refine ⟨5843288171799375147393311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895525447866250098262207 5843288171799375147393311)
        ·
          refine ⟨8764932257699062721089967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843288171799375147393311 8764932257699062721089967)
          ·
            refine ⟨13147398386548594081634951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8764932257699062721089967 13147398386548594081634951)
            ·
              refine ⟨19721097579822891122452427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13147398386548594081634951 19721097579822891122452427)
              ·
                refine ⟨29581646369734336683678641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19721097579822891122452427 29581646369734336683678641)
                ·
                  refine ⟨22186234777300752512758981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29581646369734336683678641 22186234777300752512758981)
                  ·
                    refine ⟨4159919020743891096142309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22186234777300752512758981 4159919020743891096142309)
                    ·
                      refine ⟨779984816389479580526683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4159919020743891096142309 779984816389479580526683)
                      ·
                        rfl

theorem cell23_1519015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1519015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519015 prefixEnd_1519015 := by exact prefixLift 1519015
  have htrace : WordTrace (prefixWord ++ tailWord_1519015) baseStart_1519015 baseEnd_1519015 := by
    simpa [prefixWord, tailWord_1519015, baseEnd_1519015] using wordTrace_append hprefix tailTrace_1519015
  have hstable : (prefixWord ++ tailWord_1519015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519015).length < 2 ^ (prefixWord ++ tailWord_1519015).sum := by decide
  have hdescent : baseEnd_1519015 < baseStart_1519015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519079 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1519079 : Nat := 118140960795 + 1519079 * 2 ^ 59
def prefixEnd_1519079 : Nat := 4983230072969 + 3 ^ 40 * 1519079 * 2
def baseEnd_1519079 : Nat := 780017679151367330126389

theorem tailTrace_1519079 : CollatzResearch.WordTrace tailWord_1519079 prefixEnd_1519079 780017679151367330126389 := by
  unfold tailWord_1519079
  simp only [CollatzResearch.WordTrace]
  refine ⟨55405362863643695883392291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36936908575762463922261527 55405362863643695883392291)
  ·
    refine ⟨83108044295465543825088437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55405362863643695883392291 83108044295465543825088437)
    ·
      refine ⟨7791379152699894733602041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83108044295465543825088437 7791379152699894733602041)
      ·
        refine ⟨5843534364524921050201531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7791379152699894733602041 5843534364524921050201531)
        ·
          refine ⟨8765301546787381575302297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843534364524921050201531 8765301546787381575302297)
          ·
            refine ⟨6573976160090536181476723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8765301546787381575302297 6573976160090536181476723)
            ·
              refine ⟨9860964240135804272215085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6573976160090536181476723 9860964240135804272215085)
              ·
                refine ⟨3697861590050926602080657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9860964240135804272215085 3697861590050926602080657)
                ·
                  refine ⟨2773396192538194951560493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3697861590050926602080657 2773396192538194951560493)
                  ·
                    refine ⟨1040023572201823106835185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773396192538194951560493 1040023572201823106835185)
                    ·
                      refine ⟨780017679151367330126389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040023572201823106835185 780017679151367330126389)
                      ·
                        rfl

theorem cell23_1519079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1519079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519079 prefixEnd_1519079 := by exact prefixLift 1519079
  have htrace : WordTrace (prefixWord ++ tailWord_1519079) baseStart_1519079 baseEnd_1519079 := by
    simpa [prefixWord, tailWord_1519079, baseEnd_1519079] using wordTrace_append hprefix tailTrace_1519079
  have hstable : (prefixWord ++ tailWord_1519079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519079).length < 2 ^ (prefixWord ++ tailWord_1519079).sum := by decide
  have hdescent : baseEnd_1519079 < baseStart_1519079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519086 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_1519086 : Nat := 118140960795 + 1519086 * 2 ^ 59
def prefixEnd_1519086 : Nat := 4983230072969 + 3 ^ 40 * 1519086 * 2
def baseEnd_1519086 : Nat := 780021273515948802738857

theorem tailTrace_1519086 : CollatzResearch.WordTrace tailWord_1519086 prefixEnd_1519086 780021273515948802738857 := by
  unfold tailWord_1519086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6925702271827292009862139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36937078783078890719264741 6925702271827292009862139)
  ·
    refine ⟨10388553407740938014793209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6925702271827292009862139 10388553407740938014793209)
    ·
      refine ⟨7791415055805703511094907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10388553407740938014793209 7791415055805703511094907)
      ·
        refine ⟨11687122583708555266642361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7791415055805703511094907 11687122583708555266642361)
        ·
          refine ⟨8765341937781416449981771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11687122583708555266642361 8765341937781416449981771)
          ·
            refine ⟨13148012906672124674972657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765341937781416449981771 13148012906672124674972657)
            ·
              refine ⟨9861009680004093506229493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13148012906672124674972657 9861009680004093506229493)
              ·
                refine ⟨924469657500383766209015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9861009680004093506229493 924469657500383766209015)
                ·
                  refine ⟨1386704486250575649313523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924469657500383766209015 1386704486250575649313523)
                  ·
                    refine ⟨2080056729375863473970285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1386704486250575649313523 2080056729375863473970285)
                    ·
                      refine ⟨780021273515948802738857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080056729375863473970285 780021273515948802738857)
                      ·
                        rfl

theorem cell23_1519086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_1519086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519086 prefixEnd_1519086 := by exact prefixLift 1519086
  have htrace : WordTrace (prefixWord ++ tailWord_1519086) baseStart_1519086 baseEnd_1519086 := by
    simpa [prefixWord, tailWord_1519086, baseEnd_1519086] using wordTrace_append hprefix tailTrace_1519086
  have hstable : (prefixWord ++ tailWord_1519086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519086).length < 2 ^ (prefixWord ++ tailWord_1519086).sum := by decide
  have hdescent : baseEnd_1519086 < baseStart_1519086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519089 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 1, 5]
def baseStart_1519089 : Nat := 118140960795 + 1519089 * 2 ^ 59
def prefixEnd_1519089 : Nat := 4983230072969 + 3 ^ 40 * 1519089 * 2
def baseEnd_1519089 : Nat := 260007604652637430333781

theorem tailTrace_1519089 : CollatzResearch.WordTrace tailWord_1519089 prefixEnd_1519089 260007604652637430333781 := by
  unfold tailWord_1519089
  simp only [CollatzResearch.WordTrace]
  refine ⟨55405727593607467591256321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36937151729071645060837547 55405727593607467591256321)
  ·
    refine ⟨41554295695205600693442241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55405727593607467591256321 41554295695205600693442241)
    ·
      refine ⟨31165721771404200520081681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41554295695205600693442241 31165721771404200520081681)
      ·
        refine ⟨23374291328553150390061261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31165721771404200520081681 23374291328553150390061261)
        ·
          refine ⟨8765359248207431396272973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23374291328553150390061261 8765359248207431396272973)
          ·
            refine ⟨3287009718077786773602365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8765359248207431396272973 3287009718077786773602365)
            ·
              refine ⟨1232628644279170040100887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3287009718077786773602365 1232628644279170040100887)
              ·
                refine ⟨1848942966418755060151331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232628644279170040100887 1848942966418755060151331)
                ·
                  refine ⟨2773414449628132590226997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848942966418755060151331 2773414449628132590226997)
                  ·
                    refine ⟨260007604652637430333781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2773414449628132590226997 260007604652637430333781)
                    ·
                      rfl

theorem cell23_1519089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_1519089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519089 prefixEnd_1519089 := by exact prefixLift 1519089
  have htrace : WordTrace (prefixWord ++ tailWord_1519089) baseStart_1519089 baseEnd_1519089 := by
    simpa [prefixWord, tailWord_1519089, baseEnd_1519089] using wordTrace_append hprefix tailTrace_1519089
  have hstable : (prefixWord ++ tailWord_1519089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519089).length < 2 ^ (prefixWord ++ tailWord_1519089).sum := by decide
  have hdescent : baseEnd_1519089 < baseStart_1519089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519095 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_1519095 : Nat := 118140960795 + 1519095 * 2 ^ 59
def prefixEnd_1519095 : Nat := 4983230072969 + 3 ^ 40 * 1519095 * 2
def baseEnd_1519095 : Nat := 780025894841839267526315

theorem tailTrace_1519095 : CollatzResearch.WordTrace tailWord_1519095 prefixEnd_1519095 780025894841839267526315 := by
  unfold tailWord_1519095
  simp only [CollatzResearch.WordTrace]
  refine ⟨55405946431585730615974739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36937297621057153743983159 55405946431585730615974739)
  ·
    refine ⟨83108919647378595923962109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55405946431585730615974739 83108919647378595923962109)
    ·
      refine ⟨31165844867766973471485791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83108919647378595923962109 31165844867766973471485791)
      ·
        refine ⟨46748767301650460207228687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31165844867766973471485791 46748767301650460207228687)
        ·
          refine ⟨70123150952475690310843031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46748767301650460207228687 70123150952475690310843031)
          ·
            refine ⟨105184726428713535466264547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70123150952475690310843031 105184726428713535466264547)
            ·
              refine ⟨157777089643070303199396821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105184726428713535466264547 157777089643070303199396821)
              ·
                refine ⟨3697900538509460231235863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157777089643070303199396821 3697900538509460231235863)
                ·
                  refine ⟨5546850807764190346853795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3697900538509460231235863 5546850807764190346853795)
                  ·
                    refine ⟨8320276211646285520280693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5546850807764190346853795 8320276211646285520280693)
                    ·
                      refine ⟨780025894841839267526315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8320276211646285520280693 780025894841839267526315)
                      ·
                        rfl

theorem cell23_1519095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_1519095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519095 prefixEnd_1519095 := by exact prefixLift 1519095
  have htrace : WordTrace (prefixWord ++ tailWord_1519095) baseStart_1519095 baseEnd_1519095 := by
    simpa [prefixWord, tailWord_1519095, baseEnd_1519095] using wordTrace_append hprefix tailTrace_1519095
  have hstable : (prefixWord ++ tailWord_1519095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519095).length < 2 ^ (prefixWord ++ tailWord_1519095).sum := by decide
  have hdescent : baseEnd_1519095 < baseStart_1519095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519109 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 3, 2, 2]
def baseStart_1519109 : Nat := 118140960795 + 1519109 * 2 ^ 59
def prefixEnd_1519109 : Nat := 4983230072969 + 3 ^ 40 * 1519109 * 2
def baseEnd_1519109 : Nat := 780033083571002212751251

theorem tailTrace_1519109 : CollatzResearch.WordTrace tailWord_1519109 prefixEnd_1519109 780033083571002212751251 := by
  unfold tailWord_1519109
  simp only [CollatzResearch.WordTrace]
  refine ⟨55406457053535011006984381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36937638035690007337989587 55406457053535011006984381)
  ·
    refine ⟨20777421395075629127619143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55406457053535011006984381 20777421395075629127619143)
    ·
      refine ⟨31166132092613443691428715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20777421395075629127619143 31166132092613443691428715)
      ·
        refine ⟨46749198138920165537143073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31166132092613443691428715 46749198138920165537143073)
        ·
          refine ⟨35061898604190124152857305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46749198138920165537143073 35061898604190124152857305)
          ·
            refine ⟨26296423953142593114642979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35061898604190124152857305 26296423953142593114642979)
            ·
              refine ⟨39444635929713889671964469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26296423953142593114642979 39444635929713889671964469)
              ·
                refine ⟨3697934618410677156746669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39444635929713889671964469 3697934618410677156746669)
                ·
                  refine ⟨1386725481904003933780001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3697934618410677156746669 1386725481904003933780001)
                  ·
                    refine ⟨1040044111428002950335001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386725481904003933780001 1040044111428002950335001)
                    ·
                      refine ⟨780033083571002212751251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040044111428002950335001 780033083571002212751251)
                      ·
                        rfl

theorem cell23_1519109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_1519109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519109 prefixEnd_1519109 := by exact prefixLift 1519109
  have htrace : WordTrace (prefixWord ++ tailWord_1519109) baseStart_1519109 baseEnd_1519109 := by
    simpa [prefixWord, tailWord_1519109, baseEnd_1519109] using wordTrace_append hprefix tailTrace_1519109
  have hstable : (prefixWord ++ tailWord_1519109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519109).length < 2 ^ (prefixWord ++ tailWord_1519109).sum := by decide
  have hdescent : baseEnd_1519109 < baseStart_1519109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519112 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1519112 : Nat := 118140960795 + 1519112 * 2 ^ 59
def prefixEnd_1519112 : Nat := 4983230072969 + 3 ^ 40 * 1519112 * 2
def baseEnd_1519112 : Nat := 780034624012965701013737

theorem tailTrace_1519112 : CollatzResearch.WordTrace tailWord_1519112 prefixEnd_1519112 780034624012965701013737 := by
  unfold tailWord_1519112
  simp only [CollatzResearch.WordTrace]
  refine ⟨27703283236262071259671795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36937710981682761679562393 27703283236262071259671795)
  ·
    refine ⟨41554924854393106889507693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27703283236262071259671795 41554924854393106889507693)
    ·
      refine ⟨15583096820397415083565385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41554924854393106889507693 15583096820397415083565385)
      ·
        refine ⟨11687322615298061312674039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15583096820397415083565385 11687322615298061312674039)
        ·
          refine ⟨17530983922947091969011059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11687322615298061312674039 17530983922947091969011059)
          ·
            refine ⟨26296475884420637953516589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17530983922947091969011059 26296475884420637953516589)
            ·
              refine ⟨9861178456657739232568721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26296475884420637953516589 9861178456657739232568721)
              ·
                refine ⟨7395883842493304424426541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9861178456657739232568721 7395883842493304424426541)
                ·
                  refine ⟨2773456440934989159159953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7395883842493304424426541 2773456440934989159159953)
                  ·
                    refine ⟨2080092330701241869369965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2773456440934989159159953 2080092330701241869369965)
                    ·
                      refine ⟨780034624012965701013737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080092330701241869369965 780034624012965701013737)
                      ·
                        rfl

theorem cell23_1519112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1519112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519112 prefixEnd_1519112 := by exact prefixLift 1519112
  have htrace : WordTrace (prefixWord ++ tailWord_1519112) baseStart_1519112 baseEnd_1519112 := by
    simpa [prefixWord, tailWord_1519112, baseEnd_1519112] using wordTrace_append hprefix tailTrace_1519112
  have hstable : (prefixWord ++ tailWord_1519112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519112).length < 2 ^ (prefixWord ++ tailWord_1519112).sum := by decide
  have hdescent : baseEnd_1519112 < baseStart_1519112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519132 : List Nat := [2, 2, 3, 1, 2, 1, 5, 7]
def baseStart_1519132 : Nat := 118140960795 + 1519132 * 2 ^ 59
def prefixEnd_1519132 : Nat := 4983230072969 + 3 ^ 40 * 1519132 * 2
def baseEnd_1519132 : Nat := 28890551615779837880135

theorem tailTrace_1519132 : CollatzResearch.WordTrace tailWord_1519132 prefixEnd_1519132 28890551615779837880135 := by
  unfold tailWord_1519132
  simp only [CollatzResearch.WordTrace]
  refine ⟨27703647966225842967535825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36938197288301123956714433 27703647966225842967535825)
  ·
    refine ⟨20777735974669382225651869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27703647966225842967535825 20777735974669382225651869)
    ·
      refine ⟨7791650990501018334619451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20777735974669382225651869 7791650990501018334619451)
      ·
        refine ⟨11687476485751527501929177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7791650990501018334619451 11687476485751527501929177)
        ·
          refine ⟨8765607364313645626446883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11687476485751527501929177 8765607364313645626446883)
          ·
            refine ⟨13148411046470468439670325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8765607364313645626446883 13148411046470468439670325)
            ·
              refine ⟨1232663535606606416219093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13148411046470468439670325 1232663535606606416219093)
              ·
                refine ⟨28890551615779837880135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1232663535606606416219093 28890551615779837880135)
                ·
                  rfl

theorem cell23_1519132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 7].length) (baseStart_1519132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519132 prefixEnd_1519132 := by exact prefixLift 1519132
  have htrace : WordTrace (prefixWord ++ tailWord_1519132) baseStart_1519132 baseEnd_1519132 := by
    simpa [prefixWord, tailWord_1519132, baseEnd_1519132] using wordTrace_append hprefix tailTrace_1519132
  have hstable : (prefixWord ++ tailWord_1519132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519132).length < 2 ^ (prefixWord ++ tailWord_1519132).sum := by decide
  have hdescent : baseEnd_1519132 < baseStart_1519132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519159 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_1519159 : Nat := 118140960795 + 1519159 * 2 ^ 59
def prefixEnd_1519159 : Nat := 4983230072969 + 3 ^ 40 * 1519159 * 2
def baseEnd_1519159 : Nat := 780058757603727017126021

theorem tailTrace_1519159 : CollatzResearch.WordTrace tailWord_1519159 prefixEnd_1519159 780058757603727017126021 := by
  unfold tailWord_1519159
  simp only [CollatzResearch.WordTrace]
  refine ⟨55408280703353869546304531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36938853802235913030869687 55408280703353869546304531)
  ·
    refine ⟨83112421055030804319456797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55408280703353869546304531 83112421055030804319456797)
    ·
      refine ⟨31167157895636551619796299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83112421055030804319456797 31167157895636551619796299)
      ·
        refine ⟨46750736843454827429694449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31167157895636551619796299 46750736843454827429694449)
        ·
          refine ⟨35063052632591120572270837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46750736843454827429694449 35063052632591120572270837)
          ·
            refine ⟨3287161184305417553650391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35063052632591120572270837 3287161184305417553650391)
            ·
              refine ⟨4930741776458126330475587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287161184305417553650391 4930741776458126330475587)
              ·
                refine ⟨7396112664687189495713381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930741776458126330475587 7396112664687189495713381)
                ·
                  refine ⟨1386771124628848030446259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7396112664687189495713381 1386771124628848030446259)
                  ·
                    refine ⟨2080156686943272045669389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1386771124628848030446259 2080156686943272045669389)
                    ·
                      refine ⟨780058757603727017126021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080156686943272045669389 780058757603727017126021)
                      ·
                        rfl

theorem cell23_1519159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_1519159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519159 prefixEnd_1519159 := by exact prefixLift 1519159
  have htrace : WordTrace (prefixWord ++ tailWord_1519159) baseStart_1519159 baseEnd_1519159 := by
    simpa [prefixWord, tailWord_1519159, baseEnd_1519159] using wordTrace_append hprefix tailTrace_1519159
  have hstable : (prefixWord ++ tailWord_1519159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519159).length < 2 ^ (prefixWord ++ tailWord_1519159).sum := by decide
  have hdescent : baseEnd_1519159 < baseStart_1519159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519186 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_1519186 : Nat := 118140960795 + 1519186 * 2 ^ 59
def prefixEnd_1519186 : Nat := 4983230072969 + 3 ^ 40 * 1519186 * 2
def baseEnd_1519186 : Nat := 780072621581398411488397

theorem tailTrace_1519186 : CollatzResearch.WordTrace tailWord_1519186 prefixEnd_1519186 780072621581398411488397 := by
  unfold tailWord_1519186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852316368564013289384353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36939510316170702105024941 13852316368564013289384353)
  ·
    refine ⟨10389237276423009967038265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13852316368564013289384353 10389237276423009967038265)
    ·
      refine ⟨7791927957317257475278699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10389237276423009967038265 7791927957317257475278699)
      ·
        refine ⟨11687891935975886212918049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7791927957317257475278699 11687891935975886212918049)
        ·
          refine ⟨8765918951981914659688537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11687891935975886212918049 8765918951981914659688537)
          ·
            refine ⟨6574439213986435994766403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8765918951981914659688537 6574439213986435994766403)
            ·
              refine ⟨9861658820979653992149605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574439213986435994766403 9861658820979653992149605)
              ·
                refine ⟨1849061028933685123528051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9861658820979653992149605 1849061028933685123528051)
                ·
                  refine ⟨2773591543400527685292077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849061028933685123528051 2773591543400527685292077)
                  ·
                    refine ⟨1040096828775197881984529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773591543400527685292077 1040096828775197881984529)
                    ·
                      refine ⟨780072621581398411488397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040096828775197881984529 780072621581398411488397)
                      ·
                        rfl

theorem cell23_1519186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_1519186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519186 prefixEnd_1519186 := by exact prefixLift 1519186
  have htrace : WordTrace (prefixWord ++ tailWord_1519186) baseStart_1519186 baseEnd_1519186 := by
    simpa [prefixWord, tailWord_1519186, baseEnd_1519186] using wordTrace_append hprefix tailTrace_1519186
  have hstable : (prefixWord ++ tailWord_1519186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519186).length < 2 ^ (prefixWord ++ tailWord_1519186).sum := by decide
  have hdescent : baseEnd_1519186 < baseStart_1519186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519215 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_1519215 : Nat := 118140960795 + 1519215 * 2 ^ 59
def prefixEnd_1519215 : Nat := 4983230072969 + 3 ^ 40 * 1519215 * 2
def baseEnd_1519215 : Nat := 780087512520378798025763

theorem tailTrace_1519215 : CollatzResearch.WordTrace tailWord_1519215 prefixEnd_1519215 780087512520378798025763 := by
  unfold tailWord_1519215
  simp only [CollatzResearch.WordTrace]
  refine ⟨55410323191150991110343099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36940215460767327406895399 55410323191150991110343099)
  ·
    refine ⟨83115484786726486665514649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55410323191150991110343099 83115484786726486665514649)
    ·
      refine ⟨62336613590044864999135987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83115484786726486665514649 62336613590044864999135987)
      ·
        refine ⟨93504920385067297498703981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62336613590044864999135987 93504920385067297498703981)
        ·
          refine ⟨35064345144400236562013993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93504920385067297498703981 35064345144400236562013993)
          ·
            refine ⟨26298258858300177421510495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35064345144400236562013993 26298258858300177421510495)
            ·
              refine ⟨39447388287450266132265743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26298258858300177421510495 39447388287450266132265743)
              ·
                refine ⟨59171082431175399198398615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39447388287450266132265743 59171082431175399198398615)
                ·
                  refine ⟨88756623646763098797597923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59171082431175399198398615 88756623646763098797597923)
                  ·
                    refine ⟨133134935470144648196396885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88756623646763098797597923 133134935470144648196396885)
                    ·
                      refine ⟨780087512520378798025763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 133134935470144648196396885 780087512520378798025763)
                      ·
                        rfl

theorem cell23_1519215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_1519215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519215 prefixEnd_1519215 := by exact prefixLift 1519215
  have htrace : WordTrace (prefixWord ++ tailWord_1519215) baseStart_1519215 baseEnd_1519215 := by
    simpa [prefixWord, tailWord_1519215, baseEnd_1519215] using wordTrace_append hprefix tailTrace_1519215
  have hstable : (prefixWord ++ tailWord_1519215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519215).length < 2 ^ (prefixWord ++ tailWord_1519215).sum := by decide
  have hdescent : baseEnd_1519215 < baseStart_1519215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519216 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 4, 2, 2]
def baseStart_1519216 : Nat := 118140960795 + 1519216 * 2 ^ 59
def prefixEnd_1519216 : Nat := 4983230072969 + 3 ^ 40 * 1519216 * 2
def baseEnd_1519216 : Nat := 780088026001033294113259

theorem tailTrace_1519216 : CollatzResearch.WordTrace tailWord_1519216 prefixEnd_1519216 780088026001033294113259 := by
  unfold tailWord_1519216
  simp only [CollatzResearch.WordTrace]
  refine ⟨27705179832073684140564751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36940239776098245520753001 27705179832073684140564751)
  ·
    refine ⟨41557769748110526210847127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27705179832073684140564751 41557769748110526210847127)
    ·
      refine ⟨62336654622165789316270691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41557769748110526210847127 62336654622165789316270691)
      ·
        refine ⟨93504981933248683974406037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62336654622165789316270691 93504981933248683974406037)
        ·
          refine ⟨4383046028121032061300283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93504981933248683974406037 4383046028121032061300283)
          ·
            refine ⟨6574569042181548091950425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383046028121032061300283 6574569042181548091950425)
            ·
              refine ⟨4930926781636161068962819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6574569042181548091950425 4930926781636161068962819)
              ·
                refine ⟨7396390172454241603444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930926781636161068962819 7396390172454241603444229)
                ·
                  refine ⟨1386823157335170300645793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7396390172454241603444229 1386823157335170300645793)
                  ·
                    refine ⟨1040117368001377725484345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386823157335170300645793 1040117368001377725484345)
                    ·
                      refine ⟨780088026001033294113259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040117368001377725484345 780088026001033294113259)
                      ·
                        rfl

theorem cell23_1519216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 2, 2].length) (baseStart_1519216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519216 prefixEnd_1519216 := by exact prefixLift 1519216
  have htrace : WordTrace (prefixWord ++ tailWord_1519216) baseStart_1519216 baseEnd_1519216 := by
    simpa [prefixWord, tailWord_1519216, baseEnd_1519216] using wordTrace_append hprefix tailTrace_1519216
  have hstable : (prefixWord ++ tailWord_1519216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519216).length < 2 ^ (prefixWord ++ tailWord_1519216).sum := by decide
  have hdescent : baseEnd_1519216 < baseStart_1519216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519232 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_1519232 : Nat := 118140960795 + 1519232 * 2 ^ 59
def prefixEnd_1519232 : Nat := 4983230072969 + 3 ^ 40 * 1519232 * 2
def baseEnd_1519232 : Nat := 780096241691505231513185

theorem tailTrace_1519232 : CollatzResearch.WordTrace tailWord_1519232 prefixEnd_1519232 780096241691505231513185 := by
  unfold tailWord_1519232
  simp only [CollatzResearch.WordTrace]
  refine ⟨27705471616044701506855975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36940628821392935342474633 27705471616044701506855975)
  ·
    refine ⟨41558207424067052260283963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27705471616044701506855975 41558207424067052260283963)
    ·
      refine ⟨62337311136100578390425945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41558207424067052260283963 62337311136100578390425945)
      ·
        refine ⟨46752983352075433792819459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62337311136100578390425945 46752983352075433792819459)
        ·
          refine ⟨70129475028113150689229189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46752983352075433792819459 70129475028113150689229189)
          ·
            refine ⟨13149276567771215754230473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70129475028113150689229189 13149276567771215754230473)
            ·
              refine ⟨9861957425828411815672855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13149276567771215754230473 9861957425828411815672855)
              ·
                refine ⟨14792936138742617723509283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9861957425828411815672855 14792936138742617723509283)
                ·
                  refine ⟨22189404208113926585263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14792936138742617723509283 22189404208113926585263925)
                  ·
                    refine ⟨2080256644510680617368493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22189404208113926585263925 2080256644510680617368493)
                    ·
                      refine ⟨780096241691505231513185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080256644510680617368493 780096241691505231513185)
                      ·
                        rfl

theorem cell23_1519232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_1519232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519232 prefixEnd_1519232 := by exact prefixLift 1519232
  have htrace : WordTrace (prefixWord ++ tailWord_1519232) baseStart_1519232 baseEnd_1519232 := by
    simpa [prefixWord, tailWord_1519232, baseEnd_1519232] using wordTrace_append hprefix tailTrace_1519232
  have hstable : (prefixWord ++ tailWord_1519232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519232).length < 2 ^ (prefixWord ++ tailWord_1519232).sum := by decide
  have hdescent : baseEnd_1519232 < baseStart_1519232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519233 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_1519233 : Nat := 118140960795 + 1519233 * 2 ^ 59
def prefixEnd_1519233 : Nat := 4983230072969 + 3 ^ 40 * 1519233 * 2
def baseEnd_1519233 : Nat := 780096755172159727600681

theorem tailTrace_1519233 : CollatzResearch.WordTrace tailWord_1519233 prefixEnd_1519233 780096755172159727600681 := by
  unfold tailWord_1519233
  simp only [CollatzResearch.WordTrace]
  refine ⟨55410979705085780184498353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36940653136723853456332235 55410979705085780184498353)
  ·
    refine ⟨41558234778814335138373765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55410979705085780184498353 41558234778814335138373765)
    ·
      refine ⟨7792169021027687838445081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41558234778814335138373765 7792169021027687838445081)
      ·
        refine ⟨5844126765770765878833811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7792169021027687838445081 5844126765770765878833811)
        ·
          refine ⟨8766190148656148818250717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5844126765770765878833811 8766190148656148818250717)
          ·
            refine ⟨3287321305746055806844019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8766190148656148818250717 3287321305746055806844019)
            ·
              refine ⟨4930981958619083710266029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287321305746055806844019 4930981958619083710266029)
              ·
                refine ⟨1849118234482156391349761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4930981958619083710266029 1849118234482156391349761)
                ·
                  refine ⟨1386838675861617293512321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1849118234482156391349761 1386838675861617293512321)
                  ·
                    refine ⟨1040129006896212970134241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1386838675861617293512321 1040129006896212970134241)
                    ·
                      refine ⟨780096755172159727600681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040129006896212970134241 780096755172159727600681)
                      ·
                        rfl

theorem cell23_1519233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_1519233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519233 prefixEnd_1519233 := by exact prefixLift 1519233
  have htrace : WordTrace (prefixWord ++ tailWord_1519233) baseStart_1519233 baseEnd_1519233 := by
    simpa [prefixWord, tailWord_1519233, baseEnd_1519233] using wordTrace_append hprefix tailTrace_1519233
  have hstable : (prefixWord ++ tailWord_1519233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519233).length < 2 ^ (prefixWord ++ tailWord_1519233).sum := by decide
  have hdescent : baseEnd_1519233 < baseStart_1519233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519289 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1519289 : Nat := 118140960795 + 1519289 * 2 ^ 59
def prefixEnd_1519289 : Nat := 4983230072969 + 3 ^ 40 * 1519289 * 2
def baseEnd_1519289 : Nat := 780125510088811508500423

theorem tailTrace_1519289 : CollatzResearch.WordTrace tailWord_1519289 prefixEnd_1519289 780125510088811508500423 := by
  unfold tailWord_1519289
  simp only [CollatzResearch.WordTrace]
  refine ⟨55413022192882901748536921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36942014795255267832357947 55413022192882901748536921)
  ·
    refine ⟨41559766644662176311402691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55413022192882901748536921 41559766644662176311402691)
    ·
      refine ⟨62339649966993264467104037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41559766644662176311402691 62339649966993264467104037)
      ·
        refine ⟨11688684368811237087582007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62339649966993264467104037 11688684368811237087582007)
        ·
          refine ⟨17533026553216855631373011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11688684368811237087582007 17533026553216855631373011)
          ·
            refine ⟨26299539829825283447059517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17533026553216855631373011 26299539829825283447059517)
            ·
              refine ⟨9862327436184481292647319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26299539829825283447059517 9862327436184481292647319)
              ·
                refine ⟨14793491154276721938970979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9862327436184481292647319 14793491154276721938970979)
                ·
                  refine ⟨22190236731415082908456469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14793491154276721938970979 22190236731415082908456469)
                  ·
                    refine ⟨1040167346785082011333897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22190236731415082908456469 1040167346785082011333897)
                    ·
                      refine ⟨780125510088811508500423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040167346785082011333897 780125510088811508500423)
                      ·
                        rfl

theorem cell23_1519289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1519289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519289 prefixEnd_1519289 := by exact prefixLift 1519289
  have htrace : WordTrace (prefixWord ++ tailWord_1519289) baseStart_1519289 baseEnd_1519289 := by
    simpa [prefixWord, tailWord_1519289, baseEnd_1519289] using wordTrace_append hprefix tailTrace_1519289
  have hstable : (prefixWord ++ tailWord_1519289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519289).length < 2 ^ (prefixWord ++ tailWord_1519289).sum := by decide
  have hdescent : baseEnd_1519289 < baseStart_1519289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519329 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 8]
def baseStart_1519329 : Nat := 118140960795 + 1519329 * 2 ^ 59
def prefixEnd_1519329 : Nat := 4983230072969 + 3 ^ 40 * 1519329 * 2
def baseEnd_1519329 : Nat := 86682894368332372444471

theorem tailTrace_1519329 : CollatzResearch.WordTrace tailWord_1519329 prefixEnd_1519329 86682894368332372444471 := by
  unfold tailWord_1519329
  simp only [CollatzResearch.WordTrace]
  refine ⟨55414481112737988579993041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36942987408491992386662027 55414481112737988579993041)
  ·
    refine ⟨41560860834553491434994781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55414481112737988579993041 41560860834553491434994781)
    ·
      refine ⟨15585322812957559288123043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41560860834553491434994781 15585322812957559288123043)
      ·
        refine ⟨23377984219436338932184565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15585322812957559288123043 23377984219436338932184565)
        ·
          refine ⟨2191686020572156774892303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23377984219436338932184565 2191686020572156774892303)
          ·
            refine ⟨3287529030858235162338455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191686020572156774892303 3287529030858235162338455)
            ·
              refine ⟨4931293546287352743507683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287529030858235162338455 4931293546287352743507683)
              ·
                refine ⟨7396940319431029115261525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931293546287352743507683 7396940319431029115261525)
                ·
                  refine ⟨86682894368332372444471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7396940319431029115261525 86682894368332372444471)
                  ·
                    rfl

theorem cell23_1519329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 8].length) (baseStart_1519329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519329 prefixEnd_1519329 := by exact prefixLift 1519329
  have htrace : WordTrace (prefixWord ++ tailWord_1519329) baseStart_1519329 baseEnd_1519329 := by
    simpa [prefixWord, tailWord_1519329, baseEnd_1519329] using wordTrace_append hprefix tailTrace_1519329
  have hstable : (prefixWord ++ tailWord_1519329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519329).length < 2 ^ (prefixWord ++ tailWord_1519329).sum := by decide
  have hdescent : baseEnd_1519329 < baseStart_1519329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519332 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_1519332 : Nat := 118140960795 + 1519332 * 2 ^ 59
def prefixEnd_1519332 : Nat := 4983230072969 + 3 ^ 40 * 1519332 * 2
def baseEnd_1519332 : Nat := 780147589756954840262725

theorem tailTrace_1519332 : CollatzResearch.WordTrace tailWord_1519332 prefixEnd_1519332 780147589756954840262725 := by
  unfold tailWord_1519332
  simp only [CollatzResearch.WordTrace]
  refine ⟨27707295265863560046176125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36943060354484746728234833 27707295265863560046176125)
  ·
    refine ⟨10390235724698835017316047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27707295265863560046176125 10390235724698835017316047)
    ·
      refine ⟨15585353587048252525974071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10390235724698835017316047 15585353587048252525974071)
      ·
        refine ⟨23378030380572378788961107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15585353587048252525974071 23378030380572378788961107)
        ·
          refine ⟨35067045570858568183441661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23378030380572378788961107 35067045570858568183441661)
          ·
            refine ⟨13150142089071963068790623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35067045570858568183441661 13150142089071963068790623)
            ·
              refine ⟨19725213133607944603185935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13150142089071963068790623 19725213133607944603185935)
              ·
                refine ⟨29587819700411916904778903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19725213133607944603185935 29587819700411916904778903)
                ·
                  refine ⟨44381729550617875357168355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29587819700411916904778903 44381729550617875357168355)
                  ·
                    refine ⟨66572594325926813035752533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44381729550617875357168355 66572594325926813035752533)
                    ·
                      refine ⟨780147589756954840262725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66572594325926813035752533 780147589756954840262725)
                      ·
                        rfl

theorem cell23_1519332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_1519332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519332 prefixEnd_1519332 := by exact prefixLift 1519332
  have htrace : WordTrace (prefixWord ++ tailWord_1519332) baseStart_1519332 baseEnd_1519332 := by
    simpa [prefixWord, tailWord_1519332, baseEnd_1519332] using wordTrace_append hprefix tailTrace_1519332
  have hstable : (prefixWord ++ tailWord_1519332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519332).length < 2 ^ (prefixWord ++ tailWord_1519332).sum := by decide
  have hdescent : baseEnd_1519332 < baseStart_1519332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519346 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_1519346 : Nat := 118140960795 + 1519346 * 2 ^ 59
def prefixEnd_1519346 : Nat := 4983230072969 + 3 ^ 40 * 1519346 * 2
def baseEnd_1519346 : Nat := 86683864276235309498629

theorem tailTrace_1519346 : CollatzResearch.WordTrace tailWord_1519346 prefixEnd_1519346 86683864276235309498629 := by
  unfold tailWord_1519346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13853775288419100120840473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36943400769117600322241261 13853775288419100120840473)
  ·
    refine ⟨10390331466314325090630355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13853775288419100120840473 10390331466314325090630355)
    ·
      refine ⟨15585497199471487635945533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10390331466314325090630355 15585497199471487635945533)
      ·
        refine ⟨5844561449801807863479575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15585497199471487635945533 5844561449801807863479575)
        ·
          refine ⟨8766842174702711795219363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5844561449801807863479575 8766842174702711795219363)
          ·
            refine ⟨13150263262054067692829045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766842174702711795219363 13150263262054067692829045)
            ·
              refine ⟨1232837180817568846202723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13150263262054067692829045 1232837180817568846202723)
              ·
                refine ⟨1849255771226353269304085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232837180817568846202723 1849255771226353269304085)
                ·
                  refine ⟨86683864276235309498629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1849255771226353269304085 86683864276235309498629)
                  ·
                    rfl

theorem cell23_1519346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_1519346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519346 prefixEnd_1519346 := by exact prefixLift 1519346
  have htrace : WordTrace (prefixWord ++ tailWord_1519346) baseStart_1519346 baseEnd_1519346 := by
    simpa [prefixWord, tailWord_1519346, baseEnd_1519346] using wordTrace_append hprefix tailTrace_1519346
  have hstable : (prefixWord ++ tailWord_1519346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519346).length < 2 ^ (prefixWord ++ tailWord_1519346).sum := by decide
  have hdescent : baseEnd_1519346 < baseStart_1519346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519356 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_1519356 : Nat := 118140960795 + 1519356 * 2 ^ 59
def prefixEnd_1519356 : Nat := 4983230072969 + 3 ^ 40 * 1519356 * 2
def baseEnd_1519356 : Nat := 780159913292662746362615

theorem tailTrace_1519356 : CollatzResearch.WordTrace tailWord_1519356 prefixEnd_1519356 780159913292662746362615 := by
  unfold tailWord_1519356
  simp only [CollatzResearch.WordTrace]
  refine ⟨27707732941820086095612961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36943643922426781460817281 27707732941820086095612961)
  ·
    refine ⟨20780799706365064571709721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27707732941820086095612961 20780799706365064571709721)
    ·
      refine ⟨15585599779773798428782291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20780799706365064571709721 15585599779773798428782291)
      ·
        refine ⟨23378399669660697643173437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15585599779773798428782291 23378399669660697643173437)
        ·
          refine ⟨8766899876122761616190039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23378399669660697643173437 8766899876122761616190039)
          ·
            refine ⟨13150349814184142424285059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8766899876122761616190039 13150349814184142424285059)
            ·
              refine ⟨19725524721276213636427589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13150349814184142424285059 19725524721276213636427589)
              ·
                refine ⟨3698535885239290056830173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19725524721276213636427589 3698535885239290056830173)
                ·
                  refine ⟨1386950956964733771311315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3698535885239290056830173 1386950956964733771311315)
                  ·
                    refine ⟨2080426435447100656966973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1386950956964733771311315 2080426435447100656966973)
                    ·
                      refine ⟨780159913292662746362615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080426435447100656966973 780159913292662746362615)
                      ·
                        rfl

theorem cell23_1519356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_1519356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519356 prefixEnd_1519356 := by exact prefixLift 1519356
  have htrace : WordTrace (prefixWord ++ tailWord_1519356) baseStart_1519356 baseEnd_1519356 := by
    simpa [prefixWord, tailWord_1519356, baseEnd_1519356] using wordTrace_append hprefix tailTrace_1519356
  have hstable : (prefixWord ++ tailWord_1519356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519356).length < 2 ^ (prefixWord ++ tailWord_1519356).sum := by decide
  have hdescent : baseEnd_1519356 < baseStart_1519356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519359 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 1, 5]
def baseStart_1519359 : Nat := 118140960795 + 1519359 * 2 ^ 59
def prefixEnd_1519359 : Nat := 4983230072969 + 3 ^ 40 * 1519359 * 2
def baseEnd_1519359 : Nat := 260053817911542078208367

theorem tailTrace_1519359 : CollatzResearch.WordTrace tailWord_1519359 prefixEnd_1519359 260053817911542078208367 := by
  unfold tailWord_1519359
  simp only [CollatzResearch.WordTrace]
  refine ⟨55415575302629303703585131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36943716868419535802390087 55415575302629303703585131)
  ·
    refine ⟨83123362953943955555377697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55415575302629303703585131 83123362953943955555377697)
    ·
      refine ⟨62342522215457966666533273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83123362953943955555377697 62342522215457966666533273)
      ·
        refine ⟨46756891661593474999899955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62342522215457966666533273 46756891661593474999899955)
        ·
          refine ⟨70135337492390212499849933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46756891661593474999899955 70135337492390212499849933)
          ·
            refine ⟨26300751559646329687443725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70135337492390212499849933 26300751559646329687443725)
            ·
              refine ⟨9862781834867373632791397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26300751559646329687443725 9862781834867373632791397)
              ·
                refine ⟨1849271594037632556148387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9862781834867373632791397 1849271594037632556148387)
                ·
                  refine ⟨2773907391056448834222581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849271594037632556148387 2773907391056448834222581)
                  ·
                    refine ⟨260053817911542078208367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2773907391056448834222581 260053817911542078208367)
                    ·
                      rfl

theorem cell23_1519359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_1519359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519359 prefixEnd_1519359 := by exact prefixLift 1519359
  have htrace : WordTrace (prefixWord ++ tailWord_1519359) baseStart_1519359 baseEnd_1519359 := by
    simpa [prefixWord, tailWord_1519359, baseEnd_1519359] using wordTrace_append hprefix tailTrace_1519359
  have hstable : (prefixWord ++ tailWord_1519359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519359).length < 2 ^ (prefixWord ++ tailWord_1519359).sum := by decide
  have hdescent : baseEnd_1519359 < baseStart_1519359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519367 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 1, 4]
def baseStart_1519367 : Nat := 118140960795 + 1519367 * 2 ^ 59
def prefixEnd_1519367 : Nat := 4983230072969 + 3 ^ 40 * 1519367 * 2
def baseEnd_1519367 : Nat := 260055187193287401108355

theorem tailTrace_1519367 : CollatzResearch.WordTrace tailWord_1519367 prefixEnd_1519367 260055187193287401108355 := by
  unfold tailWord_1519367
  simp only [CollatzResearch.WordTrace]
  refine ⟨55415867086600321069876355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36943911391066880713250903 55415867086600321069876355)
  ·
    refine ⟨83123800629900481604814533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55415867086600321069876355 83123800629900481604814533)
    ·
      refine ⟨15585712618106340300902725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83123800629900481604814533 15585712618106340300902725)
      ·
        refine ⟨2922321115894938806419261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15585712618106340300902725 2922321115894938806419261)
        ·
          refine ⟨1095870418460602052407223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2922321115894938806419261 1095870418460602052407223)
          ·
            refine ⟨1643805627690903078610835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095870418460602052407223 1643805627690903078610835)
            ·
              refine ⟨2465708441536354617916253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643805627690903078610835 2465708441536354617916253)
              ·
                refine ⟨924640665576132981718595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2465708441536354617916253 924640665576132981718595)
                ·
                  refine ⟨1386960998364199472577893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924640665576132981718595 1386960998364199472577893)
                  ·
                    refine ⟨260055187193287401108355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1386960998364199472577893 260055187193287401108355)
                    ·
                      rfl

theorem cell23_1519367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_1519367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519367 prefixEnd_1519367 := by exact prefixLift 1519367
  have htrace : WordTrace (prefixWord ++ tailWord_1519367) baseStart_1519367 baseEnd_1519367 := by
    simpa [prefixWord, tailWord_1519367, baseEnd_1519367] using wordTrace_append hprefix tailTrace_1519367
  have hstable : (prefixWord ++ tailWord_1519367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519367).length < 2 ^ (prefixWord ++ tailWord_1519367).sum := by decide
  have hdescent : baseEnd_1519367 < baseStart_1519367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519383 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 2, 3, 2]
def baseStart_1519383 : Nat := 118140960795 + 1519383 * 2 ^ 59
def prefixEnd_1519383 : Nat := 4983230072969 + 3 ^ 40 * 1519383 * 2
def baseEnd_1519383 : Nat := 780173777270334140724991

theorem tailTrace_1519383 : CollatzResearch.WordTrace tailWord_1519383 prefixEnd_1519383 780173777270334140724991 := by
  unfold tailWord_1519383
  simp only [CollatzResearch.WordTrace]
  refine ⟨55416450654542355802458803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36944300436361570534972535 55416450654542355802458803)
  ·
    refine ⟨83124675981813533703688205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55416450654542355802458803 83124675981813533703688205)
    ·
      refine ⟨31171753493180075138883077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83124675981813533703688205 31171753493180075138883077)
      ·
        refine ⟨5844703779971264088540577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31171753493180075138883077 5844703779971264088540577)
        ·
          refine ⟨4383527834978448066405433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5844703779971264088540577 4383527834978448066405433)
          ·
            refine ⟨3287645876233836049804075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4383527834978448066405433 3287645876233836049804075)
            ·
              refine ⟨4931468814350754074706113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287645876233836049804075 4931468814350754074706113)
              ·
                refine ⟨3698601610763065556029585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931468814350754074706113 3698601610763065556029585)
                ·
                  refine ⟨2773951208072299167022189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698601610763065556029585 2773951208072299167022189)
                  ·
                    refine ⟨1040231703027112187633321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2773951208072299167022189 1040231703027112187633321)
                    ·
                      refine ⟨780173777270334140724991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040231703027112187633321 780173777270334140724991)
                      ·
                        rfl

theorem cell23_1519383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_1519383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519383 prefixEnd_1519383 := by exact prefixLift 1519383
  have htrace : WordTrace (prefixWord ++ tailWord_1519383) baseStart_1519383 baseEnd_1519383 := by
    simpa [prefixWord, tailWord_1519383, baseEnd_1519383] using wordTrace_append hprefix tailTrace_1519383
  have hstable : (prefixWord ++ tailWord_1519383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519383).length < 2 ^ (prefixWord ++ tailWord_1519383).sum := by decide
  have hdescent : baseEnd_1519383 < baseStart_1519383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519409 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1519409 : Nat := 118140960795 + 1519409 * 2 ^ 59
def prefixEnd_1519409 : Nat := 4983230072969 + 3 ^ 40 * 1519409 * 2
def baseEnd_1519409 : Nat := 780187127767351038999871

theorem tailTrace_1519409 : CollatzResearch.WordTrace tailWord_1519409 prefixEnd_1519409 780187127767351038999871 := by
  unfold tailWord_1519409
  simp only [CollatzResearch.WordTrace]
  refine ⟨55417398952448162242905281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36944932634965441495270187 55417398952448162242905281)
  ·
    refine ⟨41563049214336121682178961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55417398952448162242905281 41563049214336121682178961)
    ·
      refine ⟨31172286910752091261634221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41563049214336121682178961 31172286910752091261634221)
      ·
        refine ⟨11689607591532034223112833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31172286910752091261634221 11689607591532034223112833)
        ·
          refine ⟨8767205693649025667334625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11689607591532034223112833 8767205693649025667334625)
          ·
            refine ⟨6575404270236769250500969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8767205693649025667334625 6575404270236769250500969)
            ·
              refine ⟨4931553202677576937875727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575404270236769250500969 4931553202677576937875727)
              ·
                refine ⟨7397329804016365406813591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931553202677576937875727 7397329804016365406813591)
                ·
                  refine ⟨11095994706024548110220387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7397329804016365406813591 11095994706024548110220387)
                  ·
                    refine ⟨16643992059036822165330581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11095994706024548110220387 16643992059036822165330581)
                    ·
                      refine ⟨780187127767351038999871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16643992059036822165330581 780187127767351038999871)
                      ·
                        rfl

theorem cell23_1519409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1519409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519409 prefixEnd_1519409 := by exact prefixLift 1519409
  have htrace : WordTrace (prefixWord ++ tailWord_1519409) baseStart_1519409 baseEnd_1519409 := by
    simpa [prefixWord, tailWord_1519409, baseEnd_1519409] using wordTrace_append hprefix tailTrace_1519409
  have hstable : (prefixWord ++ tailWord_1519409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519409).length < 2 ^ (prefixWord ++ tailWord_1519409).sum := by decide
  have hdescent : baseEnd_1519409 < baseStart_1519409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519416 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_1519416 : Nat := 118140960795 + 1519416 * 2 ^ 59
def prefixEnd_1519416 : Nat := 4983230072969 + 3 ^ 40 * 1519416 * 2
def baseEnd_1519416 : Nat := 780190722131932511612339

theorem tailTrace_1519416 : CollatzResearch.WordTrace tailWord_1519416 prefixEnd_1519416 780190722131932511612339 := by
  unfold tailWord_1519416
  simp only [CollatzResearch.WordTrace]
  refine ⟨27708827131711401219205051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36945102842281868292273401 27708827131711401219205051)
  ·
    refine ⟨41563240697567101828807577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27708827131711401219205051 41563240697567101828807577)
    ·
      refine ⟨31172430523175326371605683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41563240697567101828807577 31172430523175326371605683)
      ·
        refine ⟨46758645784762989557408525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31172430523175326371605683 46758645784762989557408525)
        ·
          refine ⟨17534492169286121084028197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46758645784762989557408525 17534492169286121084028197)
          ·
            refine ⟨3287717281741147703255287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17534492169286121084028197 3287717281741147703255287)
            ·
              refine ⟨4931575922611721554882931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287717281741147703255287 4931575922611721554882931)
              ·
                refine ⟨7397363883917582332324397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931575922611721554882931 7397363883917582332324397)
                ·
                  refine ⟨2774011456469093374621649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7397363883917582332324397 2774011456469093374621649)
                  ·
                    refine ⟨2080508592351820030966237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774011456469093374621649 2080508592351820030966237)
                    ·
                      refine ⟨780190722131932511612339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080508592351820030966237 780190722131932511612339)
                      ·
                        rfl

theorem cell23_1519416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_1519416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519416 prefixEnd_1519416 := by exact prefixLift 1519416
  have htrace : WordTrace (prefixWord ++ tailWord_1519416) baseStart_1519416 baseEnd_1519416 := by
    simpa [prefixWord, tailWord_1519416, baseEnd_1519416] using wordTrace_append hprefix tailTrace_1519416
  have hstable : (prefixWord ++ tailWord_1519416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519416).length < 2 ^ (prefixWord ++ tailWord_1519416).sum := by decide
  have hdescent : baseEnd_1519416 < baseStart_1519416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519433 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 1, 2, 3]
def baseStart_1519433 : Nat := 118140960795 + 1519433 * 2 ^ 59
def prefixEnd_1519433 : Nat := 4983230072969 + 3 ^ 40 * 1519433 * 2
def baseEnd_1519433 : Nat := 780199451303058945099761

theorem tailTrace_1519433 : CollatzResearch.WordTrace tailWord_1519433 prefixEnd_1519433 780199451303058945099761 := by
  unfold tailWord_1519433
  simp only [CollatzResearch.WordTrace]
  refine ⟨55418274304361214341778953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36945516202907476227852635 55418274304361214341778953)
  ·
    refine ⟨41563705728270910756334215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55418274304361214341778953 41563705728270910756334215)
    ·
      refine ⟨62345558592406366134501323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41563705728270910756334215 62345558592406366134501323)
      ·
        refine ⟨93518337888609549201751985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62345558592406366134501323 93518337888609549201751985)
        ·
          refine ⟨70138753416457161901313989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93518337888609549201751985 70138753416457161901313989)
          ·
            refine ⟨13151016265585717856496373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70138753416457161901313989 13151016265585717856496373)
            ·
              refine ⟨1232907774898661049046535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13151016265585717856496373 1232907774898661049046535)
              ·
                refine ⟨1849361662347991573569803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232907774898661049046535 1849361662347991573569803)
                ·
                  refine ⟨2774042493521987360354705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849361662347991573569803 2774042493521987360354705)
                  ·
                    refine ⟨2080531870141490520266029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774042493521987360354705 2080531870141490520266029)
                    ·
                      refine ⟨780199451303058945099761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080531870141490520266029 780199451303058945099761)
                      ·
                        rfl

theorem cell23_1519433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 2, 3].length) (baseStart_1519433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519433 prefixEnd_1519433 := by exact prefixLift 1519433
  have htrace : WordTrace (prefixWord ++ tailWord_1519433) baseStart_1519433 baseEnd_1519433 := by
    simpa [prefixWord, tailWord_1519433, baseEnd_1519433] using wordTrace_append hprefix tailTrace_1519433
  have hstable : (prefixWord ++ tailWord_1519433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519433).length < 2 ^ (prefixWord ++ tailWord_1519433).sum := by decide
  have hdescent : baseEnd_1519433 < baseStart_1519433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519447 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 1, 2, 2]
def baseStart_1519447 : Nat := 118140960795 + 1519447 * 2 ^ 59
def prefixEnd_1519447 : Nat := 4983230072969 + 3 ^ 40 * 1519447 * 2
def baseEnd_1519447 : Nat := 780206640032221890324697

theorem tailTrace_1519447 : CollatzResearch.WordTrace tailWord_1519447 prefixEnd_1519447 780206640032221890324697 := by
  unfold tailWord_1519447
  simp only [CollatzResearch.WordTrace]
  refine ⟨55418784926310494732788595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36945856617540329821859063 55418784926310494732788595)
  ·
    refine ⟨83128177389465742099182893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55418784926310494732788595 83128177389465742099182893)
    ·
      refine ⟨31173066521049653287193585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83128177389465742099182893 31173066521049653287193585)
      ·
        refine ⟨23379799890787239965395189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31173066521049653287193585 23379799890787239965395189)
        ·
          refine ⟨2191856239761303746755799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23379799890787239965395189 2191856239761303746755799)
          ·
            refine ⟨3287784359641955620133699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191856239761303746755799 3287784359641955620133699)
            ·
              refine ⟨4931676539462933430200549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287784359641955620133699 4931676539462933430200549)
              ·
                refine ⟨924689351149300018162603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4931676539462933430200549 924689351149300018162603)
                ·
                  refine ⟨1387034026723950027243905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924689351149300018162603 1387034026723950027243905)
                  ·
                    refine ⟨1040275520042962520432929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1387034026723950027243905 1040275520042962520432929)
                    ·
                      refine ⟨780206640032221890324697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040275520042962520432929 780206640032221890324697)
                      ·
                        rfl

theorem cell23_1519447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_1519447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519447 prefixEnd_1519447 := by exact prefixLift 1519447
  have htrace : WordTrace (prefixWord ++ tailWord_1519447) baseStart_1519447 baseEnd_1519447 := by
    simpa [prefixWord, tailWord_1519447, baseEnd_1519447] using wordTrace_append hprefix tailTrace_1519447
  have hstable : (prefixWord ++ tailWord_1519447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519447).length < 2 ^ (prefixWord ++ tailWord_1519447).sum := by decide
  have hdescent : baseEnd_1519447 < baseStart_1519447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519463 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1519463 : Nat := 118140960795 + 1519463 * 2 ^ 59
def prefixEnd_1519463 : Nat := 4983230072969 + 3 ^ 40 * 1519463 * 2
def baseEnd_1519463 : Nat := 780214855722693827724623

theorem tailTrace_1519463 : CollatzResearch.WordTrace tailWord_1519463 prefixEnd_1519463 780214855722693827724623 := by
  unfold tailWord_1519463
  simp only [CollatzResearch.WordTrace]
  refine ⟨55419368494252529465371043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36946245662835019643580695 55419368494252529465371043)
  ·
    refine ⟨83129052741378794198056565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55419368494252529465371043 83129052741378794198056565)
    ·
      refine ⟨7793348694504261956067803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83129052741378794198056565 7793348694504261956067803)
      ·
        refine ⟨11690023041756392934101705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7793348694504261956067803 11690023041756392934101705)
        ·
          refine ⟨8767517281317294700576279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11690023041756392934101705 8767517281317294700576279)
          ·
            refine ⟨13151275921975942050864419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8767517281317294700576279 13151275921975942050864419)
            ·
              refine ⟨19726913882963913076296629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13151275921975942050864419 19726913882963913076296629)
              ·
                refine ⟨1849398176527866850902809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19726913882963913076296629 1849398176527866850902809)
                ·
                  refine ⟨1387048632395900138177107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1849398176527866850902809 1387048632395900138177107)
                  ·
                    refine ⟨2080572948593850207265661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1387048632395900138177107 2080572948593850207265661)
                    ·
                      refine ⟨780214855722693827724623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080572948593850207265661 780214855722693827724623)
                      ·
                        rfl

theorem cell23_1519463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1519463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519463 prefixEnd_1519463 := by exact prefixLift 1519463
  have htrace : WordTrace (prefixWord ++ tailWord_1519463) baseStart_1519463 baseEnd_1519463 := by
    simpa [prefixWord, tailWord_1519463, baseEnd_1519463] using wordTrace_append hprefix tailTrace_1519463
  have hstable : (prefixWord ++ tailWord_1519463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519463).length < 2 ^ (prefixWord ++ tailWord_1519463).sum := by decide
  have hdescent : baseEnd_1519463 < baseStart_1519463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519473 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 1, 3, 2]
def baseStart_1519473 : Nat := 118140960795 + 1519473 * 2 ^ 59
def prefixEnd_1519473 : Nat := 4983230072969 + 3 ^ 40 * 1519473 * 2
def baseEnd_1519473 : Nat := 780219990529238788599577

theorem tailTrace_1519473 : CollatzResearch.WordTrace tailWord_1519473 prefixEnd_1519473 780219990529238788599577 := by
  unfold tailWord_1519473
  simp only [CollatzResearch.WordTrace]
  refine ⟨55419733224216301173235073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36946488816144200782156715 55419733224216301173235073)
  ·
    refine ⟨41564799918162225879926305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55419733224216301173235073 41564799918162225879926305)
    ·
      refine ⟨31173599938621669409944729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41564799918162225879926305 31173599938621669409944729)
      ·
        refine ⟨23380199953966252057458547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31173599938621669409944729 23380199953966252057458547)
        ·
          refine ⟨35070299930949378086187821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23380199953966252057458547 35070299930949378086187821)
          ·
            refine ⟨13151362474106016782320433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35070299930949378086187821 13151362474106016782320433)
            ·
              refine ⟨9863521855579512586740325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13151362474106016782320433 9863521855579512586740325)
              ·
                refine ⟨1849410347921158610013811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9863521855579512586740325 1849410347921158610013811)
                ·
                  refine ⟨2774115521881737915020717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849410347921158610013811 2774115521881737915020717)
                  ·
                    refine ⟨1040293320705651718132769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2774115521881737915020717 1040293320705651718132769)
                    ·
                      refine ⟨780219990529238788599577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040293320705651718132769 780219990529238788599577)
                      ·
                        rfl

theorem cell23_1519473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_1519473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519473 prefixEnd_1519473 := by exact prefixLift 1519473
  have htrace : WordTrace (prefixWord ++ tailWord_1519473) baseStart_1519473 baseEnd_1519473 := by
    simpa [prefixWord, tailWord_1519473, baseEnd_1519473] using wordTrace_append hprefix tailTrace_1519473
  have hstable : (prefixWord ++ tailWord_1519473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519473).length < 2 ^ (prefixWord ++ tailWord_1519473).sum := by decide
  have hdescent : baseEnd_1519473 < baseStart_1519473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519539 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 1, 7]
def baseStart_1519539 : Nat := 118140960795 + 1519539 * 2 ^ 59
def prefixEnd_1519539 : Nat := 4983230072969 + 3 ^ 40 * 1519539 * 2
def baseEnd_1519539 : Nat := 260084626750811843458091

theorem tailTrace_1519539 : CollatzResearch.WordTrace tailWord_1519539 prefixEnd_1519539 260084626750811843458091 := by
  unfold tailWord_1519539
  simp only [CollatzResearch.WordTrace]
  refine ⟨55422140441977194445137671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36948093627984796296758447 55422140441977194445137671)
  ·
    refine ⟨83133210662965791667706507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55422140441977194445137671 83133210662965791667706507)
    ·
      refine ⟨124699815994448687501559761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83133210662965791667706507 124699815994448687501559761)
      ·
        refine ⟨93524861995836515626169821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124699815994448687501559761 93524861995836515626169821)
        ·
          refine ⟨35071823248438693359813683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93524861995836515626169821 35071823248438693359813683)
          ·
            refine ⟨52607734872658040039720525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35071823248438693359813683 52607734872658040039720525)
            ·
              refine ⟨19727900577246765014895197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52607734872658040039720525 19727900577246765014895197)
              ·
                refine ⟨7397962716467536880585699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19727900577246765014895197 7397962716467536880585699)
                ·
                  refine ⟨11096944074701305320878549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7397962716467536880585699 11096944074701305320878549)
                  ·
                    refine ⟨260084626750811843458091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11096944074701305320878549 260084626750811843458091)
                    ·
                      rfl

theorem cell23_1519539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 7].length) (baseStart_1519539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519539 prefixEnd_1519539 := by exact prefixLift 1519539
  have htrace : WordTrace (prefixWord ++ tailWord_1519539) baseStart_1519539 baseEnd_1519539 := by
    simpa [prefixWord, tailWord_1519539, baseEnd_1519539] using wordTrace_append hprefix tailTrace_1519539
  have hstable : (prefixWord ++ tailWord_1519539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519539).length < 2 ^ (prefixWord ++ tailWord_1519539).sum := by decide
  have hdescent : baseEnd_1519539 < baseStart_1519539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519540 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1519540 : Nat := 118140960795 + 1519540 * 2 ^ 59
def prefixEnd_1519540 : Nat := 4983230072969 + 3 ^ 40 * 1519540 * 2
def baseEnd_1519540 : Nat := 780254393733090026461769

theorem tailTrace_1519540 : CollatzResearch.WordTrace tailWord_1519540 prefixEnd_1519540 780254393733090026461769 := by
  unfold tailWord_1519540
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711088457486785807962037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36948117943315714410616049 27711088457486785807962037)
  ·
    refine ⟨2597914542889386169496441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27711088457486785807962037 2597914542889386169496441)
    ·
      refine ⟨1948435907167039627122331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2597914542889386169496441 1948435907167039627122331)
      ·
        refine ⟨2922653860750559440683497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948435907167039627122331 2922653860750559440683497)
        ·
          refine ⟨2191990395562919580512623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922653860750559440683497 2191990395562919580512623)
          ·
            refine ⟨3287985593344379370768935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191990395562919580512623 3287985593344379370768935)
            ·
              refine ⟨4931978390016569056153403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3287985593344379370768935 4931978390016569056153403)
              ·
                refine ⟨7397967585024853584230105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4931978390016569056153403 7397967585024853584230105)
                ·
                  refine ⟨5548475688768640188172579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7397967585024853584230105 5548475688768640188172579)
                  ·
                    refine ⟨8322713533152960282258869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5548475688768640188172579 8322713533152960282258869)
                    ·
                      refine ⟨780254393733090026461769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8322713533152960282258869 780254393733090026461769)
                      ·
                        rfl

theorem cell23_1519540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1519540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519540 prefixEnd_1519540 := by exact prefixLift 1519540
  have htrace : WordTrace (prefixWord ++ tailWord_1519540) baseStart_1519540 baseEnd_1519540 := by
    simpa [prefixWord, tailWord_1519540, baseEnd_1519540] using wordTrace_append hprefix tailTrace_1519540
  have hstable : (prefixWord ++ tailWord_1519540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519540).length < 2 ^ (prefixWord ++ tailWord_1519540).sum := by decide
  have hdescent : baseEnd_1519540 < baseStart_1519540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519560 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 5]
def baseStart_1519560 : Nat := 118140960795 + 1519560 * 2 ^ 59
def prefixEnd_1519560 : Nat := 4983230072969 + 3 ^ 40 * 1519560 * 2
def baseEnd_1519560 : Nat := 86696073705131105356853

theorem tailTrace_1519560 : CollatzResearch.WordTrace tailWord_1519560 prefixEnd_1519560 86696073705131105356853 := by
  unfold tailWord_1519560
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711453187450557515826067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36948604249934076687768089 27711453187450557515826067)
  ·
    refine ⟨41567179781175836273739101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27711453187450557515826067 41567179781175836273739101)
    ·
      refine ⟨15587692417940938602652163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41567179781175836273739101 15587692417940938602652163)
      ·
        refine ⟨23381538626911407903978245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15587692417940938602652163 23381538626911407903978245)
        ·
          refine ⟨4384038492545888981995921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23381538626911407903978245 4384038492545888981995921)
          ·
            refine ⟨3288028869409416736496941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4384038492545888981995921 3288028869409416736496941)
            ·
              refine ⟨1233010826028531276186353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3288028869409416736496941 1233010826028531276186353)
              ·
                refine ⟨924758119521398457139765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233010826028531276186353 924758119521398457139765)
                ·
                  refine ⟨86696073705131105356853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 924758119521398457139765 86696073705131105356853)
                  ·
                    rfl

theorem cell23_1519560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 5].length) (baseStart_1519560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519560 prefixEnd_1519560 := by exact prefixLift 1519560
  have htrace : WordTrace (prefixWord ++ tailWord_1519560) baseStart_1519560 baseEnd_1519560 := by
    simpa [prefixWord, tailWord_1519560, baseEnd_1519560] using wordTrace_append hprefix tailTrace_1519560
  have hstable : (prefixWord ++ tailWord_1519560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519560).length < 2 ^ (prefixWord ++ tailWord_1519560).sum := by decide
  have hdescent : baseEnd_1519560 < baseStart_1519560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519566 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1519566 : Nat := 118140960795 + 1519566 * 2 ^ 59
def prefixEnd_1519566 : Nat := 4983230072969 + 3 ^ 40 * 1519566 * 2
def baseEnd_1519566 : Nat := 780267744230106924736649

theorem tailTrace_1519566 : CollatzResearch.WordTrace tailWord_1519566 prefixEnd_1519566 780267744230106924736649 := by
  unfold tailWord_1519566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6927890651609922257046319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36948750141919585370913701 6927890651609922257046319)
  ·
    refine ⟨10391835977414883385569479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6927890651609922257046319 10391835977414883385569479)
    ·
      refine ⟨15587753966122325078354219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10391835977414883385569479 15587753966122325078354219)
      ·
        refine ⟨23381630949183487617531329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15587753966122325078354219 23381630949183487617531329)
        ·
          refine ⟨17536223211887615713148497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23381630949183487617531329 17536223211887615713148497)
          ·
            refine ⟨13152167408915711784861373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17536223211887615713148497 13152167408915711784861373)
            ·
              refine ⟨4932062778343391919323015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13152167408915711784861373 4932062778343391919323015)
              ·
                refine ⟨7398094167515087878984523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932062778343391919323015 7398094167515087878984523)
                ·
                  refine ⟨11097141251272631818476785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7398094167515087878984523 11097141251272631818476785)
                  ·
                    refine ⟨8322855938454473863857589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11097141251272631818476785 8322855938454473863857589)
                    ·
                      refine ⟨780267744230106924736649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8322855938454473863857589 780267744230106924736649)
                      ·
                        rfl

theorem cell23_1519566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1519566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519566 prefixEnd_1519566 := by exact prefixLift 1519566
  have htrace : WordTrace (prefixWord ++ tailWord_1519566) baseStart_1519566 baseEnd_1519566 := by
    simpa [prefixWord, tailWord_1519566, baseEnd_1519566] using wordTrace_append hprefix tailTrace_1519566
  have hstable : (prefixWord ++ tailWord_1519566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519566).length < 2 ^ (prefixWord ++ tailWord_1519566).sum := by decide
  have hdescent : baseEnd_1519566 < baseStart_1519566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519569 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_1519569 : Nat := 118140960795 + 1519569 * 2 ^ 59
def prefixEnd_1519569 : Nat := 4983230072969 + 3 ^ 40 * 1519569 * 2
def baseEnd_1519569 : Nat := 260089761557356804333045

theorem tailTrace_1519569 : CollatzResearch.WordTrace tailWord_1519569 prefixEnd_1519569 260089761557356804333045 := by
  unfold tailWord_1519569
  simp only [CollatzResearch.WordTrace]
  refine ⟨55423234631868509568729761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36948823087912339712486507 55423234631868509568729761)
  ·
    refine ⟨41567425973901382176547321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55423234631868509568729761 41567425973901382176547321)
    ·
      refine ⟨31175569480426036632410491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41567425973901382176547321 31175569480426036632410491)
      ·
        refine ⟨46763354220639054948615737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31175569480426036632410491 46763354220639054948615737)
        ·
          refine ⟨35072515665479291211461803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46763354220639054948615737 35072515665479291211461803)
          ·
            refine ⟨52608773498218936817192705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35072515665479291211461803 52608773498218936817192705)
            ·
              refine ⟨39456580123664202612894529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52608773498218936817192705 39456580123664202612894529)
              ·
                refine ⟨29592435092748151959670897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39456580123664202612894529 29592435092748151959670897)
                ·
                  refine ⟨22194326319561113969753173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29592435092748151959670897 22194326319561113969753173)
                  ·
                    refine ⟨260089761557356804333045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22194326319561113969753173 260089761557356804333045)
                    ·
                      rfl

theorem cell23_1519569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_1519569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519569 prefixEnd_1519569 := by exact prefixLift 1519569
  have htrace : WordTrace (prefixWord ++ tailWord_1519569) baseStart_1519569 baseEnd_1519569 := by
    simpa [prefixWord, tailWord_1519569, baseEnd_1519569] using wordTrace_append hprefix tailTrace_1519569
  have hstable : (prefixWord ++ tailWord_1519569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519569).length < 2 ^ (prefixWord ++ tailWord_1519569).sum := by decide
  have hdescent : baseEnd_1519569 < baseStart_1519569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519576 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1519576 : Nat := 118140960795 + 1519576 * 2 ^ 59
def prefixEnd_1519576 : Nat := 4983230072969 + 3 ^ 40 * 1519576 * 2
def baseEnd_1519576 : Nat := 780272879036651885611603

theorem tailTrace_1519576 : CollatzResearch.WordTrace tailWord_1519576 prefixEnd_1519576 780272879036651885611603 := by
  unfold tailWord_1519576
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711744971421574882117291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36948993295228766509489721 27711744971421574882117291)
  ·
    refine ⟨41567617457132362323175937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27711744971421574882117291 41567617457132362323175937)
    ·
      refine ⟨31175713092849271742381953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41567617457132362323175937 31175713092849271742381953)
      ·
        refine ⟨23381784819636953806786465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31175713092849271742381953 23381784819636953806786465)
        ·
          refine ⟨17536338614727715355089849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23381784819636953806786465 17536338614727715355089849)
          ·
            refine ⟨13152253961045786516317387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17536338614727715355089849 13152253961045786516317387)
            ·
              refine ⟨19728380941568679774476081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13152253961045786516317387 19728380941568679774476081)
              ·
                refine ⟨14796285706176509830857061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19728380941568679774476081 14796285706176509830857061)
                ·
                  refine ⟨2774303569908095593285699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14796285706176509830857061 2774303569908095593285699)
                  ·
                    refine ⟨4161455354862143389928549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2774303569908095593285699 4161455354862143389928549)
                    ·
                      refine ⟨780272879036651885611603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4161455354862143389928549 780272879036651885611603)
                      ·
                        rfl

theorem cell23_1519576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1519576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519576 prefixEnd_1519576 := by exact prefixLift 1519576
  have htrace : WordTrace (prefixWord ++ tailWord_1519576) baseStart_1519576 baseEnd_1519576 := by
    simpa [prefixWord, tailWord_1519576, baseEnd_1519576] using wordTrace_append hprefix tailTrace_1519576
  have hstable : (prefixWord ++ tailWord_1519576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519576).length < 2 ^ (prefixWord ++ tailWord_1519576).sum := by decide
  have hdescent : baseEnd_1519576 < baseStart_1519576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519596 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_1519596 : Nat := 118140960795 + 1519596 * 2 ^ 59
def prefixEnd_1519596 : Nat := 4983230072969 + 3 ^ 40 * 1519596 * 2
def baseEnd_1519596 : Nat := 780283148649741807361511

theorem tailTrace_1519596 : CollatzResearch.WordTrace tailWord_1519596 prefixEnd_1519596 780283148649741807361511 := by
  unfold tailWord_1519596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27712109701385346589981321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36949479601847128786641761 27712109701385346589981321)
  ·
    refine ⟨20784082276039009942485991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27712109701385346589981321 20784082276039009942485991)
    ·
      refine ⟨31176123414058514913728987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20784082276039009942485991 31176123414058514913728987)
      ·
        refine ⟨46764185121087772370593481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31176123414058514913728987 46764185121087772370593481)
        ·
          refine ⟨35073138840815829277945111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46764185121087772370593481 35073138840815829277945111)
          ·
            refine ⟨52609708261223743916917667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35073138840815829277945111 52609708261223743916917667)
            ·
              refine ⟨78914562391835615875376501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52609708261223743916917667 78914562391835615875376501)
              ·
                refine ⟨7398240224234588988316547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78914562391835615875376501 7398240224234588988316547)
                ·
                  refine ⟨11097360336351883482474821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7398240224234588988316547 11097360336351883482474821)
                  ·
                    refine ⟨2080755063065978152964029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11097360336351883482474821 2080755063065978152964029)
                    ·
                      refine ⟨780283148649741807361511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080755063065978152964029 780283148649741807361511)
                      ·
                        rfl

theorem cell23_1519596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_1519596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519596 prefixEnd_1519596 := by exact prefixLift 1519596
  have htrace : WordTrace (prefixWord ++ tailWord_1519596) baseStart_1519596 baseEnd_1519596 := by
    simpa [prefixWord, tailWord_1519596, baseEnd_1519596] using wordTrace_append hprefix tailTrace_1519596
  have hstable : (prefixWord ++ tailWord_1519596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519596).length < 2 ^ (prefixWord ++ tailWord_1519596).sum := by decide
  have hdescent : baseEnd_1519596 < baseStart_1519596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519613 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1519613 : Nat := 118140960795 + 1519613 * 2 ^ 59
def prefixEnd_1519613 : Nat := 4983230072969 + 3 ^ 40 * 1519613 * 2
def baseEnd_1519613 : Nat := 780291877820868240848933

theorem tailTrace_1519613 : CollatzResearch.WordTrace tailWord_1519613 prefixEnd_1519613 780291877820868240848933 := by
  unfold tailWord_1519613
  simp only [CollatzResearch.WordTrace]
  refine ⟨55424839443709105083331493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36949892962472736722220995 55424839443709105083331493)
  ·
    refine ⟨10392157395695457203124655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55424839443709105083331493 10392157395695457203124655)
    ·
      refine ⟨15588236093543185804686983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392157395695457203124655 15588236093543185804686983)
      ·
        refine ⟨23382354140314778707030475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15588236093543185804686983 23382354140314778707030475)
        ·
          refine ⟨35073531210472168060545713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23382354140314778707030475 35073531210472168060545713)
          ·
            refine ⟨26305148407854126045409285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35073531210472168060545713 26305148407854126045409285)
            ·
              refine ⟨4932215326472648633514241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26305148407854126045409285 4932215326472648633514241)
              ·
                refine ⟨3699161494854486475135681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932215326472648633514241 3699161494854486475135681)
                ·
                  refine ⟨2774371121140864856351761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3699161494854486475135681 2774371121140864856351761)
                  ·
                    refine ⟨2080778340855648642263821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774371121140864856351761 2080778340855648642263821)
                    ·
                      refine ⟨780291877820868240848933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080778340855648642263821 780291877820868240848933)
                      ·
                        rfl

theorem cell23_1519613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1519613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519613 prefixEnd_1519613 := by exact prefixLift 1519613
  have htrace : WordTrace (prefixWord ++ tailWord_1519613) baseStart_1519613 baseEnd_1519613 := by
    simpa [prefixWord, tailWord_1519613, baseEnd_1519613] using wordTrace_append hprefix tailTrace_1519613
  have hstable : (prefixWord ++ tailWord_1519613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519613).length < 2 ^ (prefixWord ++ tailWord_1519613).sum := by decide
  have hdescent : baseEnd_1519613 < baseStart_1519613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519677 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1519677 : Nat := 118140960795 + 1519677 * 2 ^ 59
def prefixEnd_1519677 : Nat := 4983230072969 + 3 ^ 40 * 1519677 * 2
def baseEnd_1519677 : Nat := 780324740582755990448639

theorem tailTrace_1519677 : CollatzResearch.WordTrace tailWord_1519677 prefixEnd_1519677 780324740582755990448639 := by
  unfold tailWord_1519677
  simp only [CollatzResearch.WordTrace]
  refine ⟨55427173715477244013661285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36951449143651496009107523 55427173715477244013661285)
  ·
    refine ⟨10392595071651983252561491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55427173715477244013661285 10392595071651983252561491)
    ·
      refine ⟨15588892607477974878842237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392595071651983252561491 15588892607477974878842237)
      ·
        refine ⟨5845834727804240579565839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15588892607477974878842237 5845834727804240579565839)
        ·
          refine ⟨8768752091706360869348759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845834727804240579565839 8768752091706360869348759)
          ·
            refine ⟨13153128137559541304023139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8768752091706360869348759 13153128137559541304023139)
            ·
              refine ⟨19729692206339311956034709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13153128137559541304023139 19729692206339311956034709)
              ·
                refine ⟨924829322172155247939127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19729692206339311956034709 924829322172155247939127)
                ·
                  refine ⟨1387243983258232871908691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924829322172155247939127 1387243983258232871908691)
                  ·
                    refine ⟨2080865974887349307863037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1387243983258232871908691 2080865974887349307863037)
                    ·
                      refine ⟨780324740582755990448639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080865974887349307863037 780324740582755990448639)
                      ·
                        rfl

theorem cell23_1519677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1519677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519677 prefixEnd_1519677 := by exact prefixLift 1519677
  have htrace : WordTrace (prefixWord ++ tailWord_1519677) baseStart_1519677 baseEnd_1519677 := by
    simpa [prefixWord, tailWord_1519677, baseEnd_1519677] using wordTrace_append hprefix tailTrace_1519677
  have hstable : (prefixWord ++ tailWord_1519677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519677).length < 2 ^ (prefixWord ++ tailWord_1519677).sum := by decide
  have hdescent : baseEnd_1519677 < baseStart_1519677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519703 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_1519703 : Nat := 118140960795 + 1519703 * 2 ^ 59
def prefixEnd_1519703 : Nat := 4983230072969 + 3 ^ 40 * 1519703 * 2
def baseEnd_1519703 : Nat := 780338091079772888723519

theorem tailTrace_1519703 : CollatzResearch.WordTrace tailWord_1519703 prefixEnd_1519703 780338091079772888723519 := by
  unfold tailWord_1519703
  simp only [CollatzResearch.WordTrace]
  refine ⟨55428122013383050454107763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36952081342255366969405175 55428122013383050454107763)
  ·
    refine ⟨83142183020074575681161645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55428122013383050454107763 83142183020074575681161645)
    ·
      refine ⟨31178318632527965880435617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83142183020074575681161645 31178318632527965880435617)
      ·
        refine ⟨23383738974395974410326713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31178318632527965880435617 23383738974395974410326713)
        ·
          refine ⟨17537804230796980807745035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23383738974395974410326713 17537804230796980807745035)
          ·
            refine ⟨26306706346195471211617553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17537804230796980807745035 26306706346195471211617553)
            ·
              refine ⟨19730029759646603408713165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26306706346195471211617553 19730029759646603408713165)
              ·
                refine ⟨7398761159867476278267437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19730029759646603408713165 7398761159867476278267437)
                ·
                  refine ⟨2774535434950303604350289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7398761159867476278267437 2774535434950303604350289)
                  ·
                    refine ⟨2080901576212727703262717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774535434950303604350289 2080901576212727703262717)
                    ·
                      refine ⟨780338091079772888723519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2080901576212727703262717 780338091079772888723519)
                      ·
                        rfl

theorem cell23_1519703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_1519703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519703 prefixEnd_1519703 := by exact prefixLift 1519703
  have htrace : WordTrace (prefixWord ++ tailWord_1519703) baseStart_1519703 baseEnd_1519703 := by
    simpa [prefixWord, tailWord_1519703, baseEnd_1519703] using wordTrace_append hprefix tailTrace_1519703
  have hstable : (prefixWord ++ tailWord_1519703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519703).length < 2 ^ (prefixWord ++ tailWord_1519703).sum := by decide
  have hdescent : baseEnd_1519703 < baseStart_1519703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519706 : List Nat := [3, 1, 1, 2, 1, 1, 5, 9]
def baseStart_1519706 : Nat := 118140960795 + 1519706 * 2 ^ 59
def prefixEnd_1519706 : Nat := 4983230072969 + 3 ^ 40 * 1519706 * 2
def baseEnd_1519706 : Nat := 28901467834138384332815

theorem tailTrace_1519706 : CollatzResearch.WordTrace tailWord_1519706 prefixEnd_1519706 28901467834138384332815 := by
  unfold tailWord_1519706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857057858093045491616743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36952154288248121310977981 13857057858093045491616743)
  ·
    refine ⟨20785586787139568237425115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13857057858093045491616743 20785586787139568237425115)
    ·
      refine ⟨31178380180709352356137673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20785586787139568237425115 31178380180709352356137673)
      ·
        refine ⟨23383785135532014267103255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31178380180709352356137673 23383785135532014267103255)
        ·
          refine ⟨35075677703298021400654883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23383785135532014267103255 35075677703298021400654883)
          ·
            refine ⟨52613516554947032100982325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35075677703298021400654883 52613516554947032100982325)
            ·
              refine ⟨4932517177026284259467093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52613516554947032100982325 4932517177026284259467093)
              ·
                refine ⟨28901467834138384332815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4932517177026284259467093 28901467834138384332815)
                ·
                  rfl

theorem cell23_1519706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_1519706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519706 prefixEnd_1519706 := by exact prefixLift 1519706
  have htrace : WordTrace (prefixWord ++ tailWord_1519706) baseStart_1519706 baseEnd_1519706 := by
    simpa [prefixWord, tailWord_1519706, baseEnd_1519706] using wordTrace_append hprefix tailTrace_1519706
  have hstable : (prefixWord ++ tailWord_1519706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519706).length < 2 ^ (prefixWord ++ tailWord_1519706).sum := by decide
  have hdescent : baseEnd_1519706 < baseStart_1519706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519734 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1519734 : Nat := 118140960795 + 1519734 * 2 ^ 59
def prefixEnd_1519734 : Nat := 4983230072969 + 3 ^ 40 * 1519734 * 2
def baseEnd_1519734 : Nat := 780354008980062267435877

theorem tailTrace_1519734 : CollatzResearch.WordTrace tailWord_1519734 prefixEnd_1519734 780354008980062267435877 := by
  unfold tailWord_1519734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464328292266921421780391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36952835117513828498990837 3464328292266921421780391)
  ·
    refine ⟨5196492438400382132670587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3464328292266921421780391 5196492438400382132670587)
    ·
      refine ⟨7794738657600573199005881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196492438400382132670587 7794738657600573199005881)
      ·
        refine ⟨5846053993200429899254411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7794738657600573199005881 5846053993200429899254411)
        ·
          refine ⟨8769080989800644848881617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846053993200429899254411 8769080989800644848881617)
          ·
            refine ⟨6576810742350483636661213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8769080989800644848881617 6576810742350483636661213)
            ·
              refine ⟨2466304028381431363747955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6576810742350483636661213 2466304028381431363747955)
              ·
                refine ⟨3699456042572147045621933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466304028381431363747955 3699456042572147045621933)
                ·
                  refine ⟨1387296015964555142108225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3699456042572147045621933 1387296015964555142108225)
                  ·
                    refine ⟨1040472011973416356581169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1387296015964555142108225 1040472011973416356581169)
                    ·
                      refine ⟨780354008980062267435877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040472011973416356581169 780354008980062267435877)
                      ·
                        rfl

theorem cell23_1519734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1519734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519734 prefixEnd_1519734 := by exact prefixLift 1519734
  have htrace : WordTrace (prefixWord ++ tailWord_1519734) baseStart_1519734 baseEnd_1519734 := by
    simpa [prefixWord, tailWord_1519734, baseEnd_1519734] using wordTrace_append hprefix tailTrace_1519734
  have hstable : (prefixWord ++ tailWord_1519734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519734).length < 2 ^ (prefixWord ++ tailWord_1519734).sum := by decide
  have hdescent : baseEnd_1519734 < baseStart_1519734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519736 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_1519736 : Nat := 118140960795 + 1519736 * 2 ^ 59
def prefixEnd_1519736 : Nat := 4983230072969 + 3 ^ 40 * 1519736 * 2
def baseEnd_1519736 : Nat := 260118345313790419870289

theorem tailTrace_1519736 : CollatzResearch.WordTrace tailWord_1519736 prefixEnd_1519736 260118345313790419870289 := by
  unfold tailWord_1519736
  simp only [CollatzResearch.WordTrace]
  refine ⟨27714662811131748545029531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36952883748175664726706041 27714662811131748545029531)
  ·
    refine ⟨41571994216697622817544297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27714662811131748545029531 41571994216697622817544297)
    ·
      refine ⟨31178995662523217113158223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41571994216697622817544297 31178995662523217113158223)
      ·
        refine ⟨46768493493784825669737335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31178995662523217113158223 46768493493784825669737335)
        ·
          refine ⟨70152740240677238504606003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46768493493784825669737335 70152740240677238504606003)
          ·
            refine ⟨105229110361015857756909005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70152740240677238504606003 105229110361015857756909005)
            ·
              refine ⟨39460916385380946658840877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105229110361015857756909005 39460916385380946658840877)
              ·
                refine ⟨14797843644517854997065329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39460916385380946658840877 14797843644517854997065329)
                ·
                  refine ⟨11098382733388391247798997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14797843644517854997065329 11098382733388391247798997)
                  ·
                    refine ⟨260118345313790419870289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11098382733388391247798997 260118345313790419870289)
                    ·
                      rfl

theorem cell23_1519736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_1519736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519736 prefixEnd_1519736 := by exact prefixLift 1519736
  have htrace : WordTrace (prefixWord ++ tailWord_1519736) baseStart_1519736 baseEnd_1519736 := by
    simpa [prefixWord, tailWord_1519736, baseEnd_1519736] using wordTrace_append hprefix tailTrace_1519736
  have hstable : (prefixWord ++ tailWord_1519736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519736).length < 2 ^ (prefixWord ++ tailWord_1519736).sum := by decide
  have hdescent : baseEnd_1519736 < baseStart_1519736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519756 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1519756 : Nat := 118140960795 + 1519756 * 2 ^ 59
def prefixEnd_1519756 : Nat := 4983230072969 + 3 ^ 40 * 1519756 * 2
def baseEnd_1519756 : Nat := 780365305554461181360775

theorem tailTrace_1519756 : CollatzResearch.WordTrace tailWord_1519756 prefixEnd_1519756 780365305554461181360775 := by
  unfold tailWord_1519756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27715027541095520252893561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36953370054794027003858081 27715027541095520252893561)
  ·
    refine ⟨20786270655821640189670171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27715027541095520252893561 20786270655821640189670171)
    ·
      refine ⟨31179405983732460284505257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20786270655821640189670171 31179405983732460284505257)
      ·
        refine ⟨23384554487799345213378943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31179405983732460284505257 23384554487799345213378943)
        ·
          refine ⟨35076831731699017820068415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23384554487799345213378943 35076831731699017820068415)
          ·
            refine ⟨52615247597548526730102623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35076831731699017820068415 52615247597548526730102623)
            ·
              refine ⟨78922871396322790095153935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52615247597548526730102623 78922871396322790095153935)
              ·
                refine ⟨118384307094484185142730903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78922871396322790095153935 118384307094484185142730903)
                ·
                  refine ⟨177576460641726277714096355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118384307094484185142730903 177576460641726277714096355)
                  ·
                    refine ⟨266364690962589416571144533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177576460641726277714096355 266364690962589416571144533)
                    ·
                      refine ⟨780365305554461181360775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 266364690962589416571144533 780365305554461181360775)
                      ·
                        rfl

theorem cell23_1519756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1519756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519756 prefixEnd_1519756 := by exact prefixLift 1519756
  have htrace : WordTrace (prefixWord ++ tailWord_1519756) baseStart_1519756 baseEnd_1519756 := by
    simpa [prefixWord, tailWord_1519756, baseEnd_1519756] using wordTrace_append hprefix tailTrace_1519756
  have hstable : (prefixWord ++ tailWord_1519756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519756).length < 2 ^ (prefixWord ++ tailWord_1519756).sum := by decide
  have hdescent : baseEnd_1519756 < baseStart_1519756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519760 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 3, 3, 2]
def baseStart_1519760 : Nat := 118140960795 + 1519760 * 2 ^ 59
def prefixEnd_1519760 : Nat := 4983230072969 + 3 ^ 40 * 1519760 * 2
def baseEnd_1519760 : Nat := 780367359477079165710757

theorem tailTrace_1519760 : CollatzResearch.WordTrace tailWord_1519760 prefixEnd_1519760 780367359477079165710757 := by
  unfold tailWord_1519760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27715100487088274594466367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36953467316117699459288489 27715100487088274594466367)
  ·
    refine ⟨41572650730632411891699551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27715100487088274594466367 41572650730632411891699551)
    ·
      refine ⟨62358976095948617837549327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41572650730632411891699551 62358976095948617837549327)
      ·
        refine ⟨93538464143922926756323991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62358976095948617837549327 93538464143922926756323991)
        ·
          refine ⟨140307696215884390134485987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93538464143922926756323991 140307696215884390134485987)
          ·
            refine ⟨210461544323826585201728981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140307696215884390134485987 210461544323826585201728981)
            ·
              refine ⟨4932692445089685590665523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 210461544323826585201728981 4932692445089685590665523)
              ·
                refine ⟨7399038667634528385998285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932692445089685590665523 7399038667634528385998285)
                ·
                  refine ⟨2774639500362948144749357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7399038667634528385998285 2774639500362948144749357)
                  ·
                    refine ⟨1040489812636105554281009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2774639500362948144749357 1040489812636105554281009)
                    ·
                      refine ⟨780367359477079165710757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040489812636105554281009 780367359477079165710757)
                      ·
                        rfl

theorem cell23_1519760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 3, 2].length) (baseStart_1519760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519760 prefixEnd_1519760 := by exact prefixLift 1519760
  have htrace : WordTrace (prefixWord ++ tailWord_1519760) baseStart_1519760 baseEnd_1519760 := by
    simpa [prefixWord, tailWord_1519760, baseEnd_1519760] using wordTrace_append hprefix tailTrace_1519760
  have hstable : (prefixWord ++ tailWord_1519760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519760).length < 2 ^ (prefixWord ++ tailWord_1519760).sum := by decide
  have hdescent : baseEnd_1519760 < baseStart_1519760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519803 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4]
def baseStart_1519803 : Nat := 118140960795 + 1519803 * 2 ^ 59
def prefixEnd_1519803 : Nat := 4983230072969 + 3 ^ 40 * 1519803 * 2
def baseEnd_1519803 : Nat := 780389439145222497473059

theorem tailTrace_1519803 : CollatzResearch.WordTrace tailWord_1519803 prefixEnd_1519803 780389439145222497473059 := by
  unfold tailWord_1519803
  simp only [CollatzResearch.WordTrace]
  refine ⟨55431769313020767532748063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36954512875347178355165375 55431769313020767532748063)
  ·
    refine ⟨83147653969531151299122095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55431769313020767532748063 83147653969531151299122095)
    ·
      refine ⟨124721480954296726948683143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83147653969531151299122095 124721480954296726948683143)
      ·
        refine ⟨187082221431445090423024715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124721480954296726948683143 187082221431445090423024715)
        ·
          refine ⟨280623332147167635634537073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187082221431445090423024715 280623332147167635634537073)
          ·
            refine ⟨210467499110375726725902805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280623332147167635634537073 210467499110375726725902805)
            ·
              refine ⟨4932832010399431095138347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 210467499110375726725902805 4932832010399431095138347)
              ·
                refine ⟨7399248015599146642707521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932832010399431095138347 7399248015599146642707521)
                ·
                  refine ⟨5549436011699359982030641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7399248015599146642707521 5549436011699359982030641)
                  ·
                    refine ⟨4162077008774519986522981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5549436011699359982030641 4162077008774519986522981)
                    ·
                      refine ⟨780389439145222497473059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4162077008774519986522981 780389439145222497473059)
                      ·
                        rfl

theorem cell23_1519803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_1519803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519803 prefixEnd_1519803 := by exact prefixLift 1519803
  have htrace : WordTrace (prefixWord ++ tailWord_1519803) baseStart_1519803 baseEnd_1519803 := by
    simpa [prefixWord, tailWord_1519803, baseEnd_1519803] using wordTrace_append hprefix tailTrace_1519803
  have hstable : (prefixWord ++ tailWord_1519803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519803).length < 2 ^ (prefixWord ++ tailWord_1519803).sum := by decide
  have hdescent : baseEnd_1519803 < baseStart_1519803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519823 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_1519823 : Nat := 118140960795 + 1519823 * 2 ^ 59
def prefixEnd_1519823 : Nat := 4983230072969 + 3 ^ 40 * 1519823 * 2
def baseEnd_1519823 : Nat := 780399708758312419222967

theorem tailTrace_1519823 : CollatzResearch.WordTrace tailWord_1519823 prefixEnd_1519823 780399708758312419222967 := by
  unfold tailWord_1519823
  simp only [CollatzResearch.WordTrace]
  refine ⟨55432498772948310948476123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36954999181965540632317415 55432498772948310948476123)
  ·
    refine ⟨83148748159422466422714185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55432498772948310948476123 83148748159422466422714185)
    ·
      refine ⟨62361561119566849817035639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83148748159422466422714185 62361561119566849817035639)
      ·
        refine ⟨93542341679350274725553459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62361561119566849817035639 93542341679350274725553459)
        ·
          refine ⟨140313512519025412088330189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93542341679350274725553459 140313512519025412088330189)
          ·
            refine ⟨52617567194634529533123821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140313512519025412088330189 52617567194634529533123821)
            ·
              refine ⟨19731587697987948574921433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52617567194634529533123821 19731587697987948574921433)
              ·
                refine ⟨14798690773490961431191075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19731587697987948574921433 14798690773490961431191075)
                ·
                  refine ⟨22198036160236442146786613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14798690773490961431191075 22198036160236442146786613)
                  ·
                    refine ⟨2081065890022166451261245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22198036160236442146786613 2081065890022166451261245)
                    ·
                      refine ⟨780399708758312419222967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2081065890022166451261245 780399708758312419222967)
                      ·
                        rfl

theorem cell23_1519823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_1519823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519823 prefixEnd_1519823 := by exact prefixLift 1519823
  have htrace : WordTrace (prefixWord ++ tailWord_1519823) baseStart_1519823 baseEnd_1519823 := by
    simpa [prefixWord, tailWord_1519823, baseEnd_1519823] using wordTrace_append hprefix tailTrace_1519823
  have hstable : (prefixWord ++ tailWord_1519823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519823).length < 2 ^ (prefixWord ++ tailWord_1519823).sum := by decide
  have hdescent : baseEnd_1519823 < baseStart_1519823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519847 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 5]
def baseStart_1519847 : Nat := 118140960795 + 1519847 * 2 ^ 59
def prefixEnd_1519847 : Nat := 4983230072969 + 3 ^ 40 * 1519847 * 2
def baseEnd_1519847 : Nat := 86712448032668925035873

theorem tailTrace_1519847 : CollatzResearch.WordTrace tailWord_1519847 prefixEnd_1519847 86712448032668925035873 := by
  unfold tailWord_1519847
  simp only [CollatzResearch.WordTrace]
  refine ⟨55433374124861363047349795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36955582749907575364899863 55433374124861363047349795)
  ·
    refine ⟨83150061187292044571024693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55433374124861363047349795 83150061187292044571024693)
    ·
      refine ⟨7795318236308629178533565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83150061187292044571024693 7795318236308629178533565)
      ·
        refine ⟨2923244338615735941950087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7795318236308629178533565 2923244338615735941950087)
        ·
          refine ⟨4384866507923603912925131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923244338615735941950087 4384866507923603912925131)
          ·
            refine ⟨6577299761885405869387697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384866507923603912925131 6577299761885405869387697)
            ·
              refine ⟨4932974821414054402040773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577299761885405869387697 4932974821414054402040773)
              ·
                refine ⟨924932779015135200382645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4932974821414054402040773 924932779015135200382645)
                ·
                  refine ⟨86712448032668925035873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 924932779015135200382645 86712448032668925035873)
                  ·
                    rfl

theorem cell23_1519847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 5].length) (baseStart_1519847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519847 prefixEnd_1519847 := by exact prefixLift 1519847
  have htrace : WordTrace (prefixWord ++ tailWord_1519847) baseStart_1519847 baseEnd_1519847 := by
    simpa [prefixWord, tailWord_1519847, baseEnd_1519847] using wordTrace_append hprefix tailTrace_1519847
  have hstable : (prefixWord ++ tailWord_1519847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519847).length < 2 ^ (prefixWord ++ tailWord_1519847).sum := by decide
  have hdescent : baseEnd_1519847 < baseStart_1519847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519873 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1519873 : Nat := 118140960795 + 1519873 * 2 ^ 59
def prefixEnd_1519873 : Nat := 4983230072969 + 3 ^ 40 * 1519873 * 2
def baseEnd_1519873 : Nat := 260141794263679074532579

theorem tailTrace_1519873 : CollatzResearch.WordTrace tailWord_1519873 prefixEnd_1519873 260141794263679074532579 := by
  unfold tailWord_1519873
  simp only [CollatzResearch.WordTrace]
  refine ⟨55434322422767169487796273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36956214948511446325197515 55434322422767169487796273)
  ·
    refine ⟨41575741817075377115847205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55434322422767169487796273 41575741817075377115847205)
    ·
      refine ⟨7795451590701633209221351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41575741817075377115847205 7795451590701633209221351)
      ·
        refine ⟨11693177386052449813832027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795451590701633209221351 11693177386052449813832027)
        ·
          refine ⟨17539766079078674720748041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11693177386052449813832027 17539766079078674720748041)
          ·
            refine ⟨13154824559309006040561031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17539766079078674720748041 13154824559309006040561031)
            ·
              refine ⟨19732236838963509060841547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13154824559309006040561031 19732236838963509060841547)
              ·
                refine ⟨29598355258445263591262321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19732236838963509060841547 29598355258445263591262321)
                ·
                  refine ⟨22198766443833947693446741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29598355258445263591262321 22198766443833947693446741)
                  ·
                    refine ⟨260141794263679074532579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22198766443833947693446741 260141794263679074532579)
                    ·
                      rfl

theorem cell23_1519873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1519873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519873 prefixEnd_1519873 := by exact prefixLift 1519873
  have htrace : WordTrace (prefixWord ++ tailWord_1519873) baseStart_1519873 baseEnd_1519873 := by
    simpa [prefixWord, tailWord_1519873, baseEnd_1519873] using wordTrace_append hprefix tailTrace_1519873
  have hstable : (prefixWord ++ tailWord_1519873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519873).length < 2 ^ (prefixWord ++ tailWord_1519873).sum := by decide
  have hdescent : baseEnd_1519873 < baseStart_1519873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519880 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1519880 : Nat := 118140960795 + 1519880 * 2 ^ 59
def prefixEnd_1519880 : Nat := 4983230072969 + 3 ^ 40 * 1519880 * 2
def baseEnd_1519880 : Nat := 780428977155618696210205

theorem tailTrace_1519880 : CollatzResearch.WordTrace tailWord_1519880 prefixEnd_1519880 780428977155618696210205 := by
  unfold tailWord_1519880
  simp only [CollatzResearch.WordTrace]
  refine ⟨27717288866870904841650547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36956385155827873122200729 27717288866870904841650547)
  ·
    refine ⟨41575933300306357262475821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27717288866870904841650547 41575933300306357262475821)
    ·
      refine ⟨15590974987614883973428433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41575933300306357262475821 15590974987614883973428433)
      ·
        refine ⟨11693231240711162980071325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15590974987614883973428433 11693231240711162980071325)
        ·
          refine ⟨4384961715266686117526747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11693231240711162980071325 4384961715266686117526747)
          ·
            refine ⟨6577442572900029176290121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384961715266686117526747 6577442572900029176290121)
            ·
              refine ⟨4933081929675021882217591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6577442572900029176290121 4933081929675021882217591)
              ·
                refine ⟨7399622894512532823326387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933081929675021882217591 7399622894512532823326387)
                ·
                  refine ⟨11099434341768799234989581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7399622894512532823326387 11099434341768799234989581)
                  ·
                    refine ⟨4162287878163299713121093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11099434341768799234989581 4162287878163299713121093)
                    ·
                      refine ⟨780428977155618696210205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4162287878163299713121093 780428977155618696210205)
                      ·
                        rfl

theorem cell23_1519880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1519880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519880 prefixEnd_1519880 := by exact prefixLift 1519880
  have htrace : WordTrace (prefixWord ++ tailWord_1519880) baseStart_1519880 baseEnd_1519880 := by
    simpa [prefixWord, tailWord_1519880, baseEnd_1519880] using wordTrace_append hprefix tailTrace_1519880
  have hstable : (prefixWord ++ tailWord_1519880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519880).length < 2 ^ (prefixWord ++ tailWord_1519880).sum := by decide
  have hdescent : baseEnd_1519880 < baseStart_1519880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519893 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_1519893 : Nat := 118140960795 + 1519893 * 2 ^ 59
def prefixEnd_1519893 : Nat := 4983230072969 + 3 ^ 40 * 1519893 * 2
def baseEnd_1519893 : Nat := 780435652404127145347645

theorem tailTrace_1519893 : CollatzResearch.WordTrace tailWord_1519893 prefixEnd_1519893 780435652404127145347645 := by
  unfold tailWord_1519893
  simp only [CollatzResearch.WordTrace]
  refine ⟨55435051882694712903524333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36956701255129808602349555 55435051882694712903524333)
  ·
    refine ⟨20788144456010517338821625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55435051882694712903524333 20788144456010517338821625)
    ·
      refine ⟨15591108342007888004116219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20788144456010517338821625 15591108342007888004116219)
      ·
        refine ⟨23386662513011832006174329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15591108342007888004116219 23386662513011832006174329)
        ·
          refine ⟨17539996884758874004630747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23386662513011832006174329 17539996884758874004630747)
          ·
            refine ⟨26309995327138311006946121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17539996884758874004630747 26309995327138311006946121)
            ·
              refine ⟨19732496495353733255209591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26309995327138311006946121 19732496495353733255209591)
              ·
                refine ⟨29598744743030599882814387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19732496495353733255209591 29598744743030599882814387)
                ·
                  refine ⟨44398117114545899824221581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29598744743030599882814387 44398117114545899824221581)
                  ·
                    refine ⟨16649293917954712434083093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44398117114545899824221581 16649293917954712434083093)
                    ·
                      refine ⟨780435652404127145347645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16649293917954712434083093 780435652404127145347645)
                      ·
                        rfl

theorem cell23_1519893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_1519893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519893 prefixEnd_1519893 := by exact prefixLift 1519893
  have htrace : WordTrace (prefixWord ++ tailWord_1519893) baseStart_1519893 baseEnd_1519893 := by
    simpa [prefixWord, tailWord_1519893, baseEnd_1519893] using wordTrace_append hprefix tailTrace_1519893
  have hstable : (prefixWord ++ tailWord_1519893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519893).length < 2 ^ (prefixWord ++ tailWord_1519893).sum := by decide
  have hdescent : baseEnd_1519893 < baseStart_1519893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519934 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1519934 : Nat := 118140960795 + 1519934 * 2 ^ 59
def prefixEnd_1519934 : Nat := 4983230072969 + 3 ^ 40 * 1519934 * 2
def baseEnd_1519934 : Nat := 780456705110961484934957

theorem tailTrace_1519934 : CollatzResearch.WordTrace tailWord_1519934 prefixEnd_1519934 780456705110961484934957 := by
  unfold tailWord_1519934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929568409443272113220857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36957698183697451270511237 6929568409443272113220857)
  ·
    refine ⟨5197176307082454084915643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6929568409443272113220857 5197176307082454084915643)
    ·
      refine ⟨7795764460623681127373465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5197176307082454084915643 7795764460623681127373465)
      ·
        refine ⟨5846823345467760845530099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7795764460623681127373465 5846823345467760845530099)
        ·
          refine ⟨8770235018201641268295149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846823345467760845530099 8770235018201641268295149)
          ·
            refine ⟨3288838131825615475610681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8770235018201641268295149 3288838131825615475610681)
            ·
              refine ⟨2466628598869211606708011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3288838131825615475610681 2466628598869211606708011)
              ·
                refine ⟨3699942898303817410062017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466628598869211606708011 3699942898303817410062017)
                ·
                  refine ⟨2774957173727863057546513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3699942898303817410062017 2774957173727863057546513)
                  ·
                    refine ⟨2081217880295897293159885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2774957173727863057546513 2081217880295897293159885)
                    ·
                      refine ⟨780456705110961484934957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2081217880295897293159885 780456705110961484934957)
                      ·
                        rfl

theorem cell23_1519934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1519934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1519934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1519934 prefixEnd_1519934 := by exact prefixLift 1519934
  have htrace : WordTrace (prefixWord ++ tailWord_1519934) baseStart_1519934 baseEnd_1519934 := by
    simpa [prefixWord, tailWord_1519934, baseEnd_1519934] using wordTrace_append hprefix tailTrace_1519934
  have hstable : (prefixWord ++ tailWord_1519934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519934).length < 2 ^ (prefixWord ++ tailWord_1519934).sum := by decide
  have hdescent : baseEnd_1519934 < baseStart_1519934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520001 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1520001 : Nat := 118140960795 + 1520001 * 2 ^ 59
def prefixEnd_1520001 : Nat := 4983230072969 + 3 ^ 40 * 1520001 * 2
def baseEnd_1520001 : Nat := 260163702771604240932383

theorem tailTrace_1520001 : CollatzResearch.WordTrace tailWord_1520001 prefixEnd_1520001 260163702771604240932383 := by
  unfold tailWord_1520001
  simp only [CollatzResearch.WordTrace]
  refine ⟨55438990966303447348455857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36959327310868964898970571 55438990966303447348455857)
  ·
    refine ⟨41579243224727585511341893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55438990966303447348455857 41579243224727585511341893)
    ·
      refine ⟨7796108104636422283376605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41579243224727585511341893 7796108104636422283376605)
      ·
        refine ⟨2923540539238658356266227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7796108104636422283376605 2923540539238658356266227)
        ·
          refine ⟨4385310808857987534399341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923540539238658356266227 4385310808857987534399341)
          ·
            refine ⟨1644491553321745325399753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4385310808857987534399341 1644491553321745325399753)
            ·
              refine ⟨1233368664991308994049815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644491553321745325399753 1233368664991308994049815)
              ·
                refine ⟨1850052997486963491074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233368664991308994049815 1850052997486963491074723)
                ·
                  refine ⟨2775079496230445236612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850052997486963491074723 2775079496230445236612085)
                  ·
                    refine ⟨260163702771604240932383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2775079496230445236612085 260163702771604240932383)
                    ·
                      rfl

theorem cell23_1520001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1520001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520001 prefixEnd_1520001 := by exact prefixLift 1520001
  have htrace : WordTrace (prefixWord ++ tailWord_1520001) baseStart_1520001 baseEnd_1520001 := by
    simpa [prefixWord, tailWord_1520001, baseEnd_1520001] using wordTrace_append hprefix tailTrace_1520001
  have hstable : (prefixWord ++ tailWord_1520001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520001).length < 2 ^ (prefixWord ++ tailWord_1520001).sum := by decide
  have hdescent : baseEnd_1520001 < baseStart_1520001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520004 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_1520004 : Nat := 118140960795 + 1520004 * 2 ^ 59
def prefixEnd_1520004 : Nat := 4983230072969 + 3 ^ 40 * 1520004 * 2
def baseEnd_1520004 : Nat := 780492648756776211059635

theorem tailTrace_1520004 : CollatzResearch.WordTrace tailWord_1520004 prefixEnd_1520004 780492648756776211059635 := by
  unfold tailWord_1520004
  simp only [CollatzResearch.WordTrace]
  refine ⟨27719550192646289430407533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36959400256861719240543377 27719550192646289430407533)
  ·
    refine ⟨10394831322242358536402825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27719550192646289430407533 10394831322242358536402825)
    ·
      refine ⟨7796123491681768902302119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10394831322242358536402825 7796123491681768902302119)
      ·
        refine ⟨11694185237522653353453179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7796123491681768902302119 11694185237522653353453179)
        ·
          refine ⟨17541277856283980030179769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11694185237522653353453179 17541277856283980030179769)
          ·
            refine ⟨13155958392212985022634827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17541277856283980030179769 13155958392212985022634827)
            ·
              refine ⟨19733937588319477533952241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13155958392212985022634827 19733937588319477533952241)
              ·
                refine ⟨14800453191239608150464181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19733937588319477533952241 14800453191239608150464181)
                ·
                  refine ⟨1387542486678713264106017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14800453191239608150464181 1387542486678713264106017)
                  ·
                    refine ⟨1040656865009034948079513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1387542486678713264106017 1040656865009034948079513)
                    ·
                      refine ⟨780492648756776211059635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040656865009034948079513 780492648756776211059635)
                      ·
                        rfl

theorem cell23_1520004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_1520004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520004 prefixEnd_1520004 := by exact prefixLift 1520004
  have htrace : WordTrace (prefixWord ++ tailWord_1520004) baseStart_1520004 baseEnd_1520004 := by
    simpa [prefixWord, tailWord_1520004, baseEnd_1520004] using wordTrace_append hprefix tailTrace_1520004
  have hstable : (prefixWord ++ tailWord_1520004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520004).length < 2 ^ (prefixWord ++ tailWord_1520004).sum := by decide
  have hdescent : baseEnd_1520004 < baseStart_1520004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520014 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_1520014 : Nat := 118140960795 + 1520014 * 2 ^ 59
def prefixEnd_1520014 : Nat := 4983230072969 + 3 ^ 40 * 1520014 * 2
def baseEnd_1520014 : Nat := 260165927854440390644863

theorem tailTrace_1520014 : CollatzResearch.WordTrace tailWord_1520014 prefixEnd_1520014 260165927854440390644863 := by
  unfold tailWord_1520014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929933139407043821084887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36959643410170900379119397 6929933139407043821084887)
  ·
    refine ⟨10394899709110565731627331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6929933139407043821084887 10394899709110565731627331)
    ·
      refine ⟨15592349563665848597440997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10394899709110565731627331 15592349563665848597440997)
      ·
        refine ⟨2923565543187346612020187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15592349563665848597440997 2923565543187346612020187)
        ·
          refine ⟨4385348314781019918030281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923565543187346612020187 4385348314781019918030281)
          ·
            refine ⟨3289011236085764938522711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4385348314781019918030281 3289011236085764938522711)
            ·
              refine ⟨4933516854128647407784067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289011236085764938522711 4933516854128647407784067)
              ·
                refine ⟨7400275281192971111676101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4933516854128647407784067 7400275281192971111676101)
                ·
                  refine ⟨1387551615223682083439269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7400275281192971111676101 1387551615223682083439269)
                  ·
                    refine ⟨260165927854440390644863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387551615223682083439269 260165927854440390644863)
                    ·
                      rfl

theorem cell23_1520014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_1520014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520014 prefixEnd_1520014 := by exact prefixLift 1520014
  have htrace : WordTrace (prefixWord ++ tailWord_1520014) baseStart_1520014 baseEnd_1520014 := by
    simpa [prefixWord, tailWord_1520014, baseEnd_1520014] using wordTrace_append hprefix tailTrace_1520014
  have hstable : (prefixWord ++ tailWord_1520014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520014).length < 2 ^ (prefixWord ++ tailWord_1520014).sum := by decide
  have hdescent : baseEnd_1520014 < baseStart_1520014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520050 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1520050 : Nat := 118140960795 + 1520050 * 2 ^ 59
def prefixEnd_1520050 : Nat := 4983230072969 + 3 ^ 40 * 1520050 * 2
def baseEnd_1520050 : Nat := 780516268866883031084423

theorem tailTrace_1520050 : CollatzResearch.WordTrace tailWord_1520050 prefixEnd_1520050 780516268866883031084423 := by
  unfold tailWord_1520050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860194535781482179247401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36960518762083952477993069 13860194535781482179247401)
  ·
    refine ⟨10395145901836111634435551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13860194535781482179247401 10395145901836111634435551)
    ·
      refine ⟨15592718852754167451653327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10395145901836111634435551 15592718852754167451653327)
      ·
        refine ⟨23389078279131251177479991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15592718852754167451653327 23389078279131251177479991)
        ·
          refine ⟨35083617418696876766219987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23389078279131251177479991 35083617418696876766219987)
          ·
            refine ⟨52625426128045315149329981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35083617418696876766219987 52625426128045315149329981)
            ·
              refine ⟨19734534798016993180998743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52625426128045315149329981 19734534798016993180998743)
              ·
                refine ⟨29601802197025489771498115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19734534798016993180998743 29601802197025489771498115)
                ·
                  refine ⟨44402703295538234657247173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29601802197025489771498115 44402703295538234657247173)
                  ·
                    refine ⟨8325506867913418998233845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44402703295538234657247173 8325506867913418998233845)
                    ·
                      refine ⟨780516268866883031084423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8325506867913418998233845 780516268866883031084423)
                      ·
                        rfl

theorem cell23_1520050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1520050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520050 prefixEnd_1520050 := by exact prefixLift 1520050
  have htrace : WordTrace (prefixWord ++ tailWord_1520050) baseStart_1520050 baseEnd_1520050 := by
    simpa [prefixWord, tailWord_1520050, baseEnd_1520050] using wordTrace_append hprefix tailTrace_1520050
  have hstable : (prefixWord ++ tailWord_1520050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520050).length < 2 ^ (prefixWord ++ tailWord_1520050).sum := by decide
  have hdescent : baseEnd_1520050 < baseStart_1520050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520080 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_1520080 : Nat := 118140960795 + 1520080 * 2 ^ 59
def prefixEnd_1520080 : Nat := 4983230072969 + 3 ^ 40 * 1520080 * 2
def baseEnd_1520080 : Nat := 780531673286517913709285

theorem tailTrace_1520080 : CollatzResearch.WordTrace tailWord_1520080 prefixEnd_1520080 780531673286517913709285 := by
  unfold tailWord_1520080
  simp only [CollatzResearch.WordTrace]
  refine ⟨27720936166508621920290847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36961248222011495893721129 27720936166508621920290847)
  ·
    refine ⟨41581404249762932880436271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27720936166508621920290847 41581404249762932880436271)
    ·
      refine ⟨62372106374644399320654407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41581404249762932880436271 62372106374644399320654407)
      ·
        refine ⟨93558159561966598980981611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62372106374644399320654407 93558159561966598980981611)
        ·
          refine ⟨140337239342949898471472417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93558159561966598980981611 140337239342949898471472417)
          ·
            refine ⟨105252929507212423853604313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140337239342949898471472417 105252929507212423853604313)
            ·
              refine ⟨78939697130409317890203235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105252929507212423853604313 78939697130409317890203235)
              ·
                refine ⟨118409545695613976835304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78939697130409317890203235 118409545695613976835304853)
                ·
                  refine ⟨5550447454481905164154915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118409545695613976835304853 5550447454481905164154915)
                  ·
                    refine ⟨8325671181722857746232373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5550447454481905164154915 8325671181722857746232373)
                    ·
                      refine ⟨780531673286517913709285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8325671181722857746232373 780531673286517913709285)
                      ·
                        rfl

theorem cell23_1520080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_1520080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520080 prefixEnd_1520080 := by exact prefixLift 1520080
  have htrace : WordTrace (prefixWord ++ tailWord_1520080) baseStart_1520080 baseEnd_1520080 := by
    simpa [prefixWord, tailWord_1520080, baseEnd_1520080] using wordTrace_append hprefix tailTrace_1520080
  have hstable : (prefixWord ++ tailWord_1520080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520080).length < 2 ^ (prefixWord ++ tailWord_1520080).sum := by decide
  have hdescent : baseEnd_1520080 < baseStart_1520080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520127 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_1520127 : Nat := 118140960795 + 1520127 * 2 ^ 59
def prefixEnd_1520127 : Nat := 4983230072969 + 3 ^ 40 * 1520127 * 2
def baseEnd_1520127 : Nat := 780555806877279229821569

theorem tailTrace_1520127 : CollatzResearch.WordTrace tailWord_1520127 prefixEnd_1520127 780555806877279229821569 := by
  unfold tailWord_1520127
  simp only [CollatzResearch.WordTrace]
  refine ⟨55443586563846970867542635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36962391042564647245028423 55443586563846970867542635)
  ·
    refine ⟨83165379845770456301313953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55443586563846970867542635 83165379845770456301313953)
    ·
      refine ⟨62374034884327842225985465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83165379845770456301313953 62374034884327842225985465)
      ·
        refine ⟨46780526163245881669489099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62374034884327842225985465 46780526163245881669489099)
        ·
          refine ⟨70170789244868822504233649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46780526163245881669489099 70170789244868822504233649)
          ·
            refine ⟨52628091933651616878175237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70170789244868822504233649 52628091933651616878175237)
            ·
              refine ⟨9867767237559678164657857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52628091933651616878175237 9867767237559678164657857)
              ·
                refine ⟨7400825428169758623493393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9867767237559678164657857 7400825428169758623493393)
                ·
                  refine ⟨5550619071127318967620045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7400825428169758623493393 5550619071127318967620045)
                  ·
                    refine ⟨2081482151672744612857517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5550619071127318967620045 2081482151672744612857517)
                    ·
                      refine ⟨780555806877279229821569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2081482151672744612857517 780555806877279229821569)
                      ·
                        rfl

theorem cell23_1520127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_1520127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520127 prefixEnd_1520127 := by exact prefixLift 1520127
  have htrace : WordTrace (prefixWord ++ tailWord_1520127) baseStart_1520127 baseEnd_1520127 := by
    simpa [prefixWord, tailWord_1520127, baseEnd_1520127] using wordTrace_append hprefix tailTrace_1520127
  have hstable : (prefixWord ++ tailWord_1520127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520127).length < 2 ^ (prefixWord ++ tailWord_1520127).sum := by decide
  have hdescent : baseEnd_1520127 < baseStart_1520127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520141 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1520141 : Nat := 118140960795 + 1520141 * 2 ^ 59
def prefixEnd_1520141 : Nat := 4983230072969 + 3 ^ 40 * 1520141 * 2
def baseEnd_1520141 : Nat := 780562995606442175046505

theorem tailTrace_1520141 : CollatzResearch.WordTrace tailWord_1520141 prefixEnd_1520141 780562995606442175046505 := by
  unfold tailWord_1520141
  simp only [CollatzResearch.WordTrace]
  refine ⟨55444097185796251258552277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36962731457197500839034851 55444097185796251258552277)
  ·
    refine ⟨1299471027792099638872319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 55444097185796251258552277 1299471027792099638872319)
    ·
      refine ⟨1949206541688149458308479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299471027792099638872319 1949206541688149458308479)
      ·
        refine ⟨2923809812532224187462719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949206541688149458308479 2923809812532224187462719)
        ·
          refine ⟨4385714718798336281194079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923809812532224187462719 4385714718798336281194079)
          ·
            refine ⟨6578572078197504421791119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385714718798336281194079 6578572078197504421791119)
            ·
              refine ⟨9867858117296256632686679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6578572078197504421791119 9867858117296256632686679)
              ·
                refine ⟨14801787175944384949030019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9867858117296256632686679 14801787175944384949030019)
                ·
                  refine ⟨22202680763916577423545029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14801787175944384949030019 22202680763916577423545029)
                  ·
                    refine ⟨4163002643234358266914693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22202680763916577423545029 4163002643234358266914693)
                    ·
                      refine ⟨780562995606442175046505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4163002643234358266914693 780562995606442175046505)
                      ·
                        rfl

theorem cell23_1520141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1520141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520141 prefixEnd_1520141 := by exact prefixLift 1520141
  have htrace : WordTrace (prefixWord ++ tailWord_1520141) baseStart_1520141 baseEnd_1520141 := by
    simpa [prefixWord, tailWord_1520141, baseEnd_1520141] using wordTrace_append hprefix tailTrace_1520141
  have hstable : (prefixWord ++ tailWord_1520141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520141).length < 2 ^ (prefixWord ++ tailWord_1520141).sum := by decide
  have hdescent : baseEnd_1520141 < baseStart_1520141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520184 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 4, 4, 2]
def baseStart_1520184 : Nat := 118140960795 + 1520184 * 2 ^ 59
def prefixEnd_1520184 : Nat := 4983230072969 + 3 ^ 40 * 1520184 * 2
def baseEnd_1520184 : Nat := 780585075274585506808807

theorem tailTrace_1520184 : CollatzResearch.WordTrace tailWord_1520184 prefixEnd_1520184 780585075274585506808807 := by
  unfold tailWord_1520184
  simp only [CollatzResearch.WordTrace]
  refine ⟨27722832762320234801183803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36963777016426979734911737 27722832762320234801183803)
  ·
    refine ⟨41584249143480352201775705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27722832762320234801183803 41584249143480352201775705)
    ·
      refine ⟨31188186857610264151331779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41584249143480352201775705 31188186857610264151331779)
      ·
        refine ⟨46782280286415396226997669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31188186857610264151331779 46782280286415396226997669)
        ·
          refine ⟨8771677553702886792562063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46782280286415396226997669 8771677553702886792562063)
          ·
            refine ⟨13157516330554330188843095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8771677553702886792562063 13157516330554330188843095)
            ·
              refine ⟨19736274495831495283264643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13157516330554330188843095 19736274495831495283264643)
              ·
                refine ⟨29604411743747242924896965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19736274495831495283264643 29604411743747242924896965)
                ·
                  refine ⟨5550827201952608048418181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29604411743747242924896965 5550827201952608048418181)
                  ·
                    refine ⟨1040780100366114009078409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5550827201952608048418181 1040780100366114009078409)
                    ·
                      refine ⟨780585075274585506808807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040780100366114009078409 780585075274585506808807)
                      ·
                        rfl

theorem cell23_1520184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_1520184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520184 prefixEnd_1520184 := by exact prefixLift 1520184
  have htrace : WordTrace (prefixWord ++ tailWord_1520184) baseStart_1520184 baseEnd_1520184 := by
    simpa [prefixWord, tailWord_1520184, baseEnd_1520184] using wordTrace_append hprefix tailTrace_1520184
  have hstable : (prefixWord ++ tailWord_1520184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520184).length < 2 ^ (prefixWord ++ tailWord_1520184).sum := by decide
  have hdescent : baseEnd_1520184 < baseStart_1520184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520207 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 6]
def baseStart_1520207 : Nat := 118140960795 + 1520207 * 2 ^ 59
def prefixEnd_1520207 : Nat := 4983230072969 + 3 ^ 40 * 1520207 * 2
def baseEnd_1520207 : Nat := 86732987258848768535689

theorem tailTrace_1520207 : CollatzResearch.WordTrace tailWord_1520207 prefixEnd_1520207 86732987258848768535689 := by
  unfold tailWord_1520207
  simp only [CollatzResearch.WordTrace]
  refine ⟨55446504403557144530454875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36964336269038096353636583 55446504403557144530454875)
  ·
    refine ⟨83169756605335716795682313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55446504403557144530454875 83169756605335716795682313)
    ·
      refine ⟨62377317454001787596761735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83169756605335716795682313 62377317454001787596761735)
      ·
        refine ⟨93565976181002681395142603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62377317454001787596761735 93565976181002681395142603)
        ·
          refine ⟨140348964271504022092713905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93565976181002681395142603 140348964271504022092713905)
          ·
            refine ⟨105261723203628016569535429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140348964271504022092713905 105261723203628016569535429)
            ·
              refine ⟨19736573100680253106787893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105261723203628016569535429 19736573100680253106787893)
              ·
                refine ⟨1850303728188773728761365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19736573100680253106787893 1850303728188773728761365)
                ·
                  refine ⟨86732987258848768535689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1850303728188773728761365 86732987258848768535689)
                  ·
                    rfl

theorem cell23_1520207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 6].length) (baseStart_1520207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520207 prefixEnd_1520207 := by exact prefixLift 1520207
  have htrace : WordTrace (prefixWord ++ tailWord_1520207) baseStart_1520207 baseEnd_1520207 := by
    simpa [prefixWord, tailWord_1520207, baseEnd_1520207] using wordTrace_append hprefix tailTrace_1520207
  have hstable : (prefixWord ++ tailWord_1520207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520207).length < 2 ^ (prefixWord ++ tailWord_1520207).sum := by decide
  have hdescent : baseEnd_1520207 < baseStart_1520207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520245 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1520245 : Nat := 118140960795 + 1520245 * 2 ^ 59
def prefixEnd_1520245 : Nat := 4983230072969 + 3 ^ 40 * 1520245 * 2
def baseEnd_1520245 : Nat := 260205465864836589382009

theorem tailTrace_1520245 : CollatzResearch.WordTrace tailWord_1520245 prefixEnd_1520245 260205465864836589382009 := by
  unfold tailWord_1520245
  simp only [CollatzResearch.WordTrace]
  refine ⟨55447890377419477020338189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36965260251612984680225459 55447890377419477020338189)
  ·
    refine ⟨20792958891532303882626821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55447890377419477020338189 20792958891532303882626821)
    ·
      refine ⟨3898679792162306977992529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20792958891532303882626821 3898679792162306977992529)
      ·
        refine ⟨2924009844121730233494397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3898679792162306977992529 2924009844121730233494397)
        ·
          refine ⟨1096503691545648837560399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2924009844121730233494397 1096503691545648837560399)
          ·
            refine ⟨1644755537318473256340599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096503691545648837560399 1644755537318473256340599)
            ·
              refine ⟨2467133305977709884510899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644755537318473256340599 2467133305977709884510899)
              ·
                refine ⟨3700699958966564826766349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467133305977709884510899 3700699958966564826766349)
                ·
                  refine ⟨1387762484612461810037381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3700699958966564826766349 1387762484612461810037381)
                  ·
                    refine ⟨260205465864836589382009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387762484612461810037381 260205465864836589382009)
                    ·
                      rfl

theorem cell23_1520245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1520245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520245 prefixEnd_1520245 := by exact prefixLift 1520245
  have htrace : WordTrace (prefixWord ++ tailWord_1520245) baseStart_1520245 baseEnd_1520245 := by
    simpa [prefixWord, tailWord_1520245, baseEnd_1520245] using wordTrace_append hprefix tailTrace_1520245
  have hstable : (prefixWord ++ tailWord_1520245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520245).length < 2 ^ (prefixWord ++ tailWord_1520245).sum := by decide
  have hdescent : baseEnd_1520245 < baseStart_1520245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520277 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_1520277 : Nat := 118140960795 + 1520277 * 2 ^ 59
def prefixEnd_1520277 : Nat := 4983230072969 + 3 ^ 40 * 1520277 * 2
def baseEnd_1520277 : Nat := 780632828975453642945879

theorem tailTrace_1520277 : CollatzResearch.WordTrace tailWord_1520277 prefixEnd_1520277 780632828975453642945879 := by
  unfold tailWord_1520277
  simp only [CollatzResearch.WordTrace]
  refine ⟨55449057513303546485503085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36966038342202364323668723 55449057513303546485503085)
  ·
    refine ⟨20793396567488829932063657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55449057513303546485503085 20793396567488829932063657)
    ·
      refine ⟨15595047425616622449047743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20793396567488829932063657 15595047425616622449047743)
      ·
        refine ⟨23392571138424933673571615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15595047425616622449047743 23392571138424933673571615)
        ·
          refine ⟨35088856707637400510357423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23392571138424933673571615 35088856707637400510357423)
          ·
            refine ⟨52633285061456100765536135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35088856707637400510357423 52633285061456100765536135)
            ·
              refine ⟨78949927592184151148304203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52633285061456100765536135 78949927592184151148304203)
              ·
                refine ⟨118424891388276226722456305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78949927592184151148304203 118424891388276226722456305)
                ·
                  refine ⟨88818668541207170041842229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118424891388276226722456305 88818668541207170041842229)
                  ·
                    refine ⟨8326750175738172191422709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88818668541207170041842229 8326750175738172191422709)
                    ·
                      refine ⟨780632828975453642945879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8326750175738172191422709 780632828975453642945879)
                      ·
                        rfl

theorem cell23_1520277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_1520277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520277 prefixEnd_1520277 := by exact prefixLift 1520277
  have htrace : WordTrace (prefixWord ++ tailWord_1520277) baseStart_1520277 baseEnd_1520277 := by
    simpa [prefixWord, tailWord_1520277, baseEnd_1520277] using wordTrace_append hprefix tailTrace_1520277
  have hstable : (prefixWord ++ tailWord_1520277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520277).length < 2 ^ (prefixWord ++ tailWord_1520277).sum := by decide
  have hdescent : baseEnd_1520277 < baseStart_1520277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520284 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1520284 : Nat := 118140960795 + 1520284 * 2 ^ 59
def prefixEnd_1520284 : Nat := 4983230072969 + 3 ^ 40 * 1520284 * 2
def baseEnd_1520284 : Nat := 260212141113345038519449

theorem tailTrace_1520284 : CollatzResearch.WordTrace tailWord_1520284 prefixEnd_1520284 260212141113345038519449 := by
  unfold tailWord_1520284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724656412139093340503953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36966208549518791120671937 27724656412139093340503953)
  ·
    refine ⟨20793492309104320005377965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27724656412139093340503953 20793492309104320005377965)
    ·
      refine ⟨7797559615914120002016737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20793492309104320005377965 7797559615914120002016737)
      ·
        refine ⟨5848169711935590001512553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7797559615914120002016737 5848169711935590001512553)
        ·
          refine ⟨4386127283951692501134415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5848169711935590001512553 4386127283951692501134415)
          ·
            refine ⟨6579190925927538751701623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386127283951692501134415 6579190925927538751701623)
            ·
              refine ⟨9868786388891308127552435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579190925927538751701623 9868786388891308127552435)
              ·
                refine ⟨14803179583336962191328653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9868786388891308127552435 14803179583336962191328653)
                ·
                  refine ⟨5551192343751360821748245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14803179583336962191328653 5551192343751360821748245)
                  ·
                    refine ⟨260212141113345038519449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5551192343751360821748245 260212141113345038519449)
                    ·
                      rfl

theorem cell23_1520284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1520284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520284 prefixEnd_1520284 := by exact prefixLift 1520284
  have htrace : WordTrace (prefixWord ++ tailWord_1520284) baseStart_1520284 baseEnd_1520284 := by
    simpa [prefixWord, tailWord_1520284, baseEnd_1520284] using wordTrace_append hprefix tailTrace_1520284
  have hstable : (prefixWord ++ tailWord_1520284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520284).length < 2 ^ (prefixWord ++ tailWord_1520284).sum := by decide
  have hdescent : baseEnd_1520284 < baseStart_1520284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520288 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 1, 5]
def baseStart_1520288 : Nat := 118140960795 + 1520288 * 2 ^ 59
def prefixEnd_1520288 : Nat := 4983230072969 + 3 ^ 40 * 1520288 * 2
def baseEnd_1520288 : Nat := 260212825754217699969443

theorem tailTrace_1520288 : CollatzResearch.WordTrace tailWord_1520288 prefixEnd_1520288 260212825754217699969443 := by
  unfold tailWord_1520288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724729358131847682076759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36966305810842463576102345 27724729358131847682076759)
  ·
    refine ⟨41587094037197771523115139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27724729358131847682076759 41587094037197771523115139)
    ·
      refine ⟨62380641055796657284672709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41587094037197771523115139 62380641055796657284672709)
      ·
        refine ⟨11696370197961873240876133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62380641055796657284672709 11696370197961873240876133)
        ·
          refine ⟨2193069412117851232664275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11696370197961873240876133 2193069412117851232664275)
          ·
            refine ⟨3289604118176776848996413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193069412117851232664275 3289604118176776848996413)
            ·
              refine ⟨1233601544316291318373655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3289604118176776848996413 1233601544316291318373655)
              ·
                refine ⟨1850402316474436977560483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233601544316291318373655 1850402316474436977560483)
                ·
                  refine ⟨2775603474711655466340725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850402316474436977560483 2775603474711655466340725)
                  ·
                    refine ⟨260212825754217699969443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2775603474711655466340725 260212825754217699969443)
                    ·
                      rfl

theorem cell23_1520288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 5].length) (baseStart_1520288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520288 prefixEnd_1520288 := by exact prefixLift 1520288
  have htrace : WordTrace (prefixWord ++ tailWord_1520288) baseStart_1520288 baseEnd_1520288 := by
    simpa [prefixWord, tailWord_1520288, baseEnd_1520288] using wordTrace_append hprefix tailTrace_1520288
  have hstable : (prefixWord ++ tailWord_1520288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520288).length < 2 ^ (prefixWord ++ tailWord_1520288).sum := by decide
  have hdescent : baseEnd_1520288 < baseStart_1520288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520291 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 7, 2, 2]
def baseStart_1520291 : Nat := 118140960795 + 1520291 * 2 ^ 59
def prefixEnd_1520291 : Nat := 4983230072969 + 3 ^ 40 * 1520291 * 2
def baseEnd_1520291 : Nat := 780640017704616588170815

theorem tailTrace_1520291 : CollatzResearch.WordTrace tailWord_1520291 prefixEnd_1520291 780640017704616588170815 := by
  unfold tailWord_1520291
  simp only [CollatzResearch.WordTrace]
  refine ⟨55449568135252826876512727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36966378756835217917675151 55449568135252826876512727)
  ·
    refine ⟨83174352202879240314769091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55449568135252826876512727 83174352202879240314769091)
    ·
      refine ⟨124761528304318860472153637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83174352202879240314769091 124761528304318860472153637)
      ·
        refine ⟨23392786557059786338528807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124761528304318860472153637 23392786557059786338528807)
        ·
          refine ⟨35089179835589679507793211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23392786557059786338528807 35089179835589679507793211)
          ·
            refine ⟨52633769753384519261689817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35089179835589679507793211 52633769753384519261689817)
            ·
              refine ⟨39475327315038389446267363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52633769753384519261689817 39475327315038389446267363)
              ·
                refine ⟨59212990972557584169401045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39475327315038389446267363 59212990972557584169401045)
                ·
                  refine ⟨1387804475919318378970337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 59212990972557584169401045 1387804475919318378970337)
                  ·
                    refine ⟨1040853356939488784227753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1387804475919318378970337 1040853356939488784227753)
                    ·
                      refine ⟨780640017704616588170815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1040853356939488784227753 780640017704616588170815)
                      ·
                        rfl

theorem cell23_1520291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_1520291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520291 prefixEnd_1520291 := by exact prefixLift 1520291
  have htrace : WordTrace (prefixWord ++ tailWord_1520291) baseStart_1520291 baseEnd_1520291 := by
    simpa [prefixWord, tailWord_1520291, baseEnd_1520291] using wordTrace_append hprefix tailTrace_1520291
  have hstable : (prefixWord ++ tailWord_1520291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520291).length < 2 ^ (prefixWord ++ tailWord_1520291).sum := by decide
  have hdescent : baseEnd_1520291 < baseStart_1520291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520302 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1520302 : Nat := 118140960795 + 1520302 * 2 ^ 59
def prefixEnd_1520302 : Nat := 4983230072969 + 3 ^ 40 * 1520302 * 2
def baseEnd_1520302 : Nat := 780645665991816045133265

theorem tailTrace_1520302 : CollatzResearch.WordTrace tailWord_1520302 prefixEnd_1520302 780645665991816045133265 := by
  unfold tailWord_1520302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931246167276621969395395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36966646225475317170108773 6931246167276621969395395)
  ·
    refine ⟨10396869250914932954093093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6931246167276621969395395 10396869250914932954093093)
    ·
      refine ⟨1949412984546549928892455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10396869250914932954093093 1949412984546549928892455)
      ·
        refine ⟨2924119476819824893338683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949412984546549928892455 2924119476819824893338683)
        ·
          refine ⟨4386179215229737340008025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924119476819824893338683 4386179215229737340008025)
          ·
            refine ⟨3289634411422303005006019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4386179215229737340008025 3289634411422303005006019)
            ·
              refine ⟨4934451617133454507509029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289634411422303005006019 4934451617133454507509029)
              ·
                refine ⟨925209678212522720157943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4934451617133454507509029 925209678212522720157943)
                ·
                  refine ⟨1387814517318784080236915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925209678212522720157943 1387814517318784080236915)
                  ·
                    refine ⟨2081721775978176120355373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1387814517318784080236915 2081721775978176120355373)
                    ·
                      refine ⟨780645665991816045133265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2081721775978176120355373 780645665991816045133265)
                      ·
                        rfl

theorem cell23_1520302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1520302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520302 prefixEnd_1520302 := by exact prefixLift 1520302
  have htrace : WordTrace (prefixWord ++ tailWord_1520302) baseStart_1520302 baseEnd_1520302 := by
    simpa [prefixWord, tailWord_1520302, baseEnd_1520302] using wordTrace_append hprefix tailTrace_1520302
  have hstable : (prefixWord ++ tailWord_1520302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520302).length < 2 ^ (prefixWord ++ tailWord_1520302).sum := by decide
  have hdescent : baseEnd_1520302 < baseStart_1520302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520347 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_1520347 : Nat := 118140960795 + 1520347 * 2 ^ 59
def prefixEnd_1520347 : Nat := 4983230072969 + 3 ^ 40 * 1520347 * 2
def baseEnd_1520347 : Nat := 780668772621268369070557

theorem tailTrace_1520347 : CollatzResearch.WordTrace tailWord_1520347 prefixEnd_1520347 780668772621268369070557 := by
  unfold tailWord_1520347
  simp only [CollatzResearch.WordTrace]
  refine ⟨55451610623049948440551295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36967740415366632293700863 55451610623049948440551295)
  ·
    refine ⟨83177415934574922660826943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55451610623049948440551295 83177415934574922660826943)
    ·
      refine ⟨124766123901862383991240415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83177415934574922660826943 124766123901862383991240415)
      ·
        refine ⟨187149185852793575986860623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124766123901862383991240415 187149185852793575986860623)
        ·
          refine ⟨280723778779190363980290935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187149185852793575986860623 280723778779190363980290935)
          ·
            refine ⟨421085668168785545970436403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280723778779190363980290935 421085668168785545970436403)
            ·
              refine ⟨631628502253178318955654605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421085668168785545970436403 631628502253178318955654605)
              ·
                refine ⟨236860688344941869608370477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631628502253178318955654605 236860688344941869608370477)
                ·
                  refine ⟨88822758129353201103138929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236860688344941869608370477 88822758129353201103138929)
                  ·
                    refine ⟨66617068597014900827354197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88822758129353201103138929 66617068597014900827354197)
                    ·
                      refine ⟨780668772621268369070557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66617068597014900827354197 780668772621268369070557)
                      ·
                        rfl

theorem cell23_1520347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_1520347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520347 prefixEnd_1520347 := by exact prefixLift 1520347
  have htrace : WordTrace (prefixWord ++ tailWord_1520347) baseStart_1520347 baseEnd_1520347 := by
    simpa [prefixWord, tailWord_1520347, baseEnd_1520347] using wordTrace_append hprefix tailTrace_1520347
  have hstable : (prefixWord ++ tailWord_1520347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520347).length < 2 ^ (prefixWord ++ tailWord_1520347).sum := by decide
  have hdescent : baseEnd_1520347 < baseStart_1520347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520372 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1520372 : Nat := 118140960795 + 1520372 * 2 ^ 59
def prefixEnd_1520372 : Nat := 4983230072969 + 3 ^ 40 * 1520372 * 2
def baseEnd_1520372 : Nat := 780681609637630771257943

theorem tailTrace_1520372 : CollatzResearch.WordTrace tailWord_1520372 prefixEnd_1520372 780681609637630771257943 := by
  unfold tailWord_1520372
  simp only [CollatzResearch.WordTrace]
  refine ⟨27726261223979688855105685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36968348298639585140140913 27726261223979688855105685)
  ·
    refine ⟨1299668494874047915083079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27726261223979688855105685 1299668494874047915083079)
    ·
      refine ⟨1949502742311071872624619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299668494874047915083079 1949502742311071872624619)
      ·
        refine ⟨2924254113466607808936929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949502742311071872624619 2924254113466607808936929)
        ·
          refine ⟨2193190585099955856702697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924254113466607808936929 2193190585099955856702697)
          ·
            refine ⟨1644892938824966892527023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2193190585099955856702697 1644892938824966892527023)
            ·
              refine ⟨2467339408237450338790535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644892938824966892527023 2467339408237450338790535)
              ·
                refine ⟨3701009112356175508185803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467339408237450338790535 3701009112356175508185803)
                ·
                  refine ⟨5551513668534263262278705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701009112356175508185803 5551513668534263262278705)
                  ·
                    refine ⟨4163635251400697446709029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5551513668534263262278705 4163635251400697446709029)
                    ·
                      refine ⟨780681609637630771257943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4163635251400697446709029 780681609637630771257943)
                      ·
                        rfl

theorem cell23_1520372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1520372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520372 prefixEnd_1520372 := by exact prefixLift 1520372
  have htrace : WordTrace (prefixWord ++ tailWord_1520372) baseStart_1520372 baseEnd_1520372 := by
    simpa [prefixWord, tailWord_1520372, baseEnd_1520372] using wordTrace_append hprefix tailTrace_1520372
  have hstable : (prefixWord ++ tailWord_1520372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520372).length < 2 ^ (prefixWord ++ tailWord_1520372).sum := by decide
  have hdescent : baseEnd_1520372 < baseStart_1520372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520426 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1520426 : Nat := 118140960795 + 1520426 * 2 ^ 59
def prefixEnd_1520426 : Nat := 4983230072969 + 3 ^ 40 * 1520426 * 2
def baseEnd_1520426 : Nat := 780709337592973559982695

theorem tailTrace_1520426 : CollatzResearch.WordTrace tailWord_1520426 prefixEnd_1520426 780709337592973559982695 := by
  unfold tailWord_1520426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13863622997440936233169283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36969661326509163288451421 13863622997440936233169283)
  ·
    refine ⟨20795434496161404349753925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13863622997440936233169283 20795434496161404349753925)
    ·
      refine ⟨3899143968030263315578861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20795434496161404349753925 3899143968030263315578861)
      ·
        refine ⟨1462178988011348743342073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3899143968030263315578861 1462178988011348743342073)
        ·
          refine ⟨1096634241008511557506555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462178988011348743342073 1096634241008511557506555)
          ·
            refine ⟨1644951361512767336259833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096634241008511557506555 1644951361512767336259833)
            ·
              refine ⟨1233713521134575502194875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644951361512767336259833 1233713521134575502194875)
              ·
                refine ⟨1850570281701863253292313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233713521134575502194875 1850570281701863253292313)
                ·
                  refine ⟨1387927711276397439969235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1850570281701863253292313 1387927711276397439969235)
                  ·
                    refine ⟨2081891566914596159953853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1387927711276397439969235 2081891566914596159953853)
                    ·
                      refine ⟨780709337592973559982695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2081891566914596159953853 780709337592973559982695)
                      ·
                        rfl

theorem cell23_1520426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1520426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1520426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1520426 prefixEnd_1520426 := by exact prefixLift 1520426
  have htrace : WordTrace (prefixWord ++ tailWord_1520426) baseStart_1520426 baseEnd_1520426 := by
    simpa [prefixWord, tailWord_1520426, baseEnd_1520426] using wordTrace_append hprefix tailTrace_1520426
  have hstable : (prefixWord ++ tailWord_1520426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520426).length < 2 ^ (prefixWord ++ tailWord_1520426).sum := by decide
  have hdescent : baseEnd_1520426 < baseStart_1520426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
