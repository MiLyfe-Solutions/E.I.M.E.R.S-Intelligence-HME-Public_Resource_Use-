import V185TrunkScan23Chunk1394

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8262823 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 1, 5]
def baseStart_8262823 : Nat := 118140960795 + 8262823 * 2 ^ 59
def prefixEnd_8262823 : Nat := 4983230072969 + 3 ^ 40 * 8262823 * 2
def baseEnd_8262823 : Nat := 1414266587341810133570825

theorem tailTrace_8262823 : CollatzResearch.WordTrace tailWord_8262823 prefixEnd_8262823 1414266587341810133570825 := by
  unfold tailWord_8262823
  simp only [CollatzResearch.WordTrace]
  refine ⟨301369913344210923663905123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200913275562807282442603415 301369913344210923663905123)
  ·
    refine ⟨452054870016316385495857685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301369913344210923663905123 452054870016316385495857685)
    ·
      refine ⟨21190072032014830570118329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 452054870016316385495857685 21190072032014830570118329)
      ·
        refine ⟨15892554024011122927588747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21190072032014830570118329 15892554024011122927588747)
        ·
          refine ⟨23838831036016684391383121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15892554024011122927588747 23838831036016684391383121)
          ·
            refine ⟨17879123277012513293537341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23838831036016684391383121 17879123277012513293537341)
            ·
              refine ⟨6704671228879692485076503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17879123277012513293537341 6704671228879692485076503)
              ·
                refine ⟨10057006843319538727614755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704671228879692485076503 10057006843319538727614755)
                ·
                  refine ⟨15085510264979308091422133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057006843319538727614755 15085510264979308091422133)
                  ·
                    refine ⟨1414266587341810133570825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15085510264979308091422133 1414266587341810133570825)
                    ·
                      rfl

theorem cell23_8262823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_8262823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262823 prefixEnd_8262823 := by exact prefixLift 8262823
  have htrace : WordTrace (prefixWord ++ tailWord_8262823) baseStart_8262823 baseEnd_8262823 := by
    simpa [prefixWord, tailWord_8262823, baseEnd_8262823] using wordTrace_append hprefix tailTrace_8262823
  have hstable : (prefixWord ++ tailWord_8262823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262823).length < 2 ^ (prefixWord ++ tailWord_8262823).sum := by decide
  have hdescent : baseEnd_8262823 < baseStart_8262823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262846 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_8262846 : Nat := 118140960795 + 8262846 * 2 ^ 59
def prefixEnd_8262846 : Nat := 4983230072969 + 3 ^ 40 * 8262846 * 2
def baseEnd_8262846 : Nat := 4242811572080483810724869

theorem tailTrace_8262846 : CollatzResearch.WordTrace tailWord_8262846 prefixEnd_8262846 4242811572080483810724869 := by
  unfold tailWord_8262846
  simp only [CollatzResearch.WordTrace]
  refine ⟨37671344027890949823999049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200913834815418399061328261 37671344027890949823999049)
  ·
    refine ⟨28253508020918212367999287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37671344027890949823999049 28253508020918212367999287)
    ·
      refine ⟨42380262031377318551998931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28253508020918212367999287 42380262031377318551998931)
      ·
        refine ⟨63570393047065977827998397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42380262031377318551998931 63570393047065977827998397)
        ·
          refine ⟨23838897392649741685499399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63570393047065977827998397 23838897392649741685499399)
          ·
            refine ⟨35758346088974612528249099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23838897392649741685499399 35758346088974612528249099)
            ·
              refine ⟨53637519133461918792373649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35758346088974612528249099 53637519133461918792373649)
              ·
                refine ⟨40228139350096439094280237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53637519133461918792373649 40228139350096439094280237)
                ·
                  refine ⟨15085552256286164660355089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40228139350096439094280237 15085552256286164660355089)
                  ·
                    refine ⟨11314164192214623495266317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15085552256286164660355089 11314164192214623495266317)
                    ·
                      refine ⟨4242811572080483810724869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314164192214623495266317 4242811572080483810724869)
                      ·
                        rfl

theorem cell23_8262846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_8262846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262846 prefixEnd_8262846 := by exact prefixLift 8262846
  have htrace : WordTrace (prefixWord ++ tailWord_8262846) baseStart_8262846 baseEnd_8262846 := by
    simpa [prefixWord, tailWord_8262846, baseEnd_8262846] using wordTrace_append hprefix tailTrace_8262846
  have hstable : (prefixWord ++ tailWord_8262846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262846).length < 2 ^ (prefixWord ++ tailWord_8262846).sum := by decide
  have hdescent : baseEnd_8262846 < baseStart_8262846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262877 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_8262877 : Nat := 118140960795 + 8262877 * 2 ^ 59
def prefixEnd_8262877 : Nat := 4983230072969 + 3 ^ 40 * 8262877 * 2
def baseEnd_8262877 : Nat := 4242827489980773189437227

theorem tailTrace_8262877 : CollatzResearch.WordTrace tailWord_8262877 prefixEnd_8262877 4242827489980773189437227 := by
  unfold tailWord_8262877
  simp only [CollatzResearch.WordTrace]
  refine ⟨301371882886015290886370885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200914588590676860590913923 301371882886015290886370885)
  ·
    refine ⟨56507228041127867041194541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301371882886015290886370885 56507228041127867041194541)
    ·
      refine ⟨21190210515422950140447953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56507228041127867041194541 21190210515422950140447953)
      ·
        refine ⟨15892657886567212605335965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21190210515422950140447953 15892657886567212605335965)
        ·
          refine ⟨5959746707462704727000987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15892657886567212605335965 5959746707462704727000987)
          ·
            refine ⟨8939620061194057090501481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959746707462704727000987 8939620061194057090501481)
            ·
              refine ⟨6704715045895542817876111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8939620061194057090501481 6704715045895542817876111)
              ·
                refine ⟨10057072568843314226814167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704715045895542817876111 10057072568843314226814167)
                ·
                  refine ⟨15085608853264971340221251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057072568843314226814167 15085608853264971340221251)
                  ·
                    refine ⟨22628413279897457010331877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15085608853264971340221251 22628413279897457010331877)
                    ·
                      refine ⟨4242827489980773189437227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22628413279897457010331877 4242827489980773189437227)
                      ·
                        rfl

theorem cell23_8262877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_8262877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262877 prefixEnd_8262877 := by exact prefixLift 8262877
  have htrace : WordTrace (prefixWord ++ tailWord_8262877) baseStart_8262877 baseEnd_8262877 := by
    simpa [prefixWord, tailWord_8262877, baseEnd_8262877] using wordTrace_append hprefix tailTrace_8262877
  have hstable : (prefixWord ++ tailWord_8262877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262877).length < 2 ^ (prefixWord ++ tailWord_8262877).sum := by decide
  have hdescent : baseEnd_8262877 < baseStart_8262877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262893 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_8262893 : Nat := 118140960795 + 8262893 * 2 ^ 59
def prefixEnd_8262893 : Nat := 4983230072969 + 3 ^ 40 * 8262893 * 2
def baseEnd_8262893 : Nat := 4242835705671245126837153

theorem tailTrace_8262893 : CollatzResearch.WordTrace tailWord_8262893 prefixEnd_8262893 4242835705671245126837153 := by
  unfold tailWord_8262893
  simp only [CollatzResearch.WordTrace]
  refine ⟨301372466453957325618953333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200914977635971550412635555 301372466453957325618953333)
  ·
    refine ⟨28253668730058499276776875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301372466453957325618953333 28253668730058499276776875)
    ·
      refine ⟨42380503095087748915165313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28253668730058499276776875 42380503095087748915165313)
      ·
        refine ⟨31785377321315811686373985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42380503095087748915165313 31785377321315811686373985)
        ·
          refine ⟨23839032990986858764780489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31785377321315811686373985 23839032990986858764780489)
          ·
            refine ⟨17879274743240144073585367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23839032990986858764780489 17879274743240144073585367)
            ·
              refine ⟨26818912114860216110378051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879274743240144073585367 26818912114860216110378051)
              ·
                refine ⟨40228368172290324165567077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26818912114860216110378051 40228368172290324165567077)
                ·
                  refine ⟨7542819032304435781043827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40228368172290324165567077 7542819032304435781043827)
                  ·
                    refine ⟨11314228548456653671565741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7542819032304435781043827 11314228548456653671565741)
                    ·
                      refine ⟨4242835705671245126837153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314228548456653671565741 4242835705671245126837153)
                      ·
                        rfl

theorem cell23_8262893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_8262893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262893 prefixEnd_8262893 := by exact prefixLift 8262893
  have htrace : WordTrace (prefixWord ++ tailWord_8262893) baseStart_8262893 baseEnd_8262893 := by
    simpa [prefixWord, tailWord_8262893, baseEnd_8262893] using wordTrace_append hprefix tailTrace_8262893
  have hstable : (prefixWord ++ tailWord_8262893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262893).length < 2 ^ (prefixWord ++ tailWord_8262893).sum := by decide
  have hdescent : baseEnd_8262893 < baseStart_8262893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8262920 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_8262920 : Nat := 118140960795 + 8262920 * 2 ^ 59
def prefixEnd_8262920 : Nat := 4983230072969 + 3 ^ 40 * 8262920 * 2
def baseEnd_8262920 : Nat := 4242849569648916521199529

theorem tailTrace_8262920 : CollatzResearch.WordTrace tailWord_8262920 prefixEnd_8262920 4242849569648916521199529 := by
  unfold tailWord_8262920
  simp only [CollatzResearch.WordTrace]
  refine ⟨150686725612429754615093107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200915634149906339486790809 150686725612429754615093107)
  ·
    refine ⟨226030088418644631922639661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150686725612429754615093107 226030088418644631922639661)
    ·
      refine ⟨84761283156991736970989873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226030088418644631922639661 84761283156991736970989873)
      ·
        refine ⟨63570962367743802728242405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84761283156991736970989873 63570962367743802728242405)
        ·
          refine ⟨11919555443951963011545451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63570962367743802728242405 11919555443951963011545451)
          ·
            refine ⟨17879333165927944517318177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919555443951963011545451 17879333165927944517318177)
            ·
              refine ⟨13409499874445958387988633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17879333165927944517318177 13409499874445958387988633)
              ·
                refine ⟨10057124905834468790991475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13409499874445958387988633 10057124905834468790991475)
                ·
                  refine ⟨15085687358751703186487213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057124905834468790991475 15085687358751703186487213)
                  ·
                    refine ⟨5657132759531888694932705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15085687358751703186487213 5657132759531888694932705)
                    ·
                      refine ⟨4242849569648916521199529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657132759531888694932705 4242849569648916521199529)
                      ·
                        rfl

theorem cell23_8262920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_8262920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8262920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8262920 prefixEnd_8262920 := by exact prefixLift 8262920
  have htrace : WordTrace (prefixWord ++ tailWord_8262920) baseStart_8262920 baseEnd_8262920 := by
    simpa [prefixWord, tailWord_8262920, baseEnd_8262920] using wordTrace_append hprefix tailTrace_8262920
  have hstable : (prefixWord ++ tailWord_8262920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8262920).length < 2 ^ (prefixWord ++ tailWord_8262920).sum := by decide
  have hdescent : baseEnd_8262920 < baseStart_8262920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8262920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263026 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_8263026 : Nat := 118140960795 + 8263026 * 2 ^ 59
def prefixEnd_8263026 : Nat := 4983230072969 + 3 ^ 40 * 8263026 * 2
def baseEnd_8263026 : Nat := 4242903998598293106474041

theorem tailTrace_8263026 : CollatzResearch.WordTrace tailWord_8263026 prefixEnd_8263026 4242903998598293106474041 := by
  unfold tailWord_8263026
  simp only [CollatzResearch.WordTrace]
  refine ⟨75344329340618872333386233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200918211574983659555696621 75344329340618872333386233)
  ·
    refine ⟨56508247005464154250039675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75344329340618872333386233 56508247005464154250039675)
    ·
      refine ⟨84762370508196231375059513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56508247005464154250039675 84762370508196231375059513)
      ·
        refine ⟨63571777881147173531294635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84762370508196231375059513 63571777881147173531294635)
        ·
          refine ⟨95357666821720760296941953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63571777881147173531294635 95357666821720760296941953)
          ·
            refine ⟨71518250116290570222706465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95357666821720760296941953 71518250116290570222706465)
            ·
              refine ⟨53638687587217927667029849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71518250116290570222706465 53638687587217927667029849)
              ·
                refine ⟨40229015690413445750272387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53638687587217927667029849 40229015690413445750272387)
                ·
                  refine ⟨60343523535620168625408581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40229015690413445750272387 60343523535620168625408581)
                  ·
                    refine ⟨11314410662928781617264109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60343523535620168625408581 11314410662928781617264109)
                    ·
                      refine ⟨4242903998598293106474041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314410662928781617264109 4242903998598293106474041)
                      ·
                        rfl

theorem cell23_8263026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_8263026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263026 prefixEnd_8263026 := by exact prefixLift 8263026
  have htrace : WordTrace (prefixWord ++ tailWord_8263026) baseStart_8263026 baseEnd_8263026 := by
    simpa [prefixWord, tailWord_8263026, baseEnd_8263026] using wordTrace_append hprefix tailTrace_8263026
  have hstable : (prefixWord ++ tailWord_8263026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263026).length < 2 ^ (prefixWord ++ tailWord_8263026).sum := by decide
  have hdescent : baseEnd_8263026 < baseStart_8263026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263043 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 3]
def baseStart_8263043 : Nat := 118140960795 + 8263043 * 2 ^ 59
def prefixEnd_8263043 : Nat := 4983230072969 + 3 ^ 40 * 8263043 * 2
def baseEnd_8263043 : Nat := 4242912727769419539961463

theorem tailTrace_8263043 : CollatzResearch.WordTrace tailWord_8263043 prefixEnd_8263043 4242912727769419539961463 := by
  unfold tailWord_8263043
  simp only [CollatzResearch.WordTrace]
  refine ⟨301377937403413901236913783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200918624935609267491275855 301377937403413901236913783)
  ·
    refine ⟨452066906105120851855370675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301377937403413901236913783 452066906105120851855370675)
    ·
      refine ⟨678100359157681277783056013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452066906105120851855370675 678100359157681277783056013)
      ·
        refine ⟨254287634684130479168646005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678100359157681277783056013 254287634684130479168646005)
        ·
          refine ⟨23839465751637232422060563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254287634684130479168646005 23839465751637232422060563)
          ·
            refine ⟨35759198627455848633090845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23839465751637232422060563 35759198627455848633090845)
            ·
              refine ⟨13409699485295943237409067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35759198627455848633090845 13409699485295943237409067)
              ·
                refine ⟨20114549227943914856113601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13409699485295943237409067 20114549227943914856113601)
                ·
                  refine ⟨15085911920957936142085201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20114549227943914856113601 15085911920957936142085201)
                  ·
                    refine ⟨11314433940718452106563901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15085911920957936142085201 11314433940718452106563901)
                    ·
                      refine ⟨4242912727769419539961463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314433940718452106563901 4242912727769419539961463)
                      ·
                        rfl

theorem cell23_8263043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_8263043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263043 prefixEnd_8263043 := by exact prefixLift 8263043
  have htrace : WordTrace (prefixWord ++ tailWord_8263043) baseStart_8263043 baseEnd_8263043 := by
    simpa [prefixWord, tailWord_8263043, baseEnd_8263043] using wordTrace_append hprefix tailTrace_8263043
  have hstable : (prefixWord ++ tailWord_8263043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263043).length < 2 ^ (prefixWord ++ tailWord_8263043).sum := by decide
  have hdescent : baseEnd_8263043 < baseStart_8263043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263093 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_8263093 : Nat := 118140960795 + 8263093 * 2 ^ 59
def prefixEnd_8263093 : Nat := 4983230072969 + 3 ^ 40 * 8263093 * 2
def baseEnd_8263093 : Nat := 1414312800600714781445411

theorem tailTrace_8263093 : CollatzResearch.WordTrace tailWord_8263093 prefixEnd_8263093 1414312800600714781445411 := by
  unfold tailWord_8263093
  simp only [CollatzResearch.WordTrace]
  refine ⟨301379761053232759776233933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200919840702155173184155955 301379761053232759776233933)
  ·
    refine ⟨113017410394962284916087725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301379761053232759776233933 113017410394962284916087725)
    ·
      refine ⟨42381528898110856843532897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113017410394962284916087725 42381528898110856843532897)
      ·
        refine ⟨31786146673583142632649673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42381528898110856843532897 31786146673583142632649673)
        ·
          refine ⟨23839610005187356974487255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31786146673583142632649673 23839610005187356974487255)
          ·
            refine ⟨35759415007781035461730883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23839610005187356974487255 35759415007781035461730883)
            ·
              refine ⟨53639122511671553192596325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35759415007781035461730883 53639122511671553192596325)
              ·
                refine ⟨10057335470938416223611811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53639122511671553192596325 10057335470938416223611811)
                ·
                  refine ⟨15086003206407624335417717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057335470938416223611811 15086003206407624335417717)
                  ·
                    refine ⟨1414312800600714781445411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15086003206407624335417717 1414312800600714781445411)
                    ·
                      rfl

theorem cell23_8263093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_8263093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263093 prefixEnd_8263093 := by exact prefixLift 8263093
  have htrace : WordTrace (prefixWord ++ tailWord_8263093) baseStart_8263093 baseEnd_8263093 := by
    simpa [prefixWord, tailWord_8263093, baseEnd_8263093] using wordTrace_append hprefix tailTrace_8263093
  have hstable : (prefixWord ++ tailWord_8263093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263093).length < 2 ^ (prefixWord ++ tailWord_8263093).sum := by decide
  have hdescent : baseEnd_8263093 < baseStart_8263093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263096 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_8263096 : Nat := 118140960795 + 8263096 * 2 ^ 59
def prefixEnd_8263096 : Nat := 4983230072969 + 3 ^ 40 * 8263096 * 2
def baseEnd_8263096 : Nat := 4242939942244107832598719

theorem tailTrace_8263096 : CollatzResearch.WordTrace tailWord_8263096 prefixEnd_8263096 4242939942244107832598719 := by
  unfold tailWord_8263096
  simp only [CollatzResearch.WordTrace]
  refine ⟨150689935236110945644296571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200919913648147927525728761 150689935236110945644296571)
  ·
    refine ⟨226034902854166418466444857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150689935236110945644296571 226034902854166418466444857)
    ·
      refine ⟨169526177140624813849833643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226034902854166418466444857 169526177140624813849833643)
      ·
        refine ⟨254289265710937220774750465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169526177140624813849833643 254289265710937220774750465)
        ·
          refine ⟨190716949283202915581062849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254289265710937220774750465 190716949283202915581062849)
          ·
            refine ⟨143037711962402186685797137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190716949283202915581062849 143037711962402186685797137)
            ·
              refine ⟨107278283971801640014347853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143037711962402186685797137 107278283971801640014347853)
              ·
                refine ⟨40229356489425615005380445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107278283971801640014347853 40229356489425615005380445)
                ·
                  refine ⟨15086008683534605627017667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40229356489425615005380445 15086008683534605627017667)
                  ·
                    refine ⟨22629013025301908440526501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15086008683534605627017667 22629013025301908440526501)
                    ·
                      refine ⟨4242939942244107832598719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22629013025301908440526501 4242939942244107832598719)
                      ·
                        rfl

theorem cell23_8263096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_8263096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263096 prefixEnd_8263096 := by exact prefixLift 8263096
  have htrace : WordTrace (prefixWord ++ tailWord_8263096) baseStart_8263096 baseEnd_8263096 := by
    simpa [prefixWord, tailWord_8263096, baseEnd_8263096] using wordTrace_append hprefix tailTrace_8263096
  have hstable : (prefixWord ++ tailWord_8263096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263096).length < 2 ^ (prefixWord ++ tailWord_8263096).sum := by decide
  have hdescent : baseEnd_8263096 < baseStart_8263096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263099 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_8263099 : Nat := 118140960795 + 8263099 * 2 ^ 59
def prefixEnd_8263099 : Nat := 4983230072969 + 3 ^ 40 * 8263099 * 2
def baseEnd_8263099 : Nat := 4242941482686071320861205

theorem tailTrace_8263099 : CollatzResearch.WordTrace tailWord_8263099 prefixEnd_8263099 4242941482686071320861205 := by
  unfold tailWord_8263099
  simp only [CollatzResearch.WordTrace]
  refine ⟨301379979891211022800952351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200919986594140681867301567 301379979891211022800952351)
  ·
    refine ⟨452069969836816534201428527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301379979891211022800952351 452069969836816534201428527)
    ·
      refine ⟨678104954755224801302142791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452069969836816534201428527 678104954755224801302142791)
      ·
        refine ⟨1017157432132837201953214187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678104954755224801302142791 1017157432132837201953214187)
        ·
          refine ⟨1525736148199255802929821281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017157432132837201953214187 1525736148199255802929821281)
          ·
            refine ⟨1144302111149441852197365961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525736148199255802929821281 1144302111149441852197365961)
            ·
              refine ⟨858226583362081389148024471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144302111149441852197365961 858226583362081389148024471)
              ·
                refine ⟨1287339875043122083722036707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858226583362081389148024471 1287339875043122083722036707)
                ·
                  refine ⟨1931009812564683125583055061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287339875043122083722036707 1931009812564683125583055061)
                  ·
                    refine ⟨45258042481984760755852853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1931009812564683125583055061 45258042481984760755852853)
                    ·
                      refine ⟨4242941482686071320861205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45258042481984760755852853 4242941482686071320861205)
                      ·
                        rfl

theorem cell23_8263099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_8263099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263099 prefixEnd_8263099 := by exact prefixLift 8263099
  have htrace : WordTrace (prefixWord ++ tailWord_8263099) baseStart_8263099 baseEnd_8263099 := by
    simpa [prefixWord, tailWord_8263099, baseEnd_8263099] using wordTrace_append hprefix tailTrace_8263099
  have hstable : (prefixWord ++ tailWord_8263099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263099).length < 2 ^ (prefixWord ++ tailWord_8263099).sum := by decide
  have hdescent : baseEnd_8263099 < baseStart_8263099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263119 : List Nat := [1, 1, 2, 1, 1, 4, 13]
def baseStart_8263119 : Nat := 118140960795 + 8263119 * 2 ^ 59
def prefixEnd_8263119 : Nat := 4983230072969 + 3 ^ 40 * 8263119 * 2
def baseEnd_8263119 : Nat := 52382120398755077069273

theorem tailTrace_8263119 : CollatzResearch.WordTrace tailWord_8263119 prefixEnd_8263119 52382120398755077069273 := by
  unfold tailWord_8263119
  simp only [CollatzResearch.WordTrace]
  refine ⟨301380709351138566216680411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200920472900759044144453607 301380709351138566216680411)
  ·
    refine ⟨452071064026707849325020617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301380709351138566216680411 452071064026707849325020617)
    ·
      refine ⟨339053298020030886993765463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452071064026707849325020617 339053298020030886993765463)
      ·
        refine ⟨508579947030046330490648195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339053298020030886993765463 508579947030046330490648195)
        ·
          refine ⟨762869920545069495735972293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508579947030046330490648195 762869920545069495735972293)
          ·
            refine ⟨143038110102200530450494805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 762869920545069495735972293 143038110102200530450494805)
            ·
              refine ⟨52382120398755077069273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 143038110102200530450494805 52382120398755077069273)
              ·
                rfl

theorem cell23_8263119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 13].length) (baseStart_8263119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263119 prefixEnd_8263119 := by exact prefixLift 8263119
  have htrace : WordTrace (prefixWord ++ tailWord_8263119) baseStart_8263119 baseEnd_8263119 := by
    simpa [prefixWord, tailWord_8263119, baseEnd_8263119] using wordTrace_append hprefix tailTrace_8263119
  have hstable : (prefixWord ++ tailWord_8263119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263119).length < 2 ^ (prefixWord ++ tailWord_8263119).sum := by decide
  have hdescent : baseEnd_8263119 < baseStart_8263119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263124 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_8263124 : Nat := 118140960795 + 8263124 * 2 ^ 59
def prefixEnd_8263124 : Nat := 4983230072969 + 3 ^ 40 * 8263124 * 2
def baseEnd_8263124 : Nat := 4242954319702433723048591

theorem tailTrace_8263124 : CollatzResearch.WordTrace tailWord_8263124 prefixEnd_8263124 4242954319702433723048591 := by
  unfold tailWord_8263124
  simp only [CollatzResearch.WordTrace]
  refine ⟨150690445858060226035306213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200920594477413634713741617 150690445858060226035306213)
  ·
    refine ⟨28254458598386292381619915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150690445858060226035306213 28254458598386292381619915)
    ·
      refine ⟨42381687897579438572429873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28254458598386292381619915 42381687897579438572429873)
      ·
        refine ⟨31786265923184578929322405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42381687897579438572429873 31786265923184578929322405)
        ·
          refine ⟨5959924860597108549247951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31786265923184578929322405 5959924860597108549247951)
          ·
            refine ⟨8939887290895662823871927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959924860597108549247951 8939887290895662823871927)
            ·
              refine ⟨13409830936343494235807891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939887290895662823871927 13409830936343494235807891)
              ·
                refine ⟨20114746404515241353711837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13409830936343494235807891 20114746404515241353711837)
                ·
                  refine ⟨7543029901693215507641939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20114746404515241353711837 7543029901693215507641939)
                  ·
                    refine ⟨11314544852539823261462909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543029901693215507641939 11314544852539823261462909)
                    ·
                      refine ⟨4242954319702433723048591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314544852539823261462909 4242954319702433723048591)
                      ·
                        rfl

theorem cell23_8263124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_8263124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263124 prefixEnd_8263124 := by exact prefixLift 8263124
  have htrace : WordTrace (prefixWord ++ tailWord_8263124) baseStart_8263124 baseEnd_8263124 := by
    simpa [prefixWord, tailWord_8263124, baseEnd_8263124] using wordTrace_append hprefix tailTrace_8263124
  have hstable : (prefixWord ++ tailWord_8263124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263124).length < 2 ^ (prefixWord ++ tailWord_8263124).sum := by decide
  have hdescent : baseEnd_8263124 < baseStart_8263124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263133 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_8263133 : Nat := 118140960795 + 8263133 * 2 ^ 59
def prefixEnd_8263133 : Nat := 4983230072969 + 3 ^ 40 * 8263133 * 2
def baseEnd_8263133 : Nat := 4242958941028324187836049

theorem tailTrace_8263133 : CollatzResearch.WordTrace tailWord_8263133 prefixEnd_8263133 4242958941028324187836049 := by
  unfold tailWord_8263133
  simp only [CollatzResearch.WordTrace]
  refine ⟨301381219973087846607690053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200920813315391897738460035 301381219973087846607690053)
  ·
    refine ⟨56508978744953971238941885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301381219973087846607690053 56508978744953971238941885)
    ·
      refine ⟨21190867029357739214603207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56508978744953971238941885 21190867029357739214603207)
      ·
        refine ⟨31786300544036608821904811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21190867029357739214603207 31786300544036608821904811)
        ·
          refine ⟨47679450816054913232857217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31786300544036608821904811 47679450816054913232857217)
          ·
            refine ⟨35759588112041184924642913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47679450816054913232857217 35759588112041184924642913)
            ·
              refine ⟨26819691084030888693482185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35759588112041184924642913 26819691084030888693482185)
              ·
                refine ⟨20114768313023166520111639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26819691084030888693482185 20114768313023166520111639)
                ·
                  refine ⟨30172152469534749780167459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20114768313023166520111639 30172152469534749780167459)
                  ·
                    refine ⟨45258228704302124670251189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30172152469534749780167459 45258228704302124670251189)
                    ·
                      refine ⟨4242958941028324187836049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45258228704302124670251189 4242958941028324187836049)
                      ·
                        rfl

theorem cell23_8263133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_8263133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263133 prefixEnd_8263133 := by exact prefixLift 8263133
  have htrace : WordTrace (prefixWord ++ tailWord_8263133) baseStart_8263133 baseEnd_8263133 := by
    simpa [prefixWord, tailWord_8263133, baseEnd_8263133] using wordTrace_append hprefix tailTrace_8263133
  have hstable : (prefixWord ++ tailWord_8263133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263133).length < 2 ^ (prefixWord ++ tailWord_8263133).sum := by decide
  have hdescent : baseEnd_8263133 < baseStart_8263133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263176 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_8263176 : Nat := 118140960795 + 8263176 * 2 ^ 59
def prefixEnd_8263176 : Nat := 4983230072969 + 3 ^ 40 * 8263176 * 2
def baseEnd_8263176 : Nat := 4242981020696467519598351

theorem tailTrace_8263176 : CollatzResearch.WordTrace tailWord_8263176 prefixEnd_8263176 4242981020696467519598351 := by
  unfold tailWord_8263176
  simp only [CollatzResearch.WordTrace]
  refine ⟨150691394155966032475752691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200921858874621376634336921 150691394155966032475752691)
  ·
    refine ⟨226037091233949048713629037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150691394155966032475752691 226037091233949048713629037)
    ·
      refine ⟨84763909212730893267610889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226037091233949048713629037 84763909212730893267610889)
      ·
        refine ⟨63572931909548169950708167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84763909212730893267610889 63572931909548169950708167)
        ·
          refine ⟨95359397864322254926062251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63572931909548169950708167 95359397864322254926062251)
          ·
            refine ⟨143039096796483382389093377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95359397864322254926062251 143039096796483382389093377)
            ·
              refine ⟨107279322597362536791820033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143039096796483382389093377 107279322597362536791820033)
              ·
                refine ⟨80459491948021902593865025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107279322597362536791820033 80459491948021902593865025)
                ·
                  refine ⟨60344618961016426945398769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80459491948021902593865025 60344618961016426945398769)
                  ·
                    refine ⟨45258464220762320209049077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60344618961016426945398769 45258464220762320209049077)
                    ·
                      refine ⟨4242981020696467519598351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45258464220762320209049077 4242981020696467519598351)
                      ·
                        rfl

theorem cell23_8263176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_8263176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263176 prefixEnd_8263176 := by exact prefixLift 8263176
  have htrace : WordTrace (prefixWord ++ tailWord_8263176) baseStart_8263176 baseEnd_8263176 := by
    simpa [prefixWord, tailWord_8263176, baseEnd_8263176] using wordTrace_append hprefix tailTrace_8263176
  have hstable : (prefixWord ++ tailWord_8263176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263176).length < 2 ^ (prefixWord ++ tailWord_8263176).sum := by decide
  have hdescent : baseEnd_8263176 < baseStart_8263176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263198 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_8263198 : Nat := 118140960795 + 8263198 * 2 ^ 59
def prefixEnd_8263198 : Nat := 4983230072969 + 3 ^ 40 * 8263198 * 2
def baseEnd_8263198 : Nat := 4242992317270866433523251

theorem tailTrace_8263198 : CollatzResearch.WordTrace tailWord_8263198 prefixEnd_8263198 4242992317270866433523251 := by
  unfold tailWord_8263198
  simp only [CollatzResearch.WordTrace]
  refine ⟨37672948839731545338600781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200922393811901575139204165 37672948839731545338600781)
  ·
    refine ⟨14127355814899329501975293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37672948839731545338600781 14127355814899329501975293)
    ·
      refine ⟨5297758430587248563240735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14127355814899329501975293 5297758430587248563240735)
      ·
        refine ⟨7946637645880872844861103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297758430587248563240735 7946637645880872844861103)
        ·
          refine ⟨11919956468821309267291655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7946637645880872844861103 11919956468821309267291655)
          ·
            refine ⟨17879934703231963900937483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919956468821309267291655 17879934703231963900937483)
            ·
              refine ⟨26819902054847945851406225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879934703231963900937483 26819902054847945851406225)
              ·
                refine ⟨20114926541135959388554669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26819902054847945851406225 20114926541135959388554669)
                ·
                  refine ⟨7543097452925984770708001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20114926541135959388554669 7543097452925984770708001)
                  ·
                    refine ⟨5657323089694488578031001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7543097452925984770708001 5657323089694488578031001)
                    ·
                      refine ⟨4242992317270866433523251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657323089694488578031001 4242992317270866433523251)
                      ·
                        rfl

theorem cell23_8263198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_8263198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263198 prefixEnd_8263198 := by exact prefixLift 8263198
  have htrace : WordTrace (prefixWord ++ tailWord_8263198) baseStart_8263198 baseEnd_8263198 := by
    simpa [prefixWord, tailWord_8263198, baseEnd_8263198] using wordTrace_append hprefix tailTrace_8263198
  have hstable : (prefixWord ++ tailWord_8263198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263198).length < 2 ^ (prefixWord ++ tailWord_8263198).sum := by decide
  have hdescent : baseEnd_8263198 < baseStart_8263198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263216 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_8263216 : Nat := 118140960795 + 8263216 * 2 ^ 59
def prefixEnd_8263216 : Nat := 4983230072969 + 3 ^ 40 * 8263216 * 2
def baseEnd_8263216 : Nat := 4243001559922647363098167

theorem tailTrace_8263216 : CollatzResearch.WordTrace tailWord_8263216 prefixEnd_8263216 4243001559922647363098167 := by
  unfold tailWord_8263216
  simp only [CollatzResearch.WordTrace]
  refine ⟨150692123615893575891480751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200922831487858101188641001 150692123615893575891480751)
  ·
    refine ⟨226038185423840363837221127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150692123615893575891480751 226038185423840363837221127)
    ·
      refine ⟨339057278135760545755831691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226038185423840363837221127 339057278135760545755831691)
      ·
        refine ⟨508585917203640818633747537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339057278135760545755831691 508585917203640818633747537)
        ·
          refine ⟨381439437902730613975310653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508585917203640818633747537 381439437902730613975310653)
          ·
            refine ⟨143039789213523980240741495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381439437902730613975310653 143039789213523980240741495)
            ·
              refine ⟨214559683820285970361112243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143039789213523980240741495 214559683820285970361112243)
              ·
                refine ⟨321839525730428955541668365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214559683820285970361112243 321839525730428955541668365)
                ·
                  refine ⟨120689822148910858328125637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321839525730428955541668365 120689822148910858328125637)
                  ·
                    refine ⟨22629341652920785936523557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120689822148910858328125637 22629341652920785936523557)
                    ·
                      refine ⟨4243001559922647363098167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22629341652920785936523557 4243001559922647363098167)
                      ·
                        rfl

theorem cell23_8263216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_8263216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263216 prefixEnd_8263216 := by exact prefixLift 8263216
  have htrace : WordTrace (prefixWord ++ tailWord_8263216) baseStart_8263216 baseEnd_8263216 := by
    simpa [prefixWord, tailWord_8263216, baseEnd_8263216] using wordTrace_append hprefix tailTrace_8263216
  have hstable : (prefixWord ++ tailWord_8263216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263216).length < 2 ^ (prefixWord ++ tailWord_8263216).sum := by decide
  have hdescent : baseEnd_8263216 < baseStart_8263216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263224 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 1, 3, 2]
def baseStart_8263224 : Nat := 118140960795 + 8263224 * 2 ^ 59
def prefixEnd_8263224 : Nat := 4983230072969 + 3 ^ 40 * 8263224 * 2
def baseEnd_8263224 : Nat := 4243005667767883331798131

theorem tailTrace_8263224 : CollatzResearch.WordTrace tailWord_8263224 prefixEnd_8263224 4243005667767883331798131 := by
  unfold tailWord_8263224
  simp only [CollatzResearch.WordTrace]
  refine ⟨150692269507879084574626363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200923026010505446099501817 150692269507879084574626363)
  ·
    refine ⟨226038404261818626861939545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150692269507879084574626363 226038404261818626861939545)
    ·
      refine ⟨169528803196363970146454659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226038404261818626861939545 169528803196363970146454659)
      ·
        refine ⟨254293204794545955219681989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169528803196363970146454659 254293204794545955219681989)
        ·
          refine ⟨47679975898977366603690373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254293204794545955219681989 47679975898977366603690373)
          ·
            refine ⟨8939995481058256238191945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47679975898977366603690373 8939995481058256238191945)
            ·
              refine ⟨6704996610793692178643959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8939995481058256238191945 6704996610793692178643959)
              ·
                refine ⟨10057494916190538267965939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704996610793692178643959 10057494916190538267965939)
                ·
                  refine ⟨15086242374285807401948909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10057494916190538267965939 15086242374285807401948909)
                  ·
                    refine ⟨5657340890357177775730841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15086242374285807401948909 5657340890357177775730841)
                    ·
                      refine ⟨4243005667767883331798131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657340890357177775730841 4243005667767883331798131)
                      ·
                        rfl

theorem cell23_8263224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_8263224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263224 prefixEnd_8263224 := by exact prefixLift 8263224
  have htrace : WordTrace (prefixWord ++ tailWord_8263224) baseStart_8263224 baseEnd_8263224 := by
    simpa [prefixWord, tailWord_8263224, baseEnd_8263224] using wordTrace_append hprefix tailTrace_8263224
  have hstable : (prefixWord ++ tailWord_8263224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263224).length < 2 ^ (prefixWord ++ tailWord_8263224).sum := by decide
  have hdescent : baseEnd_8263224 < baseStart_8263224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263226 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_8263226 : Nat := 118140960795 + 8263226 * 2 ^ 59
def prefixEnd_8263226 : Nat := 4983230072969 + 3 ^ 40 * 8263226 * 2
def baseEnd_8263226 : Nat := 471445188303243591552569

theorem tailTrace_8263226 : CollatzResearch.WordTrace tailWord_8263226 prefixEnd_8263226 471445188303243591552569 := by
  unfold tailWord_8263226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75346152990437730872706383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200923074641167282327217021 75346152990437730872706383)
  ·
    refine ⟨113019229485656596309059575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75346152990437730872706383 113019229485656596309059575)
    ·
      refine ⟨169528844228484894463589363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113019229485656596309059575 169528844228484894463589363)
      ·
        refine ⟨254293266342727341695384045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169528844228484894463589363 254293266342727341695384045)
        ·
          refine ⟨95359974878522753135769017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254293266342727341695384045 95359974878522753135769017)
          ·
            refine ⟨71519981158892064851826763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95359974878522753135769017 71519981158892064851826763)
            ·
              refine ⟨107279971738338097277740145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71519981158892064851826763 107279971738338097277740145)
              ·
                refine ⟨80459978803753572958305109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107279971738338097277740145 80459978803753572958305109)
                ·
                  refine ⟨471445188303243591552569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80459978803753572958305109 471445188303243591552569)
                  ·
                    rfl

theorem cell23_8263226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_8263226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263226 prefixEnd_8263226 := by exact prefixLift 8263226
  have htrace : WordTrace (prefixWord ++ tailWord_8263226) baseStart_8263226 baseEnd_8263226 := by
    simpa [prefixWord, tailWord_8263226, baseEnd_8263226] using wordTrace_append hprefix tailTrace_8263226
  have hstable : (prefixWord ++ tailWord_8263226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263226).length < 2 ^ (prefixWord ++ tailWord_8263226).sum := by decide
  have hdescent : baseEnd_8263226 < baseStart_8263226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263233 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_8263233 : Nat := 118140960795 + 8263233 * 2 ^ 59
def prefixEnd_8263233 : Nat := 4983230072969 + 3 ^ 40 * 8263233 * 2
def baseEnd_8263233 : Nat := 4243010289093773796585589

theorem tailTrace_8263233 : CollatzResearch.WordTrace tailWord_8263233 prefixEnd_8263233 4243010289093773796585589 := by
  unfold tailWord_8263233
  simp only [CollatzResearch.WordTrace]
  refine ⟨301384867272725563686330353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200923244848483709124220235 301384867272725563686330353)
  ·
    refine ⟨226038650454544172764747765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301384867272725563686330353 226038650454544172764747765)
    ·
      refine ⟨21191123480113516196695103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226038650454544172764747765 21191123480113516196695103)
      ·
        refine ⟨31786685220170274295042655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21191123480113516196695103 31786685220170274295042655)
        ·
          refine ⟨47680027830255411442563983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31786685220170274295042655 47680027830255411442563983)
          ·
            refine ⟨71520041745383117163845975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47680027830255411442563983 71520041745383117163845975)
            ·
              refine ⟨107280062618074675745768963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71520041745383117163845975 107280062618074675745768963)
              ·
                refine ⟨160920093927112013618653445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107280062618074675745768963 160920093927112013618653445)
                ·
                  refine ⟨30172517611333502553497521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160920093927112013618653445 30172517611333502553497521)
                  ·
                    refine ⟨22629388208500126915123141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30172517611333502553497521 22629388208500126915123141)
                    ·
                      refine ⟨4243010289093773796585589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22629388208500126915123141 4243010289093773796585589)
                      ·
                        rfl

theorem cell23_8263233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_8263233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263233 prefixEnd_8263233 := by exact prefixLift 8263233
  have htrace : WordTrace (prefixWord ++ tailWord_8263233) baseStart_8263233 baseEnd_8263233 := by
    simpa [prefixWord, tailWord_8263233, baseEnd_8263233] using wordTrace_append hprefix tailTrace_8263233
  have hstable : (prefixWord ++ tailWord_8263233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263233).length < 2 ^ (prefixWord ++ tailWord_8263233).sum := by decide
  have hdescent : baseEnd_8263233 < baseStart_8263233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263300 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_8263300 : Nat := 118140960795 + 8263300 * 2 ^ 59
def prefixEnd_8263300 : Nat := 4983230072969 + 3 ^ 40 * 8263300 * 2
def baseEnd_8263300 : Nat := 4243044692297625034447781

theorem tailTrace_8263300 : CollatzResearch.WordTrace tailWord_8263300 prefixEnd_8263300 4243044692297625034447781 := by
  unfold tailWord_8263300
  simp only [CollatzResearch.WordTrace]
  refine ⟨150693655481741417064509677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200924873975655222752679569 150693655481741417064509677)
  ·
    refine ⟨56510120805653031399191129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150693655481741417064509677 56510120805653031399191129)
    ·
      refine ⟨42382590604239773549393347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56510120805653031399191129 42382590604239773549393347)
      ·
        refine ⟨63573885906359660324090021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42382590604239773549393347 63573885906359660324090021)
        ·
          refine ⟨11920103607442436310766879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63573885906359660324090021 11920103607442436310766879)
          ·
            refine ⟨17880155411163654466150319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920103607442436310766879 17880155411163654466150319)
            ·
              refine ⟨26820233116745481699225479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17880155411163654466150319 26820233116745481699225479)
              ·
                refine ⟨40230349675118222548838219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26820233116745481699225479 40230349675118222548838219)
                ·
                  refine ⟨60345524512677333823257329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40230349675118222548838219 60345524512677333823257329)
                  ·
                    refine ⟨45259143384508000367442997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60345524512677333823257329 45259143384508000367442997)
                    ·
                      refine ⟨4243044692297625034447781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45259143384508000367442997 4243044692297625034447781)
                      ·
                        rfl

theorem cell23_8263300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_8263300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263300 prefixEnd_8263300 := by exact prefixLift 8263300
  have htrace : WordTrace (prefixWord ++ tailWord_8263300) baseStart_8263300 baseEnd_8263300 := by
    simpa [prefixWord, tailWord_8263300, baseEnd_8263300] using wordTrace_append hprefix tailTrace_8263300
  have hstable : (prefixWord ++ tailWord_8263300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263300).length < 2 ^ (prefixWord ++ tailWord_8263300).sum := by decide
  have hdescent : baseEnd_8263300 < baseStart_8263300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263313 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_8263313 : Nat := 118140960795 + 8263313 * 2 ^ 59
def prefixEnd_8263313 : Nat := 4983230072969 + 3 ^ 40 * 8263313 * 2
def baseEnd_8263313 : Nat := 4243051367546133483585221

theorem tailTrace_8263313 : CollatzResearch.WordTrace tailWord_8263313 prefixEnd_8263313 4243051367546133483585221 := by
  unfold tailWord_8263313
  simp only [CollatzResearch.WordTrace]
  refine ⟨301387785112435737349242593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200925190074957158232828395 301387785112435737349242593)
  ·
    refine ⟨226040838834326803011931945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301387785112435737349242593 226040838834326803011931945)
    ·
      refine ⟨169530629125745102258948959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226040838834326803011931945 169530629125745102258948959)
      ·
        refine ⟨254295943688617653388423439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169530629125745102258948959 254295943688617653388423439)
        ·
          refine ⟨381443915532926480082635159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254295943688617653388423439 381443915532926480082635159)
          ·
            refine ⟨572165873299389720123952739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381443915532926480082635159 572165873299389720123952739)
            ·
              refine ⟨858248809949084580185929109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572165873299389720123952739 858248809949084580185929109)
              ·
                refine ⟨40230412966363339696215427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858248809949084580185929109 40230412966363339696215427)
                ·
                  refine ⟨60345619449545009544323141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40230412966363339696215427 60345619449545009544323141)
                  ·
                    refine ⟨11314803646789689289560589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60345619449545009544323141 11314803646789689289560589)
                    ·
                      refine ⟨4243051367546133483585221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314803646789689289560589 4243051367546133483585221)
                      ·
                        rfl

theorem cell23_8263313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_8263313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263313 prefixEnd_8263313 := by exact prefixLift 8263313
  have htrace : WordTrace (prefixWord ++ tailWord_8263313) baseStart_8263313 baseEnd_8263313 := by
    simpa [prefixWord, tailWord_8263313, baseEnd_8263313] using wordTrace_append hprefix tailTrace_8263313
  have hstable : (prefixWord ++ tailWord_8263313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263313).length < 2 ^ (prefixWord ++ tailWord_8263313).sum := by decide
  have hdescent : baseEnd_8263313 < baseStart_8263313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263354 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_8263354 : Nat := 118140960795 + 8263354 * 2 ^ 59
def prefixEnd_8263354 : Nat := 4983230072969 + 3 ^ 40 * 8263354 * 2
def baseEnd_8263354 : Nat := 1414357473417655941057511

theorem tailTrace_8263354 : CollatzResearch.WordTrace tailWord_8263354 prefixEnd_8263354 1414357473417655941057511 := by
  unfold tailWord_8263354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75347320126321800337871279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200926187003524800900990077 75347320126321800337871279)
  ·
    refine ⟨113020980189482700506806919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75347320126321800337871279 113020980189482700506806919)
    ·
      refine ⟨169531470284224050760210379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113020980189482700506806919 169531470284224050760210379)
      ·
        refine ⟨254297205426336076140315569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169531470284224050760210379 254297205426336076140315569)
        ·
          refine ⟨190722904069752057105236677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254297205426336076140315569 190722904069752057105236677)
          ·
            refine ⟨35760544513078510707231877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190722904069752057105236677 35760544513078510707231877)
            ·
              refine ⟨6705102096202220757605977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35760544513078510707231877 6705102096202220757605977)
              ·
                refine ⟨5028826572151665568204483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6705102096202220757605977 5028826572151665568204483)
                ·
                  refine ⟨7543239858227498352306725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028826572151665568204483 7543239858227498352306725)
                  ·
                    refine ⟨1414357473417655941057511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543239858227498352306725 1414357473417655941057511)
                    ·
                      rfl

theorem cell23_8263354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_8263354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263354 prefixEnd_8263354 := by exact prefixLift 8263354
  have htrace : WordTrace (prefixWord ++ tailWord_8263354) baseStart_8263354 baseEnd_8263354 := by
    simpa [prefixWord, tailWord_8263354, baseEnd_8263354] using wordTrace_append hprefix tailTrace_8263354
  have hstable : (prefixWord ++ tailWord_8263354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263354).length < 2 ^ (prefixWord ++ tailWord_8263354).sum := by decide
  have hdescent : baseEnd_8263354 < baseStart_8263354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263377 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_8263377 : Nat := 118140960795 + 8263377 * 2 ^ 59
def prefixEnd_8263377 : Nat := 4983230072969 + 3 ^ 40 * 8263377 * 2
def baseEnd_8263377 : Nat := 4243084230308021233184927

theorem tailTrace_8263377 : CollatzResearch.WordTrace tailWord_8263377 prefixEnd_8263377 4243084230308021233184927 := by
  unfold tailWord_8263377
  simp only [CollatzResearch.WordTrace]
  refine ⟨301390119384203876279572385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200926746256135917519714923 301390119384203876279572385)
  ·
    refine ⟨226042589538152907209679289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301390119384203876279572385 226042589538152907209679289)
    ·
      refine ⟨169531942153614680407259467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226042589538152907209679289 169531942153614680407259467)
      ·
        refine ⟨254297913230422020610889201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169531942153614680407259467 254297913230422020610889201)
        ·
          refine ⟨190723434922816515458166901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254297913230422020610889201 190723434922816515458166901)
          ·
            refine ⟨17880322024014048324203147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190723434922816515458166901 17880322024014048324203147)
            ·
              refine ⟨26820483036021072486304721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17880322024014048324203147 26820483036021072486304721)
              ·
                refine ⟨20115362277015804364728541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26820483036021072486304721 20115362277015804364728541)
                ·
                  refine ⟨7543260853880926636773203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20115362277015804364728541 7543260853880926636773203)
                  ·
                    refine ⟨11314891280821389955159805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543260853880926636773203 11314891280821389955159805)
                    ·
                      refine ⟨4243084230308021233184927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11314891280821389955159805 4243084230308021233184927)
                      ·
                        rfl

theorem cell23_8263377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_8263377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263377 prefixEnd_8263377 := by exact prefixLift 8263377
  have htrace : WordTrace (prefixWord ++ tailWord_8263377) baseStart_8263377 baseEnd_8263377 := by
    simpa [prefixWord, tailWord_8263377, baseEnd_8263377] using wordTrace_append hprefix tailTrace_8263377
  have hstable : (prefixWord ++ tailWord_8263377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263377).length < 2 ^ (prefixWord ++ tailWord_8263377).sum := by decide
  have hdescent : baseEnd_8263377 < baseStart_8263377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263420 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_8263420 : Nat := 118140960795 + 8263420 * 2 ^ 59
def prefixEnd_8263420 : Nat := 4983230072969 + 3 ^ 40 * 8263420 * 2
def baseEnd_8263420 : Nat := 4243106309976164564947229

theorem tailTrace_8263420 : CollatzResearch.WordTrace tailWord_8263420 prefixEnd_8263420 4243106309976164564947229 := by
  unfold tailWord_8263420
  simp only [CollatzResearch.WordTrace]
  refine ⟨150695843861524047311693857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200927791815365396415591809 150695843861524047311693857)
  ·
    refine ⟨113021882896143035483770393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150695843861524047311693857 113021882896143035483770393)
    ·
      refine ⟨84766412172107276612827795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113021882896143035483770393 84766412172107276612827795)
      ·
        refine ⟨127149618258160914919241693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84766412172107276612827795 127149618258160914919241693)
        ·
          refine ⟨47681106846810343094715635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127149618258160914919241693 47681106846810343094715635)
          ·
            refine ⟨71521660270215514642073453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47681106846810343094715635 71521660270215514642073453)
            ·
              refine ⟨26820622601330817990777545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71521660270215514642073453 26820622601330817990777545)
              ·
                refine ⟨20115466950998113493083159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26820622601330817990777545 20115466950998113493083159)
                ·
                  refine ⟨30173200426497170239624739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20115466950998113493083159 30173200426497170239624739)
                  ·
                    refine ⟨45259800639745755359437109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30173200426497170239624739 45259800639745755359437109)
                    ·
                      refine ⟨4243106309976164564947229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45259800639745755359437109 4243106309976164564947229)
                      ·
                        rfl

theorem cell23_8263420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_8263420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263420 prefixEnd_8263420 := by exact prefixLift 8263420
  have htrace : WordTrace (prefixWord ++ tailWord_8263420) baseStart_8263420 baseEnd_8263420 := by
    simpa [prefixWord, tailWord_8263420, baseEnd_8263420] using wordTrace_append hprefix tailTrace_8263420
  have hstable : (prefixWord ++ tailWord_8263420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263420).length < 2 ^ (prefixWord ++ tailWord_8263420).sum := by decide
  have hdescent : baseEnd_8263420 < baseStart_8263420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263434 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_8263434 : Nat := 118140960795 + 8263434 * 2 ^ 59
def prefixEnd_8263434 : Nat := 4983230072969 + 3 ^ 40 * 8263434 * 2
def baseEnd_8263434 : Nat := 4243113498705327510172165

theorem tailTrace_8263434 : CollatzResearch.WordTrace tailWord_8263434 prefixEnd_8263434 4243113498705327510172165 := by
  unfold tailWord_8263434
  simp only [CollatzResearch.WordTrace]
  refine ⟨75348049586249343753599339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200928132229998250009598237 75348049586249343753599339)
  ·
    refine ⟨113022074379374015630399009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75348049586249343753599339 113022074379374015630399009)
    ·
      refine ⟨84766555784530511722799257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113022074379374015630399009 84766555784530511722799257)
      ·
        refine ⟨63574916838397883792099443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84766555784530511722799257 63574916838397883792099443)
        ·
          refine ⟨95362375257596825688149165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63574916838397883792099443 95362375257596825688149165)
          ·
            refine ⟨35760890721598809633055937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95362375257596825688149165 35760890721598809633055937)
            ·
              refine ⟨26820668041199107224791953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35760890721598809633055937 26820668041199107224791953)
              ·
                refine ⟨20115501030899330418593965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26820668041199107224791953 20115501030899330418593965)
                ·
                  refine ⟨7543312886587248906972737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20115501030899330418593965 7543312886587248906972737)
                  ·
                    refine ⟨5657484664940436680229553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7543312886587248906972737 5657484664940436680229553)
                    ·
                      refine ⟨4243113498705327510172165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657484664940436680229553 4243113498705327510172165)
                      ·
                        rfl

theorem cell23_8263434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_8263434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263434 prefixEnd_8263434 := by exact prefixLift 8263434
  have htrace : WordTrace (prefixWord ++ tailWord_8263434) baseStart_8263434 baseEnd_8263434 := by
    simpa [prefixWord, tailWord_8263434, baseEnd_8263434] using wordTrace_append hprefix tailTrace_8263434
  have hstable : (prefixWord ++ tailWord_8263434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263434).length < 2 ^ (prefixWord ++ tailWord_8263434).sum := by decide
  have hdescent : baseEnd_8263434 < baseStart_8263434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263468 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 1, 2, 2]
def baseStart_8263468 : Nat := 118140960795 + 8263468 * 2 ^ 59
def prefixEnd_8263468 : Nat := 4983230072969 + 3 ^ 40 * 8263468 * 2
def baseEnd_8263468 : Nat := 4243130957047580377147009

theorem tailTrace_8263468 : CollatzResearch.WordTrace tailWord_8263468 prefixEnd_8263468 4243130957047580377147009 := by
  unfold tailWord_8263468
  simp only [CollatzResearch.WordTrace]
  refine ⟨150696719213437099410567529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200928958951249465880756705 150696719213437099410567529)
  ·
    refine ⟨113022539410077824557925647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150696719213437099410567529 113022539410077824557925647)
    ·
      refine ⟨169533809115116736836888471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113022539410077824557925647 169533809115116736836888471)
      ·
        refine ⟨254300713672675105255332707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169533809115116736836888471 254300713672675105255332707)
        ·
          refine ⟨381451070509012657882999061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254300713672675105255332707 381451070509012657882999061)
          ·
            refine ⟨17880518930109968338265581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381451070509012657882999061 17880518930109968338265581)
            ·
              refine ⟨6705194598791238126849593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17880518930109968338265581 6705194598791238126849593)
              ·
                refine ⟨5028895949093428595137195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6705194598791238126849593 5028895949093428595137195)
                ·
                  refine ⟨7543343923640142892705793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028895949093428595137195 7543343923640142892705793)
                  ·
                    refine ⟨5657507942730107169529345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7543343923640142892705793 5657507942730107169529345)
                    ·
                      refine ⟨4243130957047580377147009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657507942730107169529345 4243130957047580377147009)
                      ·
                        rfl

theorem cell23_8263468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_8263468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263468 prefixEnd_8263468 := by exact prefixLift 8263468
  have htrace : WordTrace (prefixWord ++ tailWord_8263468) baseStart_8263468 baseEnd_8263468 := by
    simpa [prefixWord, tailWord_8263468, baseEnd_8263468] using wordTrace_append hprefix tailTrace_8263468
  have hstable : (prefixWord ++ tailWord_8263468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263468).length < 2 ^ (prefixWord ++ tailWord_8263468).sum := by decide
  have hdescent : baseEnd_8263468 < baseStart_8263468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263478 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_8263478 : Nat := 118140960795 + 8263478 * 2 ^ 59
def prefixEnd_8263478 : Nat := 4983230072969 + 3 ^ 40 * 8263478 * 2
def baseEnd_8263478 : Nat := 1414378697284708446007321

theorem tailTrace_8263478 : CollatzResearch.WordTrace tailWord_8263478 prefixEnd_8263478 1414378697284708446007321 := by
  unfold tailWord_8263478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18837112697302373158062443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200929202104558647019332725 18837112697302373158062443)
  ·
    refine ⟨28255669045953559737093665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18837112697302373158062443 28255669045953559737093665)
    ·
      refine ⟨21191751784465169802820249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28255669045953559737093665 21191751784465169802820249)
      ·
        refine ⟨15893813838348877352115187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21191751784465169802820249 15893813838348877352115187)
        ·
          refine ⟨23840720757523316028172781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15893813838348877352115187 23840720757523316028172781)
          ·
            refine ⟨8940270284071243510564793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23840720757523316028172781 8940270284071243510564793)
            ·
              refine ⟨6705202713053432632923595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940270284071243510564793 6705202713053432632923595)
              ·
                refine ⟨10057804069580148949385393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705202713053432632923595 10057804069580148949385393)
                ·
                  refine ⟨7543353052185111712039045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10057804069580148949385393 7543353052185111712039045)
                  ·
                    refine ⟨1414378697284708446007321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543353052185111712039045 1414378697284708446007321)
                    ·
                      rfl

theorem cell23_8263478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_8263478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263478 prefixEnd_8263478 := by exact prefixLift 8263478
  have htrace : WordTrace (prefixWord ++ tailWord_8263478) baseStart_8263478 baseEnd_8263478 := by
    simpa [prefixWord, tailWord_8263478, baseEnd_8263478] using wordTrace_append hprefix tailTrace_8263478
  have hstable : (prefixWord ++ tailWord_8263478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263478).length < 2 ^ (prefixWord ++ tailWord_8263478).sum := by decide
  have hdescent : baseEnd_8263478 < baseStart_8263478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263541 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_8263541 : Nat := 118140960795 + 8263541 * 2 ^ 59
def prefixEnd_8263541 : Nat := 4983230072969 + 3 ^ 40 * 8263541 * 2
def baseEnd_8263541 : Nat := 4243168441135358591534173

theorem tailTrace_8263541 : CollatzResearch.WordTrace tailWord_8263541 prefixEnd_8263541 4243168441135358591534173 := by
  unfold tailWord_8263541
  simp only [CollatzResearch.WordTrace]
  refine ⟨301396100955609732288542477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200930733970406488192361651 301396100955609732288542477)
  ·
    refine ⟨113023537858353649608203429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301396100955609732288542477 113023537858353649608203429)
    ·
      refine ⟨21191913348441309301538143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113023537858353649608203429 21191913348441309301538143)
      ·
        refine ⟨31787870022661963952307215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21191913348441309301538143 31787870022661963952307215)
        ·
          refine ⟨47681805033992945928460823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31787870022661963952307215 47681805033992945928460823)
          ·
            refine ⟨71522707550989418892691235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47681805033992945928460823 71522707550989418892691235)
            ·
              refine ⟨107284061326484128339036853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71522707550989418892691235 107284061326484128339036853)
              ·
                refine ⟨10057880749357887031784705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107284061326484128339036853 10057880749357887031784705)
                ·
                  refine ⟨7543410562018415273838529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10057880749357887031784705 7543410562018415273838529)
                  ·
                    refine ⟨5657557921513811455378897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7543410562018415273838529 5657557921513811455378897)
                    ·
                      refine ⟨4243168441135358591534173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657557921513811455378897 4243168441135358591534173)
                      ·
                        rfl

theorem cell23_8263541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_8263541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263541 prefixEnd_8263541 := by exact prefixLift 8263541
  have htrace : WordTrace (prefixWord ++ tailWord_8263541) baseStart_8263541 baseEnd_8263541 := by
    simpa [prefixWord, tailWord_8263541, baseEnd_8263541] using wordTrace_append hprefix tailTrace_8263541
  have hstable : (prefixWord ++ tailWord_8263541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263541).length < 2 ^ (prefixWord ++ tailWord_8263541).sum := by decide
  have hdescent : baseEnd_8263541 < baseStart_8263541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263592 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_8263592 : Nat := 118140960795 + 8263592 * 2 ^ 59
def prefixEnd_8263592 : Nat := 4983230072969 + 3 ^ 40 * 8263592 * 2
def baseEnd_8263592 : Nat := 4243194628648737891996439

theorem tailTrace_8263592 : CollatzResearch.WordTrace tailWord_8263592 prefixEnd_8263592 4243194628648737891996439 := by
  unfold tailWord_8263592
  simp only [CollatzResearch.WordTrace]
  refine ⟨150698980539212483999324515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200931974052283311999099353 150698980539212483999324515)
  ·
    refine ⟨226048470808818725998986773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150698980539212483999324515 226048470808818725998986773)
    ·
      refine ⟨10596022069163377781202505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226048470808818725998986773 10596022069163377781202505)
      ·
        refine ⟨7947016551872533335901879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10596022069163377781202505 7947016551872533335901879)
        ·
          refine ⟨11920524827808800003852819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947016551872533335901879 11920524827808800003852819)
          ·
            refine ⟨17880787241713200005779229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920524827808800003852819 17880787241713200005779229)
            ·
              refine ⟨6705295215642450002167211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17880787241713200005779229 6705295215642450002167211)
              ·
                refine ⟨10057942823463675003250817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705295215642450002167211 10057942823463675003250817)
                ·
                  refine ⟨7543457117597756252438113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10057942823463675003250817 7543457117597756252438113)
                  ·
                    refine ⟨5657592838198317189328585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7543457117597756252438113 5657592838198317189328585)
                    ·
                      refine ⟨4243194628648737891996439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657592838198317189328585 4243194628648737891996439)
                      ·
                        rfl

theorem cell23_8263592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_8263592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263592 prefixEnd_8263592 := by exact prefixLift 8263592
  have htrace : WordTrace (prefixWord ++ tailWord_8263592) baseStart_8263592 baseEnd_8263592 := by
    simpa [prefixWord, tailWord_8263592, baseEnd_8263592] using wordTrace_append hprefix tailTrace_8263592
  have hstable : (prefixWord ++ tailWord_8263592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263592).length < 2 ^ (prefixWord ++ tailWord_8263592).sum := by decide
  have hdescent : baseEnd_8263592 < baseStart_8263592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263610 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_8263610 : Nat := 118140960795 + 8263610 * 2 ^ 59
def prefixEnd_8263610 : Nat := 4983230072969 + 3 ^ 40 * 8263610 * 2
def baseEnd_8263610 : Nat := 4243203871300518821571355

theorem tailTrace_8263610 : CollatzResearch.WordTrace tailWord_8263610 prefixEnd_8263610 4243203871300518821571355 := by
  unfold tailWord_8263610
  simp only [CollatzResearch.WordTrace]
  refine ⟨75349654398089939268201071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200932411728239838048536189 75349654398089939268201071)
  ·
    refine ⟨113024481597134908902301607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75349654398089939268201071 113024481597134908902301607)
    ·
      refine ⟨169536722395702363353452411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113024481597134908902301607 169536722395702363353452411)
      ·
        refine ⟨254305083593553545030178617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169536722395702363353452411 254305083593553545030178617)
        ·
          refine ⟨190728812695165158772633963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254305083593553545030178617 190728812695165158772633963)
          ·
            refine ⟨286093219042747738158950945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190728812695165158772633963 286093219042747738158950945)
            ·
              refine ⟨214569914282060803619213209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286093219042747738158950945 214569914282060803619213209)
              ·
                refine ⟨160927435711545602714409907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214569914282060803619213209 160927435711545602714409907)
                ·
                  refine ⟨241391153567318404071614861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160927435711545602714409907 241391153567318404071614861)
                  ·
                    refine ⟨90521682587744401526855573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241391153567318404071614861 90521682587744401526855573)
                    ·
                      refine ⟨4243203871300518821571355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90521682587744401526855573 4243203871300518821571355)
                      ·
                        rfl

theorem cell23_8263610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_8263610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263610 prefixEnd_8263610 := by exact prefixLift 8263610
  have htrace : WordTrace (prefixWord ++ tailWord_8263610) baseStart_8263610 baseEnd_8263610 := by
    simpa [prefixWord, tailWord_8263610, baseEnd_8263610] using wordTrace_append hprefix tailTrace_8263610
  have hstable : (prefixWord ++ tailWord_8263610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263610).length < 2 ^ (prefixWord ++ tailWord_8263610).sum := by decide
  have hdescent : baseEnd_8263610 < baseStart_8263610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263637 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 8]
def baseStart_8263637 : Nat := 118140960795 + 8263637 * 2 ^ 59
def prefixEnd_8263637 : Nat := 4983230072969 + 3 ^ 40 * 8263637 * 2
def baseEnd_8263637 : Nat := 471468637253132246214859

theorem tailTrace_8263637 : CollatzResearch.WordTrace tailWord_8263637 prefixEnd_8263637 471468637253132246214859 := by
  unfold tailWord_8263637
  simp only [CollatzResearch.WordTrace]
  refine ⟨301399602363261940684037165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200933068242174627122691443 301399602363261940684037165)
  ·
    refine ⟨113024850886223227756513937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301399602363261940684037165 113024850886223227756513937)
    ·
      refine ⟨84768638164667420817385453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113024850886223227756513937 84768638164667420817385453)
      ·
        refine ⟨31788239311750282806519545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84768638164667420817385453 31788239311750282806519545)
        ·
          refine ⟨23841179483812712104889659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31788239311750282806519545 23841179483812712104889659)
          ·
            refine ⟨35761769225719068157334489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23841179483812712104889659 35761769225719068157334489)
            ·
              refine ⟨26821326919289301118000867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35761769225719068157334489 26821326919289301118000867)
              ·
                refine ⟨40231990378933951677001301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26821326919289301118000867 40231990378933951677001301)
                ·
                  refine ⟨471468637253132246214859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40231990378933951677001301 471468637253132246214859)
                  ·
                    rfl

theorem cell23_8263637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_8263637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263637 prefixEnd_8263637 := by exact prefixLift 8263637
  have htrace : WordTrace (prefixWord ++ tailWord_8263637) baseStart_8263637 baseEnd_8263637 := by
    simpa [prefixWord, tailWord_8263637, baseEnd_8263637] using wordTrace_append hprefix tailTrace_8263637
  have hstable : (prefixWord ++ tailWord_8263637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263637).length < 2 ^ (prefixWord ++ tailWord_8263637).sum := by decide
  have hdescent : baseEnd_8263637 < baseStart_8263637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263641 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 3, 4]
def baseStart_8263641 : Nat := 118140960795 + 8263641 * 2 ^ 59
def prefixEnd_8263641 : Nat := 4983230072969 + 3 ^ 40 * 8263641 * 2
def baseEnd_8263641 : Nat := 1414406596400269400094571

theorem tailTrace_8263641 : CollatzResearch.WordTrace tailWord_8263641 prefixEnd_8263641 1414406596400269400094571 := by
  unfold tailWord_8263641
  simp only [CollatzResearch.WordTrace]
  refine ⟨301399748255247449367182777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200933165503498299578121851 301399748255247449367182777)
  ·
    refine ⟨226049811191435587025387083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301399748255247449367182777 226049811191435587025387083)
    ·
      refine ⟨339074716787153380538080625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226049811191435587025387083 339074716787153380538080625)
      ·
        refine ⟨254306037590365035403560469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339074716787153380538080625 254306037590365035403560469)
        ·
          refine ⟨11920595512048361034541897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 254306037590365035403560469 11920595512048361034541897)
          ·
            refine ⟨8940446634036270775906423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11920595512048361034541897 8940446634036270775906423)
            ·
              refine ⟨13410669951054406163859635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940446634036270775906423 13410669951054406163859635)
              ·
                refine ⟨20116004926581609245789453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13410669951054406163859635 20116004926581609245789453)
                ·
                  refine ⟨7543501847468103467171045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20116004926581609245789453 7543501847468103467171045)
                  ·
                    refine ⟨1414406596400269400094571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543501847468103467171045 1414406596400269400094571)
                    ·
                      rfl

theorem cell23_8263641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_8263641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263641 prefixEnd_8263641 := by exact prefixLift 8263641
  have htrace : WordTrace (prefixWord ++ tailWord_8263641) baseStart_8263641 baseEnd_8263641 := by
    simpa [prefixWord, tailWord_8263641, baseEnd_8263641] using wordTrace_append hprefix tailTrace_8263641
  have hstable : (prefixWord ++ tailWord_8263641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263641).length < 2 ^ (prefixWord ++ tailWord_8263641).sum := by decide
  have hdescent : baseEnd_8263641 < baseStart_8263641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263664 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 3, 1, 3]
def baseStart_8263664 : Nat := 118140960795 + 8263664 * 2 ^ 59
def prefixEnd_8263664 : Nat := 4983230072969 + 3 ^ 40 * 8263664 * 2
def baseEnd_8263664 : Nat := 4243231599255861610296107

theorem tailTrace_8263664 : CollatzResearch.WordTrace tailWord_8263664 prefixEnd_8263664 4243231599255861610296107 := by
  unfold tailWord_8263664
  simp only [CollatzResearch.WordTrace]
  refine ⟨150700293567082062147635023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200933724756109416196846697 150700293567082062147635023)
  ·
    refine ⟨226050440350623093221452535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150700293567082062147635023 226050440350623093221452535)
    ·
      refine ⟨339075660525934639832178803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226050440350623093221452535 339075660525934639832178803)
      ·
        refine ⟨508613490788901959748268205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339075660525934639832178803 508613490788901959748268205)
        ·
          refine ⟨190730059045838234905600577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508613490788901959748268205 190730059045838234905600577)
          ·
            refine ⟨143047544284378676179200433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190730059045838234905600577 143047544284378676179200433)
            ·
              refine ⟨107285658213284007134400325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143047544284378676179200433 107285658213284007134400325)
              ·
                refine ⟨20116060914990751337700061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107285658213284007134400325 20116060914990751337700061)
                ·
                  refine ⟨7543522843121531751637523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20116060914990751337700061 7543522843121531751637523)
                  ·
                    refine ⟨11315284264682297627456285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543522843121531751637523 11315284264682297627456285)
                    ·
                      refine ⟨4243231599255861610296107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315284264682297627456285 4243231599255861610296107)
                      ·
                        rfl

theorem cell23_8263664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_8263664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263664 prefixEnd_8263664 := by exact prefixLift 8263664
  have htrace : WordTrace (prefixWord ++ tailWord_8263664) baseStart_8263664 baseEnd_8263664 := by
    simpa [prefixWord, tailWord_8263664, baseEnd_8263664] using wordTrace_append hprefix tailTrace_8263664
  have hstable : (prefixWord ++ tailWord_8263664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263664).length < 2 ^ (prefixWord ++ tailWord_8263664).sum := by decide
  have hdescent : baseEnd_8263664 < baseStart_8263664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263714 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_8263714 : Nat := 118140960795 + 8263714 * 2 ^ 59
def prefixEnd_8263714 : Nat := 4983230072969 + 3 ^ 40 * 8263714 * 2
def baseEnd_8263714 : Nat := 1414419091096195471556959

theorem tailTrace_8263714 : CollatzResearch.WordTrace tailWord_8263714 prefixEnd_8263714 1414419091096195471556959 := by
  unfold tailWord_8263714
  simp only [CollatzResearch.WordTrace]
  refine ⟨75350602695995745708647549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200934940522655321889726797 75350602695995745708647549)
  ·
    refine ⟨28256476010998404640742831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75350602695995745708647549 28256476010998404640742831)
    ·
      refine ⟨42384714016497606961114247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28256476010998404640742831 42384714016497606961114247)
      ·
        refine ⟨63577071024746410441671371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42384714016497606961114247 63577071024746410441671371)
        ·
          refine ⟨95365606537119615662507057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63577071024746410441671371 95365606537119615662507057)
          ·
            refine ⟨71524204902839711746880293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95365606537119615662507057 71524204902839711746880293)
            ·
              refine ⟨13410788419282445952540055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71524204902839711746880293 13410788419282445952540055)
              ·
                refine ⟨20116182628923668928810083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13410788419282445952540055 20116182628923668928810083)
                ·
                  refine ⟨30174273943385503393215125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20116182628923668928810083 30174273943385503393215125)
                  ·
                    refine ⟨1414419091096195471556959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30174273943385503393215125 1414419091096195471556959)
                    ·
                      rfl

theorem cell23_8263714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_8263714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263714 prefixEnd_8263714 := by exact prefixLift 8263714
  have htrace : WordTrace (prefixWord ++ tailWord_8263714) baseStart_8263714 baseEnd_8263714 := by
    simpa [prefixWord, tailWord_8263714, baseEnd_8263714] using wordTrace_append hprefix tailTrace_8263714
  have hstable : (prefixWord ++ tailWord_8263714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263714).length < 2 ^ (prefixWord ++ tailWord_8263714).sum := by decide
  have hdescent : baseEnd_8263714 < baseStart_8263714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263732 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_8263732 : Nat := 118140960795 + 8263732 * 2 ^ 59
def prefixEnd_8263732 : Nat := 4983230072969 + 3 ^ 40 * 8263732 * 2
def baseEnd_8263732 : Nat := 4243266515940367344245795

theorem tailTrace_8263732 : CollatzResearch.WordTrace tailWord_8263732 prefixEnd_8263732 4243266515940367344245795 := by
  unfold tailWord_8263732
  simp only [CollatzResearch.WordTrace]
  refine ⟨150701533648958885954372725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200935378198611847939163633 150701533648958885954372725)
  ·
    refine ⟨14128268779589895558222443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150701533648958885954372725 14128268779589895558222443)
    ·
      refine ⟨21192403169384843337333665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14128268779589895558222443 21192403169384843337333665)
      ·
        refine ⟨15894302377038632503000249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21192403169384843337333665 15894302377038632503000249)
        ·
          refine ⟨11920726782778974377250187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15894302377038632503000249 11920726782778974377250187)
          ·
            refine ⟨17881090174168461565875281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920726782778974377250187 17881090174168461565875281)
            ·
              refine ⟨13410817630626346174406461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17881090174168461565875281 13410817630626346174406461)
              ·
                refine ⟨5029056611484879815402423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13410817630626346174406461 5029056611484879815402423)
                ·
                  refine ⟨7543584917227319723103635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029056611484879815402423 7543584917227319723103635)
                  ·
                    refine ⟨11315377375840979584655453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543584917227319723103635 11315377375840979584655453)
                    ·
                      refine ⟨4243266515940367344245795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315377375840979584655453 4243266515940367344245795)
                      ·
                        rfl

theorem cell23_8263732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_8263732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263732 prefixEnd_8263732 := by exact prefixLift 8263732
  have htrace : WordTrace (prefixWord ++ tailWord_8263732) baseStart_8263732 baseEnd_8263732 := by
    simpa [prefixWord, tailWord_8263732, baseEnd_8263732] using wordTrace_append hprefix tailTrace_8263732
  have hstable : (prefixWord ++ tailWord_8263732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263732).length < 2 ^ (prefixWord ++ tailWord_8263732).sum := by decide
  have hdescent : baseEnd_8263732 < baseStart_8263732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263741 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_8263741 : Nat := 118140960795 + 8263741 * 2 ^ 59
def prefixEnd_8263741 : Nat := 4983230072969 + 3 ^ 40 * 8263741 * 2
def baseEnd_8263741 : Nat := 4243271137266257809033253

theorem tailTrace_8263741 : CollatzResearch.WordTrace tailWord_8263741 prefixEnd_8263741 4243271137266257809033253 := by
  unfold tailWord_8263741
  simp only [CollatzResearch.WordTrace]
  refine ⟨301403395554885166445823077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200935597036590110963882051 301403395554885166445823077)
  ·
    refine ⟨56513136666540968708591827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301403395554885166445823077 56513136666540968708591827)
    ·
      refine ⟨84769704999811453062887741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56513136666540968708591827 84769704999811453062887741)
      ·
        refine ⟨31788639374929294898582903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84769704999811453062887741 31788639374929294898582903)
        ·
          refine ⟨47682959062393942347874355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31788639374929294898582903 47682959062393942347874355)
          ·
            refine ⟨71524438593590913521811533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47682959062393942347874355 71524438593590913521811533)
            ·
              refine ⟨26821664472596592570679325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71524438593590913521811533 26821664472596592570679325)
              ·
                refine ⟨10058124177223722214004747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26821664472596592570679325 10058124177223722214004747)
                ·
                  refine ⟨15087186265835583321007121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058124177223722214004747 15087186265835583321007121)
                  ·
                    refine ⟨11315389699376687490755341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15087186265835583321007121 11315389699376687490755341)
                    ·
                      refine ⟨4243271137266257809033253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315389699376687490755341 4243271137266257809033253)
                      ·
                        rfl

theorem cell23_8263741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_8263741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263741 prefixEnd_8263741 := by exact prefixLift 8263741
  have htrace : WordTrace (prefixWord ++ tailWord_8263741) baseStart_8263741 baseEnd_8263741 := by
    simpa [prefixWord, tailWord_8263741, baseEnd_8263741] using wordTrace_append hprefix tailTrace_8263741
  have hstable : (prefixWord ++ tailWord_8263741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263741).length < 2 ^ (prefixWord ++ tailWord_8263741).sum := by decide
  have hdescent : baseEnd_8263741 < baseStart_8263741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263778 : List Nat := [3, 3, 2, 2, 2, 2, 2, 7]
def baseStart_8263778 : Nat := 118140960795 + 8263778 * 2 ^ 59
def prefixEnd_8263778 : Nat := 4983230072969 + 3 ^ 40 * 8263778 * 2
def baseEnd_8263778 : Nat := 157158893927795339417429

theorem tailTrace_8263778 : CollatzResearch.WordTrace tailWord_8263778 prefixEnd_8263778 157158893927795339417429 := by
  unfold tailWord_8263778
  simp only [CollatzResearch.WordTrace]
  refine ⟨75351186263937780441229997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200936496703834081176613325 75351186263937780441229997)
  ·
    refine ⟨28256694848976667665461249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75351186263937780441229997 28256694848976667665461249)
    ·
      refine ⟨21192521136732500749095937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28256694848976667665461249 21192521136732500749095937)
      ·
        refine ⟨15894390852549375561821953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21192521136732500749095937 15894390852549375561821953)
        ·
          refine ⟨11920793139412031671366465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15894390852549375561821953 11920793139412031671366465)
          ·
            refine ⟨8940594854559023753524849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11920793139412031671366465 8940594854559023753524849)
            ·
              refine ⟨6705446140919267815143637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940594854559023753524849 6705446140919267815143637)
              ·
                refine ⟨157158893927795339417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6705446140919267815143637 157158893927795339417429)
                ·
                  rfl

theorem cell23_8263778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_8263778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263778 prefixEnd_8263778 := by exact prefixLift 8263778
  have htrace : WordTrace (prefixWord ++ tailWord_8263778) baseStart_8263778 baseEnd_8263778 := by
    simpa [prefixWord, tailWord_8263778, baseEnd_8263778] using wordTrace_append hprefix tailTrace_8263778
  have hstable : (prefixWord ++ tailWord_8263778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263778).length < 2 ^ (prefixWord ++ tailWord_8263778).sum := by decide
  have hdescent : baseEnd_8263778 < baseStart_8263778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263822 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_8263822 : Nat := 118140960795 + 8263822 * 2 ^ 59
def prefixEnd_8263822 : Nat := 4983230072969 + 3 ^ 40 * 8263822 * 2
def baseEnd_8263822 : Nat := 4243312729199271992120381

theorem tailTrace_8263822 : CollatzResearch.WordTrace tailWord_8263822 prefixEnd_8263822 4243312729199271992120381 := by
  unfold tailWord_8263822
  simp only [CollatzResearch.WordTrace]
  refine ⟨37675793733448964659940215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200937566578394478186347813 37675793733448964659940215)
  ·
    refine ⟨56513690600173446989910323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37675793733448964659940215 56513690600173446989910323)
    ·
      refine ⟨84770535900260170484865485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56513690600173446989910323 84770535900260170484865485)
      ·
        refine ⟨31788950962597563931824557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84770535900260170484865485 31788950962597563931824557)
        ·
          refine ⟨11920856610974086474434209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31788950962597563931824557 11920856610974086474434209)
          ·
            refine ⟨8940642458230564855825657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11920856610974086474434209 8940642458230564855825657)
            ·
              refine ⟨6705481843672923641869243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940642458230564855825657 6705481843672923641869243)
              ·
                refine ⟨10058222765509385462803865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705481843672923641869243 10058222765509385462803865)
                ·
                  refine ⟨7543667074132039097102899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10058222765509385462803865 7543667074132039097102899)
                  ·
                    refine ⟨11315500611198058645654349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7543667074132039097102899 11315500611198058645654349)
                    ·
                      refine ⟨4243312729199271992120381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315500611198058645654349 4243312729199271992120381)
                      ·
                        rfl

theorem cell23_8263822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_8263822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263822 prefixEnd_8263822 := by exact prefixLift 8263822
  have htrace : WordTrace (prefixWord ++ tailWord_8263822) baseStart_8263822 baseEnd_8263822 := by
    simpa [prefixWord, tailWord_8263822, baseEnd_8263822] using wordTrace_append hprefix tailTrace_8263822
  have hstable : (prefixWord ++ tailWord_8263822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263822).length < 2 ^ (prefixWord ++ tailWord_8263822).sum := by decide
  have hdescent : baseEnd_8263822 < baseStart_8263822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263832 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 1, 3, 2]
def baseStart_8263832 : Nat := 118140960795 + 8263832 * 2 ^ 59
def prefixEnd_8263832 : Nat := 4983230072969 + 3 ^ 40 * 8263832 * 2
def baseEnd_8263832 : Nat := 4243317864005816952995335

theorem tailTrace_8263832 : CollatzResearch.WordTrace tailWord_8263832 prefixEnd_8263832 4243317864005816952995335 := by
  unfold tailWord_8263832
  simp only [CollatzResearch.WordTrace]
  refine ⟨150703357298777744493692875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200937809731703659324923833 150703357298777744493692875)
  ·
    refine ⟨226055035948166616740539313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150703357298777744493692875 226055035948166616740539313)
    ·
      refine ⟨169541276961124962555404485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226055035948166616740539313 169541276961124962555404485)
      ·
        refine ⟨31788989430210930479138341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169541276961124962555404485 31788989430210930479138341)
        ·
          refine ⟨5960435518164549464838439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31788989430210930479138341 5960435518164549464838439)
          ·
            refine ⟨8940653277246824197257659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960435518164549464838439 8940653277246824197257659)
            ·
              refine ⟨13410979915870236295886489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940653277246824197257659 13410979915870236295886489)
              ·
                refine ⟨10058234936902677221914867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13410979915870236295886489 10058234936902677221914867)
                ·
                  refine ⟨15087352405354015832872301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058234936902677221914867 15087352405354015832872301)
                  ·
                    refine ⟨5657757152007755937327113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15087352405354015832872301 5657757152007755937327113)
                    ·
                      refine ⟨4243317864005816952995335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5657757152007755937327113 4243317864005816952995335)
                      ·
                        rfl

theorem cell23_8263832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_8263832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263832 prefixEnd_8263832 := by exact prefixLift 8263832
  have htrace : WordTrace (prefixWord ++ tailWord_8263832) baseStart_8263832 baseEnd_8263832 := by
    simpa [prefixWord, tailWord_8263832, baseEnd_8263832] using wordTrace_append hprefix tailTrace_8263832
  have hstable : (prefixWord ++ tailWord_8263832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263832).length < 2 ^ (prefixWord ++ tailWord_8263832).sum := by decide
  have hdescent : baseEnd_8263832 < baseStart_8263832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263864 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_8263864 : Nat := 118140960795 + 8263864 * 2 ^ 59
def prefixEnd_8263864 : Nat := 4983230072969 + 3 ^ 40 * 8263864 * 2
def baseEnd_8263864 : Nat := 1414444765128920275931729

theorem tailTrace_8263864 : CollatzResearch.WordTrace tailWord_8263864 prefixEnd_8263864 1414444765128920275931729 := by
  unfold tailWord_8263864
  simp only [CollatzResearch.WordTrace]
  refine ⟨150703940866719779226275323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200938587822293038968367097 150703940866719779226275323)
  ·
    refine ⟨226055911300079668839412985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150703940866719779226275323 226055911300079668839412985)
    ·
      refine ⟨169541933475059751629559739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226055911300079668839412985 169541933475059751629559739)
      ·
        refine ⟨254312900212589627444339609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169541933475059751629559739 254312900212589627444339609)
        ·
          refine ⟨190734675159442220583254707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254312900212589627444339609 190734675159442220583254707)
          ·
            refine ⟨286102012739163330874882061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190734675159442220583254707 286102012739163330874882061)
            ·
              refine ⟨107288254777186249078080773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286102012739163330874882061 107288254777186249078080773)
              ·
                refine ⟨20116547770722421702140145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107288254777186249078080773 20116547770722421702140145)
                ·
                  refine ⟨15087410828041816276605109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20116547770722421702140145 15087410828041816276605109)
                  ·
                    refine ⟨1414444765128920275931729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15087410828041816276605109 1414444765128920275931729)
                    ·
                      rfl

theorem cell23_8263864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_8263864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263864 prefixEnd_8263864 := by exact prefixLift 8263864
  have htrace : WordTrace (prefixWord ++ tailWord_8263864) baseStart_8263864 baseEnd_8263864 := by
    simpa [prefixWord, tailWord_8263864, baseEnd_8263864] using wordTrace_append hprefix tailTrace_8263864
  have hstable : (prefixWord ++ tailWord_8263864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263864).length < 2 ^ (prefixWord ++ tailWord_8263864).sum := by decide
  have hdescent : baseEnd_8263864 < baseStart_8263864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263868 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 5]
def baseStart_8263868 : Nat := 118140960795 + 8263868 * 2 ^ 59
def prefixEnd_8263868 : Nat := 4983230072969 + 3 ^ 40 * 8263868 * 2
def baseEnd_8263868 : Nat := 471481816589930979127241

theorem tailTrace_8263868 : CollatzResearch.WordTrace tailWord_8263868 prefixEnd_8263868 471481816589930979127241 := by
  unfold tailWord_8263868
  simp only [CollatzResearch.WordTrace]
  refine ⟨150704013812712533567848129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200938685083616711423797505 150704013812712533567848129)
  ·
    refine ⟨113028010359534400175886097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150704013812712533567848129 113028010359534400175886097)
    ·
      refine ⟨84771007769650800131914573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113028010359534400175886097 84771007769650800131914573)
      ·
        refine ⟨31789127913619050049467965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84771007769650800131914573 31789127913619050049467965)
        ·
          refine ⟨11920922967607143768550487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31789127913619050049467965 11920922967607143768550487)
          ·
            refine ⟨17881384451410715652825731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920922967607143768550487 17881384451410715652825731)
            ·
              refine ⟨26822076677116073479238597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17881384451410715652825731 26822076677116073479238597)
              ·
                refine ⟨5029139376959263777357237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26822076677116073479238597 5029139376959263777357237)
                ·
                  refine ⟨471481816589930979127241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5029139376959263777357237 471481816589930979127241)
                  ·
                    rfl

theorem cell23_8263868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_8263868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263868 prefixEnd_8263868 := by exact prefixLift 8263868
  have htrace : WordTrace (prefixWord ++ tailWord_8263868) baseStart_8263868 baseEnd_8263868 := by
    simpa [prefixWord, tailWord_8263868, baseEnd_8263868] using wordTrace_append hprefix tailTrace_8263868
  have hstable : (prefixWord ++ tailWord_8263868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263868).length < 2 ^ (prefixWord ++ tailWord_8263868).sum := by decide
  have hdescent : baseEnd_8263868 < baseStart_8263868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263914 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_8263914 : Nat := 118140960795 + 8263914 * 2 ^ 59
def prefixEnd_8263914 : Nat := 4983230072969 + 3 ^ 40 * 8263914 * 2
def baseEnd_8263914 : Nat := 4243359969419485632169957

theorem tailTrace_8263914 : CollatzResearch.WordTrace tailWord_8263914 prefixEnd_8263914 4243359969419485632169957 := by
  unfold tailWord_8263914
  simp only [CollatzResearch.WordTrace]
  refine ⟨75352426345814604247967699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200939803588838944661247197 75352426345814604247967699)
  ·
    refine ⟨113028639518721906371951549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75352426345814604247967699 113028639518721906371951549)
    ·
      refine ⟨42385739819520714889481831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113028639518721906371951549 42385739819520714889481831)
      ·
        refine ⟨63578609729281072334222747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42385739819520714889481831 63578609729281072334222747)
        ·
          refine ⟨95367914593921608501334121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63578609729281072334222747 95367914593921608501334121)
          ·
            refine ⟨71525935945441206376000591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95367914593921608501334121 71525935945441206376000591)
            ·
              refine ⟨107288903918161809564000887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71525935945441206376000591 107288903918161809564000887)
              ·
                refine ⟨160933355877242714346001331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107288903918161809564000887 160933355877242714346001331)
                ·
                  refine ⟨241400033815864071519001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160933355877242714346001331 241400033815864071519001997)
                  ·
                    refine ⟨90525012680949026819625749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241400033815864071519001997 90525012680949026819625749)
                    ·
                      refine ⟨4243359969419485632169957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90525012680949026819625749 4243359969419485632169957)
                      ·
                        rfl

theorem cell23_8263914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_8263914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263914 prefixEnd_8263914 := by exact prefixLift 8263914
  have htrace : WordTrace (prefixWord ++ tailWord_8263914) baseStart_8263914 baseEnd_8263914 := by
    simpa [prefixWord, tailWord_8263914, baseEnd_8263914] using wordTrace_append hprefix tailTrace_8263914
  have hstable : (prefixWord ++ tailWord_8263914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263914).length < 2 ^ (prefixWord ++ tailWord_8263914).sum := by decide
  have hdescent : baseEnd_8263914 < baseStart_8263914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263921 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_8263921 : Nat := 118140960795 + 8263921 * 2 ^ 59
def prefixEnd_8263921 : Nat := 4983230072969 + 3 ^ 40 * 8263921 * 2
def baseEnd_8263921 : Nat := 4243363563784067104782425

theorem tailTrace_8263921 : CollatzResearch.WordTrace tailWord_8263921 prefixEnd_8263921 4243363563784067104782425 := by
  unfold tailWord_8263921
  simp only [CollatzResearch.WordTrace]
  refine ⟨301409960694233057187375617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200939973796155371458250411 301409960694233057187375617)
  ·
    refine ⟨226057470520674792890531713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301409960694233057187375617 226057470520674792890531713)
    ·
      refine ⟨169543102890506094667898785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226057470520674792890531713 169543102890506094667898785)
      ·
        refine ⟨127157327167879571000924089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169543102890506094667898785 127157327167879571000924089)
        ·
          refine ⟨95367995375909678250693067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127157327167879571000924089 95367995375909678250693067)
          ·
            refine ⟨143051993063864517376039601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95367995375909678250693067 143051993063864517376039601)
            ·
              refine ⟨107288994797898388032029701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143051993063864517376039601 107288994797898388032029701)
              ·
                refine ⟨20116686524605947756005569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107288994797898388032029701 20116686524605947756005569)
                ·
                  refine ⟨15087514893454460817004177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20116686524605947756005569 15087514893454460817004177)
                  ·
                    refine ⟨11315636170090845612753133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15087514893454460817004177 11315636170090845612753133)
                    ·
                      refine ⟨4243363563784067104782425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315636170090845612753133 4243363563784067104782425)
                      ·
                        rfl

theorem cell23_8263921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_8263921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263921 prefixEnd_8263921 := by exact prefixLift 8263921
  have htrace : WordTrace (prefixWord ++ tailWord_8263921) baseStart_8263921 baseEnd_8263921 := by
    simpa [prefixWord, tailWord_8263921, baseEnd_8263921] using wordTrace_append hprefix tailTrace_8263921
  have hstable : (prefixWord ++ tailWord_8263921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263921).length < 2 ^ (prefixWord ++ tailWord_8263921).sum := by decide
  have hdescent : baseEnd_8263921 < baseStart_8263921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263938 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_8263938 : Nat := 118140960795 + 8263938 * 2 ^ 59
def prefixEnd_8263938 : Nat := 4983230072969 + 3 ^ 40 * 8263938 * 2
def baseEnd_8263938 : Nat := 4243372292955193538269847

theorem tailTrace_8263938 : CollatzResearch.WordTrace tailWord_8263938 prefixEnd_8263938 4243372292955193538269847 := by
  unfold tailWord_8263938
  simp only [CollatzResearch.WordTrace]
  refine ⟨75352645183792867272686117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200940387156780979393829645 75352645183792867272686117)
  ·
    refine ⟨14128620971961162613628647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75352645183792867272686117 14128620971961162613628647)
    ·
      refine ⟨21192931457941743920442971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14128620971961162613628647 21192931457941743920442971)
      ·
        refine ⟨31789397186912615880664457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21192931457941743920442971 31789397186912615880664457)
        ·
          refine ⟨23842047890184461910498343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31789397186912615880664457 23842047890184461910498343)
          ·
            refine ⟨35763071835276692865747515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23842047890184461910498343 35763071835276692865747515)
            ·
              refine ⟨53644607752915039298621273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35763071835276692865747515 53644607752915039298621273)
              ·
                refine ⟨40233455814686279473965955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53644607752915039298621273 40233455814686279473965955)
                ·
                  refine ⟨60350183722029419210948933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40233455814686279473965955 60350183722029419210948933)
                  ·
                    refine ⟨11315659447880516102052925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60350183722029419210948933 11315659447880516102052925)
                    ·
                      refine ⟨4243372292955193538269847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315659447880516102052925 4243372292955193538269847)
                      ·
                        rfl

theorem cell23_8263938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_8263938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263938 prefixEnd_8263938 := by exact prefixLift 8263938
  have htrace : WordTrace (prefixWord ++ tailWord_8263938) baseStart_8263938 baseEnd_8263938 := by
    simpa [prefixWord, tailWord_8263938, baseEnd_8263938] using wordTrace_append hprefix tailTrace_8263938
  have hstable : (prefixWord ++ tailWord_8263938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263938).length < 2 ^ (prefixWord ++ tailWord_8263938).sum := by decide
  have hdescent : baseEnd_8263938 < baseStart_8263938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263962 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_8263962 : Nat := 118140960795 + 8263962 * 2 ^ 59
def prefixEnd_8263962 : Nat := 4983230072969 + 3 ^ 40 * 8263962 * 2
def baseEnd_8263962 : Nat := 1414461538830300481456579

theorem tailTrace_8263962 : CollatzResearch.WordTrace tailWord_8263962 prefixEnd_8263962 1414461538830300481456579 := by
  unfold tailWord_8263962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75352864021771130297404535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200940970724723014126412093 75352864021771130297404535)
  ·
    refine ⟨113029296032656695446106803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75352864021771130297404535 113029296032656695446106803)
    ·
      refine ⟨169543944048985043169160205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113029296032656695446106803 169543944048985043169160205)
      ·
        refine ⟨63578979018369391188435077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169543944048985043169160205 63578979018369391188435077)
        ·
          refine ⟨11921058565944260847831577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63578979018369391188435077 11921058565944260847831577)
          ·
            refine ⟨8940793924458195635873683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11921058565944260847831577 8940793924458195635873683)
            ·
              refine ⟨13411190886687293453810525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940793924458195635873683 13411190886687293453810525)
              ·
                refine ⟨5029196582507735045178947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13411190886687293453810525 5029196582507735045178947)
                ·
                  refine ⟨7543794873761602567768421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029196582507735045178947 7543794873761602567768421)
                  ·
                    refine ⟨1414461538830300481456579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543794873761602567768421 1414461538830300481456579)
                    ·
                      rfl

theorem cell23_8263962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_8263962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263962 prefixEnd_8263962 := by exact prefixLift 8263962
  have htrace : WordTrace (prefixWord ++ tailWord_8263962) baseStart_8263962 baseEnd_8263962 := by
    simpa [prefixWord, tailWord_8263962, baseEnd_8263962] using wordTrace_append hprefix tailTrace_8263962
  have hstable : (prefixWord ++ tailWord_8263962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263962).length < 2 ^ (prefixWord ++ tailWord_8263962).sum := by decide
  have hdescent : baseEnd_8263962 < baseStart_8263962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263971 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 1, 5]
def baseStart_8263971 : Nat := 118140960795 + 8263971 * 2 ^ 59
def prefixEnd_8263971 : Nat := 4983230072969 + 3 ^ 40 * 8263971 * 2
def baseEnd_8263971 : Nat := 1414463079272263969719065

theorem tailTrace_8263971 : CollatzResearch.WordTrace tailWord_8263971 prefixEnd_8263971 1414463079272263969719065 := by
  unfold tailWord_8263971
  simp only [CollatzResearch.WordTrace]
  refine ⟨301411784344051915726695767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200941189562701277151130511 301411784344051915726695767)
  ·
    refine ⟨452117676516077873590043651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301411784344051915726695767 452117676516077873590043651)
    ·
      refine ⟨678176514774116810385065477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452117676516077873590043651 678176514774116810385065477)
      ·
        refine ⟨127158096520146901947199777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678176514774116810385065477 127158096520146901947199777)
        ·
          refine ⟨95368572390110176460399833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127158096520146901947199777 95368572390110176460399833)
          ·
            refine ⟨71526429292582632345299875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95368572390110176460399833 71526429292582632345299875)
            ·
              refine ⟨107289643938873948517949813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71526429292582632345299875 107289643938873948517949813)
              ·
                refine ⟨10058404119269432673557795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107289643938873948517949813 10058404119269432673557795)
                ·
                  refine ⟨15087606178904149010336693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058404119269432673557795 15087606178904149010336693)
                  ·
                    refine ⟨1414463079272263969719065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15087606178904149010336693 1414463079272263969719065)
                    ·
                      rfl

theorem cell23_8263971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 5].length) (baseStart_8263971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263971 prefixEnd_8263971 := by exact prefixLift 8263971
  have htrace : WordTrace (prefixWord ++ tailWord_8263971) baseStart_8263971 baseEnd_8263971 := by
    simpa [prefixWord, tailWord_8263971, baseEnd_8263971] using wordTrace_append hprefix tailTrace_8263971
  have hstable : (prefixWord ++ tailWord_8263971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263971).length < 2 ^ (prefixWord ++ tailWord_8263971).sum := by decide
  have hdescent : baseEnd_8263971 < baseStart_8263971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263984 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_8263984 : Nat := 118140960795 + 8263984 * 2 ^ 59
def prefixEnd_8263984 : Nat := 4983230072969 + 3 ^ 40 * 8263984 * 2
def baseEnd_8263984 : Nat := 1414465304355100119431545

theorem tailTrace_8263984 : CollatzResearch.WordTrace tailWord_8263984 prefixEnd_8263984 1414465304355100119431545 := by
  unfold tailWord_8263984
  simp only [CollatzResearch.WordTrace]
  refine ⟨150706129246502409473459503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200941505662003212631279337 150706129246502409473459503)
  ·
    refine ⟨226059193869753614210189255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150706129246502409473459503 226059193869753614210189255)
    ·
      refine ⟨339088790804630421315283883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226059193869753614210189255 339088790804630421315283883)
      ·
        refine ⟨508633186206945631972925825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339088790804630421315283883 508633186206945631972925825)
        ·
          refine ⟨381474889655209223979694369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508633186206945631972925825 381474889655209223979694369)
          ·
            refine ⟨286106167241406917984770777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381474889655209223979694369 286106167241406917984770777)
            ·
              refine ⟨214579625431055188488578083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286106167241406917984770777 214579625431055188488578083)
              ·
                refine ⟨321869438146582782732867125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214579625431055188488578083 321869438146582782732867125)
                ·
                  refine ⟨30175259826242135881206293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321869438146582782732867125 30175259826242135881206293)
                  ·
                    refine ⟨1414465304355100119431545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30175259826242135881206293 1414465304355100119431545)
                    ·
                      rfl

theorem cell23_8263984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_8263984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263984 prefixEnd_8263984 := by exact prefixLift 8263984
  have htrace : WordTrace (prefixWord ++ tailWord_8263984) baseStart_8263984 baseEnd_8263984 := by
    simpa [prefixWord, tailWord_8263984, baseEnd_8263984] using wordTrace_append hprefix tailTrace_8263984
  have hstable : (prefixWord ++ tailWord_8263984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263984).length < 2 ^ (prefixWord ++ tailWord_8263984).sum := by decide
  have hdescent : baseEnd_8263984 < baseStart_8263984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264008 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_8264008 : Nat := 118140960795 + 8264008 * 2 ^ 59
def prefixEnd_8264008 : Nat := 4983230072969 + 3 ^ 40 * 8264008 * 2
def baseEnd_8264008 : Nat := 4243408236601008264394525

theorem tailTrace_8264008 : CollatzResearch.WordTrace tailWord_8264008 prefixEnd_8264008 4243408236601008264394525 := by
  unfold tailWord_8264008
  simp only [CollatzResearch.WordTrace]
  refine ⟨150706566922458935522896339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200942089229945247363861785 150706566922458935522896339)
  ·
    refine ⟨226059850383688403284344509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150706566922458935522896339 226059850383688403284344509)
    ·
      refine ⟨84772443893883151231629191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226059850383688403284344509 84772443893883151231629191)
      ·
        refine ⟨127158665840824726847443787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84772443893883151231629191 127158665840824726847443787)
        ·
          refine ⟨190737998761237090271165681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127158665840824726847443787 190737998761237090271165681)
          ·
            refine ⟨143053499070927817703374261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190737998761237090271165681 143053499070927817703374261)
            ·
              refine ⟨13411265537899482909691337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143053499070927817703374261 13411265537899482909691337)
              ·
                refine ⟨10058449153424612182268503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13411265537899482909691337 10058449153424612182268503)
                ·
                  refine ⟨15087673730136918273402755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058449153424612182268503 15087673730136918273402755)
                  ·
                    refine ⟨22631510595205377410104133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15087673730136918273402755 22631510595205377410104133)
                    ·
                      refine ⟨4243408236601008264394525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22631510595205377410104133 4243408236601008264394525)
                      ·
                        rfl

theorem cell23_8264008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_8264008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264008 prefixEnd_8264008 := by exact prefixLift 8264008
  have htrace : WordTrace (prefixWord ++ tailWord_8264008) baseStart_8264008 baseEnd_8264008 := by
    simpa [prefixWord, tailWord_8264008, baseEnd_8264008] using wordTrace_append hprefix tailTrace_8264008
  have hstable : (prefixWord ++ tailWord_8264008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264008).length < 2 ^ (prefixWord ++ tailWord_8264008).sum := by decide
  have hdescent : baseEnd_8264008 < baseStart_8264008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264030 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_8264030 : Nat := 118140960795 + 8264030 * 2 ^ 59
def prefixEnd_8264030 : Nat := 4983230072969 + 3 ^ 40 * 8264030 * 2
def baseEnd_8264030 : Nat := 1414473177725135726106475

theorem tailTrace_8264030 : CollatzResearch.WordTrace tailWord_8264030 prefixEnd_8264030 1414473177725135726106475 := by
  unfold tailWord_8264030
  simp only [CollatzResearch.WordTrace]
  refine ⟨37676742031354771100386693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200942624167225445868729029 37676742031354771100386693)
  ·
    refine ⟨7064389130879019581322505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37676742031354771100386693 7064389130879019581322505)
    ·
      refine ⟨5298291848159264685991879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7064389130879019581322505 5298291848159264685991879)
      ·
        refine ⟨7947437772238897028987819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298291848159264685991879 7947437772238897028987819)
        ·
          refine ⟨11921156658358345543481729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947437772238897028987819 11921156658358345543481729)
          ·
            refine ⟨8940867493768759157611297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11921156658358345543481729 8940867493768759157611297)
            ·
              refine ⟨6705650620326569368208473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940867493768759157611297 6705650620326569368208473)
              ·
                refine ⟨5029237965244927026156355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6705650620326569368208473 5029237965244927026156355)
                ·
                  refine ⟨7543856947867390539234533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029237965244927026156355 7543856947867390539234533)
                  ·
                    refine ⟨1414473177725135726106475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543856947867390539234533 1414473177725135726106475)
                    ·
                      rfl

theorem cell23_8264030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_8264030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264030 prefixEnd_8264030 := by exact prefixLift 8264030
  have htrace : WordTrace (prefixWord ++ tailWord_8264030) baseStart_8264030 baseEnd_8264030 := by
    simpa [prefixWord, tailWord_8264030, baseEnd_8264030] using wordTrace_append hprefix tailTrace_8264030
  have hstable : (prefixWord ++ tailWord_8264030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264030).length < 2 ^ (prefixWord ++ tailWord_8264030).sum := by decide
  have hdescent : baseEnd_8264030 < baseStart_8264030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264041 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_8264041 : Nat := 118140960795 + 8264041 * 2 ^ 59
def prefixEnd_8264041 : Nat := 4983230072969 + 3 ^ 40 * 8264041 * 2
def baseEnd_8264041 : Nat := 4243425181462606635281873

theorem tailTrace_8264041 : CollatzResearch.WordTrace tailWord_8264041 prefixEnd_8264041 4243425181462606635281873 := by
  unfold tailWord_8264041
  simp only [CollatzResearch.WordTrace]
  refine ⟨301414337453798317681743977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200942891635865545121162651 301414337453798317681743977)
  ·
    refine ⟨226060753090348738261307983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301414337453798317681743977 226060753090348738261307983)
    ·
      refine ⟨339091129635523107391961975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226060753090348738261307983 339091129635523107391961975)
      ·
        refine ⟨508636694453284661087942963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339091129635523107391961975 508636694453284661087942963)
        ·
          refine ⟨762955041679926991631914445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508636694453284661087942963 762955041679926991631914445)
          ·
            refine ⟨286108140629972621861967917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762955041679926991631914445 286108140629972621861967917)
            ·
              refine ⟨107290552736239733198237969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286108140629972621861967917 107290552736239733198237969)
              ·
                refine ⟨80467914552179799898678477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107290552736239733198237969 80467914552179799898678477)
                ·
                  refine ⟨30175467957067424962004429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80467914552179799898678477 30175467957067424962004429)
                  ·
                    refine ⟨11315800483900284360751661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30175467957067424962004429 11315800483900284360751661)
                    ·
                      refine ⟨4243425181462606635281873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315800483900284360751661 4243425181462606635281873)
                      ·
                        rfl

theorem cell23_8264041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_8264041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264041 prefixEnd_8264041 := by exact prefixLift 8264041
  have htrace : WordTrace (prefixWord ++ tailWord_8264041) baseStart_8264041 baseEnd_8264041 := by
    simpa [prefixWord, tailWord_8264041, baseEnd_8264041] using wordTrace_append hprefix tailTrace_8264041
  have hstable : (prefixWord ++ tailWord_8264041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264041).length < 2 ^ (prefixWord ++ tailWord_8264041).sum := by decide
  have hdescent : baseEnd_8264041 < baseStart_8264041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264071 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_8264071 : Nat := 118140960795 + 8264071 * 2 ^ 59
def prefixEnd_8264071 : Nat := 4983230072969 + 3 ^ 40 * 8264071 * 2
def baseEnd_8264071 : Nat := 4243440585882241517906735

theorem tailTrace_8264071 : CollatzResearch.WordTrace tailWord_8264071 prefixEnd_8264071 4243440585882241517906735 := by
  unfold tailWord_8264071
  simp only [CollatzResearch.WordTrace]
  refine ⟨301415431643689632805336067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200943621095793088536890711 301415431643689632805336067)
  ·
    refine ⟨452123147465534449208004101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301415431643689632805336067 452123147465534449208004101)
    ·
      refine ⟨84773090149787709226500769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452123147465534449208004101 84773090149787709226500769)
      ·
        refine ⟨63579817612340781919875577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84773090149787709226500769 63579817612340781919875577)
        ·
          refine ⟨47684863209255586439906683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63579817612340781919875577 47684863209255586439906683)
          ·
            refine ⟨71527294813883379659860025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47684863209255586439906683 71527294813883379659860025)
            ·
              refine ⟨53645471110412534744895019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71527294813883379659860025 53645471110412534744895019)
              ·
                refine ⟨80468206665618802117342529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53645471110412534744895019 80468206665618802117342529)
                ·
                  refine ⟨60351154999214101588006897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80468206665618802117342529 60351154999214101588006897)
                  ·
                    refine ⟨45263366249410576191005173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60351154999214101588006897 45263366249410576191005173)
                    ·
                      refine ⟨4243440585882241517906735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45263366249410576191005173 4243440585882241517906735)
                      ·
                        rfl

theorem cell23_8264071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_8264071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264071 prefixEnd_8264071 := by exact prefixLift 8264071
  have htrace : WordTrace (prefixWord ++ tailWord_8264071) baseStart_8264071 baseEnd_8264071 := by
    simpa [prefixWord, tailWord_8264071, baseEnd_8264071] using wordTrace_append hprefix tailTrace_8264071
  have hstable : (prefixWord ++ tailWord_8264071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264071).length < 2 ^ (prefixWord ++ tailWord_8264071).sum := by decide
  have hdescent : baseEnd_8264071 < baseStart_8264071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264106 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_8264106 : Nat := 118140960795 + 8264106 * 2 ^ 59
def prefixEnd_8264106 : Nat := 4983230072969 + 3 ^ 40 * 8264106 * 2
def baseEnd_8264106 : Nat := 4243458557705148880969075

theorem tailTrace_8264106 : CollatzResearch.WordTrace tailWord_8264106 prefixEnd_8264106 4243458557705148880969075 := by
  unfold tailWord_8264106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75354177049640708445715043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200944472132375222521906781 75354177049640708445715043)
  ·
    refine ⟨113031265574461062668572565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75354177049640708445715043 113031265574461062668572565)
    ·
      refine ⟨5298340573802862312589339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113031265574461062668572565 5298340573802862312589339)
      ·
        refine ⟨7947510860704293468884009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298340573802862312589339 7947510860704293468884009)
        ·
          refine ⟨5960633145528220101663007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7947510860704293468884009 5960633145528220101663007)
          ·
            refine ⟨8940949718292330152494511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960633145528220101663007 8940949718292330152494511)
            ·
              refine ⟨13411424577438495228741767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940949718292330152494511 13411424577438495228741767)
              ·
                refine ⟨20117136866157742843112651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13411424577438495228741767 20117136866157742843112651)
                ·
                  refine ⟨30175705299236614264668977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20117136866157742843112651 30175705299236614264668977)
                  ·
                    refine ⟨22631778974427460698501733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30175705299236614264668977 22631778974427460698501733)
                    ·
                      refine ⟨4243458557705148880969075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22631778974427460698501733 4243458557705148880969075)
                      ·
                        rfl

theorem cell23_8264106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_8264106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264106 prefixEnd_8264106 := by exact prefixLift 8264106
  have htrace : WordTrace (prefixWord ++ tailWord_8264106) baseStart_8264106 baseEnd_8264106 := by
    simpa [prefixWord, tailWord_8264106, baseEnd_8264106] using wordTrace_append hprefix tailTrace_8264106
  have hstable : (prefixWord ++ tailWord_8264106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264106).length < 2 ^ (prefixWord ++ tailWord_8264106).sum := by decide
  have hdescent : baseEnd_8264106 < baseStart_8264106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264109 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_8264109 : Nat := 118140960795 + 8264109 * 2 ^ 59
def prefixEnd_8264109 : Nat := 4983230072969 + 3 ^ 40 * 8264109 * 2
def baseEnd_8264109 : Nat := 4243460098147112369231561

theorem tailTrace_8264109 : CollatzResearch.WordTrace tailWord_8264109 prefixEnd_8264109 4243460098147112369231561 := by
  unfold tailWord_8264109
  simp only [CollatzResearch.WordTrace]
  refine ⟨301416817617551965295219381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200944545078367976863479587 301416817617551965295219381)
  ·
    refine ⟨28257826651645496746426817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301416817617551965295219381 28257826651645496746426817)
    ·
      refine ⟨21193369988734122559820113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28257826651645496746426817 21193369988734122559820113)
      ·
        refine ⟨15895027491550591919865085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21193369988734122559820113 15895027491550591919865085)
        ·
          refine ⟨5960635309331471969949407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15895027491550591919865085 5960635309331471969949407)
          ·
            refine ⟨8940952963997207954924111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960635309331471969949407 8940952963997207954924111)
            ·
              refine ⟨13411429445995811932386167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940952963997207954924111 13411429445995811932386167)
              ·
                refine ⟨20117144168993717898579251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13411429445995811932386167 20117144168993717898579251)
                ·
                  refine ⟨30175716253490576847868877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20117144168993717898579251 30175716253490576847868877)
                  ·
                    refine ⟨11315893595058966317950829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30175716253490576847868877 11315893595058966317950829)
                    ·
                      refine ⟨4243460098147112369231561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11315893595058966317950829 4243460098147112369231561)
                      ·
                        rfl

theorem cell23_8264109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_8264109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264109 prefixEnd_8264109 := by exact prefixLift 8264109
  have htrace : WordTrace (prefixWord ++ tailWord_8264109) baseStart_8264109 baseEnd_8264109 := by
    simpa [prefixWord, tailWord_8264109, baseEnd_8264109] using wordTrace_append hprefix tailTrace_8264109
  have hstable : (prefixWord ++ tailWord_8264109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264109).length < 2 ^ (prefixWord ++ tailWord_8264109).sum := by decide
  have hdescent : baseEnd_8264109 < baseStart_8264109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264208 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_8264208 : Nat := 118140960795 + 8264208 * 2 ^ 59
def prefixEnd_8264208 : Nat := 4983230072969 + 3 ^ 40 * 8264208 * 2
def baseEnd_8264208 : Nat := 4243510932731907481893605

theorem tailTrace_8264208 : CollatzResearch.WordTrace tailWord_8264208 prefixEnd_8264208 4243510932731907481893605 := by
  unfold tailWord_8264208
  simp only [CollatzResearch.WordTrace]
  refine ⟨150710214222096652601536639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200946952296128870135382185 150710214222096652601536639)
  ·
    refine ⟨226065321333144978902304959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150710214222096652601536639 226065321333144978902304959)
    ·
      refine ⟨339097981999717468353457439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226065321333144978902304959 339097981999717468353457439)
      ·
        refine ⟨508646972999576202530186159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339097981999717468353457439 508646972999576202530186159)
        ·
          refine ⟨762970459499364303795279239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508646972999576202530186159 762970459499364303795279239)
          ·
            refine ⟨1144455689249046455692918859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762970459499364303795279239 1144455689249046455692918859)
            ·
              refine ⟨1716683533873569683539378289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144455689249046455692918859 1716683533873569683539378289)
              ·
                refine ⟨1287512650405177262654533717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716683533873569683539378289 1287512650405177262654533717)
                ·
                  refine ⟨15088038871935671046732817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1287512650405177262654533717 15088038871935671046732817)
                  ·
                    refine ⟨11316029153951753285049613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15088038871935671046732817 11316029153951753285049613)
                    ·
                      refine ⟨4243510932731907481893605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316029153951753285049613 4243510932731907481893605)
                      ·
                        rfl

theorem cell23_8264208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_8264208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264208 prefixEnd_8264208 := by exact prefixLift 8264208
  have htrace : WordTrace (prefixWord ++ tailWord_8264208) baseStart_8264208 baseEnd_8264208 := by
    simpa [prefixWord, tailWord_8264208, baseEnd_8264208] using wordTrace_append hprefix tailTrace_8264208
  have hstable : (prefixWord ++ tailWord_8264208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264208).length < 2 ^ (prefixWord ++ tailWord_8264208).sum := by decide
  have hdescent : baseEnd_8264208 < baseStart_8264208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264232 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 3, 4]
def baseStart_8264232 : Nat := 118140960795 + 8264232 * 2 ^ 59
def prefixEnd_8264232 : Nat := 4983230072969 + 3 ^ 40 * 8264232 * 2
def baseEnd_8264232 : Nat := 1414507752089205129331165

theorem tailTrace_8264232 : CollatzResearch.WordTrace tailWord_8264232 prefixEnd_8264232 1414507752089205129331165 := by
  unfold tailWord_8264232
  simp only [CollatzResearch.WordTrace]
  refine ⟨150710651898053178650973475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200947535864070904867964633 150710651898053178650973475)
  ·
    refine ⟨226065977847079767976460213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150710651898053178650973475 226065977847079767976460213)
    ·
      refine ⟨21193685423163728247793145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226065977847079767976460213 21193685423163728247793145)
      ·
        refine ⟨15895264067372796185844859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21193685423163728247793145 15895264067372796185844859)
        ·
          refine ⟨23842896101059194278767289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15895264067372796185844859 23842896101059194278767289)
          ·
            refine ⟨17882172075794395709075467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23842896101059194278767289 17882172075794395709075467)
            ·
              refine ⟨26823258113691593563613201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882172075794395709075467 26823258113691593563613201)
              ·
                refine ⟨20117443585268695172709901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26823258113691593563613201 20117443585268695172709901)
                ·
                  refine ⟨7544041344475760689766213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20117443585268695172709901 7544041344475760689766213)
                  ·
                    refine ⟨1414507752089205129331165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7544041344475760689766213 1414507752089205129331165)
                    ·
                      rfl

theorem cell23_8264232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_8264232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264232 prefixEnd_8264232 := by exact prefixLift 8264232
  have htrace : WordTrace (prefixWord ++ tailWord_8264232) baseStart_8264232 baseEnd_8264232 := by
    simpa [prefixWord, tailWord_8264232, baseEnd_8264232] using wordTrace_append hprefix tailTrace_8264232
  have hstable : (prefixWord ++ tailWord_8264232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264232).length < 2 ^ (prefixWord ++ tailWord_8264232).sum := by decide
  have hdescent : baseEnd_8264232 < baseStart_8264232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264255 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 3]
def baseStart_8264255 : Nat := 118140960795 + 8264255 * 2 ^ 59
def prefixEnd_8264255 : Nat := 4983230072969 + 3 ^ 40 * 8264255 * 2
def baseEnd_8264255 : Nat := 4243535066322668798005889

theorem tailTrace_8264255 : CollatzResearch.WordTrace tailWord_8264255 prefixEnd_8264255 4243535066322668798005889 := by
  unfold tailWord_8264255
  simp only [CollatzResearch.WordTrace]
  refine ⟨301422142675023032230034219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200948095116682021486689479 301422142675023032230034219)
  ·
    refine ⟨452133214012534548345051329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301422142675023032230034219 452133214012534548345051329)
    ·
      refine ⟨339099910509400911258788497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452133214012534548345051329 339099910509400911258788497)
      ·
        refine ⟨254324932882050683444091373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339099910509400911258788497 254324932882050683444091373)
        ·
          refine ⟨95371849830769006291534265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254324932882050683444091373 95371849830769006291534265)
          ·
            refine ⟨71528887373076754718650699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95371849830769006291534265 71528887373076754718650699)
            ·
              refine ⟨107293331059615132077976049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71528887373076754718650699 107293331059615132077976049)
              ·
                refine ⟨80469998294711349058482037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107293331059615132077976049 80469998294711349058482037)
                ·
                  refine ⟨7544062340129188974232691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80469998294711349058482037 7544062340129188974232691)
                  ·
                    refine ⟨11316093510193783461349037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544062340129188974232691 11316093510193783461349037)
                    ·
                      refine ⟨4243535066322668798005889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316093510193783461349037 4243535066322668798005889)
                      ·
                        rfl

theorem cell23_8264255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_8264255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264255 prefixEnd_8264255 := by exact prefixLift 8264255
  have htrace : WordTrace (prefixWord ++ tailWord_8264255) baseStart_8264255 baseEnd_8264255 := by
    simpa [prefixWord, tailWord_8264255, baseEnd_8264255] using wordTrace_append hprefix tailTrace_8264255
  have hstable : (prefixWord ++ tailWord_8264255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264255).length < 2 ^ (prefixWord ++ tailWord_8264255).sum := by decide
  have hdescent : baseEnd_8264255 < baseStart_8264255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264262 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_8264262 : Nat := 118140960795 + 8264262 * 2 ^ 59
def prefixEnd_8264262 : Nat := 4983230072969 + 3 ^ 40 * 8264262 * 2
def baseEnd_8264262 : Nat := 471504295631916696735373

theorem tailTrace_8264262 : CollatzResearch.WordTrace tailWord_8264262 prefixEnd_8264262 471504295631916696735373 := by
  unfold tailWord_8264262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9419449937062427263298095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200948265323998448283692693 9419449937062427263298095)
  ·
    refine ⟨14129174905593640894947143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9419449937062427263298095 14129174905593640894947143)
    ·
      refine ⟨21193762358390461342420715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14129174905593640894947143 21193762358390461342420715)
      ·
        refine ⟨31790643537585692013631073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21193762358390461342420715 31790643537585692013631073)
        ·
          refine ⟨23842982653189269010223305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31790643537585692013631073 23842982653189269010223305)
          ·
            refine ⟨17882236989891951757667479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23842982653189269010223305 17882236989891951757667479)
            ·
              refine ⟨26823355484837927636501219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882236989891951757667479 26823355484837927636501219)
              ·
                refine ⟨40235033227256891454751829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26823355484837927636501219 40235033227256891454751829)
                ·
                  refine ⟨471504295631916696735373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40235033227256891454751829 471504295631916696735373)
                  ·
                    rfl

theorem cell23_8264262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_8264262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264262 prefixEnd_8264262 := by exact prefixLift 8264262
  have htrace : WordTrace (prefixWord ++ tailWord_8264262) baseStart_8264262 baseEnd_8264262 := by
    simpa [prefixWord, tailWord_8264262, baseEnd_8264262] using wordTrace_append hprefix tailTrace_8264262
  have hstable : (prefixWord ++ tailWord_8264262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264262).length < 2 ^ (prefixWord ++ tailWord_8264262).sum := by decide
  have hdescent : baseEnd_8264262 < baseStart_8264262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264295 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_8264295 : Nat := 118140960795 + 8264295 * 2 ^ 59
def prefixEnd_8264295 : Nat := 4983230072969 + 3 ^ 40 * 8264295 * 2
def baseEnd_8264295 : Nat := 4243555605548848641505705

theorem tailTrace_8264295 : CollatzResearch.WordTrace tailWord_8264295 prefixEnd_8264295 4243555605548848641505705 := by
  unfold tailWord_8264295
  simp only [CollatzResearch.WordTrace]
  refine ⟨301423601594878119061490339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200949067729918746040993559 301423601594878119061490339)
  ·
    refine ⟨452135402392317178592235509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301423601594878119061490339 452135402392317178592235509)
    ·
      refine ⟨42387693974279735493022079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452135402392317178592235509 42387693974279735493022079)
      ·
        refine ⟨63581540961419603239533119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42387693974279735493022079 63581540961419603239533119)
        ·
          refine ⟨95372311442129404859299679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63581540961419603239533119 95372311442129404859299679)
          ·
            refine ⟨143058467163194107288949519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95372311442129404859299679 143058467163194107288949519)
            ·
              refine ⟨214587700744791160933424279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143058467163194107288949519 214587700744791160933424279)
              ·
                refine ⟨321881551117186741400136419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214587700744791160933424279 321881551117186741400136419)
                ·
                  refine ⟨482822326675780112100204629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321881551117186741400136419 482822326675780112100204629)
                  ·
                    refine ⟨5658074140731798188674273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 482822326675780112100204629 5658074140731798188674273)
                    ·
                      refine ⟨4243555605548848641505705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658074140731798188674273 4243555605548848641505705)
                      ·
                        rfl

theorem cell23_8264295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_8264295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264295 prefixEnd_8264295 := by exact prefixLift 8264295
  have htrace : WordTrace (prefixWord ++ tailWord_8264295) baseStart_8264295 baseEnd_8264295 := by
    simpa [prefixWord, tailWord_8264295, baseEnd_8264295] using wordTrace_append hprefix tailTrace_8264295
  have hstable : (prefixWord ++ tailWord_8264295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264295).length < 2 ^ (prefixWord ++ tailWord_8264295).sum := by decide
  have hdescent : baseEnd_8264295 < baseStart_8264295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264345 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_8264345 : Nat := 118140960795 + 8264345 * 2 ^ 59
def prefixEnd_8264345 : Nat := 4983230072969 + 3 ^ 40 * 8264345 * 2
def baseEnd_8264345 : Nat := 4243581279581573445880475

theorem tailTrace_8264345 : CollatzResearch.WordTrace tailWord_8264345 prefixEnd_8264345 4243581279581573445880475 := by
  unfold tailWord_8264345
  simp only [CollatzResearch.WordTrace]
  refine ⟨301425425244696977600810489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200950283496464651733873659 301425425244696977600810489)
  ·
    refine ⟨226069068933522733200607867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301425425244696977600810489 226069068933522733200607867)
    ·
      refine ⟨339103603400284099800911801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226069068933522733200607867 339103603400284099800911801)
      ·
        refine ⟨254327702550213074850683851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339103603400284099800911801 254327702550213074850683851)
        ·
          refine ⟨381491553825319612276025777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254327702550213074850683851 381491553825319612276025777)
          ·
            refine ⟨286118665368989709207019333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381491553825319612276025777 286118665368989709207019333)
            ·
              refine ⟨53647249756685570476316125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286118665368989709207019333 53647249756685570476316125)
              ·
                refine ⟨20117718658757088928618547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53647249756685570476316125 20117718658757088928618547)
                ·
                  refine ⟨30176577988135633392927821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20117718658757088928618547 30176577988135633392927821)
                  ·
                    refine ⟨11316216745550862522347933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30176577988135633392927821 11316216745550862522347933)
                    ·
                      refine ⟨4243581279581573445880475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316216745550862522347933 4243581279581573445880475)
                      ·
                        rfl

theorem cell23_8264345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_8264345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264345 prefixEnd_8264345 := by exact prefixLift 8264345
  have htrace : WordTrace (prefixWord ++ tailWord_8264345) baseStart_8264345 baseEnd_8264345 := by
    simpa [prefixWord, tailWord_8264345, baseEnd_8264345] using wordTrace_append hprefix tailTrace_8264345
  have hstable : (prefixWord ++ tailWord_8264345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264345).length < 2 ^ (prefixWord ++ tailWord_8264345).sum := by decide
  have hdescent : baseEnd_8264345 < baseStart_8264345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264346 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_8264346 : Nat := 118140960795 + 8264346 * 2 ^ 59
def prefixEnd_8264346 : Nat := 4983230072969 + 3 ^ 40 * 8264346 * 2
def baseEnd_8264346 : Nat := 4243581793062227941967971

theorem tailTrace_8264346 : CollatzResearch.WordTrace tailWord_8264346 prefixEnd_8264346 4243581793062227941967971 := by
  unfold tailWord_8264346
  simp only [CollatzResearch.WordTrace]
  refine ⟨75356365429423338692899223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200950307811795569847731261 75356365429423338692899223)
  ·
    refine ⟨113034548144135008039348835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75356365429423338692899223 113034548144135008039348835)
    ·
      refine ⟨169551822216202512059023253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113034548144135008039348835 169551822216202512059023253)
      ·
        refine ⟨7947741666384492752766715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169551822216202512059023253 7947741666384492752766715)
        ·
          refine ⟨11921612499576739129150073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947741666384492752766715 11921612499576739129150073)
          ·
            refine ⟨8941209374682554346862555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11921612499576739129150073 8941209374682554346862555)
            ·
              refine ⟨13411814062023831520293833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941209374682554346862555 13411814062023831520293833)
              ·
                refine ⟨10058860546517873640220375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13411814062023831520293833 10058860546517873640220375)
                ·
                  refine ⟨15088290819776810460330563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058860546517873640220375 15088290819776810460330563)
                  ·
                    refine ⟨22632436229665215690495845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15088290819776810460330563 22632436229665215690495845)
                    ·
                      refine ⟨4243581793062227941967971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22632436229665215690495845 4243581793062227941967971)
                      ·
                        rfl

theorem cell23_8264346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_8264346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264346 prefixEnd_8264346 := by exact prefixLift 8264346
  have htrace : WordTrace (prefixWord ++ tailWord_8264346) baseStart_8264346 baseEnd_8264346 := by
    simpa [prefixWord, tailWord_8264346, baseEnd_8264346] using wordTrace_append hprefix tailTrace_8264346
  have hstable : (prefixWord ++ tailWord_8264346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264346).length < 2 ^ (prefixWord ++ tailWord_8264346).sum := by decide
  have hdescent : baseEnd_8264346 < baseStart_8264346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264359 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_8264359 : Nat := 118140960795 + 8264359 * 2 ^ 59
def prefixEnd_8264359 : Nat := 4983230072969 + 3 ^ 40 * 8264359 * 2
def baseEnd_8264359 : Nat := 4243588468310736391105411

theorem tailTrace_8264359 : CollatzResearch.WordTrace tailWord_8264359 prefixEnd_8264359 4243588468310736391105411 := by
  unfold tailWord_8264359
  simp only [CollatzResearch.WordTrace]
  refine ⟨301425935866646257991820131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200950623911097505327880087 301425935866646257991820131)
  ·
    refine ⟨452138903799969386987730197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301425935866646257991820131 452138903799969386987730197)
    ·
      refine ⟨21194011115623565015049853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 452138903799969386987730197 21194011115623565015049853)
      ·
        refine ⟨7947754168358836880643695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21194011115623565015049853 7947754168358836880643695)
        ·
          refine ⟨11921631252538255320965543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947754168358836880643695 11921631252538255320965543)
          ·
            refine ⟨17882446878807382981448315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11921631252538255320965543 17882446878807382981448315)
            ·
              refine ⟨26823670318211074472172473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882446878807382981448315 26823670318211074472172473)
              ·
                refine ⟨20117752738658305854129355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26823670318211074472172473 20117752738658305854129355)
                ·
                  refine ⟨30176629107987458781194033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20117752738658305854129355 30176629107987458781194033)
                  ·
                    refine ⟨22632471830990594085895525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30176629107987458781194033 22632471830990594085895525)
                    ·
                      refine ⟨4243588468310736391105411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22632471830990594085895525 4243588468310736391105411)
                      ·
                        rfl

theorem cell23_8264359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_8264359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264359 prefixEnd_8264359 := by exact prefixLift 8264359
  have htrace : WordTrace (prefixWord ++ tailWord_8264359) baseStart_8264359 baseEnd_8264359 := by
    simpa [prefixWord, tailWord_8264359, baseEnd_8264359] using wordTrace_append hprefix tailTrace_8264359
  have hstable : (prefixWord ++ tailWord_8264359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264359).length < 2 ^ (prefixWord ++ tailWord_8264359).sum := by decide
  have hdescent : baseEnd_8264359 < baseStart_8264359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264419 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 1, 4, 2]
def baseStart_8264419 : Nat := 118140960795 + 8264419 * 2 ^ 59
def prefixEnd_8264419 : Nat := 4983230072969 + 3 ^ 40 * 8264419 * 2
def baseEnd_8264419 : Nat := 4243619277150006156355135

theorem tailTrace_8264419 : CollatzResearch.WordTrace tailWord_8264419 prefixEnd_8264419 4243619277150006156355135 := by
  unfold tailWord_8264419
  simp only [CollatzResearch.WordTrace]
  refine ⟨301428124246428888239004311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200952082830952592159336207 301428124246428888239004311)
  ·
    refine ⟨452142186369643332358506467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301428124246428888239004311 452142186369643332358506467)
    ·
      refine ⟨678213279554464998537759701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452142186369643332358506467 678213279554464998537759701)
      ·
        refine ⟨15895623739557773403228743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 678213279554464998537759701 15895623739557773403228743)
        ·
          refine ⟨23843435609336660104843115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15895623739557773403228743 23843435609336660104843115)
          ·
            refine ⟨35765153414004990157264673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23843435609336660104843115 35765153414004990157264673)
            ·
              refine ⟨26823865060503742617948505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35765153414004990157264673 26823865060503742617948505)
              ·
                refine ⟨20117898795377806963461379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26823865060503742617948505 20117898795377806963461379)
                ·
                  refine ⟨30176848193066710445192069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20117898795377806963461379 30176848193066710445192069)
                  ·
                    refine ⟨5658159036200008208473513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30176848193066710445192069 5658159036200008208473513)
                    ·
                      refine ⟨4243619277150006156355135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658159036200008208473513 4243619277150006156355135)
                      ·
                        rfl

theorem cell23_8264419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_8264419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264419 prefixEnd_8264419 := by exact prefixLift 8264419
  have htrace : WordTrace (prefixWord ++ tailWord_8264419) baseStart_8264419 baseEnd_8264419 := by
    simpa [prefixWord, tailWord_8264419, baseEnd_8264419] using wordTrace_append hprefix tailTrace_8264419
  have hstable : (prefixWord ++ tailWord_8264419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264419).length < 2 ^ (prefixWord ++ tailWord_8264419).sum := by decide
  have hdescent : baseEnd_8264419 < baseStart_8264419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264442 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_8264442 : Nat := 118140960795 + 8264442 * 2 ^ 59
def prefixEnd_8264442 : Nat := 4983230072969 + 3 ^ 40 * 8264442 * 2
def baseEnd_8264442 : Nat := 471514565245006618485281

theorem tailTrace_8264442 : CollatzResearch.WordTrace tailWord_8264442 prefixEnd_8264442 471514565245006618485281 := by
  unfold tailWord_8264442
  simp only [CollatzResearch.WordTrace]
  refine ⟨75357240781336390791772895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200952642083563708778061053 75357240781336390791772895)
  ·
    refine ⟨113035861172004586187659343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75357240781336390791772895 113035861172004586187659343)
    ·
      refine ⟨169553791758006879281489015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113035861172004586187659343 169553791758006879281489015)
      ·
        refine ⟨254330687637010318922233523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169553791758006879281489015 254330687637010318922233523)
        ·
          refine ⟨381496031455515478383350285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254330687637010318922233523 381496031455515478383350285)
          ·
            refine ⟨143061011795818304393756357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381496031455515478383350285 143061011795818304393756357)
            ·
              refine ⟨26823939711715932073829317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143061011795818304393756357 26823939711715932073829317)
              ·
                refine ⟨5029488695946737263842997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26823939711715932073829317 5029488695946737263842997)
                ·
                  refine ⟨471514565245006618485281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5029488695946737263842997 471514565245006618485281)
                  ·
                    rfl

theorem cell23_8264442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_8264442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264442 prefixEnd_8264442 := by exact prefixLift 8264442
  have htrace : WordTrace (prefixWord ++ tailWord_8264442) baseStart_8264442 baseEnd_8264442 := by
    simpa [prefixWord, tailWord_8264442, baseEnd_8264442] using wordTrace_append hprefix tailTrace_8264442
  have hstable : (prefixWord ++ tailWord_8264442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264442).length < 2 ^ (prefixWord ++ tailWord_8264442).sum := by decide
  have hdescent : baseEnd_8264442 < baseStart_8264442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264452 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_8264452 : Nat := 118140960795 + 8264452 * 2 ^ 59
def prefixEnd_8264452 : Nat := 4983230072969 + 3 ^ 40 * 8264452 * 2
def baseEnd_8264452 : Nat := 4243636222011604527242483

theorem tailTrace_8264452 : CollatzResearch.WordTrace tailWord_8264452 prefixEnd_8264452 4243636222011604527242483 := by
  unfold tailWord_8264452
  simp only [CollatzResearch.WordTrace]
  refine ⟨150714663927654667437477805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200952885236872889916637073 150714663927654667437477805)
  ·
    refine ⟨56517998972870500289054177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150714663927654667437477805 56517998972870500289054177)
    ·
      refine ⟨42388499229652875216790633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56517998972870500289054177 42388499229652875216790633)
      ·
        refine ⟨31791374422239656412592975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42388499229652875216790633 31791374422239656412592975)
        ·
          refine ⟨47687061633359484618889463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31791374422239656412592975 47687061633359484618889463)
          ·
            refine ⟨71530592450039226928334195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47687061633359484618889463 71530592450039226928334195)
            ·
              refine ⟨107295888675058840392501293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71530592450039226928334195 107295888675058840392501293)
              ·
                refine ⟨40235958253147065147187985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107295888675058840392501293 40235958253147065147187985)
                ·
                  refine ⟨30176968689860298860390989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40235958253147065147187985 30176968689860298860390989)
                  ·
                    refine ⟨11316363258697612072646621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30176968689860298860390989 11316363258697612072646621)
                    ·
                      refine ⟨4243636222011604527242483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316363258697612072646621 4243636222011604527242483)
                      ·
                        rfl

theorem cell23_8264452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_8264452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264452 prefixEnd_8264452 := by exact prefixLift 8264452
  have htrace : WordTrace (prefixWord ++ tailWord_8264452) baseStart_8264452 baseEnd_8264452 := by
    simpa [prefixWord, tailWord_8264452, baseEnd_8264452] using wordTrace_append hprefix tailTrace_8264452
  have hstable : (prefixWord ++ tailWord_8264452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264452).length < 2 ^ (prefixWord ++ tailWord_8264452).sum := by decide
  have hdescent : baseEnd_8264452 < baseStart_8264452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264492 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_8264492 : Nat := 118140960795 + 8264492 * 2 ^ 59
def prefixEnd_8264492 : Nat := 4983230072969 + 3 ^ 40 * 8264492 * 2
def baseEnd_8264492 : Nat := 4243656761237784370742299

theorem tailTrace_8264492 : CollatzResearch.WordTrace tailWord_8264492 prefixEnd_8264492 4243656761237784370742299 := by
  unfold tailWord_8264492
  simp only [CollatzResearch.WordTrace]
  refine ⟨150715393387582210853205865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200953857850109614470941153 150715393387582210853205865)
  ·
    refine ⟨113036545040686658139904399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150715393387582210853205865 113036545040686658139904399)
    ·
      refine ⟨169554817561029987209856599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113036545040686658139904399 169554817561029987209856599)
      ·
        refine ⟨254332226341544980814784899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169554817561029987209856599 254332226341544980814784899)
        ·
          refine ⟨381498339512317471222177349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254332226341544980814784899 381498339512317471222177349)
          ·
            refine ⟨71530938658559525854158253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381498339512317471222177349 71530938658559525854158253)
            ·
              refine ⟨26824101996959822195309345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71530938658559525854158253 26824101996959822195309345)
              ·
                refine ⟨20118076497719866646482009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26824101996959822195309345 20118076497719866646482009)
                ·
                  refine ⟨15088557373289899984861507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20118076497719866646482009 15088557373289899984861507)
                  ·
                    refine ⟨22632836059934849977292261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15088557373289899984861507 22632836059934849977292261)
                    ·
                      refine ⟨4243656761237784370742299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22632836059934849977292261 4243656761237784370742299)
                      ·
                        rfl

theorem cell23_8264492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_8264492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264492 prefixEnd_8264492 := by exact prefixLift 8264492
  have htrace : WordTrace (prefixWord ++ tailWord_8264492) baseStart_8264492 baseEnd_8264492 := by
    simpa [prefixWord, tailWord_8264492, baseEnd_8264492] using wordTrace_append hprefix tailTrace_8264492
  have hstable : (prefixWord ++ tailWord_8264492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264492).length < 2 ^ (prefixWord ++ tailWord_8264492).sum := by decide
  have hdescent : baseEnd_8264492 < baseStart_8264492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264493 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 7]
def baseStart_8264493 : Nat := 118140960795 + 8264493 * 2 ^ 59
def prefixEnd_8264493 : Nat := 4983230072969 + 3 ^ 40 * 8264493 * 2
def baseEnd_8264493 : Nat := 471517474968715429647755

theorem tailTrace_8264493 : CollatzResearch.WordTrace tailWord_8264493 prefixEnd_8264493 471517474968715429647755 := by
  unfold tailWord_8264493
  simp only [CollatzResearch.WordTrace]
  refine ⟨301430823248160798877198133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200953882165440532584798755 301430823248160798877198133)
  ·
    refine ⟨28259139679515074894737325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301430823248160798877198133 28259139679515074894737325)
    ·
      refine ⟨10597177379818153085526497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28259139679515074894737325 10597177379818153085526497)
      ·
        refine ⟨7947883034863614814144873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10597177379818153085526497 7947883034863614814144873)
        ·
          refine ⟨5960912276147711110608655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7947883034863614814144873 5960912276147711110608655)
          ·
            refine ⟨8941368414221566665912983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960912276147711110608655 8941368414221566665912983)
            ·
              refine ⟨13412052621332349998869475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941368414221566665912983 13412052621332349998869475)
              ·
                refine ⟨20118078931998524998304213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13412052621332349998869475 20118078931998524998304213)
                ·
                  refine ⟨471517474968715429647755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20118078931998524998304213 471517474968715429647755)
                  ·
                    rfl

theorem cell23_8264493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_8264493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264493 prefixEnd_8264493 := by exact prefixLift 8264493
  have htrace : WordTrace (prefixWord ++ tailWord_8264493) baseStart_8264493 baseEnd_8264493 := by
    simpa [prefixWord, tailWord_8264493, baseEnd_8264493] using wordTrace_append hprefix tailTrace_8264493
  have hstable : (prefixWord ++ tailWord_8264493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264493).length < 2 ^ (prefixWord ++ tailWord_8264493).sum := by decide
  have hdescent : baseEnd_8264493 < baseStart_8264493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264562 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_8264562 : Nat := 118140960795 + 8264562 * 2 ^ 59
def prefixEnd_8264562 : Nat := 4983230072969 + 3 ^ 40 * 8264562 * 2
def baseEnd_8264562 : Nat := 1414564234961199698955659

theorem tailTrace_8264562 : CollatzResearch.WordTrace tailWord_8264562 prefixEnd_8264562 1414564234961199698955659 := by
  unfold tailWord_8264562
  simp only [CollatzResearch.WordTrace]
  refine ⟨75358334971227705915364985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200955559923273882440973293 75358334971227705915364985)
  ·
    refine ⟨56518751228420779436523739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75358334971227705915364985 56518751228420779436523739)
    ·
      refine ⟨84778126842631169154785609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56518751228420779436523739 84778126842631169154785609)
      ·
        refine ⟨63583595131973376866089207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84778126842631169154785609 63583595131973376866089207)
        ·
          refine ⟨95375392697960065299133811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63583595131973376866089207 95375392697960065299133811)
          ·
            refine ⟨143063089046940097948700717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95375392697960065299133811 143063089046940097948700717)
            ·
              refine ⟨53648658392602536730762769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143063089046940097948700717 53648658392602536730762769)
              ·
                refine ⟨40236493794451902548072077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53648658392602536730762769 40236493794451902548072077)
                ·
                  refine ⟨15088685172919463455527029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40236493794451902548072077 15088685172919463455527029)
                  ·
                    refine ⟨1414564234961199698955659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15088685172919463455527029 1414564234961199698955659)
                    ·
                      rfl

theorem cell23_8264562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_8264562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264562 prefixEnd_8264562 := by exact prefixLift 8264562
  have htrace : WordTrace (prefixWord ++ tailWord_8264562) baseStart_8264562 baseEnd_8264562 := by
    simpa [prefixWord, tailWord_8264562, baseEnd_8264562] using wordTrace_append hprefix tailTrace_8264562
  have hstable : (prefixWord ++ tailWord_8264562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264562).length < 2 ^ (prefixWord ++ tailWord_8264562).sum := by decide
  have hdescent : baseEnd_8264562 < baseStart_8264562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264586 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_8264586 : Nat := 118140960795 + 8264586 * 2 ^ 59
def prefixEnd_8264586 : Nat := 4983230072969 + 3 ^ 40 * 8264586 * 2
def baseEnd_8264586 : Nat := 4243705028419307002966867

theorem tailTrace_8264586 : CollatzResearch.WordTrace tailWord_8264586 prefixEnd_8264586 4243705028419307002966867 := by
  unfold tailWord_8264586
  simp only [CollatzResearch.WordTrace]
  refine ⟨75358553809205968940083403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200956143491215917173555741 75358553809205968940083403)
  ·
    refine ⟨113037830713808953410125105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75358553809205968940083403 113037830713808953410125105)
    ·
      refine ⟨84778373035356715057593829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113037830713808953410125105 84778373035356715057593829)
      ·
        refine ⟨15895944944129384073298843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84778373035356715057593829 15895944944129384073298843)
        ·
          refine ⟨23843917416194076109948265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15895944944129384073298843 23843917416194076109948265)
          ·
            refine ⟨17882938062145557082461199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23843917416194076109948265 17882938062145557082461199)
            ·
              refine ⟨26824407093218335623691799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882938062145557082461199 26824407093218335623691799)
              ·
                refine ⟨40236610639827503435537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26824407093218335623691799 40236610639827503435537699)
                ·
                  refine ⟨60354915959741255153306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40236610639827503435537699 60354915959741255153306549)
                  ·
                    refine ⟨5658273371225742670622489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60354915959741255153306549 5658273371225742670622489)
                    ·
                      refine ⟨4243705028419307002966867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658273371225742670622489 4243705028419307002966867)
                      ·
                        rfl

theorem cell23_8264586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_8264586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264586 prefixEnd_8264586 := by exact prefixLift 8264586
  have htrace : WordTrace (prefixWord ++ tailWord_8264586) baseStart_8264586 baseEnd_8264586 := by
    simpa [prefixWord, tailWord_8264586, baseEnd_8264586] using wordTrace_append hprefix tailTrace_8264586
  have hstable : (prefixWord ++ tailWord_8264586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264586).length < 2 ^ (prefixWord ++ tailWord_8264586).sum := by decide
  have hdescent : baseEnd_8264586 < baseStart_8264586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264599 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_8264599 : Nat := 118140960795 + 8264599 * 2 ^ 59
def prefixEnd_8264599 : Nat := 4983230072969 + 3 ^ 40 * 8264599 * 2
def baseEnd_8264599 : Nat := 4243711703667815452104307

theorem tailTrace_8264599 : CollatzResearch.WordTrace tailWord_8264599 prefixEnd_8264599 4243711703667815452104307 := by
  unfold tailWord_8264599
  simp only [CollatzResearch.WordTrace]
  refine ⟨301434689385776778980556851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200956459590517852653704567 301434689385776778980556851)
  ·
    refine ⟨452152034078665168470835277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301434689385776778980556851 452152034078665168470835277)
    ·
      refine ⟨169557012779499438176563229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452152034078665168470835277 169557012779499438176563229)
      ·
        refine ⟨63583879792312289316211211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169557012779499438176563229 63583879792312289316211211)
        ·
          refine ⟨95375819688468433974316817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63583879792312289316211211 95375819688468433974316817)
          ·
            refine ⟨71531864766351325480737613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95375819688468433974316817 71531864766351325480737613)
            ·
              refine ⟨26824449287381747055276605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71531864766351325480737613 26824449287381747055276605)
              ·
                refine ⟨10059168482768155145728727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26824449287381747055276605 10059168482768155145728727)
                ·
                  refine ⟨15088752724152232718593091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10059168482768155145728727 15088752724152232718593091)
                  ·
                    refine ⟨22633129086228349077889637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15088752724152232718593091 22633129086228349077889637)
                    ·
                      refine ⟨4243711703667815452104307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22633129086228349077889637 4243711703667815452104307)
                      ·
                        rfl

theorem cell23_8264599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_8264599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264599 prefixEnd_8264599 := by exact prefixLift 8264599
  have htrace : WordTrace (prefixWord ++ tailWord_8264599) baseStart_8264599 baseEnd_8264599 := by
    simpa [prefixWord, tailWord_8264599, baseEnd_8264599] using wordTrace_append hprefix tailTrace_8264599
  have hstable : (prefixWord ++ tailWord_8264599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264599).length < 2 ^ (prefixWord ++ tailWord_8264599).sum := by decide
  have hdescent : baseEnd_8264599 < baseStart_8264599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264612 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_8264612 : Nat := 118140960795 + 8264612 * 2 ^ 59
def prefixEnd_8264612 : Nat := 4983230072969 + 3 ^ 40 * 8264612 * 2
def baseEnd_8264612 : Nat := 4243718378916323901241747

theorem tailTrace_8264612 : CollatzResearch.WordTrace tailWord_8264612 prefixEnd_8264612 4243718378916323901241747 := by
  unfold tailWord_8264612
  simp only [CollatzResearch.WordTrace]
  refine ⟨150717581767364841100390045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200956775689819788133853393 150717581767364841100390045)
  ·
    refine ⟨56519093162761815412646267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150717581767364841100390045 56519093162761815412646267)
    ·
      refine ⟨84778639744142723118969401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56519093162761815412646267 84778639744142723118969401)
      ·
        refine ⟨63583979808107042339227051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84778639744142723118969401 63583979808107042339227051)
        ·
          refine ⟨95375969712160563508840577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63583979808107042339227051 95375969712160563508840577)
          ·
            refine ⟨71531977284120422631630433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95375969712160563508840577 71531977284120422631630433)
            ·
              refine ⟨53648982963090316973722825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71531977284120422631630433 53648982963090316973722825)
              ·
                refine ⟨40236737222317737730292119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53648982963090316973722825 40236737222317737730292119)
                ·
                  refine ⟨60355105833476606595438179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40236737222317737730292119 60355105833476606595438179)
                  ·
                    refine ⟨90532658750214909893157269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60355105833476606595438179 90532658750214909893157269)
                    ·
                      refine ⟨4243718378916323901241747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90532658750214909893157269 4243718378916323901241747)
                      ·
                        rfl

theorem cell23_8264612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_8264612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264612 prefixEnd_8264612 := by exact prefixLift 8264612
  have htrace : WordTrace (prefixWord ++ tailWord_8264612) baseStart_8264612 baseEnd_8264612 := by
    simpa [prefixWord, tailWord_8264612, baseEnd_8264612] using wordTrace_append hprefix tailTrace_8264612
  have hstable : (prefixWord ++ tailWord_8264612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264612).length < 2 ^ (prefixWord ++ tailWord_8264612).sum := by decide
  have hdescent : baseEnd_8264612 < baseStart_8264612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264644 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_8264644 : Nat := 118140960795 + 8264644 * 2 ^ 59
def prefixEnd_8264644 : Nat := 4983230072969 + 3 ^ 40 * 8264644 * 2
def baseEnd_8264644 : Nat := 4243734810297267776041601

theorem tailTrace_8264644 : CollatzResearch.WordTrace tailWord_8264644 prefixEnd_8264644 4243734810297267776041601 := by
  unfold tailWord_8264644
  simp only [CollatzResearch.WordTrace]
  refine ⟨150718165335306875832972493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200957553780409167777296657 150718165335306875832972493)
  ·
    refine ⟨56519312000740078437364685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150718165335306875832972493 56519312000740078437364685)
    ·
      refine ⟨21194742000277529414011757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56519312000740078437364685 21194742000277529414011757)
      ·
        refine ⟨7948028250104073530254409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21194742000277529414011757 7948028250104073530254409)
        ·
          refine ⟨5961021187578055147690807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7948028250104073530254409 5961021187578055147690807)
          ·
            refine ⟨8941531781367082721536211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961021187578055147690807 8941531781367082721536211)
            ·
              refine ⟨13412297672050624082304317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941531781367082721536211 13412297672050624082304317)
              ·
                refine ⟨5029611627018984030864119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13412297672050624082304317 5029611627018984030864119)
                ·
                  refine ⟨7544417440528476046296179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029611627018984030864119 7544417440528476046296179)
                  ·
                    refine ⟨11316626160792714069444269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544417440528476046296179 11316626160792714069444269)
                    ·
                      refine ⟨4243734810297267776041601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316626160792714069444269 4243734810297267776041601)
                      ·
                        rfl

theorem cell23_8264644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_8264644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264644 prefixEnd_8264644 := by exact prefixLift 8264644
  have htrace : WordTrace (prefixWord ++ tailWord_8264644) baseStart_8264644 baseEnd_8264644 := by
    simpa [prefixWord, tailWord_8264644, baseEnd_8264644] using wordTrace_append hprefix tailTrace_8264644
  have hstable : (prefixWord ++ tailWord_8264644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264644).length < 2 ^ (prefixWord ++ tailWord_8264644).sum := by decide
  have hdescent : baseEnd_8264644 < baseStart_8264644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264666 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_8264666 : Nat := 118140960795 + 8264666 * 2 ^ 59
def prefixEnd_8264666 : Nat := 4983230072969 + 3 ^ 40 * 8264666 * 2
def baseEnd_8264666 : Nat := 4243746106871666689966499

theorem tailTrace_8264666 : CollatzResearch.WordTrace tailWord_8264666 prefixEnd_8264666 4243746106871666689966499 := by
  unfold tailWord_8264666
  simp only [CollatzResearch.WordTrace]
  refine ⟨75359283269133512355811463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200958088717689366282163901 75359283269133512355811463)
  ·
    refine ⟨113038924903700268533717195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75359283269133512355811463 113038924903700268533717195)
    ·
      refine ⟨169558387355550402800575793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113038924903700268533717195 169558387355550402800575793)
      ·
        refine ⟨127168790516662802100431845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169558387355550402800575793 127168790516662802100431845)
        ·
          refine ⟨23844148221874275393830971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127168790516662802100431845 23844148221874275393830971)
          ·
            refine ⟨35766222332811413090746457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23844148221874275393830971 35766222332811413090746457)
            ·
              refine ⟨26824666749608559818059843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35766222332811413090746457 26824666749608559818059843)
              ·
                refine ⟨40237000124412839727089765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26824666749608559818059843 40237000124412839727089765)
                ·
                  refine ⟨7544437523327407448829331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40237000124412839727089765 7544437523327407448829331)
                  ·
                    refine ⟨11316656284991111173243997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544437523327407448829331 11316656284991111173243997)
                    ·
                      refine ⟨4243746106871666689966499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316656284991111173243997 4243746106871666689966499)
                      ·
                        rfl

theorem cell23_8264666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_8264666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264666 prefixEnd_8264666 := by exact prefixLift 8264666
  have htrace : WordTrace (prefixWord ++ tailWord_8264666) baseStart_8264666 baseEnd_8264666 := by
    simpa [prefixWord, tailWord_8264666, baseEnd_8264666] using wordTrace_append hprefix tailTrace_8264666
  have hstable : (prefixWord ++ tailWord_8264666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264666).length < 2 ^ (prefixWord ++ tailWord_8264666).sum := by decide
  have hdescent : baseEnd_8264666 < baseStart_8264666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264677 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_8264677 : Nat := 118140960795 + 8264677 * 2 ^ 59
def prefixEnd_8264677 : Nat := 4983230072969 + 3 ^ 40 * 8264677 * 2
def baseEnd_8264677 : Nat := 1414583918386288715642983

theorem tailTrace_8264677 : CollatzResearch.WordTrace tailWord_8264677 prefixEnd_8264677 1414583918386288715642983 := by
  unfold tailWord_8264677
  simp only [CollatzResearch.WordTrace]
  refine ⟨301437534279494198301896285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200958356186329465534597523 301437534279494198301896285)
  ·
    refine ⟨113039075354810324363211107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301437534279494198301896285 113039075354810324363211107)
    ·
      refine ⟨169558613032215486544816661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113039075354810324363211107 169558613032215486544816661)
      ·
        refine ⟨7948059985885100931788281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169558613032215486544816661 7948059985885100931788281)
        ·
          refine ⟨5961044989413825698841211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7948059985885100931788281 5961044989413825698841211)
          ·
            refine ⟨8941567484120738548261817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961044989413825698841211 8941567484120738548261817)
            ·
              refine ⟨6706175613090553911196363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8941567484120738548261817 6706175613090553911196363)
              ·
                refine ⟨10059263419635830866794545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706175613090553911196363 10059263419635830866794545)
                ·
                  refine ⟨7544447564726873150095909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10059263419635830866794545 7544447564726873150095909)
                  ·
                    refine ⟨1414583918386288715642983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7544447564726873150095909 1414583918386288715642983)
                    ·
                      rfl

theorem cell23_8264677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_8264677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264677 prefixEnd_8264677 := by exact prefixLift 8264677
  have htrace : WordTrace (prefixWord ++ tailWord_8264677) baseStart_8264677 baseEnd_8264677 := by
    simpa [prefixWord, tailWord_8264677, baseEnd_8264677] using wordTrace_append hprefix tailTrace_8264677
  have hstable : (prefixWord ++ tailWord_8264677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264677).length < 2 ^ (prefixWord ++ tailWord_8264677).sum := by decide
  have hdescent : baseEnd_8264677 < baseStart_8264677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264739 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 3]
def baseStart_8264739 : Nat := 118140960795 + 8264739 * 2 ^ 59
def prefixEnd_8264739 : Nat := 4983230072969 + 3 ^ 40 * 8264739 * 2
def baseEnd_8264739 : Nat := 4243783590959444904353663

theorem tailTrace_8264739 : CollatzResearch.WordTrace tailWord_8264739 prefixEnd_8264739 4243783590959444904353663 := by
  unfold tailWord_8264739
  simp only [CollatzResearch.WordTrace]
  refine ⟨301439795605269582890653271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200959863736846388593768847 301439795605269582890653271)
  ·
    refine ⟨452159693407904374335979907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301439795605269582890653271 452159693407904374335979907)
    ·
      refine ⟨678239540111856561503969861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452159693407904374335979907 678239540111856561503969861)
      ·
        refine ⟨127169913770973105281994349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678239540111856561503969861 127169913770973105281994349)
        ·
          refine ⟨47688717664114914480747881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127169913770973105281994349 47688717664114914480747881)
          ·
            refine ⟨35766538248086185860560911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47688717664114914480747881 35766538248086185860560911)
            ·
              refine ⟨53649807372129278790841367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35766538248086185860560911 53649807372129278790841367)
              ·
                refine ⟨80474711058193918186262051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53649807372129278790841367 80474711058193918186262051)
                ·
                  refine ⟨120712066587290877279393077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80474711058193918186262051 120712066587290877279393077)
                  ·
                    refine ⟨11316756242558519744943101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120712066587290877279393077 11316756242558519744943101)
                    ·
                      refine ⟨4243783590959444904353663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316756242558519744943101 4243783590959444904353663)
                      ·
                        rfl

theorem cell23_8264739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_8264739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264739 prefixEnd_8264739 := by exact prefixLift 8264739
  have htrace : WordTrace (prefixWord ++ tailWord_8264739) baseStart_8264739 baseEnd_8264739 := by
    simpa [prefixWord, tailWord_8264739, baseEnd_8264739] using wordTrace_append hprefix tailTrace_8264739
  have hstable : (prefixWord ++ tailWord_8264739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264739).length < 2 ^ (prefixWord ++ tailWord_8264739).sum := by decide
  have hdescent : baseEnd_8264739 < baseStart_8264739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264740 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_8264740 : Nat := 118140960795 + 8264740 * 2 ^ 59
def prefixEnd_8264740 : Nat := 4983230072969 + 3 ^ 40 * 8264740 * 2
def baseEnd_8264740 : Nat := 4243784104440099400441159

theorem tailTrace_8264740 : CollatzResearch.WordTrace tailWord_8264740 prefixEnd_8264740 4243784104440099400441159 := by
  unfold tailWord_8264740
  simp only [CollatzResearch.WordTrace]
  refine ⟨150719916039132980030719837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200959888052177306707626449 150719916039132980030719837)
  ·
    refine ⟨56519968514674867511519939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150719916039132980030719837 56519968514674867511519939)
    ·
      refine ⟨84779952772012301267279909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56519968514674867511519939 84779952772012301267279909)
      ·
        refine ⟨15896241144752306487614983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84779952772012301267279909 15896241144752306487614983)
        ·
          refine ⟨23844361717128459731422475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15896241144752306487614983 23844361717128459731422475)
          ·
            refine ⟨35766542575692689597133713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23844361717128459731422475 35766542575692689597133713)
            ·
              refine ⟨26824906931769517197850285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35766542575692689597133713 26824906931769517197850285)
              ·
                refine ⟨10059340099413568949193857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26824906931769517197850285 10059340099413568949193857)
                ·
                  refine ⟨7544505074560176711895393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10059340099413568949193857 7544505074560176711895393)
                  ·
                    refine ⟨5658378805920132533921545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7544505074560176711895393 5658378805920132533921545)
                    ·
                      refine ⟨4243784104440099400441159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658378805920132533921545 4243784104440099400441159)
                      ·
                        rfl

theorem cell23_8264740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_8264740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264740 prefixEnd_8264740 := by exact prefixLift 8264740
  have htrace : WordTrace (prefixWord ++ tailWord_8264740) baseStart_8264740 baseEnd_8264740 := by
    simpa [prefixWord, tailWord_8264740, baseEnd_8264740] using wordTrace_append hprefix tailTrace_8264740
  have hstable : (prefixWord ++ tailWord_8264740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264740).length < 2 ^ (prefixWord ++ tailWord_8264740).sum := by decide
  have hdescent : baseEnd_8264740 < baseStart_8264740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264746 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_8264746 : Nat := 118140960795 + 8264746 * 2 ^ 59
def prefixEnd_8264746 : Nat := 4983230072969 + 3 ^ 40 * 8264746 * 2
def baseEnd_8264746 : Nat := 471531909480447375218459

theorem tailTrace_8264746 : CollatzResearch.WordTrace tailWord_8264746 prefixEnd_8264746 471531909480447375218459 := by
  unfold tailWord_8264746
  simp only [CollatzResearch.WordTrace]
  refine ⟨75360012729061055771539523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200960033944162815390772061 75360012729061055771539523)
  ·
    refine ⟨113040019093591583657309285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75360012729061055771539523 113040019093591583657309285)
    ·
      refine ⟨21195003580048421935745491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113040019093591583657309285 21195003580048421935745491)
      ·
        refine ⟨31792505370072632903618237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21195003580048421935745491 31792505370072632903618237)
        ·
          refine ⟨11922189513777237338856839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31792505370072632903618237 11922189513777237338856839)
          ·
            refine ⟨17883284270665856008285259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11922189513777237338856839 17883284270665856008285259)
            ·
              refine ⟨26824926405998784012427889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17883284270665856008285259 26824926405998784012427889)
              ·
                refine ⟨20118694804499088009320917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26824926405998784012427889 20118694804499088009320917)
                ·
                  refine ⟨471531909480447375218459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20118694804499088009320917 471531909480447375218459)
                  ·
                    rfl

theorem cell23_8264746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_8264746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264746 prefixEnd_8264746 := by exact prefixLift 8264746
  have htrace : WordTrace (prefixWord ++ tailWord_8264746) baseStart_8264746 baseEnd_8264746 := by
    simpa [prefixWord, tailWord_8264746, baseEnd_8264746] using wordTrace_append hprefix tailTrace_8264746
  have hstable : (prefixWord ++ tailWord_8264746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264746).length < 2 ^ (prefixWord ++ tailWord_8264746).sum := by decide
  have hdescent : baseEnd_8264746 < baseStart_8264746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264774 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_8264774 : Nat := 118140960795 + 8264774 * 2 ^ 59
def prefixEnd_8264774 : Nat := 4983230072969 + 3 ^ 40 * 8264774 * 2
def baseEnd_8264774 : Nat := 4243801562782352267416003

theorem tailTrace_8264774 : CollatzResearch.WordTrace tailWord_8264774 prefixEnd_8264774 4243801562782352267416003 := by
  unfold tailWord_8264774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420033505004461995880543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200960714773428522578784917 9420033505004461995880543)
  ·
    refine ⟨14130050257506692993820815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9420033505004461995880543 14130050257506692993820815)
    ·
      refine ⟨21195075386260039490731223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14130050257506692993820815 21195075386260039490731223)
      ·
        refine ⟨31792613079390059236096835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21195075386260039490731223 31792613079390059236096835)
        ·
          refine ⟨47688919619085088854145253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31792613079390059236096835 47688919619085088854145253)
          ·
            refine ⟨8941672428578454160152235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47688919619085088854145253 8941672428578454160152235)
            ·
              refine ⟨13412508642867681240228353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941672428578454160152235 13412508642867681240228353)
              ·
                refine ⟨10059381482150760930171265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13412508642867681240228353 10059381482150760930171265)
                ·
                  refine ⟨7544536111613070697628449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10059381482150760930171265 7544536111613070697628449)
                  ·
                    refine ⟨5658402083709803023221337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7544536111613070697628449 5658402083709803023221337)
                    ·
                      refine ⟨4243801562782352267416003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658402083709803023221337 4243801562782352267416003)
                      ·
                        rfl

theorem cell23_8264774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_8264774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264774 prefixEnd_8264774 := by exact prefixLift 8264774
  have htrace : WordTrace (prefixWord ++ tailWord_8264774) baseStart_8264774 baseEnd_8264774 := by
    simpa [prefixWord, tailWord_8264774, baseEnd_8264774] using wordTrace_append hprefix tailTrace_8264774
  have hstable : (prefixWord ++ tailWord_8264774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264774).length < 2 ^ (prefixWord ++ tailWord_8264774).sum := by decide
  have hdescent : baseEnd_8264774 < baseStart_8264774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264799 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_8264799 : Nat := 118140960795 + 8264799 * 2 ^ 59
def prefixEnd_8264799 : Nat := 4983230072969 + 3 ^ 40 * 8264799 * 2
def baseEnd_8264799 : Nat := 4243814399798714669603387

theorem tailTrace_8264799 : CollatzResearch.WordTrace tailWord_8264799 prefixEnd_8264799 4243814399798714669603387 := by
  unfold tailWord_8264799
  simp only [CollatzResearch.WordTrace]
  refine ⟨301441983985052213137837451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200961322656701475425224967 301441983985052213137837451)
  ·
    refine ⟨452162975977578319706756177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301441983985052213137837451 452162975977578319706756177)
    ·
      refine ⟨339122231983183739780067133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452162975977578319706756177 339122231983183739780067133)
      ·
        refine ⟨127170836993693902417525175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339122231983183739780067133 127170836993693902417525175)
        ·
          refine ⟨190756255490540853626287763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127170836993693902417525175 190756255490540853626287763)
          ·
            refine ⟨286134383235811280439431645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190756255490540853626287763 286134383235811280439431645)
            ·
              refine ⟨107300393713429230164786867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286134383235811280439431645 107300393713429230164786867)
              ·
                refine ⟨160950590570143845247180301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107300393713429230164786867 160950590570143845247180301)
                ·
                  refine ⟨60356471463803941967692613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160950590570143845247180301 60356471463803941967692613)
                  ·
                    refine ⟨11316838399463239118942365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60356471463803941967692613 11316838399463239118942365)
                    ·
                      refine ⟨4243814399798714669603387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316838399463239118942365 4243814399798714669603387)
                      ·
                        rfl

theorem cell23_8264799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_8264799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264799 prefixEnd_8264799 := by exact prefixLift 8264799
  have htrace : WordTrace (prefixWord ++ tailWord_8264799) baseStart_8264799 baseEnd_8264799 := by
    simpa [prefixWord, tailWord_8264799, baseEnd_8264799] using wordTrace_append hprefix tailTrace_8264799
  have hstable : (prefixWord ++ tailWord_8264799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264799).length < 2 ^ (prefixWord ++ tailWord_8264799).sum := by decide
  have hdescent : baseEnd_8264799 < baseStart_8264799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264816 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_8264816 : Nat := 118140960795 + 8264816 * 2 ^ 59
def prefixEnd_8264816 : Nat := 4983230072969 + 3 ^ 40 * 8264816 * 2
def baseEnd_8264816 : Nat := 4243823128969841103090809

theorem tailTrace_8264816 : CollatzResearch.WordTrace tailWord_8264816 prefixEnd_8264816 4243823128969841103090809 := by
  unfold tailWord_8264816
  simp only [CollatzResearch.WordTrace]
  refine ⟨150721302012995312520603151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200961736017327083360804201 150721302012995312520603151)
  ·
    refine ⟨226081953019492968780904727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150721302012995312520603151 226081953019492968780904727)
    ·
      refine ⟨339122929529239453171357091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226081953019492968780904727 339122929529239453171357091)
      ·
        refine ⟨508684394293859179757035637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339122929529239453171357091 508684394293859179757035637)
        ·
          refine ⟨47689161965049298102222091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 508684394293859179757035637 47689161965049298102222091)
          ·
            refine ⟨71533742947573947153333137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47689161965049298102222091 71533742947573947153333137)
            ·
              refine ⟨53650307210680460364999853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71533742947573947153333137 53650307210680460364999853)
              ·
                refine ⟨20118865204005172636874945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53650307210680460364999853 20118865204005172636874945)
                ·
                  refine ⟨15089148903003879477656209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20118865204005172636874945 15089148903003879477656209)
                  ·
                    refine ⟨11316861677252909608242157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15089148903003879477656209 11316861677252909608242157)
                    ·
                      refine ⟨4243823128969841103090809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316861677252909608242157 4243823128969841103090809)
                      ·
                        rfl

theorem cell23_8264816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_8264816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264816 prefixEnd_8264816 := by exact prefixLift 8264816
  have htrace : WordTrace (prefixWord ++ tailWord_8264816) baseStart_8264816 baseEnd_8264816 := by
    simpa [prefixWord, tailWord_8264816, baseEnd_8264816] using wordTrace_append hprefix tailTrace_8264816
  have hstable : (prefixWord ++ tailWord_8264816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264816).length < 2 ^ (prefixWord ++ tailWord_8264816).sum := by decide
  have hdescent : baseEnd_8264816 < baseStart_8264816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264833 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_8264833 : Nat := 118140960795 + 8264833 * 2 ^ 59
def prefixEnd_8264833 : Nat := 4983230072969 + 3 ^ 40 * 8264833 * 2
def baseEnd_8264833 : Nat := 4243831858140967536578231

theorem tailTrace_8264833 : CollatzResearch.WordTrace tailWord_8264833 prefixEnd_8264833 4243831858140967536578231 := by
  unfold tailWord_8264833
  simp only [CollatzResearch.WordTrace]
  refine ⟨301443224066929036944575153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200962149377952691296383435 301443224066929036944575153)
  ·
    refine ⟨226082418050196777708431365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301443224066929036944575153 226082418050196777708431365)
    ·
      refine ⟨42390453384411895820330881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226082418050196777708431365 42390453384411895820330881)
      ·
        refine ⟨31792840038308921865248161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42390453384411895820330881 31792840038308921865248161)
        ·
          refine ⟨23844630028731691398936121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31792840038308921865248161 23844630028731691398936121)
          ·
            refine ⟨17883472521548768549202091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23844630028731691398936121 17883472521548768549202091)
            ·
              refine ⟨26825208782323152823803137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17883472521548768549202091 26825208782323152823803137)
              ·
                refine ⟨20118906586742364617852353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26825208782323152823803137 20118906586742364617852353)
                ·
                  refine ⟨15089179940056773463389265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20118906586742364617852353 15089179940056773463389265)
                  ·
                    refine ⟨11316884955042580097541949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15089179940056773463389265 11316884955042580097541949)
                    ·
                      refine ⟨4243831858140967536578231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11316884955042580097541949 4243831858140967536578231)
                      ·
                        rfl

theorem cell23_8264833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_8264833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264833 prefixEnd_8264833 := by exact prefixLift 8264833
  have htrace : WordTrace (prefixWord ++ tailWord_8264833) baseStart_8264833 baseEnd_8264833 := by
    simpa [prefixWord, tailWord_8264833, baseEnd_8264833] using wordTrace_append hprefix tailTrace_8264833
  have hstable : (prefixWord ++ tailWord_8264833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264833).length < 2 ^ (prefixWord ++ tailWord_8264833).sum := by decide
  have hdescent : baseEnd_8264833 < baseStart_8264833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264840 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 3, 4]
def baseStart_8264840 : Nat := 118140960795 + 8264840 * 2 ^ 59
def prefixEnd_8264840 : Nat := 4983230072969 + 3 ^ 40 * 8264840 * 2
def baseEnd_8264840 : Nat := 1414611817501849669730233

theorem tailTrace_8264840 : CollatzResearch.WordTrace tailWord_8264840 prefixEnd_8264840 1414611817501849669730233 := by
  unfold tailWord_8264840
  simp only [CollatzResearch.WordTrace]
  refine ⟨150721739688951838570039987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200962319585269118093386649 150721739688951838570039987)
  ·
    refine ⟨226082609533427757855059981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150721739688951838570039987 226082609533427757855059981)
    ·
      refine ⟨84780978575035409195647493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226082609533427757855059981 84780978575035409195647493)
      ·
        refine ⟨15896433482819139224183905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84780978575035409195647493 15896433482819139224183905)
        ·
          refine ⟨11922325112114354418137929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15896433482819139224183905 11922325112114354418137929)
          ·
            refine ⟨8941743834085765813603447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11922325112114354418137929 8941743834085765813603447)
            ·
              refine ⟨13412615751128648720405171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941743834085765813603447 13412615751128648720405171)
              ·
                refine ⟨20118923626692973080607757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13412615751128648720405171 20118923626692973080607757)
                ·
                  refine ⟨7544596360009864905227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20118923626692973080607757 7544596360009864905227909)
                  ·
                    refine ⟨1414611817501849669730233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7544596360009864905227909 1414611817501849669730233)
                    ·
                      rfl

theorem cell23_8264840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_8264840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264840 prefixEnd_8264840 := by exact prefixLift 8264840
  have htrace : WordTrace (prefixWord ++ tailWord_8264840) baseStart_8264840 baseEnd_8264840 := by
    simpa [prefixWord, tailWord_8264840, baseEnd_8264840] using wordTrace_append hprefix tailTrace_8264840
  have hstable : (prefixWord ++ tailWord_8264840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264840).length < 2 ^ (prefixWord ++ tailWord_8264840).sum := by decide
  have hdescent : baseEnd_8264840 < baseStart_8264840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264879 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 3, 6]
def baseStart_8264879 : Nat := 118140960795 + 8264879 * 2 ^ 59
def prefixEnd_8264879 : Nat := 4983230072969 + 3 ^ 40 * 8264879 * 2
def baseEnd_8264879 : Nat := 1414618492750358118867673

theorem tailTrace_8264879 : CollatzResearch.WordTrace tailWord_8264879 prefixEnd_8264879 1414618492750358118867673 := by
  unfold tailWord_8264879
  simp only [CollatzResearch.WordTrace]
  refine ⟨301444901824762386800749691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200963267883174924533833127 301444901824762386800749691)
  ·
    refine ⟨452167352737143580201124537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301444901824762386800749691 452167352737143580201124537)
    ·
      refine ⟨339125514552857685150843403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452167352737143580201124537 339125514552857685150843403)
      ·
        refine ⟨508688271829286527726265105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339125514552857685150843403 508688271829286527726265105)
        ·
          refine ⟨381516203871964895794698829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508688271829286527726265105 381516203871964895794698829)
          ·
            refine ⟨143068576451986835923012061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381516203871964895794698829 143068576451986835923012061)
            ·
              refine ⟨53650716169495063471129523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143068576451986835923012061 53650716169495063471129523)
              ·
                refine ⟨80476074254242595206694285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53650716169495063471129523 80476074254242595206694285)
                ·
                  refine ⟨30178527845340973202510357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80476074254242595206694285 30178527845340973202510357)
                  ·
                    refine ⟨1414618492750358118867673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30178527845340973202510357 1414618492750358118867673)
                    ·
                      rfl

theorem cell23_8264879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_8264879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264879 prefixEnd_8264879 := by exact prefixLift 8264879
  have htrace : WordTrace (prefixWord ++ tailWord_8264879) baseStart_8264879 baseEnd_8264879 := by
    simpa [prefixWord, tailWord_8264879, baseEnd_8264879] using wordTrace_append hprefix tailTrace_8264879
  have hstable : (prefixWord ++ tailWord_8264879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264879).length < 2 ^ (prefixWord ++ tailWord_8264879).sum := by decide
  have hdescent : baseEnd_8264879 < baseStart_8264879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264899 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6]
def baseStart_8264899 : Nat := 118140960795 + 8264899 * 2 ^ 59
def prefixEnd_8264899 : Nat := 4983230072969 + 3 ^ 40 * 8264899 * 2
def baseEnd_8264899 : Nat := 4243865747864164278352927

theorem tailTrace_8264899 : CollatzResearch.WordTrace tailWord_8264899 prefixEnd_8264899 4243865747864164278352927 := by
  unfold tailWord_8264899
  simp only [CollatzResearch.WordTrace]
  refine ⟨301445631284689930216477751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200963754189793286810985167 301445631284689930216477751)
  ·
    refine ⟨452168446927034895324716627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301445631284689930216477751 452168446927034895324716627)
    ·
      refine ⟨678252670390552342987074941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452168446927034895324716627 678252670390552342987074941)
      ·
        refine ⟨254344751396457128620153103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678252670390552342987074941 254344751396457128620153103)
        ·
          refine ⟨381517127094685692930229655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254344751396457128620153103 381517127094685692930229655)
          ·
            refine ⟨572275690642028539395344483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381517127094685692930229655 572275690642028539395344483)
            ·
              refine ⟨858413535963042809093016725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572275690642028539395344483 858413535963042809093016725)
              ·
                refine ⟨40238134498267631676235159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858413535963042809093016725 40238134498267631676235159)
                ·
                  refine ⟨60357201747401447514352739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40238134498267631676235159 60357201747401447514352739)
                  ·
                    refine ⟨90535802621102171271529109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60357201747401447514352739 90535802621102171271529109)
                    ·
                      refine ⟨4243865747864164278352927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90535802621102171271529109 4243865747864164278352927)
                      ·
                        rfl

theorem cell23_8264899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_8264899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264899 prefixEnd_8264899 := by exact prefixLift 8264899
  have htrace : WordTrace (prefixWord ++ tailWord_8264899) baseStart_8264899 baseEnd_8264899 := by
    simpa [prefixWord, tailWord_8264899, baseEnd_8264899] using wordTrace_append hprefix tailTrace_8264899
  have hstable : (prefixWord ++ tailWord_8264899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264899).length < 2 ^ (prefixWord ++ tailWord_8264899).sum := by decide
  have hdescent : baseEnd_8264899 < baseStart_8264899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264903 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_8264903 : Nat := 118140960795 + 8264903 * 2 ^ 59
def prefixEnd_8264903 : Nat := 4983230072969 + 3 ^ 40 * 8264903 * 2
def baseEnd_8264903 : Nat := 4243867801786782262702909

theorem tailTrace_8264903 : CollatzResearch.WordTrace tailWord_8264903 prefixEnd_8264903 4243867801786782262702909 := by
  unfold tailWord_8264903
  simp only [CollatzResearch.WordTrace]
  refine ⟨301445777176675438899623363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200963851451116959266415575 301445777176675438899623363)
  ·
    refine ⟨452168665765013158349435045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301445777176675438899623363 452168665765013158349435045)
    ·
      refine ⟨84781624830939967190519071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452168665765013158349435045 84781624830939967190519071)
      ·
        refine ⟨127172437246409950785778607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84781624830939967190519071 127172437246409950785778607)
        ·
          refine ⟨190758655869614926178667911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127172437246409950785778607 190758655869614926178667911)
          ·
            refine ⟨286137983804422389268001867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190758655869614926178667911 286137983804422389268001867)
            ·
              refine ⟨429206975706633583902002801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286137983804422389268001867 429206975706633583902002801)
              ·
                refine ⟨321905231779975187926502101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429206975706633583902002801 321905231779975187926502101)
                ·
                  refine ⟨7544653869843168467027393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 321905231779975187926502101 7544653869843168467027393)
                  ·
                    refine ⟨5658490402382376350270545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7544653869843168467027393 5658490402382376350270545)
                    ·
                      refine ⟨4243867801786782262702909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658490402382376350270545 4243867801786782262702909)
                      ·
                        rfl

theorem cell23_8264903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_8264903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264903 prefixEnd_8264903 := by exact prefixLift 8264903
  have htrace : WordTrace (prefixWord ++ tailWord_8264903) baseStart_8264903 baseEnd_8264903 := by
    simpa [prefixWord, tailWord_8264903, baseEnd_8264903] using wordTrace_append hprefix tailTrace_8264903
  have hstable : (prefixWord ++ tailWord_8264903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264903).length < 2 ^ (prefixWord ++ tailWord_8264903).sum := by decide
  have hdescent : baseEnd_8264903 < baseStart_8264903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264940 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 3]
def baseStart_8264940 : Nat := 118140960795 + 8264940 * 2 ^ 59
def prefixEnd_8264940 : Nat := 4983230072969 + 3 ^ 40 * 8264940 * 2
def baseEnd_8264940 : Nat := 4243886800570998617940239

theorem tailTrace_8264940 : CollatzResearch.WordTrace tailWord_8264940 prefixEnd_8264940 4243886800570998617940239 := by
  unfold tailWord_8264940
  simp only [CollatzResearch.WordTrace]
  refine ⟨150723563338770697109360137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200964751118360929479146849 150723563338770697109360137)
  ·
    refine ⟨113042672504078022832020103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150723563338770697109360137 113042672504078022832020103)
    ·
      refine ⟨169564008756117034248030155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113042672504078022832020103 169564008756117034248030155)
      ·
        refine ⟨254346013134175551372045233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169564008756117034248030155 254346013134175551372045233)
        ·
          refine ⟨190759509850631663529033925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254346013134175551372045233 190759509850631663529033925)
          ·
            refine ⟨35767408096993436911693861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190759509850631663529033925 35767408096993436911693861)
            ·
              refine ⟨6706389018186269420942599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35767408096993436911693861 6706389018186269420942599)
              ·
                refine ⟨10059583527279404131413899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706389018186269420942599 10059583527279404131413899)
                ·
                  refine ⟨15089375290919106197120849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10059583527279404131413899 15089375290919106197120849)
                  ·
                    refine ⟨11317031468189329647840637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15089375290919106197120849 11317031468189329647840637)
                    ·
                      refine ⟨4243886800570998617940239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317031468189329647840637 4243886800570998617940239)
                      ·
                        rfl

theorem cell23_8264940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_8264940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264940 prefixEnd_8264940 := by exact prefixLift 8264940
  have htrace : WordTrace (prefixWord ++ tailWord_8264940) baseStart_8264940 baseEnd_8264940 := by
    simpa [prefixWord, tailWord_8264940, baseEnd_8264940] using wordTrace_append hprefix tailTrace_8264940
  have hstable : (prefixWord ++ tailWord_8264940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264940).length < 2 ^ (prefixWord ++ tailWord_8264940).sum := by decide
  have hdescent : baseEnd_8264940 < baseStart_8264940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264953 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 3]
def baseStart_8264953 : Nat := 118140960795 + 8264953 * 2 ^ 59
def prefixEnd_8264953 : Nat := 4983230072969 + 3 ^ 40 * 8264953 * 2
def baseEnd_8264953 : Nat := 4243893475819507067077679

theorem tailTrace_8264953 : CollatzResearch.WordTrace tailWord_8264953 prefixEnd_8264953 4243893475819507067077679 := by
  unfold tailWord_8264953
  simp only [CollatzResearch.WordTrace]
  refine ⟨301447600826494297438943513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200965067217662864959295675 301447600826494297438943513)
  ·
    refine ⟨226085700619870723079207635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301447600826494297438943513 226085700619870723079207635)
    ·
      refine ⟨339128550929806084618811453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226085700619870723079207635 339128550929806084618811453)
      ·
        refine ⟨127173206598677281732054295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339128550929806084618811453 127173206598677281732054295)
        ·
          refine ⟨190759809898015922598081443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127173206598677281732054295 190759809898015922598081443)
          ·
            refine ⟨286139714847023883897122165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190759809898015922598081443 286139714847023883897122165)
            ·
              refine ⟨26825598266908489115355203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286139714847023883897122165 26825598266908489115355203)
              ·
                refine ⟨40238397400362733673032805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26825598266908489115355203 40238397400362733673032805)
                ·
                  refine ⟨7544699512568012563693651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40238397400362733673032805 7544699512568012563693651)
                  ·
                    refine ⟨11317049268852018845540477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544699512568012563693651 11317049268852018845540477)
                    ·
                      refine ⟨4243893475819507067077679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317049268852018845540477 4243893475819507067077679)
                      ·
                        rfl

theorem cell23_8264953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_8264953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264953 prefixEnd_8264953 := by exact prefixLift 8264953
  have htrace : WordTrace (prefixWord ++ tailWord_8264953) baseStart_8264953 baseEnd_8264953 := by
    simpa [prefixWord, tailWord_8264953, baseEnd_8264953] using wordTrace_append hprefix tailTrace_8264953
  have hstable : (prefixWord ++ tailWord_8264953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264953).length < 2 ^ (prefixWord ++ tailWord_8264953).sum := by decide
  have hdescent : baseEnd_8264953 < baseStart_8264953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8264993 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_8264993 : Nat := 118140960795 + 8264993 * 2 ^ 59
def prefixEnd_8264993 : Nat := 4983230072969 + 3 ^ 40 * 8264993 * 2
def baseEnd_8264993 : Nat := 4243914015045686910577495

theorem tailTrace_8264993 : CollatzResearch.WordTrace tailWord_8264993 prefixEnd_8264993 4243914015045686910577495 := by
  unfold tailWord_8264993
  simp only [CollatzResearch.WordTrace]
  refine ⟨301449059746349384270399633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200966039830899589513599755 301449059746349384270399633)
  ·
    refine ⟨226086794809762038202799725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301449059746349384270399633 226086794809762038202799725)
    ·
      refine ⟨84782548053660764326049897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226086794809762038202799725 84782548053660764326049897)
      ·
        refine ⟨63586911040245573244537423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84782548053660764326049897 63586911040245573244537423)
        ·
          refine ⟨95380366560368359866806135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63586911040245573244537423 95380366560368359866806135)
          ·
            refine ⟨143070549840552539800209203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95380366560368359866806135 143070549840552539800209203)
            ·
              refine ⟨214605824760828809700313805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143070549840552539800209203 214605824760828809700313805)
              ·
                refine ⟨80477184285310803637617677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214605824760828809700313805 80477184285310803637617677)
                ·
                  refine ⟨30178944106991551364106629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80477184285310803637617677 30178944106991551364106629)
                  ·
                    refine ⟨5658552020060915880769993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30178944106991551364106629 5658552020060915880769993)
                    ·
                      refine ⟨4243914015045686910577495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658552020060915880769993 4243914015045686910577495)
                      ·
                        rfl

theorem cell23_8264993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_8264993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8264993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8264993 prefixEnd_8264993 := by exact prefixLift 8264993
  have htrace : WordTrace (prefixWord ++ tailWord_8264993) baseStart_8264993 baseEnd_8264993 := by
    simpa [prefixWord, tailWord_8264993, baseEnd_8264993] using wordTrace_append hprefix tailTrace_8264993
  have hstable : (prefixWord ++ tailWord_8264993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8264993).length < 2 ^ (prefixWord ++ tailWord_8264993).sum := by decide
  have hdescent : baseEnd_8264993 < baseStart_8264993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8264993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265021 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_8265021 : Nat := 118140960795 + 8265021 * 2 ^ 59
def prefixEnd_8265021 : Nat := 4983230072969 + 3 ^ 40 * 8265021 * 2
def baseEnd_8265021 : Nat := 4243928392504012801027367

theorem tailTrace_8265021 : CollatzResearch.WordTrace tailWord_8265021 prefixEnd_8265021 4243928392504012801027367 := by
  unfold tailWord_8265021
  simp only [CollatzResearch.WordTrace]
  refine ⟨301450080990247945052418917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200966720660165296701612611 301450080990247945052418917)
  ·
    refine ⟨56521890185671489697328547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301450080990247945052418917 56521890185671489697328547)
    ·
      refine ⟨84782835278507234545992821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56521890185671489697328547 84782835278507234545992821)
      ·
        refine ⟨7948390807360053238686827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84782835278507234545992821 7948390807360053238686827)
        ·
          refine ⟨11922586211040079858030241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7948390807360053238686827 11922586211040079858030241)
          ·
            refine ⟨8941939658280059893522681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11922586211040079858030241 8941939658280059893522681)
            ·
              refine ⟨6706454743710044920142011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8941939658280059893522681 6706454743710044920142011)
              ·
                refine ⟨10059682115565067380213017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706454743710044920142011 10059682115565067380213017)
                ·
                  refine ⟨7544761586673800535159763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10059682115565067380213017 7544761586673800535159763)
                  ·
                    refine ⟨11317142380010700802739645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7544761586673800535159763 11317142380010700802739645)
                    ·
                      refine ⟨4243928392504012801027367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317142380010700802739645 4243928392504012801027367)
                      ·
                        rfl

theorem cell23_8265021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_8265021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265021 prefixEnd_8265021 := by exact prefixLift 8265021
  have htrace : WordTrace (prefixWord ++ tailWord_8265021) baseStart_8265021 baseEnd_8265021 := by
    simpa [prefixWord, tailWord_8265021, baseEnd_8265021] using wordTrace_append hprefix tailTrace_8265021
  have hstable : (prefixWord ++ tailWord_8265021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265021).length < 2 ^ (prefixWord ++ tailWord_8265021).sum := by decide
  have hdescent : baseEnd_8265021 < baseStart_8265021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265093 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_8265093 : Nat := 118140960795 + 8265093 * 2 ^ 59
def prefixEnd_8265093 : Nat := 4983230072969 + 3 ^ 40 * 8265093 * 2
def baseEnd_8265093 : Nat := 1414655121037045506442345

theorem tailTrace_8265093 : CollatzResearch.WordTrace tailWord_8265093 prefixEnd_8265093 1414655121037045506442345 := by
  unfold tailWord_8265093
  simp only [CollatzResearch.WordTrace]
  refine ⟨301452707045987101349039933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200968471363991400899359955 301452707045987101349039933)
  ·
    refine ⟨113044765142245163005889975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301452707045987101349039933 113044765142245163005889975)
    ·
      refine ⟨169567147713367744508834963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113044765142245163005889975 169567147713367744508834963)
      ·
        refine ⟨254350721570051616763252445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169567147713367744508834963 254350721570051616763252445)
        ·
          refine ⟨95381520588769356286219667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254350721570051616763252445 95381520588769356286219667)
          ·
            refine ⟨143072280883154034429329501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95381520588769356286219667 143072280883154034429329501)
            ·
              refine ⟨53652105331182762910998563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143072280883154034429329501 53652105331182762910998563)
              ·
                refine ⟨80478157996774144366497845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53652105331182762910998563 80478157996774144366497845)
                ·
                  refine ⟨7544827312197576034359173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80478157996774144366497845 7544827312197576034359173)
                  ·
                    refine ⟨1414655121037045506442345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7544827312197576034359173 1414655121037045506442345)
                    ·
                      rfl

theorem cell23_8265093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_8265093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265093 prefixEnd_8265093 := by exact prefixLift 8265093
  have htrace : WordTrace (prefixWord ++ tailWord_8265093) baseStart_8265093 baseEnd_8265093 := by
    simpa [prefixWord, tailWord_8265093, baseEnd_8265093] using wordTrace_append hprefix tailTrace_8265093
  have hstable : (prefixWord ++ tailWord_8265093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265093).length < 2 ^ (prefixWord ++ tailWord_8265093).sum := by decide
  have hdescent : baseEnd_8265093 < baseStart_8265093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265097 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 2, 5]
def baseStart_8265097 : Nat := 118140960795 + 8265097 * 2 ^ 59
def prefixEnd_8265097 : Nat := 4983230072969 + 3 ^ 40 * 8265097 * 2
def baseEnd_8265097 : Nat := 1414655805677918167892339

theorem tailTrace_8265097 : CollatzResearch.WordTrace tailWord_8265097 prefixEnd_8265097 1414655805677918167892339 := by
  unfold tailWord_8265097
  simp only [CollatzResearch.WordTrace]
  refine ⟨301452852937972610032185545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200968568625315073354790363 301452852937972610032185545)
  ·
    refine ⟨226089639703479457524139159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301452852937972610032185545 226089639703479457524139159)
    ·
      refine ⟨339134459555219186286208739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226089639703479457524139159 339134459555219186286208739)
      ·
        refine ⟨508701689332828779429313109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339134459555219186286208739 508701689332828779429313109)
        ·
          refine ⟨5961347921869087258937263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 508701689332828779429313109 5961347921869087258937263)
          ·
            refine ⟨8942021882803630888405895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961347921869087258937263 8942021882803630888405895)
            ·
              refine ⟨13413032824205446332608843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942021882803630888405895 13413032824205446332608843)
              ·
                refine ⟨20119549236308169498913265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413032824205446332608843 20119549236308169498913265)
                ·
                  refine ⟨15089661927231127124184949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20119549236308169498913265 15089661927231127124184949)
                  ·
                    refine ⟨1414655805677918167892339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15089661927231127124184949 1414655805677918167892339)
                    ·
                      rfl

theorem cell23_8265097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 5].length) (baseStart_8265097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265097 prefixEnd_8265097 := by exact prefixLift 8265097
  have htrace : WordTrace (prefixWord ++ tailWord_8265097) baseStart_8265097 baseEnd_8265097 := by
    simpa [prefixWord, tailWord_8265097, baseEnd_8265097] using wordTrace_append hprefix tailTrace_8265097
  have hstable : (prefixWord ++ tailWord_8265097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265097).length < 2 ^ (prefixWord ++ tailWord_8265097).sum := by decide
  have hdescent : baseEnd_8265097 < baseStart_8265097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265127 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 1, 4]
def baseStart_8265127 : Nat := 118140960795 + 8265127 * 2 ^ 59
def prefixEnd_8265127 : Nat := 4983230072969 + 3 ^ 40 * 8265127 * 2
def baseEnd_8265127 : Nat := 1414660940484463128767293

theorem tailTrace_8265127 : CollatzResearch.WordTrace tailWord_8265127 prefixEnd_8265127 1414660940484463128767293 := by
  unfold tailWord_8265127
  simp only [CollatzResearch.WordTrace]
  refine ⟨301453947127863925155777635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200969298085242616770518423 301453947127863925155777635)
  ·
    refine ⟨452180920691795887733666453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301453947127863925155777635 452180920691795887733666453)
    ·
      refine ⟨21195980657427932237515615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 452180920691795887733666453 21195980657427932237515615)
      ·
        refine ⟨31793970986141898356273423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21195980657427932237515615 31793970986141898356273423)
        ·
          refine ⟨47690956479212847534410135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31793970986141898356273423 47690956479212847534410135)
          ·
            refine ⟨71536434718819271301615203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47690956479212847534410135 71536434718819271301615203)
            ·
              refine ⟨107304652078228906952422805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71536434718819271301615203 107304652078228906952422805)
              ·
                refine ⟨5029905566166980013394819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107304652078228906952422805 5029905566166980013394819)
                ·
                  refine ⟨7544858349250470020092229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5029905566166980013394819 7544858349250470020092229)
                  ·
                    refine ⟨1414660940484463128767293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7544858349250470020092229 1414660940484463128767293)
                    ·
                      rfl

theorem cell23_8265127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_8265127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265127 prefixEnd_8265127 := by exact prefixLift 8265127
  have htrace : WordTrace (prefixWord ++ tailWord_8265127) baseStart_8265127 baseEnd_8265127 := by
    simpa [prefixWord, tailWord_8265127, baseEnd_8265127] using wordTrace_append hprefix tailTrace_8265127
  have hstable : (prefixWord ++ tailWord_8265127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265127).length < 2 ^ (prefixWord ++ tailWord_8265127).sum := by decide
  have hdescent : baseEnd_8265127 < baseStart_8265127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265136 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_8265136 : Nat := 118140960795 + 8265136 * 2 ^ 59
def prefixEnd_8265136 : Nat := 4983230072969 + 3 ^ 40 * 8265136 * 2
def baseEnd_8265136 : Nat := 1414662480926426617029779

theorem tailTrace_8265136 : CollatzResearch.WordTrace tailWord_8265136 prefixEnd_8265136 1414662480926426617029779 := by
  unfold tailWord_8265136
  simp only [CollatzResearch.WordTrace]
  refine ⟨150727137692415659846427631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200969516923220879795236841 150727137692415659846427631)
  ·
    refine ⟨226090706538623489769641447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150727137692415659846427631 226090706538623489769641447)
    ·
      refine ⟨339136059807935234654462171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226090706538623489769641447 339136059807935234654462171)
      ·
        refine ⟨508704089711902851981693257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339136059807935234654462171 508704089711902851981693257)
        ·
          refine ⟨381528067283927138986269943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508704089711902851981693257 381528067283927138986269943)
          ·
            refine ⟨572292100925890708479404915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381528067283927138986269943 572292100925890708479404915)
            ·
              refine ⟨858438151388836062719107373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572292100925890708479404915 858438151388836062719107373)
              ·
                refine ⟨321914306770813523519665265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858438151388836062719107373 321914306770813523519665265)
                ·
                  refine ⟨241435730078110142639748949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321914306770813523519665265 241435730078110142639748949)
                  ·
                    refine ⟨1414662480926426617029779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241435730078110142639748949 1414662480926426617029779)
                    ·
                      rfl

theorem cell23_8265136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_8265136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265136 prefixEnd_8265136 := by exact prefixLift 8265136
  have htrace : WordTrace (prefixWord ++ tailWord_8265136) baseStart_8265136 baseEnd_8265136 := by
    simpa [prefixWord, tailWord_8265136, baseEnd_8265136] using wordTrace_append hprefix tailTrace_8265136
  have hstable : (prefixWord ++ tailWord_8265136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265136).length < 2 ^ (prefixWord ++ tailWord_8265136).sum := by decide
  have hdescent : baseEnd_8265136 < baseStart_8265136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265160 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_8265160 : Nat := 118140960795 + 8265160 * 2 ^ 59
def prefixEnd_8265160 : Nat := 4983230072969 + 3 ^ 40 * 8265160 * 2
def baseEnd_8265160 : Nat := 4243999766314987757189227

theorem tailTrace_8265160 : CollatzResearch.WordTrace tailWord_8265160 prefixEnd_8265160 4243999766314987757189227 := by
  unfold tailWord_8265160
  simp only [CollatzResearch.WordTrace]
  refine ⟨150727575368372185895864467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200970100491162914527819289 150727575368372185895864467)
  ·
    refine ⟨226091363052558278843796701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150727575368372185895864467 226091363052558278843796701)
    ·
      refine ⟨84784261144709354566423763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226091363052558278843796701 84784261144709354566423763)
      ·
        refine ⟨127176391717064031849635645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84784261144709354566423763 127176391717064031849635645)
        ·
          refine ⟨47691146893899011943613367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127176391717064031849635645 47691146893899011943613367)
          ·
            refine ⟨71536720340848517915420051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47691146893899011943613367 71536720340848517915420051)
            ·
              refine ⟨107305080511272776873130077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71536720340848517915420051 107305080511272776873130077)
              ·
                refine ⟨40239405191727291327423779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107305080511272776873130077 40239405191727291327423779)
                ·
                  refine ⟨60359107787590936991135669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40239405191727291327423779 60359107787590936991135669)
                  ·
                    refine ⟨5658666355086650342918969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60359107787590936991135669 5658666355086650342918969)
                    ·
                      refine ⟨4243999766314987757189227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658666355086650342918969 4243999766314987757189227)
                      ·
                        rfl

theorem cell23_8265160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_8265160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265160 prefixEnd_8265160 := by exact prefixLift 8265160
  have htrace : WordTrace (prefixWord ++ tailWord_8265160) baseStart_8265160 baseEnd_8265160 := by
    simpa [prefixWord, tailWord_8265160, baseEnd_8265160] using wordTrace_append hprefix tailTrace_8265160
  have hstable : (prefixWord ++ tailWord_8265160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265160).length < 2 ^ (prefixWord ++ tailWord_8265160).sum := by decide
  have hdescent : baseEnd_8265160 < baseStart_8265160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265177 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 2, 3, 2]
def baseStart_8265177 : Nat := 118140960795 + 8265177 * 2 ^ 59
def prefixEnd_8265177 : Nat := 4983230072969 + 3 ^ 40 * 8265177 * 2
def baseEnd_8265177 : Nat := 4244008495486114190676649

theorem tailTrace_8265177 : CollatzResearch.WordTrace tailWord_8265177 prefixEnd_8265177 4244008495486114190676649 := by
  unfold tailWord_8265177
  simp only [CollatzResearch.WordTrace]
  refine ⟨301455770777682783695097785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200970513851788522463398523 301455770777682783695097785)
  ·
    refine ⟨226091828083262087771323339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301455770777682783695097785 226091828083262087771323339)
    ·
      refine ⟨339137742124893131656985009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226091828083262087771323339 339137742124893131656985009)
      ·
        refine ⟨254353306593669848742738757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339137742124893131656985009 254353306593669848742738757)
        ·
          refine ⟨47691244986313096639263517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254353306593669848742738757 47691244986313096639263517)
          ·
            refine ⟨17884216869867411239723819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47691244986313096639263517 17884216869867411239723819)
            ·
              refine ⟨26826325304801116859585729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17884216869867411239723819 26826325304801116859585729)
              ·
                refine ⟨20119743978600837644689297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26826325304801116859585729 20119743978600837644689297)
                ·
                  refine ⟨15089807983950628233516973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20119743978600837644689297 15089807983950628233516973)
                  ·
                    refine ⟨5658677993981485587568865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15089807983950628233516973 5658677993981485587568865)
                    ·
                      refine ⟨4244008495486114190676649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658677993981485587568865 4244008495486114190676649)
                      ·
                        rfl

theorem cell23_8265177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_8265177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265177 prefixEnd_8265177 := by exact prefixLift 8265177
  have htrace : WordTrace (prefixWord ++ tailWord_8265177) baseStart_8265177 baseEnd_8265177 := by
    simpa [prefixWord, tailWord_8265177, baseEnd_8265177] using wordTrace_append hprefix tailTrace_8265177
  have hstable : (prefixWord ++ tailWord_8265177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265177).length < 2 ^ (prefixWord ++ tailWord_8265177).sum := by decide
  have hdescent : baseEnd_8265177 < baseStart_8265177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265210 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_8265210 : Nat := 118140960795 + 8265210 * 2 ^ 59
def prefixEnd_8265210 : Nat := 4983230072969 + 3 ^ 40 * 8265210 * 2
def baseEnd_8265210 : Nat := 4244025440347712561563997

theorem tailTrace_8265210 : CollatzResearch.WordTrace tailWord_8265210 prefixEnd_8265210 4244025440347712561563997 := by
  unfold tailWord_8265210
  simp only [CollatzResearch.WordTrace]
  refine ⟨75364243596640807582762271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200971316257708820220699389 75364243596640807582762271)
  ·
    refine ⟨113046365394961211374143407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75364243596640807582762271 113046365394961211374143407)
    ·
      refine ⟨169569548092441817061215111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113046365394961211374143407 169569548092441817061215111)
      ·
        refine ⟨254354322138662725591822667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169569548092441817061215111 254354322138662725591822667)
        ·
          refine ⟨381531483207994088387734001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254354322138662725591822667 381531483207994088387734001)
          ·
            refine ⟨286148612405995566290800501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381531483207994088387734001 286148612405995566290800501)
            ·
              refine ⟨26826432413062084339762547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286148612405995566290800501 26826432413062084339762547)
              ·
                refine ⟨40239648619593126509643821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26826432413062084339762547 40239648619593126509643821)
                ·
                  refine ⟨15089868232347422441116433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40239648619593126509643821 15089868232347422441116433)
                  ·
                    refine ⟨11317401174260566830837325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15089868232347422441116433 11317401174260566830837325)
                    ·
                      refine ⟨4244025440347712561563997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317401174260566830837325 4244025440347712561563997)
                      ·
                        rfl

theorem cell23_8265210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_8265210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265210 prefixEnd_8265210 := by exact prefixLift 8265210
  have htrace : WordTrace (prefixWord ++ tailWord_8265210) baseStart_8265210 baseEnd_8265210 := by
    simpa [prefixWord, tailWord_8265210, baseEnd_8265210] using wordTrace_append hprefix tailTrace_8265210
  have hstable : (prefixWord ++ tailWord_8265210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265210).length < 2 ^ (prefixWord ++ tailWord_8265210).sum := by decide
  have hdescent : baseEnd_8265210 < baseStart_8265210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265213 : List Nat := [1, 4, 1, 1, 1, 4, 2, 9]
def baseStart_8265213 : Nat := 118140960795 + 8265213 * 2 ^ 59
def prefixEnd_8265213 : Nat := 4983230072969 + 3 ^ 40 * 8265213 * 2
def baseEnd_8265213 : Nat := 157186184473691705549129

theorem tailTrace_8265213 : CollatzResearch.WordTrace tailWord_8265213 prefixEnd_8265213 157186184473691705549129 := by
  unfold tailWord_8265213
  simp only [CollatzResearch.WordTrace]
  refine ⟨301457083805552361843408293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200971389203701574562272195 301457083805552361843408293)
  ·
    refine ⟨56523203213541067845639055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301457083805552361843408293 56523203213541067845639055)
    ·
      refine ⟨84784804820311601768458583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56523203213541067845639055 84784804820311601768458583)
      ·
        refine ⟨127177207230467402652687875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84784804820311601768458583 127177207230467402652687875)
        ·
          refine ⟨190765810845701103979031813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127177207230467402652687875 190765810845701103979031813)
          ·
            refine ⟨35768589533568956996068465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190765810845701103979031813 35768589533568956996068465)
            ·
              refine ⟨26826442150176717747051349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35768589533568956996068465 26826442150176717747051349)
              ·
                refine ⟨157186184473691705549129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26826442150176717747051349 157186184473691705549129)
                ·
                  rfl

theorem cell23_8265213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 9].length) (baseStart_8265213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265213 prefixEnd_8265213 := by exact prefixLift 8265213
  have htrace : WordTrace (prefixWord ++ tailWord_8265213) baseStart_8265213 baseEnd_8265213 := by
    simpa [prefixWord, tailWord_8265213, baseEnd_8265213] using wordTrace_append hprefix tailTrace_8265213
  have hstable : (prefixWord ++ tailWord_8265213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265213).length < 2 ^ (prefixWord ++ tailWord_8265213).sum := by decide
  have hdescent : baseEnd_8265213 < baseStart_8265213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265227 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 5]
def baseStart_8265227 : Nat := 118140960795 + 8265227 * 2 ^ 59
def prefixEnd_8265227 : Nat := 4983230072969 + 3 ^ 40 * 8265227 * 2
def baseEnd_8265227 : Nat := 4244034169518838995051419

theorem tailTrace_8265227 : CollatzResearch.WordTrace tailWord_8265227 prefixEnd_8265227 4244034169518838995051419 := by
  unfold tailWord_8265227
  simp only [CollatzResearch.WordTrace]
  refine ⟨301457594427501642234417935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200971729618334428156278623 301457594427501642234417935)
  ·
    refine ⟨452186391641252463351626903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301457594427501642234417935 452186391641252463351626903)
    ·
      refine ⟨678279587461878695027440355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452186391641252463351626903 678279587461878695027440355)
      ·
        refine ⟨1017419381192818042541160533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678279587461878695027440355 1017419381192818042541160533)
        ·
          refine ⟨11922883373353336436029225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 1017419381192818042541160533 11922883373353336436029225)
          ·
            refine ⟨8942162530015002327021919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11922883373353336436029225 8942162530015002327021919)
            ·
              refine ⟨13413243795022503490532879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942162530015002327021919 13413243795022503490532879)
              ·
                refine ⟨20119865692533755235799319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413243795022503490532879 20119865692533755235799319)
                ·
                  refine ⟨30179798538800632853698979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20119865692533755235799319 30179798538800632853698979)
                  ·
                    refine ⟨45269697808200949280548469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30179798538800632853698979 45269697808200949280548469)
                    ·
                      refine ⟨4244034169518838995051419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45269697808200949280548469 4244034169518838995051419)
                      ·
                        rfl

theorem cell23_8265227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 5].length) (baseStart_8265227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265227 prefixEnd_8265227 := by exact prefixLift 8265227
  have htrace : WordTrace (prefixWord ++ tailWord_8265227) baseStart_8265227 baseEnd_8265227 := by
    simpa [prefixWord, tailWord_8265227, baseEnd_8265227] using wordTrace_append hprefix tailTrace_8265227
  have hstable : (prefixWord ++ tailWord_8265227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265227).length < 2 ^ (prefixWord ++ tailWord_8265227).sum := by decide
  have hdescent : baseEnd_8265227 < baseStart_8265227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265230 : List Nat := [4, 1, 1, 2, 5, 10]
def baseStart_8265230 : Nat := 118140960795 + 8265230 * 2 ^ 59
def prefixEnd_8265230 : Nat := 4983230072969 + 3 ^ 40 * 8265230 * 2
def baseEnd_8265230 : Nat := 17465167530702890877835

theorem tailTrace_8265230 : CollatzResearch.WordTrace tailWord_8265230 prefixEnd_8265230 17465167530702890877835 := by
  unfold tailWord_8265230
  simp only [CollatzResearch.WordTrace]
  refine ⟨37682212980811346718347143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200971802564327182497851429 37682212980811346718347143)
  ·
    refine ⟨56523319471217020077520715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37682212980811346718347143 56523319471217020077520715)
    ·
      refine ⟨84784979206825530116281073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56523319471217020077520715 84784979206825530116281073)
      ·
        refine ⟨63588734405119147587210805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84784979206825530116281073 63588734405119147587210805)
        ·
          refine ⟨5961443850479920086301013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63588734405119147587210805 5961443850479920086301013)
          ·
            refine ⟨17465167530702890877835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5961443850479920086301013 17465167530702890877835)
            ·
              rfl

theorem cell23_8265230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 10].length) (baseStart_8265230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265230 prefixEnd_8265230 := by exact prefixLift 8265230
  have htrace : WordTrace (prefixWord ++ tailWord_8265230) baseStart_8265230 baseEnd_8265230 := by
    simpa [prefixWord, tailWord_8265230, baseEnd_8265230] using wordTrace_append hprefix tailTrace_8265230
  have hstable : (prefixWord ++ tailWord_8265230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265230).length < 2 ^ (prefixWord ++ tailWord_8265230).sum := by decide
  have hdescent : baseEnd_8265230 < baseStart_8265230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265253 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_8265253 : Nat := 118140960795 + 8265253 * 2 ^ 59
def prefixEnd_8265253 : Nat := 4983230072969 + 3 ^ 40 * 8265253 * 2
def baseEnd_8265253 : Nat := 4244047520015855893326299

theorem tailTrace_8265253 : CollatzResearch.WordTrace tailWord_8265253 prefixEnd_8265253 4244047520015855893326299 := by
  unfold tailWord_8265253
  simp only [CollatzResearch.WordTrace]
  refine ⟨301458542725407448674864413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200972361816938299116576275 301458542725407448674864413)
  ·
    refine ⟨113046953522027793253074155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301458542725407448674864413 113046953522027793253074155)
    ·
      refine ⟨169570430283041689879611233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113046953522027793253074155 169570430283041689879611233)
      ·
        refine ⟨127177822712281267409708425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169570430283041689879611233 127177822712281267409708425)
        ·
          refine ⟨95383367034210950557281319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127177822712281267409708425 95383367034210950557281319)
          ·
            refine ⟨143075050551316425835921979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95383367034210950557281319 143075050551316425835921979)
            ·
              refine ⟨214612575826974638753882969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143075050551316425835921979 214612575826974638753882969)
              ·
                refine ⟨160959431870230979065412227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214612575826974638753882969 160959431870230979065412227)
                ·
                  refine ⟨241439147805346468598118341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160959431870230979065412227 241439147805346468598118341)
                  ·
                    refine ⟨45269840213502462862147189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241439147805346468598118341 45269840213502462862147189)
                    ·
                      refine ⟨4244047520015855893326299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45269840213502462862147189 4244047520015855893326299)
                      ·
                        rfl

theorem cell23_8265253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_8265253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265253 prefixEnd_8265253 := by exact prefixLift 8265253
  have htrace : WordTrace (prefixWord ++ tailWord_8265253) baseStart_8265253 baseEnd_8265253 := by
    simpa [prefixWord, tailWord_8265253, baseEnd_8265253] using wordTrace_append hprefix tailTrace_8265253
  have hstable : (prefixWord ++ tailWord_8265253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265253).length < 2 ^ (prefixWord ++ tailWord_8265253).sum := by decide
  have hdescent : baseEnd_8265253 < baseStart_8265253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265267 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 3, 3, 2]
def baseStart_8265267 : Nat := 118140960795 + 8265267 * 2 ^ 59
def prefixEnd_8265267 : Nat := 4983230072969 + 3 ^ 40 * 8265267 * 2
def baseEnd_8265267 : Nat := 4244054708745018838551235

theorem tailTrace_8265267 : CollatzResearch.WordTrace tailWord_8265267 prefixEnd_8265267 4244054708745018838551235 := by
  unfold tailWord_8265267
  simp only [CollatzResearch.WordTrace]
  refine ⟨301459053347356729065874055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200972702231571152710582703 301459053347356729065874055)
  ·
    refine ⟨452188580021035093598811083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301459053347356729065874055 452188580021035093598811083)
    ·
      refine ⟨678282870031552640398216625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452188580021035093598811083 678282870031552640398216625)
      ·
        refine ⟨508712152523664480298662469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678282870031552640398216625 508712152523664480298662469)
        ·
          refine ⟨95383528598187090055999213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508712152523664480298662469 95383528598187090055999213)
          ·
            refine ⟨35768823224320158770999705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95383528598187090055999213 35768823224320158770999705)
            ·
              refine ⟨26826617418240119078249779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35768823224320158770999705 26826617418240119078249779)
              ·
                refine ⟨40239926127360178617374669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26826617418240119078249779 40239926127360178617374669)
                ·
                  refine ⟨15089972297760066981515501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40239926127360178617374669 15089972297760066981515501)
                  ·
                    refine ⟨5658739611660025118068313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15089972297760066981515501 5658739611660025118068313)
                    ·
                      refine ⟨4244054708745018838551235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658739611660025118068313 4244054708745018838551235)
                      ·
                        rfl

theorem cell23_8265267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3, 2].length) (baseStart_8265267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265267 prefixEnd_8265267 := by exact prefixLift 8265267
  have htrace : WordTrace (prefixWord ++ tailWord_8265267) baseStart_8265267 baseEnd_8265267 := by
    simpa [prefixWord, tailWord_8265267, baseEnd_8265267] using wordTrace_append hprefix tailTrace_8265267
  have hstable : (prefixWord ++ tailWord_8265267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265267).length < 2 ^ (prefixWord ++ tailWord_8265267).sum := by decide
  have hdescent : baseEnd_8265267 < baseStart_8265267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265323 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_8265323 : Nat := 118140960795 + 8265323 * 2 ^ 59
def prefixEnd_8265323 : Nat := 4983230072969 + 3 ^ 40 * 8265323 * 2
def baseEnd_8265323 : Nat := 4244083463661670619450977

theorem tailTrace_8265323 : CollatzResearch.WordTrace tailWord_8265323 prefixEnd_8265323 4244083463661670619450977 := by
  unfold tailWord_8265323
  simp only [CollatzResearch.WordTrace]
  refine ⟨301461095835153850629912623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200974063890102567086608415 301461095835153850629912623)
  ·
    refine ⟨452191643752730775944868935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301461095835153850629912623 452191643752730775944868935)
    ·
      refine ⟨678287465629096163917303403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452191643752730775944868935 678287465629096163917303403)
      ·
        refine ⟨1017431198443644245875955105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678287465629096163917303403 1017431198443644245875955105)
        ·
          refine ⟨763073398832733184406966329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017431198443644245875955105 763073398832733184406966329)
          ·
            refine ⟨572305049124549888305224747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763073398832733184406966329 572305049124549888305224747)
            ·
              refine ⟨858457573686824832457837121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572305049124549888305224747 858457573686824832457837121)
              ·
                refine ⟨643843180265118624343377841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858457573686824832457837121 643843180265118624343377841)
                ·
                  refine ⟨482882385198838968257533381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643843180265118624343377841 482882385198838968257533381)
                  ·
                    refine ⟨90540447224782306548287509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482882385198838968257533381 90540447224782306548287509)
                    ·
                      refine ⟨4244083463661670619450977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90540447224782306548287509 4244083463661670619450977)
                      ·
                        rfl

theorem cell23_8265323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_8265323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265323 prefixEnd_8265323 := by exact prefixLift 8265323
  have htrace : WordTrace (prefixWord ++ tailWord_8265323) baseStart_8265323 baseEnd_8265323 := by
    simpa [prefixWord, tailWord_8265323, baseEnd_8265323] using wordTrace_append hprefix tailTrace_8265323
  have hstable : (prefixWord ++ tailWord_8265323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265323).length < 2 ^ (prefixWord ++ tailWord_8265323).sum := by decide
  have hdescent : baseEnd_8265323 < baseStart_8265323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265407 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_8265407 : Nat := 118140960795 + 8265407 * 2 ^ 59
def prefixEnd_8265407 : Nat := 4983230072969 + 3 ^ 40 * 8265407 * 2
def baseEnd_8265407 : Nat := 4244126596036648290800591

theorem tailTrace_8265407 : CollatzResearch.WordTrace tailWord_8265407 prefixEnd_8265407 4244126596036648290800591 := by
  unfold tailWord_8265407
  simp only [CollatzResearch.WordTrace]
  refine ⟨301464159566849532975970475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200976106377899688650646983 301464159566849532975970475)
  ·
    refine ⟨452196239350274299463955713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301464159566849532975970475 452196239350274299463955713)
    ·
      refine ⟨339147179512705724597966785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452196239350274299463955713 339147179512705724597966785)
      ·
        refine ⟨254360384634529293448475089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339147179512705724597966785 254360384634529293448475089)
        ·
          refine ⟨190770288475896970086356317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254360384634529293448475089 190770288475896970086356317)
          ·
            refine ⟨71538858178461363782383619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190770288475896970086356317 71538858178461363782383619)
            ·
              refine ⟨107308287267692045673575429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71538858178461363782383619 107308287267692045673575429)
              ·
                refine ⟨20120303862692258563795393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107308287267692045673575429 20120303862692258563795393)
                ·
                  refine ⟨15090227897019193922846545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20120303862692258563795393 15090227897019193922846545)
                  ·
                    refine ⟨11317670922764395442134909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15090227897019193922846545 11317670922764395442134909)
                    ·
                      refine ⟨4244126596036648290800591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317670922764395442134909 4244126596036648290800591)
                      ·
                        rfl

theorem cell23_8265407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_8265407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265407 prefixEnd_8265407 := by exact prefixLift 8265407
  have htrace : WordTrace (prefixWord ++ tailWord_8265407) baseStart_8265407 baseEnd_8265407 := by
    simpa [prefixWord, tailWord_8265407, baseEnd_8265407] using wordTrace_append hprefix tailTrace_8265407
  have hstable : (prefixWord ++ tailWord_8265407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265407).length < 2 ^ (prefixWord ++ tailWord_8265407).sum := by decide
  have hdescent : baseEnd_8265407 < baseStart_8265407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265421 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_8265421 : Nat := 118140960795 + 8265421 * 2 ^ 59
def prefixEnd_8265421 : Nat := 4983230072969 + 3 ^ 40 * 8265421 * 2
def baseEnd_8265421 : Nat := 4244133784765811236025527

theorem tailTrace_8265421 : CollatzResearch.WordTrace tailWord_8265421 prefixEnd_8265421 4244133784765811236025527 := by
  unfold tailWord_8265421
  simp only [CollatzResearch.WordTrace]
  refine ⟨301464670188798813366980117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200976446792532542244653411 301464670188798813366980117)
  ·
    refine ⟨14131156415099944376577193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 301464670188798813366980117 14131156415099944376577193)
    ·
      refine ⟨10598367311324958282432895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14131156415099944376577193 10598367311324958282432895)
      ·
        refine ⟨15897550966987437423649343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598367311324958282432895 15897550966987437423649343)
        ·
          refine ⟨23846326450481156135474015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15897550966987437423649343 23846326450481156135474015)
          ·
            refine ⟨35769489675721734203211023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23846326450481156135474015 35769489675721734203211023)
            ·
              refine ⟨53654234513582601304816535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35769489675721734203211023 53654234513582601304816535)
              ·
                refine ⟨80481351770373901957224803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53654234513582601304816535 80481351770373901957224803)
                ·
                  refine ⟨120722027655560852935837205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80481351770373901957224803 120722027655560852935837205)
                  ·
                    refine ⟨5658845046354414981367369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120722027655560852935837205 5658845046354414981367369)
                    ·
                      refine ⟨4244133784765811236025527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658845046354414981367369 4244133784765811236025527)
                      ·
                        rfl

theorem cell23_8265421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_8265421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265421 prefixEnd_8265421 := by exact prefixLift 8265421
  have htrace : WordTrace (prefixWord ++ tailWord_8265421) baseStart_8265421 baseEnd_8265421 := by
    simpa [prefixWord, tailWord_8265421, baseEnd_8265421] using wordTrace_append hprefix tailTrace_8265421
  have hstable : (prefixWord ++ tailWord_8265421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265421).length < 2 ^ (prefixWord ++ tailWord_8265421).sum := by decide
  have hdescent : baseEnd_8265421 < baseStart_8265421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265441 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_8265441 : Nat := 118140960795 + 8265441 * 2 ^ 59
def prefixEnd_8265441 : Nat := 4983230072969 + 3 ^ 40 * 8265441 * 2
def baseEnd_8265441 : Nat := 4244144054378901157775435

theorem tailTrace_8265441 : CollatzResearch.WordTrace tailWord_8265441 prefixEnd_8265441 4244144054378901157775435 := by
  unfold tailWord_8265441
  simp only [CollatzResearch.WordTrace]
  refine ⟨301465399648726356782708177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200976933099150904521805451 301465399648726356782708177)
  ·
    refine ⟨226099049736544767587031133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301465399648726356782708177 226099049736544767587031133)
    ·
      refine ⟨84787143651204287845136675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226099049736544767587031133 84787143651204287845136675)
      ·
        refine ⟨127180715476806431767705013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84787143651204287845136675 127180715476806431767705013)
        ·
          refine ⟨11923192075950602978222345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127180715476806431767705013 11923192075950602978222345)
          ·
            refine ⟨8942394056962952233666759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11923192075950602978222345 8942394056962952233666759)
            ·
              refine ⟨13413591085444428350500139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942394056962952233666759 13413591085444428350500139)
              ·
                refine ⟨20120386628166642525750209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413591085444428350500139 20120386628166642525750209)
                ·
                  refine ⟨15090289971124981894312657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20120386628166642525750209 15090289971124981894312657)
                  ·
                    refine ⟨11317717478343736420734493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15090289971124981894312657 11317717478343736420734493)
                    ·
                      refine ⟨4244144054378901157775435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317717478343736420734493 4244144054378901157775435)
                      ·
                        rfl

theorem cell23_8265441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_8265441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265441 prefixEnd_8265441 := by exact prefixLift 8265441
  have htrace : WordTrace (prefixWord ++ tailWord_8265441) baseStart_8265441 baseEnd_8265441 := by
    simpa [prefixWord, tailWord_8265441, baseEnd_8265441] using wordTrace_append hprefix tailTrace_8265441
  have hstable : (prefixWord ++ tailWord_8265441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265441).length < 2 ^ (prefixWord ++ tailWord_8265441).sum := by decide
  have hdescent : baseEnd_8265441 < baseStart_8265441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265454 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_8265454 : Nat := 118140960795 + 8265454 * 2 ^ 59
def prefixEnd_8265454 : Nat := 4983230072969 + 3 ^ 40 * 8265454 * 2
def baseEnd_8265454 : Nat := 4244150729627409606912875

theorem tailTrace_8265454 : CollatzResearch.WordTrace tailWord_8265454 prefixEnd_8265454 4244150729627409606912875 := by
  unfold tailWord_8265454
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683234224709907500366427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200977249198452840001954277 37683234224709907500366427)
  ·
    refine ⟨56524851337064861250549641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37683234224709907500366427 56524851337064861250549641)
    ·
      refine ⟨42393638502798645937912231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56524851337064861250549641 42393638502798645937912231)
      ·
        refine ⟨63590457754197968906868347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42393638502798645937912231 63590457754197968906868347)
        ·
          refine ⟨95385686631296953360302521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63590457754197968906868347 95385686631296953360302521)
          ·
            refine ⟨71539264973472715020226891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95385686631296953360302521 71539264973472715020226891)
            ·
              refine ⟨107308897460209072530340337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71539264973472715020226891 107308897460209072530340337)
              ·
                refine ⟨80481673095156804397755253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107308897460209072530340337 80481673095156804397755253)
                ·
                  refine ⟨7545156852670950412289555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80481673095156804397755253 7545156852670950412289555)
                  ·
                    refine ⟨11317735279006425618434333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545156852670950412289555 11317735279006425618434333)
                    ·
                      refine ⟨4244150729627409606912875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317735279006425618434333 4244150729627409606912875)
                      ·
                        rfl

theorem cell23_8265454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_8265454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265454 prefixEnd_8265454 := by exact prefixLift 8265454
  have htrace : WordTrace (prefixWord ++ tailWord_8265454) baseStart_8265454 baseEnd_8265454 := by
    simpa [prefixWord, tailWord_8265454, baseEnd_8265454] using wordTrace_append hprefix tailTrace_8265454
  have hstable : (prefixWord ++ tailWord_8265454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265454).length < 2 ^ (prefixWord ++ tailWord_8265454).sum := by decide
  have hdescent : baseEnd_8265454 < baseStart_8265454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265471 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 1, 1, 3]
def baseStart_8265471 : Nat := 118140960795 + 8265471 * 2 ^ 59
def prefixEnd_8265471 : Nat := 4983230072969 + 3 ^ 40 * 8265471 * 2
def baseEnd_8265471 : Nat := 4244159458798536040400297

theorem tailTrace_8265471 : CollatzResearch.WordTrace tailWord_8265471 prefixEnd_8265471 4244159458798536040400297 := by
  unfold tailWord_8265471
  simp only [CollatzResearch.WordTrace]
  refine ⟨301466493838617671906300267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200977662559078447937533511 301466493838617671906300267)
  ·
    refine ⟨452199740757926507859450401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301466493838617671906300267 452199740757926507859450401)
    ·
      refine ⟨339149805568444880894587801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452199740757926507859450401 339149805568444880894587801)
      ·
        refine ⟨254362354176333660670940851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339149805568444880894587801 254362354176333660670940851)
        ·
          refine ⟨381543531264500491006411277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254362354176333660670940851 381543531264500491006411277)
          ·
            refine ⟨143078824224187684127404229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381543531264500491006411277 143078824224187684127404229)
            ·
              refine ⟨26827279542035190773888293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143078824224187684127404229 26827279542035190773888293)
              ·
                refine ⟨5030114914131598270104055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26827279542035190773888293 5030114914131598270104055)
                ·
                  refine ⟨7545172371197397405156083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030114914131598270104055 7545172371197397405156083)
                  ·
                    refine ⟨11317758556796096107734125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545172371197397405156083 11317758556796096107734125)
                    ·
                      refine ⟨4244159458798536040400297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317758556796096107734125 4244159458798536040400297)
                      ·
                        rfl

theorem cell23_8265471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_8265471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265471 prefixEnd_8265471 := by exact prefixLift 8265471
  have htrace : WordTrace (prefixWord ++ tailWord_8265471) baseStart_8265471 baseEnd_8265471 := by
    simpa [prefixWord, tailWord_8265471, baseEnd_8265471] using wordTrace_append hprefix tailTrace_8265471
  have hstable : (prefixWord ++ tailWord_8265471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265471).length < 2 ^ (prefixWord ++ tailWord_8265471).sum := by decide
  have hdescent : baseEnd_8265471 < baseStart_8265471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265497 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_8265497 : Nat := 118140960795 + 8265497 * 2 ^ 59
def prefixEnd_8265497 : Nat := 4983230072969 + 3 ^ 40 * 8265497 * 2
def baseEnd_8265497 : Nat := 4244172809295552938675177

theorem tailTrace_8265497 : CollatzResearch.WordTrace tailWord_8265497 prefixEnd_8265497 4244172809295552938675177 := by
  unfold tailWord_8265497
  simp only [CollatzResearch.WordTrace]
  refine ⟨301467442136523478346746745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200978294757682318897831163 301467442136523478346746745)
  ·
    refine ⟨226100581602392608760060059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301467442136523478346746745 226100581602392608760060059)
    ·
      refine ⟨339150872403588913140090089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226100581602392608760060059 339150872403588913140090089)
      ·
        refine ⟨254363154302691684855067567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339150872403588913140090089 254363154302691684855067567)
        ·
          refine ⟨381544731454037527282601351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254363154302691684855067567 381544731454037527282601351)
          ·
            refine ⟨572317097181056290923902027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381544731454037527282601351 572317097181056290923902027)
            ·
              refine ⟨858475645771584436385853041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572317097181056290923902027 858475645771584436385853041)
              ·
                refine ⟨643856734328688327289389781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858475645771584436385853041 643856734328688327289389781)
                ·
                  refine ⟨15090392210828632670845073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 643856734328688327289389781 15090392210828632670845073)
                  ·
                    refine ⟨11317794158121474503133805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15090392210828632670845073 11317794158121474503133805)
                    ·
                      refine ⟨4244172809295552938675177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317794158121474503133805 4244172809295552938675177)
                      ·
                        rfl

theorem cell23_8265497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_8265497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265497 prefixEnd_8265497 := by exact prefixLift 8265497
  have htrace : WordTrace (prefixWord ++ tailWord_8265497) baseStart_8265497 baseEnd_8265497 := by
    simpa [prefixWord, tailWord_8265497, baseEnd_8265497] using wordTrace_append hprefix tailTrace_8265497
  have hstable : (prefixWord ++ tailWord_8265497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265497).length < 2 ^ (prefixWord ++ tailWord_8265497).sum := by decide
  have hdescent : baseEnd_8265497 < baseStart_8265497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265507 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4]
def baseStart_8265507 : Nat := 118140960795 + 8265507 * 2 ^ 59
def prefixEnd_8265507 : Nat := 4983230072969 + 3 ^ 40 * 8265507 * 2
def baseEnd_8265507 : Nat := 4244177944102097899550131

theorem tailTrace_8265507 : CollatzResearch.WordTrace tailWord_8265507 prefixEnd_8265507 4244177944102097899550131 := by
  unfold tailWord_8265507
  simp only [CollatzResearch.WordTrace]
  refine ⟨301467806866487250054610775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200978537910991500036407183 301467806866487250054610775)
  ·
    refine ⟨452201710299730875081916163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301467806866487250054610775 452201710299730875081916163)
    ·
      refine ⟨678302565449596312622874245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452201710299730875081916163 678302565449596312622874245)
      ·
        refine ⟨127181731021799308616788921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678302565449596312622874245 127181731021799308616788921)
        ·
          refine ⟨95386298266349481462591691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127181731021799308616788921 95386298266349481462591691)
          ·
            refine ⟨143079447399524222193887537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95386298266349481462591691 143079447399524222193887537)
            ·
              refine ⟨107309585549643166645415653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143079447399524222193887537 107309585549643166645415653)
              ·
                refine ⟨20120547290558093746015435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107309585549643166645415653 20120547290558093746015435)
                ·
                  refine ⟨30180820935837140619023153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20120547290558093746015435 30180820935837140619023153)
                  ·
                    refine ⟨22635615701877855464267365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30180820935837140619023153 22635615701877855464267365)
                    ·
                      refine ⟨4244177944102097899550131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22635615701877855464267365 4244177944102097899550131)
                      ·
                        rfl

theorem cell23_8265507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_8265507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265507 prefixEnd_8265507 := by exact prefixLift 8265507
  have htrace : WordTrace (prefixWord ++ tailWord_8265507) baseStart_8265507 baseEnd_8265507 := by
    simpa [prefixWord, tailWord_8265507, baseEnd_8265507] using wordTrace_append hprefix tailTrace_8265507
  have hstable : (prefixWord ++ tailWord_8265507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265507).length < 2 ^ (prefixWord ++ tailWord_8265507).sum := by decide
  have hdescent : baseEnd_8265507 < baseStart_8265507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265524 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_8265524 : Nat := 118140960795 + 8265524 * 2 ^ 59
def prefixEnd_8265524 : Nat := 4983230072969 + 3 ^ 40 * 8265524 * 2
def baseEnd_8265524 : Nat := 4244186673273224333037553

theorem tailTrace_8265524 : CollatzResearch.WordTrace tailWord_8265524 prefixEnd_8265524 4244186673273224333037553 := by
  unfold tailWord_8265524
  simp only [CollatzResearch.WordTrace]
  refine ⟨150734213453712830978989813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200978951271617107971986417 150734213453712830978989813)
  ·
    refine ⟨14131332511285577904280295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150734213453712830978989813 14131332511285577904280295)
    ·
      refine ⟨21196998766928366856420443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131332511285577904280295 21196998766928366856420443)
      ·
        refine ⟨31795498150392550284630665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21196998766928366856420443 31795498150392550284630665)
        ·
          refine ⟨23846623612794412713472999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31795498150392550284630665 23846623612794412713472999)
          ·
            refine ⟨35769935419191619070209499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23846623612794412713472999 35769935419191619070209499)
            ·
              refine ⟨53654903128787428605314249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35769935419191619070209499 53654903128787428605314249)
              ·
                refine ⟨40241177346590571453985687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53654903128787428605314249 40241177346590571453985687)
                ·
                  refine ⟨60361766019885857180978531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40241177346590571453985687 60361766019885857180978531)
                  ·
                    refine ⟨90542649029828785771467797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60361766019885857180978531 90542649029828785771467797)
                    ·
                      refine ⟨4244186673273224333037553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90542649029828785771467797 4244186673273224333037553)
                      ·
                        rfl

theorem cell23_8265524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_8265524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265524 prefixEnd_8265524 := by exact prefixLift 8265524
  have htrace : WordTrace (prefixWord ++ tailWord_8265524) baseStart_8265524 baseEnd_8265524 := by
    simpa [prefixWord, tailWord_8265524, baseEnd_8265524] using wordTrace_append hprefix tailTrace_8265524
  have hstable : (prefixWord ++ tailWord_8265524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265524).length < 2 ^ (prefixWord ++ tailWord_8265524).sum := by decide
  have hdescent : baseEnd_8265524 < baseStart_8265524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265527 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_8265527 : Nat := 118140960795 + 8265527 * 2 ^ 59
def prefixEnd_8265527 : Nat := 4983230072969 + 3 ^ 40 * 8265527 * 2
def baseEnd_8265527 : Nat := 4244188213715187821300039

theorem tailTrace_8265527 : CollatzResearch.WordTrace tailWord_8265527 prefixEnd_8265527 4244188213715187821300039 := by
  unfold tailWord_8265527
  simp only [CollatzResearch.WordTrace]
  refine ⟨301468536326414793470338835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200979024217609862313559223 301468536326414793470338835)
  ·
    refine ⟨452202804489622190205508253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301468536326414793470338835 452202804489622190205508253)
    ·
      refine ⟨169576051683608321327065595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452202804489622190205508253 169576051683608321327065595)
      ·
        refine ⟨254364077525412481990598393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169576051683608321327065595 254364077525412481990598393)
        ·
          refine ⟨190773058144059361492948795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254364077525412481990598393 190773058144059361492948795)
          ·
            refine ⟨286159587216089042239423193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190773058144059361492948795 286159587216089042239423193)
            ·
              refine ⟨214619690412066781679567395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286159587216089042239423193 214619690412066781679567395)
              ·
                refine ⟨321929535618100172519351093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214619690412066781679567395 321929535618100172519351093)
                ·
                  refine ⟨30180893964196891173689165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321929535618100172519351093 30180893964196891173689165)
                  ·
                    refine ⟨11317835236573834190133437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30180893964196891173689165 11317835236573834190133437)
                    ·
                      refine ⟨4244188213715187821300039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317835236573834190133437 4244188213715187821300039)
                      ·
                        rfl

theorem cell23_8265527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_8265527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265527 prefixEnd_8265527 := by exact prefixLift 8265527
  have htrace : WordTrace (prefixWord ++ tailWord_8265527) baseStart_8265527 baseEnd_8265527 := by
    simpa [prefixWord, tailWord_8265527, baseEnd_8265527] using wordTrace_append hprefix tailTrace_8265527
  have hstable : (prefixWord ++ tailWord_8265527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265527).length < 2 ^ (prefixWord ++ tailWord_8265527).sum := by decide
  have hdescent : baseEnd_8265527 < baseStart_8265527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265528 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 3, 2, 2]
def baseStart_8265528 : Nat := 118140960795 + 8265528 * 2 ^ 59
def prefixEnd_8265528 : Nat := 4983230072969 + 3 ^ 40 * 8265528 * 2
def baseEnd_8265528 : Nat := 4244188727195842317387535

theorem tailTrace_8265528 : CollatzResearch.WordTrace tailWord_8265528 prefixEnd_8265528 4244188727195842317387535 := by
  unfold tailWord_8265528
  simp only [CollatzResearch.WordTrace]
  refine ⟨150734286399705585320562619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200979048532940780427416825 150734286399705585320562619)
  ·
    refine ⟨226101429599558377980843929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150734286399705585320562619 226101429599558377980843929)
    ·
      refine ⟨169576072199668783485632947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226101429599558377980843929 169576072199668783485632947)
      ·
        refine ⟨254364108299503175228449421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169576072199668783485632947 254364108299503175228449421)
        ·
          refine ⟨95386540612313690710668533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254364108299503175228449421 95386540612313690710668533)
          ·
            refine ⟨8942488182404408504125175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95386540612313690710668533 8942488182404408504125175)
            ·
              refine ⟨13413732273606612756187763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942488182404408504125175 13413732273606612756187763)
              ·
                refine ⟨20120598410409919134281645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413732273606612756187763 20120598410409919134281645)
                ·
                  refine ⟨7545224403903719675355617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20120598410409919134281645 7545224403903719675355617)
                  ·
                    refine ⟨5658918302927789756516713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7545224403903719675355617 5658918302927789756516713)
                    ·
                      refine ⟨4244188727195842317387535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658918302927789756516713 4244188727195842317387535)
                      ·
                        rfl

theorem cell23_8265528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_8265528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265528 prefixEnd_8265528 := by exact prefixLift 8265528
  have htrace : WordTrace (prefixWord ++ tailWord_8265528) baseStart_8265528 baseEnd_8265528 := by
    simpa [prefixWord, tailWord_8265528, baseEnd_8265528] using wordTrace_append hprefix tailTrace_8265528
  have hstable : (prefixWord ++ tailWord_8265528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265528).length < 2 ^ (prefixWord ++ tailWord_8265528).sum := by decide
  have hdescent : baseEnd_8265528 < baseStart_8265528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265534 : List Nat := [4, 2, 1, 2, 2, 2, 2, 8]
def baseStart_8265534 : Nat := 118140960795 + 8265534 * 2 ^ 59
def prefixEnd_8265534 : Nat := 4983230072969 + 3 ^ 40 * 8265534 * 2
def baseEnd_8265534 : Nat := 157192289188139603478241

theorem tailTrace_8265534 : CollatzResearch.WordTrace tailWord_8265534 prefixEnd_8265534 157192289188139603478241 := by
  unfold tailWord_8265534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683598954673679208230457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200979194424926289110562437 37683598954673679208230457)
  ·
    refine ⟨28262699216005259406172843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37683598954673679208230457 28262699216005259406172843)
    ·
      refine ⟨42394048824007889109259265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28262699216005259406172843 42394048824007889109259265)
      ·
        refine ⟨31795536618005916831944449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42394048824007889109259265 31795536618005916831944449)
        ·
          refine ⟨23846652463504437623958337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31795536618005916831944449 23846652463504437623958337)
          ·
            refine ⟨17884989347628328217968753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23846652463504437623958337 17884989347628328217968753)
            ·
              refine ⟨13413742010721246163476565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17884989347628328217968753 13413742010721246163476565)
              ·
                refine ⟨157192289188139603478241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13413742010721246163476565 157192289188139603478241)
                ·
                  rfl

theorem cell23_8265534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_8265534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265534 prefixEnd_8265534 := by exact prefixLift 8265534
  have htrace : WordTrace (prefixWord ++ tailWord_8265534) baseStart_8265534 baseEnd_8265534 := by
    simpa [prefixWord, tailWord_8265534, baseEnd_8265534] using wordTrace_append hprefix tailTrace_8265534
  have hstable : (prefixWord ++ tailWord_8265534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265534).length < 2 ^ (prefixWord ++ tailWord_8265534).sum := by decide
  have hdescent : baseEnd_8265534 < baseStart_8265534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265548 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_8265548 : Nat := 118140960795 + 8265548 * 2 ^ 59
def prefixEnd_8265548 : Nat := 4983230072969 + 3 ^ 40 * 8265548 * 2
def baseEnd_8265548 : Nat := 4244198996808932239137443

theorem tailTrace_8265548 : CollatzResearch.WordTrace tailWord_8265548 prefixEnd_8265548 4244198996808932239137443 := by
  unfold tailWord_8265548
  simp only [CollatzResearch.WordTrace]
  refine ⟨150734651129669357028426649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200979534839559142704568865 150734651129669357028426649)
  ·
    refine ⟨113050988347252017771319987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150734651129669357028426649 113050988347252017771319987)
    ·
      refine ⟨169576482520878026656979981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113050988347252017771319987 169576482520878026656979981)
      ·
        refine ⟨63591180945329259996367493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169576482520878026656979981 63591180945329259996367493)
        ·
          refine ⟨11923346427249236249318905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63591180945329259996367493 11923346427249236249318905)
          ·
            refine ⟨8942509820436927186989179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11923346427249236249318905 8942509820436927186989179)
            ·
              refine ⟨13413764730655390780483769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942509820436927186989179 13413764730655390780483769)
              ·
                refine ⟨10060323547991543085362827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13413764730655390780483769 10060323547991543085362827)
                ·
                  refine ⟨15090485321987314628044241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10060323547991543085362827 15090485321987314628044241)
                  ·
                    refine ⟨11317863991490485971033181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15090485321987314628044241 11317863991490485971033181)
                    ·
                      refine ⟨4244198996808932239137443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11317863991490485971033181 4244198996808932239137443)
                      ·
                        rfl

theorem cell23_8265548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_8265548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265548 prefixEnd_8265548 := by exact prefixLift 8265548
  have htrace : WordTrace (prefixWord ++ tailWord_8265548) baseStart_8265548 baseEnd_8265548 := by
    simpa [prefixWord, tailWord_8265548, baseEnd_8265548] using wordTrace_append hprefix tailTrace_8265548
  have hstable : (prefixWord ++ tailWord_8265548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265548).length < 2 ^ (prefixWord ++ tailWord_8265548).sum := by decide
  have hdescent : baseEnd_8265548 < baseStart_8265548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265584 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 5, 4, 2]
def baseStart_8265584 : Nat := 118140960795 + 8265584 * 2 ^ 59
def prefixEnd_8265584 : Nat := 4983230072969 + 3 ^ 40 * 8265584 * 2
def baseEnd_8265584 : Nat := 4244217482112494098287277

theorem tailTrace_8265584 : CollatzResearch.WordTrace tailWord_8265584 prefixEnd_8265584 4244217482112494098287277 := by
  unfold tailWord_8265584
  simp only [CollatzResearch.WordTrace]
  refine ⟨150735307643604146102581903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200980410191472194803442537 150735307643604146102581903)
  ·
    refine ⟨226102961465406219153872855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150735307643604146102581903 226102961465406219153872855)
    ·
      refine ⟨339154442198109328730809283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226102961465406219153872855 339154442198109328730809283)
      ·
        refine ⟨508731663297163993096213925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339154442198109328730809283 508731663297163993096213925)
        ·
          refine ⟨95387186868218248705540111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508731663297163993096213925 95387186868218248705540111)
          ·
            refine ⟨143080780302327373058310167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95387186868218248705540111 143080780302327373058310167)
            ·
              refine ⟨214621170453491059587465251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143080780302327373058310167 214621170453491059587465251)
              ·
                refine ⟨321931755680236589381197877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214621170453491059587465251 321931755680236589381197877)
                ·
                  refine ⟨30181102095022180254487301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321931755680236589381197877 30181102095022180254487301)
                  ·
                    refine ⟨5658956642816658797716369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30181102095022180254487301 5658956642816658797716369)
                    ·
                      refine ⟨4244217482112494098287277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658956642816658797716369 4244217482112494098287277)
                      ·
                        rfl

theorem cell23_8265584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 4, 2].length) (baseStart_8265584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265584 prefixEnd_8265584 := by exact prefixLift 8265584
  have htrace : WordTrace (prefixWord ++ tailWord_8265584) baseStart_8265584 baseEnd_8265584 := by
    simpa [prefixWord, tailWord_8265584, baseEnd_8265584] using wordTrace_append hprefix tailTrace_8265584
  have hstable : (prefixWord ++ tailWord_8265584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265584).length < 2 ^ (prefixWord ++ tailWord_8265584).sum := by decide
  have hdescent : baseEnd_8265584 < baseStart_8265584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265618 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_8265618 : Nat := 118140960795 + 8265618 * 2 ^ 59
def prefixEnd_8265618 : Nat := 4983230072969 + 3 ^ 40 * 8265618 * 2
def baseEnd_8265618 : Nat := 4244234940454746965262121

theorem tailTrace_8265618 : CollatzResearch.WordTrace tailWord_8265618 prefixEnd_8265618 4244234940454746965262121 := by
  unfold tailWord_8265618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75367963842271279002975377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200981236912723410674601005 75367963842271279002975377)
  ·
    refine ⟨56525972881703459252231533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75367963842271279002975377 56525972881703459252231533)
    ·
      refine ⟨21197239830638797219586825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56525972881703459252231533 21197239830638797219586825)
      ·
        refine ⟨15897929872979097914690119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21197239830638797219586825 15897929872979097914690119)
        ·
          refine ⟨23846894809468646872035179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15897929872979097914690119 23846894809468646872035179)
          ·
            refine ⟨35770342214202970308052769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23846894809468646872035179 35770342214202970308052769)
            ·
              refine ⟨26827756660652227731039577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35770342214202970308052769 26827756660652227731039577)
              ·
                refine ⟨20120817495489170798279683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26827756660652227731039577 20120817495489170798279683)
                ·
                  refine ⟨30181226243233756197419525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20120817495489170798279683 30181226243233756197419525)
                  ·
                    refine ⟨5658979920606329287016161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30181226243233756197419525 5658979920606329287016161)
                    ·
                      refine ⟨4244234940454746965262121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5658979920606329287016161 4244234940454746965262121)
                      ·
                        rfl

theorem cell23_8265618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_8265618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265618 prefixEnd_8265618 := by exact prefixLift 8265618
  have htrace : WordTrace (prefixWord ++ tailWord_8265618) baseStart_8265618 baseEnd_8265618 := by
    simpa [prefixWord, tailWord_8265618, baseEnd_8265618] using wordTrace_append hprefix tailTrace_8265618
  have hstable : (prefixWord ++ tailWord_8265618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265618).length < 2 ^ (prefixWord ++ tailWord_8265618).sum := by decide
  have hdescent : baseEnd_8265618 < baseStart_8265618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265647 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_8265647 : Nat := 118140960795 + 8265647 * 2 ^ 59
def prefixEnd_8265647 : Nat := 4983230072969 + 3 ^ 40 * 8265647 * 2
def baseEnd_8265647 : Nat := 4244249831393727351799487

theorem tailTrace_8265647 : CollatzResearch.WordTrace tailWord_8265647 prefixEnd_8265647 4244249831393727351799487 := by
  unfold tailWord_8265647
  simp only [CollatzResearch.WordTrace]
  refine ⟨301472913085980053964707195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200981942057320035976471463 301472913085980053964707195)
  ·
    refine ⟨452209369628970080947060793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301472913085980053964707195 452209369628970080947060793)
    ·
      refine ⟨339157027221727560710295595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452209369628970080947060793 339157027221727560710295595)
      ·
        refine ⟨508735540832591341065443393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339157027221727560710295595 508735540832591341065443393)
        ·
          refine ⟨381551655624443505799082545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508735540832591341065443393 381551655624443505799082545)
          ·
            refine ⟨286163741718332629349311909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381551655624443505799082545 286163741718332629349311909)
            ·
              refine ⟨53655701572187368002995983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286163741718332629349311909 53655701572187368002995983)
              ·
                refine ⟨80483552358281052004493975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53655701572187368002995983 80483552358281052004493975)
                ·
                  refine ⟨120725328537421578006740963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80483552358281052004493975 120725328537421578006740963)
                  ·
                    refine ⟨181087992806132367010111445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120725328537421578006740963 181087992806132367010111445)
                    ·
                      refine ⟨4244249831393727351799487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181087992806132367010111445 4244249831393727351799487)
                      ·
                        rfl

theorem cell23_8265647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_8265647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265647 prefixEnd_8265647 := by exact prefixLift 8265647
  have htrace : WordTrace (prefixWord ++ tailWord_8265647) baseStart_8265647 baseEnd_8265647 := by
    simpa [prefixWord, tailWord_8265647, baseEnd_8265647] using wordTrace_append hprefix tailTrace_8265647
  have hstable : (prefixWord ++ tailWord_8265647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265647).length < 2 ^ (prefixWord ++ tailWord_8265647).sum := by decide
  have hdescent : baseEnd_8265647 < baseStart_8265647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265652 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_8265652 : Nat := 118140960795 + 8265652 * 2 ^ 59
def prefixEnd_8265652 : Nat := 4983230072969 + 3 ^ 40 * 8265652 * 2
def baseEnd_8265652 : Nat := 4244252398796999832236965

theorem tailTrace_8265652 : CollatzResearch.WordTrace tailWord_8265652 prefixEnd_8265652 4244252398796999832236965 := by
  unfold tailWord_8265652
  simp only [CollatzResearch.WordTrace]
  refine ⟨150736547725480969909319605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200982063633974626545759473 150736547725480969909319605)
  ·
    refine ⟨14131551349263840928998713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150736547725480969909319605 14131551349263840928998713)
    ·
      refine ⟨10598663511947880696749035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14131551349263840928998713 10598663511947880696749035)
      ·
        refine ⟨15897995267921821045123553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598663511947880696749035 15897995267921821045123553)
        ·
          refine ⟨11923496450941365783842665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15897995267921821045123553 11923496450941365783842665)
          ·
            refine ⟨8942622338206024337881999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11923496450941365783842665 8942622338206024337881999)
            ·
              refine ⟨13413933507309036506822999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942622338206024337881999 13413933507309036506822999)
              ·
                refine ⟨20120900260963554760234499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413933507309036506822999 20120900260963554760234499)
                ·
                  refine ⟨30181350391445332140351749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20120900260963554760234499 30181350391445332140351749)
                  ·
                    refine ⟨5659003198395999776315953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30181350391445332140351749 5659003198395999776315953)
                    ·
                      refine ⟨4244252398796999832236965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659003198395999776315953 4244252398796999832236965)
                      ·
                        rfl

theorem cell23_8265652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_8265652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265652 prefixEnd_8265652 := by exact prefixLift 8265652
  have htrace : WordTrace (prefixWord ++ tailWord_8265652) baseStart_8265652 baseEnd_8265652 := by
    simpa [prefixWord, tailWord_8265652, baseEnd_8265652] using wordTrace_append hprefix tailTrace_8265652
  have hstable : (prefixWord ++ tailWord_8265652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265652).length < 2 ^ (prefixWord ++ tailWord_8265652).sum := by decide
  have hdescent : baseEnd_8265652 < baseStart_8265652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265674 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_8265674 : Nat := 118140960795 + 8265674 * 2 ^ 59
def prefixEnd_8265674 : Nat := 4983230072969 + 3 ^ 40 * 8265674 * 2
def baseEnd_8265674 : Nat := 4244263695371398746161863

theorem tailTrace_8265674 : CollatzResearch.WordTrace tailWord_8265674 prefixEnd_8265674 4244263695371398746161863 := by
  unfold tailWord_8265674
  simp only [CollatzResearch.WordTrace]
  refine ⟨75368474464220559393985019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200982598571254825050626717 75368474464220559393985019)
  ·
    refine ⟨113052711696330839090977529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75368474464220559393985019 113052711696330839090977529)
    ·
      refine ⟨84789533772248129318233147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113052711696330839090977529 84789533772248129318233147)
      ·
        refine ⟨127184300658372193977349721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84789533772248129318233147 127184300658372193977349721)
        ·
          refine ⟨95388225493779145483012291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127184300658372193977349721 95388225493779145483012291)
          ·
            refine ⟨143082338240668718224518437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95388225493779145483012291 143082338240668718224518437)
            ·
              refine ⟨26827938420125384667097207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143082338240668718224518437 26827938420125384667097207)
              ·
                refine ⟨40241907630188077000645811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26827938420125384667097207 40241907630188077000645811)
                ·
                  refine ⟨60362861445282115500968717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40241907630188077000645811 60362861445282115500968717)
                  ·
                    refine ⟨22636073041980793312863269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60362861445282115500968717 22636073041980793312863269)
                    ·
                      refine ⟨4244263695371398746161863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22636073041980793312863269 4244263695371398746161863)
                      ·
                        rfl

theorem cell23_8265674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_8265674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265674 prefixEnd_8265674 := by exact prefixLift 8265674
  have htrace : WordTrace (prefixWord ++ tailWord_8265674) baseStart_8265674 baseEnd_8265674 := by
    simpa [prefixWord, tailWord_8265674, baseEnd_8265674] using wordTrace_append hprefix tailTrace_8265674
  have hstable : (prefixWord ++ tailWord_8265674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265674).length < 2 ^ (prefixWord ++ tailWord_8265674).sum := by decide
  have hdescent : baseEnd_8265674 < baseStart_8265674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265692 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 7]
def baseStart_8265692 : Nat := 118140960795 + 8265692 * 2 ^ 59
def prefixEnd_8265692 : Nat := 4983230072969 + 3 ^ 40 * 8265692 * 2
def baseEnd_8265692 : Nat := 471585882002575519526309

theorem tailTrace_8265692 : CollatzResearch.WordTrace tailWord_8265692 prefixEnd_8265692 471585882002575519526309 := by
  unfold tailWord_8265692
  simp only [CollatzResearch.WordTrace]
  refine ⟨150737277185408513325047665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200983036247211351100063553 150737277185408513325047665)
  ·
    refine ⟨113052957889056384993785749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150737277185408513325047665 113052957889056384993785749)
    ·
      refine ⟨5299357401049518046583707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113052957889056384993785749 5299357401049518046583707)
      ·
        refine ⟨7949036101574277069875561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299357401049518046583707 7949036101574277069875561)
        ·
          refine ⟨5961777076180707802406671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949036101574277069875561 5961777076180707802406671)
          ·
            refine ⟨8942665614271061703610007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961777076180707802406671 8942665614271061703610007)
            ·
              refine ⟨13413998421406592555415011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942665614271061703610007 13413998421406592555415011)
              ·
                refine ⟨20120997632109888833122517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413998421406592555415011 20120997632109888833122517)
                ·
                  refine ⟨471585882002575519526309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20120997632109888833122517 471585882002575519526309)
                  ·
                    rfl

theorem cell23_8265692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_8265692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265692 prefixEnd_8265692 := by exact prefixLift 8265692
  have htrace : WordTrace (prefixWord ++ tailWord_8265692) baseStart_8265692 baseEnd_8265692 := by
    simpa [prefixWord, tailWord_8265692, baseEnd_8265692] using wordTrace_append hprefix tailTrace_8265692
  have hstable : (prefixWord ++ tailWord_8265692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265692).length < 2 ^ (prefixWord ++ tailWord_8265692).sum := by decide
  have hdescent : baseEnd_8265692 < baseStart_8265692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265698 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_8265698 : Nat := 118140960795 + 8265698 * 2 ^ 59
def prefixEnd_8265698 : Nat := 4983230072969 + 3 ^ 40 * 8265698 * 2
def baseEnd_8265698 : Nat := 4244276018907106652261753

theorem tailTrace_8265698 : CollatzResearch.WordTrace tailWord_8265698 prefixEnd_8265698 4244276018907106652261753 := by
  unfold tailWord_8265698
  simp only [CollatzResearch.WordTrace]
  refine ⟨75368693302198822418703437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200983182139196859783209165 75368693302198822418703437)
  ·
    refine ⟨28263259988324558407013789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75368693302198822418703437 28263259988324558407013789)
    ·
      refine ⟨10598722495621709402630171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28263259988324558407013789 10598722495621709402630171)
      ·
        refine ⟨15898083743432564103945257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598722495621709402630171 15898083743432564103945257)
        ·
          refine ⟨11923562807574423077958943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15898083743432564103945257 11923562807574423077958943)
          ·
            refine ⟨17885344211361634616938415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923562807574423077958943 17885344211361634616938415)
            ·
              refine ⟨26828016317042451925407623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17885344211361634616938415 26828016317042451925407623)
              ·
                refine ⟨40242024475563677888111435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26828016317042451925407623 40242024475563677888111435)
                ·
                  refine ⟨60363036713345516832167153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40242024475563677888111435 60363036713345516832167153)
                  ·
                    refine ⟨45272277535009137624125365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60363036713345516832167153 45272277535009137624125365)
                    ·
                      refine ⟨4244276018907106652261753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45272277535009137624125365 4244276018907106652261753)
                      ·
                        rfl

theorem cell23_8265698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_8265698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265698 prefixEnd_8265698 := by exact prefixLift 8265698
  have htrace : WordTrace (prefixWord ++ tailWord_8265698) baseStart_8265698 baseEnd_8265698 := by
    simpa [prefixWord, tailWord_8265698, baseEnd_8265698] using wordTrace_append hprefix tailTrace_8265698
  have hstable : (prefixWord ++ tailWord_8265698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265698).length < 2 ^ (prefixWord ++ tailWord_8265698).sum := by decide
  have hdescent : baseEnd_8265698 < baseStart_8265698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265781 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_8265781 : Nat := 118140960795 + 8265781 * 2 ^ 59
def prefixEnd_8265781 : Nat := 4983230072969 + 3 ^ 40 * 8265781 * 2
def baseEnd_8265781 : Nat := 4244318637801429827523871

theorem tailTrace_8265781 : CollatzResearch.WordTrace tailWord_8265781 prefixEnd_8265781 4244318637801429827523871 := by
  unfold tailWord_8265781
  simp only [CollatzResearch.WordTrace]
  refine ⟨301477800467494594850085197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200985200311663063233390131 301477800467494594850085197)
  ·
    refine ⟨113054175175310473068781949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301477800467494594850085197 113054175175310473068781949)
    ·
      refine ⟨42395315690741427400793231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113054175175310473068781949 42395315690741427400793231)
      ·
        refine ⟨63592973536112141101189847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42395315690741427400793231 63592973536112141101189847)
        ·
          refine ⟨95389460304168211651784771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63592973536112141101189847 95389460304168211651784771)
          ·
            refine ⟨143084190456252317477677157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95389460304168211651784771 143084190456252317477677157)
            ·
              refine ⟨26828285710547309527064467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143084190456252317477677157 26828285710547309527064467)
              ·
                refine ⟨40242428565820964290596701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26828285710547309527064467 40242428565820964290596701)
                ·
                  refine ⟨15090910712182861608973763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40242428565820964290596701 15090910712182861608973763)
                  ·
                    refine ⟨22636366068274292413460645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15090910712182861608973763 22636366068274292413460645)
                    ·
                      refine ⟨4244318637801429827523871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22636366068274292413460645 4244318637801429827523871)
                      ·
                        rfl

theorem cell23_8265781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_8265781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265781 prefixEnd_8265781 := by exact prefixLift 8265781
  have htrace : WordTrace (prefixWord ++ tailWord_8265781) baseStart_8265781 baseEnd_8265781 := by
    simpa [prefixWord, tailWord_8265781, baseEnd_8265781] using wordTrace_append hprefix tailTrace_8265781
  have hstable : (prefixWord ++ tailWord_8265781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265781).length < 2 ^ (prefixWord ++ tailWord_8265781).sum := by decide
  have hdescent : baseEnd_8265781 < baseStart_8265781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265849 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 1, 2, 2]
def baseStart_8265849 : Nat := 118140960795 + 8265849 * 2 ^ 59
def prefixEnd_8265849 : Nat := 4983230072969 + 3 ^ 40 * 8265849 * 2
def baseEnd_8265849 : Nat := 4244353554485935561473559

theorem tailTrace_8265849 : CollatzResearch.WordTrace tailWord_8265849 prefixEnd_8265849 4244353554485935561473559 := by
  unfold tailWord_8265849
  simp only [CollatzResearch.WordTrace]
  refine ⟨301480280631248242463560601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200986853754165494975707067 301480280631248242463560601)
  ·
    refine ⟨226110210473436181847670451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301480280631248242463560601 226110210473436181847670451)
    ·
      refine ⟨339165315710154272771505677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226110210473436181847670451 339165315710154272771505677)
      ·
        refine ⟨127186993391307852289314629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339165315710154272771505677 127186993391307852289314629)
        ·
          refine ⟨23847561260870222304246493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127186993391307852289314629 23847561260870222304246493)
          ·
            refine ⟨8942835472826333364092435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23847561260870222304246493 8942835472826333364092435)
            ·
              refine ⟨13414253209239500046138653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942835472826333364092435 13414253209239500046138653)
              ·
                refine ⟨5030344953464812517301995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13414253209239500046138653 5030344953464812517301995)
                ·
                  refine ⟨7545517430197218775952993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030344953464812517301995 7545517430197218775952993)
                  ·
                    refine ⟨5659138072647914081964745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7545517430197218775952993 5659138072647914081964745)
                    ·
                      refine ⟨4244353554485935561473559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659138072647914081964745 4244353554485935561473559)
                      ·
                        rfl

theorem cell23_8265849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_8265849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265849 prefixEnd_8265849 := by exact prefixLift 8265849
  have htrace : WordTrace (prefixWord ++ tailWord_8265849) baseStart_8265849 baseEnd_8265849 := by
    simpa [prefixWord, tailWord_8265849, baseEnd_8265849] using wordTrace_append hprefix tailTrace_8265849
  have hstable : (prefixWord ++ tailWord_8265849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265849).length < 2 ^ (prefixWord ++ tailWord_8265849).sum := by decide
  have hdescent : baseEnd_8265849 < baseStart_8265849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265876 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_8265876 : Nat := 118140960795 + 8265876 * 2 ^ 59
def prefixEnd_8265876 : Nat := 4983230072969 + 3 ^ 40 * 8265876 * 2
def baseEnd_8265876 : Nat := 1414789139487868985278645

theorem tailTrace_8265876 : CollatzResearch.WordTrace tailWord_8265876 prefixEnd_8265876 1414789139487868985278645 := by
  unfold tailWord_8265876
  simp only [CollatzResearch.WordTrace]
  refine ⟨150740632701075213037396741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200987510268100284049862321 150740632701075213037396741)
  ·
    refine ⟨28263868631451602444511889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150740632701075213037396741 28263868631451602444511889)
    ·
      refine ⟨21197901473588701833383917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28263868631451602444511889 21197901473588701833383917)
      ·
        refine ⟨7949213052595763187518969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21197901473588701833383917 7949213052595763187518969)
        ·
          refine ⟨5961909789446822390639227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949213052595763187518969 5961909789446822390639227)
          ·
            refine ⟨8942864684170233585958841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961909789446822390639227 8942864684170233585958841)
            ·
              refine ⟨6707148513127675189469131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8942864684170233585958841 6707148513127675189469131)
              ·
                refine ⟨10060722769691512784203697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6707148513127675189469131 10060722769691512784203697)
                ·
                  refine ⟨7545542077268634588152773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10060722769691512784203697 7545542077268634588152773)
                  ·
                    refine ⟨1414789139487868985278645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7545542077268634588152773 1414789139487868985278645)
                    ·
                      rfl

theorem cell23_8265876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_8265876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265876 prefixEnd_8265876 := by exact prefixLift 8265876
  have htrace : WordTrace (prefixWord ++ tailWord_8265876) baseStart_8265876 baseEnd_8265876 := by
    simpa [prefixWord, tailWord_8265876, baseEnd_8265876] using wordTrace_append hprefix tailTrace_8265876
  have hstable : (prefixWord ++ tailWord_8265876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265876).length < 2 ^ (prefixWord ++ tailWord_8265876).sum := by decide
  have hdescent : baseEnd_8265876 < baseStart_8265876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265882 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_8265882 : Nat := 118140960795 + 8265882 * 2 ^ 59
def prefixEnd_8265882 : Nat := 4983230072969 + 3 ^ 40 * 8265882 * 2
def baseEnd_8265882 : Nat := 4244370499347533932360907

theorem tailTrace_8265882 : CollatzResearch.WordTrace tailWord_8265882 prefixEnd_8265882 4244370499347533932360907 := by
  unfold tailWord_8265882
  simp only [CollatzResearch.WordTrace]
  refine ⟨75370371060032172274877975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200987656160085792733007933 75370371060032172274877975)
  ·
    refine ⟨113055556590048258412316963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75370371060032172274877975 113055556590048258412316963)
    ·
      refine ⟨169583334885072387618475445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113055556590048258412316963 169583334885072387618475445)
      ·
        refine ⟨15898437645475536339232073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169583334885072387618475445 15898437645475536339232073)
        ·
          refine ⟨11923828234106652254424055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15898437645475536339232073 11923828234106652254424055)
          ·
            refine ⟨17885742351159978381636083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923828234106652254424055 17885742351159978381636083)
            ·
              refine ⟨26828613526739967572454125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17885742351159978381636083 26828613526739967572454125)
              ·
                refine ⟨10060730072527487839670297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26828613526739967572454125 10060730072527487839670297)
                ·
                  refine ⟨7545547554395615879752723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10060730072527487839670297 7545547554395615879752723)
                  ·
                    refine ⟨11318321331593423819629085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545547554395615879752723 11318321331593423819629085)
                    ·
                      refine ⟨4244370499347533932360907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11318321331593423819629085 4244370499347533932360907)
                      ·
                        rfl

theorem cell23_8265882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_8265882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265882 prefixEnd_8265882 := by exact prefixLift 8265882
  have htrace : WordTrace (prefixWord ++ tailWord_8265882) baseStart_8265882 baseEnd_8265882 := by
    simpa [prefixWord, tailWord_8265882, baseEnd_8265882] using wordTrace_append hprefix tailTrace_8265882
  have hstable : (prefixWord ++ tailWord_8265882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265882).length < 2 ^ (prefixWord ++ tailWord_8265882).sum := by decide
  have hdescent : baseEnd_8265882 < baseStart_8265882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265938 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_8265938 : Nat := 118140960795 + 8265938 * 2 ^ 59
def prefixEnd_8265938 : Nat := 4983230072969 + 3 ^ 40 * 8265938 * 2
def baseEnd_8265938 : Nat := 4244399254264185713260649

theorem tailTrace_8265938 : CollatzResearch.WordTrace tailWord_8265938 prefixEnd_8265938 4244399254264185713260649 := by
  unfold tailWord_8265938
  simp only [CollatzResearch.WordTrace]
  refine ⟨75370881681981452665887617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200989017818617207109033645 75370881681981452665887617)
  ·
    refine ⟨56528161261486089499415713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75370881681981452665887617 56528161261486089499415713)
    ·
      refine ⟨42396120946114567124561785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56528161261486089499415713 42396120946114567124561785)
      ·
        refine ⟨31797090709585925343421339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42396120946114567124561785 31797090709585925343421339)
        ·
          refine ⟨47695636064378888015132009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31797090709585925343421339 47695636064378888015132009)
          ·
            refine ⟨35771727048284166011349007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47695636064378888015132009 35771727048284166011349007)
            ·
              refine ⟨53657590572426249017023511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35771727048284166011349007 53657590572426249017023511)
              ·
                refine ⟨80486385858639373525535267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53657590572426249017023511 80486385858639373525535267)
                ·
                  refine ⟨120729578787959060288302901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80486385858639373525535267 120729578787959060288302901)
                  ·
                    refine ⟨11318398011371161902028397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120729578787959060288302901 11318398011371161902028397)
                    ·
                      refine ⟨4244399254264185713260649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11318398011371161902028397 4244399254264185713260649)
                      ·
                        rfl

theorem cell23_8265938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_8265938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265938 prefixEnd_8265938 := by exact prefixLift 8265938
  have htrace : WordTrace (prefixWord ++ tailWord_8265938) baseStart_8265938 baseEnd_8265938 := by
    simpa [prefixWord, tailWord_8265938, baseEnd_8265938] using wordTrace_append hprefix tailTrace_8265938
  have hstable : (prefixWord ++ tailWord_8265938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265938).length < 2 ^ (prefixWord ++ tailWord_8265938).sum := by decide
  have hdescent : baseEnd_8265938 < baseStart_8265938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265961 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_8265961 : Nat := 118140960795 + 8265961 * 2 ^ 59
def prefixEnd_8265961 : Nat := 4983230072969 + 3 ^ 40 * 8265961 * 2
def baseEnd_8265961 : Nat := 4244411064319239123273043

theorem tailTrace_8265961 : CollatzResearch.WordTrace tailWord_8265961 prefixEnd_8265961 4244411064319239123273043 := by
  unfold tailWord_8265961
  simp only [CollatzResearch.WordTrace]
  refine ⟨301484365606842485591637737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200989577071228323727758491 301484365606842485591637737)
  ·
    refine ⟨226113274205131864193728303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301484365606842485591637737 226113274205131864193728303)
    ·
      refine ⟨339169911307697796290592455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226113274205131864193728303 339169911307697796290592455)
      ·
        refine ⟨508754866961546694435888683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339169911307697796290592455 508754866961546694435888683)
        ·
          refine ⟨763132300442320041653833025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508754866961546694435888683 763132300442320041653833025)
          ·
            refine ⟨572349225331740031240374769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763132300442320041653833025 572349225331740031240374769)
            ·
              refine ⟨429261918998805023430281077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572349225331740031240374769 429261918998805023430281077)
              ·
                refine ⟨40243304906137970946588851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429261918998805023430281077 40243304906137970946588851)
                ·
                  refine ⟨60364957359206956419883277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40243304906137970946588851 60364957359206956419883277)
                  ·
                    refine ⟨22636859009702608657456229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60364957359206956419883277 22636859009702608657456229)
                    ·
                      refine ⟨4244411064319239123273043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22636859009702608657456229 4244411064319239123273043)
                      ·
                        rfl

theorem cell23_8265961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_8265961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265961 prefixEnd_8265961 := by exact prefixLift 8265961
  have htrace : WordTrace (prefixWord ++ tailWord_8265961) baseStart_8265961 baseEnd_8265961 := by
    simpa [prefixWord, tailWord_8265961, baseEnd_8265961] using wordTrace_append hprefix tailTrace_8265961
  have hstable : (prefixWord ++ tailWord_8265961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265961).length < 2 ^ (prefixWord ++ tailWord_8265961).sum := by decide
  have hdescent : baseEnd_8265961 < baseStart_8265961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265981 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_8265981 : Nat := 118140960795 + 8265981 * 2 ^ 59
def prefixEnd_8265981 : Nat := 4983230072969 + 3 ^ 40 * 8265981 * 2
def baseEnd_8265981 : Nat := 4244421333932329045022951

theorem tailTrace_8265981 : CollatzResearch.WordTrace tailWord_8265981 prefixEnd_8265981 4244421333932329045022951 := by
  unfold tailWord_8265981
  simp only [CollatzResearch.WordTrace]
  refine ⟨301485095066770029007365797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200990063377846686004910531 301485095066770029007365797)
  ·
    refine ⟨56528455325019380438881087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301485095066770029007365797 56528455325019380438881087)
    ·
      refine ⟨84792682987529070658321631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56528455325019380438881087 84792682987529070658321631)
      ·
        refine ⟨127189024481293605987482447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84792682987529070658321631 127189024481293605987482447)
        ·
          refine ⟨190783536721940408981223671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127189024481293605987482447 190783536721940408981223671)
          ·
            refine ⟨286175305082910613471835507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190783536721940408981223671 286175305082910613471835507)
            ·
              refine ⟨429262957624365920207753261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286175305082910613471835507 429262957624365920207753261)
              ·
                refine ⟨160973609109137220077907473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429262957624365920207753261 160973609109137220077907473)
                ·
                  refine ⟨120730206831852915058430605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160973609109137220077907473 120730206831852915058430605)
                  ·
                    refine ⟨45273827561944843146911477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120730206831852915058430605 45273827561944843146911477)
                    ·
                      refine ⟨4244421333932329045022951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45273827561944843146911477 4244421333932329045022951)
                      ·
                        rfl

theorem cell23_8265981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_8265981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265981 prefixEnd_8265981 := by exact prefixLift 8265981
  have htrace : WordTrace (prefixWord ++ tailWord_8265981) baseStart_8265981 baseEnd_8265981 := by
    simpa [prefixWord, tailWord_8265981, baseEnd_8265981] using wordTrace_append hprefix tailTrace_8265981
  have hstable : (prefixWord ++ tailWord_8265981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265981).length < 2 ^ (prefixWord ++ tailWord_8265981).sum := by decide
  have hdescent : baseEnd_8265981 < baseStart_8265981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8265998 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_8265998 : Nat := 118140960795 + 8265998 * 2 ^ 59
def prefixEnd_8265998 : Nat := 4983230072969 + 3 ^ 40 * 8265998 * 2
def baseEnd_8265998 : Nat := 4244430063103455478510373

theorem tailTrace_8265998 : CollatzResearch.WordTrace tailWord_8265998 prefixEnd_8265998 4244430063103455478510373 := by
  unfold tailWord_8265998
  simp only [CollatzResearch.WordTrace]
  refine ⟨37685714388463555113841831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200990476738472293940489765 37685714388463555113841831)
  ·
    refine ⟨56528571582695332670762747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37685714388463555113841831 56528571582695332670762747)
    ·
      refine ⟨84792857374042999006144121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56528571582695332670762747 84792857374042999006144121)
      ·
        refine ⟨63594643030532249254608091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84792857374042999006144121 63594643030532249254608091)
        ·
          refine ⟨95391964545798373881912137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63594643030532249254608091 95391964545798373881912137)
          ·
            refine ⟨71543973409348780411434103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95391964545798373881912137 71543973409348780411434103)
            ·
              refine ⟨107315960114023170617151155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71543973409348780411434103 107315960114023170617151155)
              ·
                refine ⟨160973940171034755925726733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107315960114023170617151155 160973940171034755925726733)
                ·
                  refine ⟨60365227564138033472147525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160973940171034755925726733 60365227564138033472147525)
                  ·
                    refine ⟨11318480168275881276027661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60365227564138033472147525 11318480168275881276027661)
                    ·
                      refine ⟨4244430063103455478510373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11318480168275881276027661 4244430063103455478510373)
                      ·
                        rfl

theorem cell23_8265998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_8265998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8265998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8265998 prefixEnd_8265998 := by exact prefixLift 8265998
  have htrace : WordTrace (prefixWord ++ tailWord_8265998) baseStart_8265998 baseEnd_8265998 := by
    simpa [prefixWord, tailWord_8265998, baseEnd_8265998] using wordTrace_append hprefix tailTrace_8265998
  have hstable : (prefixWord ++ tailWord_8265998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8265998).length < 2 ^ (prefixWord ++ tailWord_8265998).sum := by decide
  have hdescent : baseEnd_8265998 < baseStart_8265998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8265998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266018 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_8266018 : Nat := 118140960795 + 8266018 * 2 ^ 59
def prefixEnd_8266018 : Nat := 4983230072969 + 3 ^ 40 * 8266018 * 2
def baseEnd_8266018 : Nat := 471604481412949488917809

theorem tailTrace_8266018 : CollatzResearch.WordTrace tailWord_8266018 prefixEnd_8266018 471604481412949488917809 := by
  unfold tailWord_8266018
  simp only [CollatzResearch.WordTrace]
  refine ⟨75371611141908996081615677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200990963045090656217641805 75371611141908996081615677)
  ·
    refine ⟨28264354178215873530605879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75371611141908996081615677 28264354178215873530605879)
    ·
      refine ⟨42396531267323810295908819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28264354178215873530605879 42396531267323810295908819)
      ·
        refine ⟨63594796900985715443863229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42396531267323810295908819 63594796900985715443863229)
        ·
          refine ⟨23848048837869643291448711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63594796900985715443863229 23848048837869643291448711)
          ·
            refine ⟨35772073256804464937173067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23848048837869643291448711 35772073256804464937173067)
            ·
              refine ⟨53658109885206697405759601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35772073256804464937173067 53658109885206697405759601)
              ·
                refine ⟨40243582413905023054319701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53658109885206697405759601 40243582413905023054319701)
                ·
                  refine ⟨471604481412949488917809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40243582413905023054319701 471604481412949488917809)
                  ·
                    rfl

theorem cell23_8266018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_8266018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266018 prefixEnd_8266018 := by exact prefixLift 8266018
  have htrace : WordTrace (prefixWord ++ tailWord_8266018) baseStart_8266018 baseEnd_8266018 := by
    simpa [prefixWord, tailWord_8266018, baseEnd_8266018] using wordTrace_append hprefix tailTrace_8266018
  have hstable : (prefixWord ++ tailWord_8266018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266018).length < 2 ^ (prefixWord ++ tailWord_8266018).sum := by decide
  have hdescent : baseEnd_8266018 < baseStart_8266018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266052 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 6]
def baseStart_8266052 : Nat := 118140960795 + 8266052 * 2 ^ 59
def prefixEnd_8266052 : Nat := 4983230072969 + 3 ^ 40 * 8266052 * 2
def baseEnd_8266052 : Nat := 471606421228755363026125

theorem tailTrace_8266052 : CollatzResearch.WordTrace tailWord_8266052 prefixEnd_8266052 471606421228755363026125 := by
  unfold tailWord_8266052
  simp only [CollatzResearch.WordTrace]
  refine ⟨150743842324756404066600205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200991789766341872088800273 150743842324756404066600205)
  ·
    refine ⟨56528940871783651524975077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150743842324756404066600205 56528940871783651524975077)
    ·
      refine ⟨10599176413459434660932827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56528940871783651524975077 10599176413459434660932827)
      ·
        refine ⟨15898764620189151991399241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599176413459434660932827 15898764620189151991399241)
        ·
          refine ⟨11924073465141863993549431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15898764620189151991399241 11924073465141863993549431)
          ·
            refine ⟨17886110197712795990324147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924073465141863993549431 17886110197712795990324147)
            ·
              refine ⟨26829165296569193985486221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17886110197712795990324147 26829165296569193985486221)
              ·
                refine ⟨10060936986213447744557333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26829165296569193985486221 10060936986213447744557333)
                ·
                  refine ⟨471606421228755363026125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10060936986213447744557333 471606421228755363026125)
                  ·
                    rfl

theorem cell23_8266052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_8266052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266052 prefixEnd_8266052 := by exact prefixLift 8266052
  have htrace : WordTrace (prefixWord ++ tailWord_8266052) baseStart_8266052 baseEnd_8266052 := by
    simpa [prefixWord, tailWord_8266052, baseEnd_8266052] using wordTrace_append hprefix tailTrace_8266052
  have hstable : (prefixWord ++ tailWord_8266052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266052).length < 2 ^ (prefixWord ++ tailWord_8266052).sum := by decide
  have hdescent : baseEnd_8266052 < baseStart_8266052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266055 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_8266055 : Nat := 118140960795 + 8266055 * 2 ^ 59
def prefixEnd_8266055 : Nat := 4983230072969 + 3 ^ 40 * 8266055 * 2
def baseEnd_8266055 : Nat := 4244459331500761755497611

theorem tailTrace_8266055 : CollatzResearch.WordTrace tailWord_8266055 prefixEnd_8266055 4244459331500761755497611 := by
  unfold tailWord_8266055
  simp only [CollatzResearch.WordTrace]
  refine ⟨301487794068501939645559619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200991862712334626430373079 301487794068501939645559619)
  ·
    refine ⟨452231691102752909468339429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301487794068501939645559619 452231691102752909468339429)
    ·
      refine ⟨84793442081766170525313643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452231691102752909468339429 84793442081766170525313643)
      ·
        refine ⟨127190163122649255787970465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84793442081766170525313643 127190163122649255787970465)
        ·
          refine ⟨95392622341986941840977849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127190163122649255787970465 95392622341986941840977849)
          ·
            refine ⟨71544466756490206380733387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95392622341986941840977849 71544466756490206380733387)
            ·
              refine ⟨107316700134735309571100081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71544466756490206380733387 107316700134735309571100081)
              ·
                refine ⟨80487525101051482178325061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107316700134735309571100081 80487525101051482178325061)
                ·
                  refine ⟨15091410956447152908435949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80487525101051482178325061 15091410956447152908435949)
                  ·
                    refine ⟨5659279108667682340663481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15091410956447152908435949 5659279108667682340663481)
                    ·
                      refine ⟨4244459331500761755497611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659279108667682340663481 4244459331500761755497611)
                      ·
                        rfl

theorem cell23_8266055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_8266055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266055 prefixEnd_8266055 := by exact prefixLift 8266055
  have htrace : WordTrace (prefixWord ++ tailWord_8266055) baseStart_8266055 baseEnd_8266055 := by
    simpa [prefixWord, tailWord_8266055, baseEnd_8266055] using wordTrace_append hprefix tailTrace_8266055
  have hstable : (prefixWord ++ tailWord_8266055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266055).length < 2 ^ (prefixWord ++ tailWord_8266055).sum := by decide
  have hdescent : baseEnd_8266055 < baseStart_8266055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266065 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 1, 5]
def baseStart_8266065 : Nat := 118140960795 + 8266065 * 2 ^ 59
def prefixEnd_8266065 : Nat := 4983230072969 + 3 ^ 40 * 8266065 * 2
def baseEnd_8266065 : Nat := 1414821488769102238790855

theorem tailTrace_8266065 : CollatzResearch.WordTrace tailWord_8266065 prefixEnd_8266065 1414821488769102238790855 := by
  unfold tailWord_8266065
  simp only [CollatzResearch.WordTrace]
  refine ⟨301488158798465711353423649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200992105865643807568949099 301488158798465711353423649)
  ·
    refine ⟨226116119098849283515067737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301488158798465711353423649 226116119098849283515067737)
    ·
      refine ⟨169587089324136962636300803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226116119098849283515067737 169587089324136962636300803)
      ·
        refine ⟨254380633986205443954451205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169587089324136962636300803 254380633986205443954451205)
        ·
          refine ⟨47696368872413520741459601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254380633986205443954451205 47696368872413520741459601)
          ·
            refine ⟨35772276654310140556094701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47696368872413520741459601 35772276654310140556094701)
            ·
              refine ⟨13414603745366302708535513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35772276654310140556094701 13414603745366302708535513)
              ·
                refine ⟨10060952809024727031401635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13414603745366302708535513 10060952809024727031401635)
                ·
                  refine ⟨15091429213537090547102453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10060952809024727031401635 15091429213537090547102453)
                  ·
                    refine ⟨1414821488769102238790855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15091429213537090547102453 1414821488769102238790855)
                    ·
                      rfl

theorem cell23_8266065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_8266065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266065 prefixEnd_8266065 := by exact prefixLift 8266065
  have htrace : WordTrace (prefixWord ++ tailWord_8266065) baseStart_8266065 baseEnd_8266065 := by
    simpa [prefixWord, tailWord_8266065, baseEnd_8266065] using wordTrace_append hprefix tailTrace_8266065
  have hstable : (prefixWord ++ tailWord_8266065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266065).length < 2 ^ (prefixWord ++ tailWord_8266065).sum := by decide
  have hdescent : baseEnd_8266065 < baseStart_8266065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266096 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 1, 1, 3]
def baseStart_8266096 : Nat := 118140960795 + 8266096 * 2 ^ 59
def prefixEnd_8266096 : Nat := 4983230072969 + 3 ^ 40 * 8266096 * 2
def baseEnd_8266096 : Nat := 4244480384207596095084923

theorem tailTrace_8266096 : CollatzResearch.WordTrace tailWord_8266096 prefixEnd_8266096 4244480384207596095084923 := by
  unfold tailWord_8266096
  simp only [CollatzResearch.WordTrace]
  refine ⟨150744644730676701823901071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200992859640902269098534761 150744644730676701823901071)
  ·
    refine ⟨226116967096015052735851607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150744644730676701823901071 226116967096015052735851607)
    ·
      refine ⟨339175450644022579103777411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226116967096015052735851607 339175450644022579103777411)
      ·
        refine ⟨508763175966033868655666117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339175450644022579103777411 508763175966033868655666117)
        ·
          refine ⟨95393095493631350372937397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508763175966033868655666117 95393095493631350372937397)
          ·
            refine ⟨8943102702527939097462881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95393095493631350372937397 8943102702527939097462881)
            ·
              refine ⟨6707327026895954323097161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8943102702527939097462881 6707327026895954323097161)
              ·
                refine ⟨5030495270171965742322871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707327026895954323097161 5030495270171965742322871)
                ·
                  refine ⟨7545742905257948613484307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030495270171965742322871 7545742905257948613484307)
                  ·
                    refine ⟨11318614357886922920226461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545742905257948613484307 11318614357886922920226461)
                    ·
                      refine ⟨4244480384207596095084923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11318614357886922920226461 4244480384207596095084923)
                      ·
                        rfl

theorem cell23_8266096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 1, 3].length) (baseStart_8266096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266096 prefixEnd_8266096 := by exact prefixLift 8266096
  have htrace : WordTrace (prefixWord ++ tailWord_8266096) baseStart_8266096 baseEnd_8266096 := by
    simpa [prefixWord, tailWord_8266096, baseEnd_8266096] using wordTrace_append hprefix tailTrace_8266096
  have hstable : (prefixWord ++ tailWord_8266096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266096).length < 2 ^ (prefixWord ++ tailWord_8266096).sum := by decide
  have hdescent : baseEnd_8266096 < baseStart_8266096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266135 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_8266135 : Nat := 118140960795 + 8266135 * 2 ^ 59
def prefixEnd_8266135 : Nat := 4983230072969 + 3 ^ 40 * 8266135 * 2
def baseEnd_8266135 : Nat := 4244500409953121442497243

theorem tailTrace_8266135 : CollatzResearch.WordTrace tailWord_8266135 prefixEnd_8266135 4244500409953121442497243 := by
  unfold tailWord_8266135
  simp only [CollatzResearch.WordTrace]
  refine ⟨301490711908212113308471859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200993807938808075538981239 301490711908212113308471859)
  ·
    refine ⟨452236067862318169962707789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301490711908212113308471859 452236067862318169962707789)
    ·
      refine ⟨169588525448369313736015421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452236067862318169962707789 169588525448369313736015421)
      ·
        refine ⟨63595697043138492651005783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169588525448369313736015421 63595697043138492651005783)
        ·
          refine ⟨95393545564707738976508675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63595697043138492651005783 95393545564707738976508675)
          ·
            refine ⟨143090318347061608464763013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95393545564707738976508675 143090318347061608464763013)
            ·
              refine ⟨26829434690074051587143065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143090318347061608464763013 26829434690074051587143065)
              ·
                refine ⟨20122076017555538690357299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26829434690074051587143065 20122076017555538690357299)
                ·
                  refine ⟨30183114026333308035535949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20122076017555538690357299 30183114026333308035535949)
                  ·
                    refine ⟨11318667759874990513325981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30183114026333308035535949 11318667759874990513325981)
                    ·
                      refine ⟨4244500409953121442497243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11318667759874990513325981 4244500409953121442497243)
                      ·
                        rfl

theorem cell23_8266135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_8266135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266135 prefixEnd_8266135 := by exact prefixLift 8266135
  have htrace : WordTrace (prefixWord ++ tailWord_8266135) baseStart_8266135 baseEnd_8266135 := by
    simpa [prefixWord, tailWord_8266135, baseEnd_8266135] using wordTrace_append hprefix tailTrace_8266135
  have hstable : (prefixWord ++ tailWord_8266135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266135).length < 2 ^ (prefixWord ++ tailWord_8266135).sum := by decide
  have hdescent : baseEnd_8266135 < baseStart_8266135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266136 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 1, 2, 2]
def baseStart_8266136 : Nat := 118140960795 + 8266136 * 2 ^ 59
def prefixEnd_8266136 : Nat := 4983230072969 + 3 ^ 40 * 8266136 * 2
def baseEnd_8266136 : Nat := 4244500923433775938584739

theorem tailTrace_8266136 : CollatzResearch.WordTrace tailWord_8266136 prefixEnd_8266136 4244500923433775938584739 := by
  unfold tailWord_8266136
  simp only [CollatzResearch.WordTrace]
  refine ⟨150745374190604245239629131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200993832254138993652838841 150745374190604245239629131)
  ·
    refine ⟨226118061285906367859443697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150745374190604245239629131 226118061285906367859443697)
    ·
      refine ⟨169588545964429775894582773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226118061285906367859443697 169588545964429775894582773)
      ·
        refine ⟨15898926184165291490117135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169588545964429775894582773 15898926184165291490117135)
        ·
          refine ⟨23848389276247937235175703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15898926184165291490117135 23848389276247937235175703)
          ·
            refine ⟨35772583914371905852763555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23848389276247937235175703 35772583914371905852763555)
            ·
              refine ⟨53658875871557858779145333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35772583914371905852763555 53658875871557858779145333)
              ·
                refine ⟨5030519612958549260544875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53658875871557858779145333 5030519612958549260544875)
                ·
                  refine ⟨7545779419437823890817313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030519612958549260544875 7545779419437823890817313)
                  ·
                    refine ⟨5659334564578367918112985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7545779419437823890817313 5659334564578367918112985)
                    ·
                      refine ⟨4244500923433775938584739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659334564578367918112985 4244500923433775938584739)
                      ·
                        rfl

theorem cell23_8266136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_8266136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266136 prefixEnd_8266136 := by exact prefixLift 8266136
  have htrace : WordTrace (prefixWord ++ tailWord_8266136) baseStart_8266136 baseEnd_8266136 := by
    simpa [prefixWord, tailWord_8266136, baseEnd_8266136] using wordTrace_append hprefix tailTrace_8266136
  have hstable : (prefixWord ++ tailWord_8266136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266136).length < 2 ^ (prefixWord ++ tailWord_8266136).sum := by decide
  have hdescent : baseEnd_8266136 < baseStart_8266136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266208 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_8266208 : Nat := 118140960795 + 8266208 * 2 ^ 59
def prefixEnd_8266208 : Nat := 4983230072969 + 3 ^ 40 * 8266208 * 2
def baseEnd_8266208 : Nat := 4244537894040899656884407

theorem tailTrace_8266208 : CollatzResearch.WordTrace tailWord_8266208 prefixEnd_8266208 4244537894040899656884407 := by
  unfold tailWord_8266208
  simp only [CollatzResearch.WordTrace]
  refine ⟨150746687218473823387939639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200995582957965097850586185 150746687218473823387939639)
  ·
    refine ⟨226120030827710735081909459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150746687218473823387939639 226120030827710735081909459)
    ·
      refine ⟨339180046241566102622864189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226120030827710735081909459 339180046241566102622864189)
      ·
        refine ⟨127192517340587288483574071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339180046241566102622864189 127192517340587288483574071)
        ·
          refine ⟨190788776010880932725361107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127192517340587288483574071 190788776010880932725361107)
          ·
            refine ⟨286183164016321399088041661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190788776010880932725361107 286183164016321399088041661)
            ·
              refine ⟨107318686506120524658015623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286183164016321399088041661 107318686506120524658015623)
              ·
                refine ⟨160978029759180786987023435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107318686506120524658015623 160978029759180786987023435)
                ·
                  refine ⟨241467044638771180480535153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160978029759180786987023435 241467044638771180480535153)
                  ·
                    refine ⟨181100283479078385360401365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241467044638771180480535153 181100283479078385360401365)
                    ·
                      refine ⟨4244537894040899656884407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181100283479078385360401365 4244537894040899656884407)
                      ·
                        rfl

theorem cell23_8266208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_8266208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266208 prefixEnd_8266208 := by exact prefixLift 8266208
  have htrace : WordTrace (prefixWord ++ tailWord_8266208) baseStart_8266208 baseEnd_8266208 := by
    simpa [prefixWord, tailWord_8266208, baseEnd_8266208] using wordTrace_append hprefix tailTrace_8266208
  have hstable : (prefixWord ++ tailWord_8266208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266208).length < 2 ^ (prefixWord ++ tailWord_8266208).sum := by decide
  have hdescent : baseEnd_8266208 < baseStart_8266208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266209 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_8266209 : Nat := 118140960795 + 8266209 * 2 ^ 59
def prefixEnd_8266209 : Nat := 4983230072969 + 3 ^ 40 * 8266209 * 2
def baseEnd_8266209 : Nat := 4244538407521554152971903

theorem tailTrace_8266209 : CollatzResearch.WordTrace tailWord_8266209 prefixEnd_8266209 4244538407521554152971903 := by
  unfold tailWord_8266209
  simp only [CollatzResearch.WordTrace]
  refine ⟨301493410909944023946665681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200995607273296015964443787 301493410909944023946665681)
  ·
    refine ⟨226120058182458017959999261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301493410909944023946665681 226120058182458017959999261)
    ·
      refine ⟨84795021818421756734999723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226120058182458017959999261 84795021818421756734999723)
      ·
        refine ⟨127192532727632635102499585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84795021818421756734999723 127192532727632635102499585)
        ·
          refine ⟨95394399545724476326874689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127192532727632635102499585 95394399545724476326874689)
          ·
            refine ⟨71545799659293357245156017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95394399545724476326874689 71545799659293357245156017)
            ·
              refine ⟨53659349744470017933867013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71545799659293357245156017 53659349744470017933867013)
              ·
                refine ⟨10061128077088128362600065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53659349744470017933867013 10061128077088128362600065)
                ·
                  refine ⟨7545846057816096271950049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10061128077088128362600065 7545846057816096271950049)
                  ·
                    refine ⟨5659384543362072203962537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7545846057816096271950049 5659384543362072203962537)
                    ·
                      refine ⟨4244538407521554152971903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659384543362072203962537 4244538407521554152971903)
                      ·
                        rfl

theorem cell23_8266209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_8266209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266209 prefixEnd_8266209 := by exact prefixLift 8266209
  have htrace : WordTrace (prefixWord ++ tailWord_8266209) baseStart_8266209 baseEnd_8266209 := by
    simpa [prefixWord, tailWord_8266209, baseEnd_8266209] using wordTrace_append hprefix tailTrace_8266209
  have hstable : (prefixWord ++ tailWord_8266209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266209).length < 2 ^ (prefixWord ++ tailWord_8266209).sum := by decide
  have hdescent : baseEnd_8266209 < baseStart_8266209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266225 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_8266225 : Nat := 118140960795 + 8266225 * 2 ^ 59
def prefixEnd_8266225 : Nat := 4983230072969 + 3 ^ 40 * 8266225 * 2
def baseEnd_8266225 : Nat := 4244546623212026090371829

theorem tailTrace_8266225 : CollatzResearch.WordTrace tailWord_8266225 prefixEnd_8266225 4244546623212026090371829 := by
  unfold tailWord_8266225
  simp only [CollatzResearch.WordTrace]
  refine ⟨301493994477886058679248129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200995996318590705786165419 301493994477886058679248129)
  ·
    refine ⟨226120495858414544009436097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301493994477886058679248129 226120495858414544009436097)
    ·
      refine ⟨169590371893810908007077073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226120495858414544009436097 169590371893810908007077073)
      ·
        refine ⟨127192778920358181005307805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169590371893810908007077073 127192778920358181005307805)
        ·
          refine ⟨47697292095134317876990427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127192778920358181005307805 47697292095134317876990427)
          ·
            refine ⟨71545938142701476815485641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47697292095134317876990427 71545938142701476815485641)
            ·
              refine ⟨53659453607026107611614231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71545938142701476815485641 53659453607026107611614231)
              ·
                refine ⟨80489180410539161417421347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53659453607026107611614231 80489180410539161417421347)
                ·
                  refine ⟨120733770615808742126132021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80489180410539161417421347 120733770615808742126132021)
                  ·
                    refine ⟨11318790995232069574324877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120733770615808742126132021 11318790995232069574324877)
                    ·
                      refine ⟨4244546623212026090371829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11318790995232069574324877 4244546623212026090371829)
                      ·
                        rfl

theorem cell23_8266225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_8266225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266225 prefixEnd_8266225 := by exact prefixLift 8266225
  have htrace : WordTrace (prefixWord ++ tailWord_8266225) baseStart_8266225 baseEnd_8266225 := by
    simpa [prefixWord, tailWord_8266225, baseEnd_8266225] using wordTrace_append hprefix tailTrace_8266225
  have hstable : (prefixWord ++ tailWord_8266225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266225).length < 2 ^ (prefixWord ++ tailWord_8266225).sum := by decide
  have hdescent : baseEnd_8266225 < baseStart_8266225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266245 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_8266245 : Nat := 118140960795 + 8266245 * 2 ^ 59
def prefixEnd_8266245 : Nat := 4983230072969 + 3 ^ 40 * 8266245 * 2
def baseEnd_8266245 : Nat := 1414852297608372004040579

theorem tailTrace_8266245 : CollatzResearch.WordTrace tailWord_8266245 prefixEnd_8266245 1414852297608372004040579 := by
  unfold tailWord_8266245
  simp only [CollatzResearch.WordTrace]
  refine ⟨301494723937813602094976189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200996482625209068063317459 301494723937813602094976189)
  ·
    refine ⟨113060521476680100785616071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301494723937813602094976189 113060521476680100785616071)
    ·
      refine ⟨169590782215020151178424107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113060521476680100785616071 169590782215020151178424107)
      ·
        refine ⟨254386173322530226767636161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169590782215020151178424107 254386173322530226767636161)
        ·
          refine ⟨190789629991897670075727121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254386173322530226767636161 190789629991897670075727121)
          ·
            refine ⟨143092222493923252556795341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190789629991897670075727121 143092222493923252556795341)
            ·
              refine ⟨53659583435221219708798253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143092222493923252556795341 53659583435221219708798253)
              ·
                refine ⟨20122343788207957390799345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53659583435221219708798253 20122343788207957390799345)
                ·
                  refine ⟨15091757841155968043099509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20122343788207957390799345 15091757841155968043099509)
                  ·
                    refine ⟨1414852297608372004040579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15091757841155968043099509 1414852297608372004040579)
                    ·
                      rfl

theorem cell23_8266245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_8266245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266245 prefixEnd_8266245 := by exact prefixLift 8266245
  have htrace : WordTrace (prefixWord ++ tailWord_8266245) baseStart_8266245 baseEnd_8266245 := by
    simpa [prefixWord, tailWord_8266245, baseEnd_8266245] using wordTrace_append hprefix tailTrace_8266245
  have hstable : (prefixWord ++ tailWord_8266245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266245).length < 2 ^ (prefixWord ++ tailWord_8266245).sum := by decide
  have hdescent : baseEnd_8266245 < baseStart_8266245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266246 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_8266246 : Nat := 118140960795 + 8266246 * 2 ^ 59
def prefixEnd_8266246 : Nat := 4983230072969 + 3 ^ 40 * 8266246 * 2
def baseEnd_8266246 : Nat := 4244557406305770508209233

theorem tailTrace_8266246 : CollatzResearch.WordTrace tailWord_8266246 prefixEnd_8266246 4244557406305770508209233 := by
  unfold tailWord_8266246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421711262837811852055081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200996506940539986177175061 9421711262837811852055081)
  ·
    refine ⟨7066283447128358889041311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9421711262837811852055081 7066283447128358889041311)
    ·
      refine ⟨10599425170692538333561967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066283447128358889041311 10599425170692538333561967)
      ·
        refine ⟨15899137756038807500342951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599425170692538333561967 15899137756038807500342951)
        ·
          refine ⟨23848706634058211250514427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15899137756038807500342951 23848706634058211250514427)
          ·
            refine ⟨35773059951087316875771641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23848706634058211250514427 35773059951087316875771641)
            ·
              refine ⟨26829794963315487656828731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35773059951087316875771641 26829794963315487656828731)
              ·
                refine ⟨40244692444973231485243097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26829794963315487656828731 40244692444973231485243097)
                ·
                  refine ⟨30183519333729923613932323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40244692444973231485243097 30183519333729923613932323)
                  ·
                    refine ⟨45275279000594885420898485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30183519333729923613932323 45275279000594885420898485)
                    ·
                      refine ⟨4244557406305770508209233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45275279000594885420898485 4244557406305770508209233)
                      ·
                        rfl

theorem cell23_8266246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_8266246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266246 prefixEnd_8266246 := by exact prefixLift 8266246
  have htrace : WordTrace (prefixWord ++ tailWord_8266246) baseStart_8266246 baseEnd_8266246 := by
    simpa [prefixWord, tailWord_8266246, baseEnd_8266246] using wordTrace_append hprefix tailTrace_8266246
  have hstable : (prefixWord ++ tailWord_8266246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266246).length < 2 ^ (prefixWord ++ tailWord_8266246).sum := by decide
  have hdescent : baseEnd_8266246 < baseStart_8266246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266309 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_8266309 : Nat := 118140960795 + 8266309 * 2 ^ 59
def prefixEnd_8266309 : Nat := 4983230072969 + 3 ^ 40 * 8266309 * 2
def baseEnd_8266309 : Nat := 1414863251862334587240481

theorem tailTrace_8266309 : CollatzResearch.WordTrace tailWord_8266309 prefixEnd_8266309 1414863251862334587240481 := by
  unfold tailWord_8266309
  simp only [CollatzResearch.WordTrace]
  refine ⟨301497058209581741025305981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200998038806387827350203987 301497058209581741025305981)
  ·
    refine ⟨113061396828593152884489743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301497058209581741025305981 113061396828593152884489743)
    ·
      refine ⟨169592095242889729326734615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113061396828593152884489743 169592095242889729326734615)
      ·
        refine ⟨254388142864334593990101923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169592095242889729326734615 254388142864334593990101923)
        ·
          refine ⟨381582214296501890985152885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254388142864334593990101923 381582214296501890985152885)
          ·
            refine ⟨35773332590297052279858083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 381582214296501890985152885 35773332590297052279858083)
            ·
              refine ⟨53659998885445578419787125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35773332590297052279858083 53659998885445578419787125)
              ·
                refine ⟨5030624895510522976855043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53659998885445578419787125 5030624895510522976855043)
                ·
                  refine ⟨7545937343265784465282565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030624895510522976855043 7545937343265784465282565)
                  ·
                    refine ⟨1414863251862334587240481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7545937343265784465282565 1414863251862334587240481)
                    ·
                      rfl

theorem cell23_8266309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_8266309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266309 prefixEnd_8266309 := by exact prefixLift 8266309
  have htrace : WordTrace (prefixWord ++ tailWord_8266309) baseStart_8266309 baseEnd_8266309 := by
    simpa [prefixWord, tailWord_8266309, baseEnd_8266309] using wordTrace_append hprefix tailTrace_8266309
  have hstable : (prefixWord ++ tailWord_8266309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266309).length < 2 ^ (prefixWord ++ tailWord_8266309).sum := by decide
  have hdescent : baseEnd_8266309 < baseStart_8266309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266325 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_8266325 : Nat := 118140960795 + 8266325 * 2 ^ 59
def prefixEnd_8266325 : Nat := 4983230072969 + 3 ^ 40 * 8266325 * 2
def baseEnd_8266325 : Nat := 4244597971277475699121369

theorem tailTrace_8266325 : CollatzResearch.WordTrace tailWord_8266325 prefixEnd_8266325 4244597971277475699121369 := by
  unfold tailWord_8266325
  simp only [CollatzResearch.WordTrace]
  refine ⟨301497641777523775757888429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200998427851682517171925619 301497641777523775757888429)
  ·
    refine ⟨113061615666571415909208161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301497641777523775757888429 113061615666571415909208161)
    ·
      refine ⟨84796211749928561931906121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113061615666571415909208161 84796211749928561931906121)
      ·
        refine ⟨63597158812446421448929591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84796211749928561931906121 63597158812446421448929591)
        ·
          refine ⟨95395738218669632173394387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63597158812446421448929591 95395738218669632173394387)
          ·
            refine ⟨143093607328004448260091581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95395738218669632173394387 143093607328004448260091581)
            ·
              refine ⟨53660102748001668097534343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143093607328004448260091581 53660102748001668097534343)
              ·
                refine ⟨80490154122002502146301515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53660102748001668097534343 80490154122002502146301515)
                ·
                  refine ⟨120735231183003753219452273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80490154122002502146301515 120735231183003753219452273)
                  ·
                    refine ⟨90551423387252814914589205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120735231183003753219452273 90551423387252814914589205)
                    ·
                      refine ⟨4244597971277475699121369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90551423387252814914589205 4244597971277475699121369)
                      ·
                        rfl

theorem cell23_8266325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_8266325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266325 prefixEnd_8266325 := by exact prefixLift 8266325
  have htrace : WordTrace (prefixWord ++ tailWord_8266325) baseStart_8266325 baseEnd_8266325 := by
    simpa [prefixWord, tailWord_8266325, baseEnd_8266325] using wordTrace_append hprefix tailTrace_8266325
  have hstable : (prefixWord ++ tailWord_8266325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266325).length < 2 ^ (prefixWord ++ tailWord_8266325).sum := by decide
  have hdescent : baseEnd_8266325 < baseStart_8266325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266335 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 5, 5]
def baseStart_8266335 : Nat := 118140960795 + 8266335 * 2 ^ 59
def prefixEnd_8266335 : Nat := 4983230072969 + 3 ^ 40 * 8266335 * 2
def baseEnd_8266335 : Nat := 1414867702028006886665441

theorem tailTrace_8266335 : CollatzResearch.WordTrace tailWord_8266335 prefixEnd_8266335 1414867702028006886665441 := by
  unfold tailWord_8266335
  simp only [CollatzResearch.WordTrace]
  refine ⟨301498006507487547465752459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200998671004991698310501639 301498006507487547465752459)
  ·
    refine ⟨452247009761231321198628689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301498006507487547465752459 452247009761231321198628689)
    ·
      refine ⟨339185257320923490898971517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452247009761231321198628689 339185257320923490898971517)
      ·
        refine ⟨127194471495346309087114319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339185257320923490898971517 127194471495346309087114319)
        ·
          refine ⟨190791707243019463630671479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127194471495346309087114319 190791707243019463630671479)
          ·
            refine ⟨286187560864529195446007219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190791707243019463630671479 286187560864529195446007219)
            ·
              refine ⟨429281341296793793169010829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286187560864529195446007219 429281341296793793169010829)
              ·
                refine ⟨160980502986297672438379061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429281341296793793169010829 160980502986297672438379061)
                ·
                  refine ⟨15091922154965406791098037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160980502986297672438379061 15091922154965406791098037)
                  ·
                    refine ⟨1414867702028006886665441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15091922154965406791098037 1414867702028006886665441)
                    ·
                      rfl

theorem cell23_8266335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_8266335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266335 prefixEnd_8266335 := by exact prefixLift 8266335
  have htrace : WordTrace (prefixWord ++ tailWord_8266335) baseStart_8266335 baseEnd_8266335 := by
    simpa [prefixWord, tailWord_8266335, baseEnd_8266335] using wordTrace_append hprefix tailTrace_8266335
  have hstable : (prefixWord ++ tailWord_8266335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266335).length < 2 ^ (prefixWord ++ tailWord_8266335).sum := by decide
  have hdescent : baseEnd_8266335 < baseStart_8266335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266370 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8266370 : Nat := 118140960795 + 8266370 * 2 ^ 59
def prefixEnd_8266370 : Nat := 4983230072969 + 3 ^ 40 * 8266370 * 2
def baseEnd_8266370 : Nat := 4244621077906928023058663

theorem tailTrace_8266370 : CollatzResearch.WordTrace tailWord_8266370 prefixEnd_8266370 4244621077906928023058663 := by
  unfold tailWord_8266370
  simp only [CollatzResearch.WordTrace]
  refine ⟨75374820765590187110819141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200999522041573832295517709 75374820765590187110819141)
  ·
    refine ⟨14132778893548160083278589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75374820765590187110819141 14132778893548160083278589)
    ·
      refine ⟨5299792085080560031229471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14132778893548160083278589 5299792085080560031229471)
      ·
        refine ⟨7949688127620840046844207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299792085080560031229471 7949688127620840046844207)
        ·
          refine ⟨11924532191431260070266311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949688127620840046844207 11924532191431260070266311)
          ·
            refine ⟨17886798287146890105399467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924532191431260070266311 17886798287146890105399467)
            ·
              refine ⟨26830197430720335158099201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17886798287146890105399467 26830197430720335158099201)
              ·
                refine ⟨20122648073040251368574401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26830197430720335158099201 20122648073040251368574401)
                ·
                  refine ⟨15091986054780188526430801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20122648073040251368574401 15091986054780188526430801)
                  ·
                    refine ⟨11318989541085141394823101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15091986054780188526430801 11318989541085141394823101)
                    ·
                      refine ⟨4244621077906928023058663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11318989541085141394823101 4244621077906928023058663)
                      ·
                        rfl

theorem cell23_8266370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8266370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266370 prefixEnd_8266370 := by exact prefixLift 8266370
  have htrace : WordTrace (prefixWord ++ tailWord_8266370) baseStart_8266370 baseEnd_8266370 := by
    simpa [prefixWord, tailWord_8266370, baseEnd_8266370] using wordTrace_append hprefix tailTrace_8266370
  have hstable : (prefixWord ++ tailWord_8266370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266370).length < 2 ^ (prefixWord ++ tailWord_8266370).sum := by decide
  have hdescent : baseEnd_8266370 < baseStart_8266370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266392 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_8266392 : Nat := 118140960795 + 8266392 * 2 ^ 59
def prefixEnd_8266392 : Nat := 4983230072969 + 3 ^ 40 * 8266392 * 2
def baseEnd_8266392 : Nat := 4244632374481326936983561

theorem tailTrace_8266392 : CollatzResearch.WordTrace tailWord_8266392 prefixEnd_8266392 4244632374481326936983561 := by
  unfold tailWord_8266392
  simp only [CollatzResearch.WordTrace]
  refine ⟨150750042734140523100288715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201000056978854030800384953 150750042734140523100288715)
  ·
    refine ⟨226125064101210784650433073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150750042734140523100288715 226125064101210784650433073)
    ·
      refine ⟨169593798075908088487824805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226125064101210784650433073 169593798075908088487824805)
      ·
        refine ⟨31798837139232766591467151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169593798075908088487824805 31798837139232766591467151)
        ·
          refine ⟨47698255708849149887200727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31798837139232766591467151 47698255708849149887200727)
          ·
            refine ⟨71547383563273724830801091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47698255708849149887200727 71547383563273724830801091)
            ·
              refine ⟨107321075344910587246201637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71547383563273724830801091 107321075344910587246201637)
              ·
                refine ⟨20122701627170735108662807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107321075344910587246201637 20122701627170735108662807)
                ·
                  refine ⟨30184052440756102662994211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20122701627170735108662807 30184052440756102662994211)
                  ·
                    refine ⟨45276078661134153994491317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30184052440756102662994211 45276078661134153994491317)
                    ·
                      refine ⟨4244632374481326936983561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45276078661134153994491317 4244632374481326936983561)
                      ·
                        rfl

theorem cell23_8266392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_8266392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266392 prefixEnd_8266392 := by exact prefixLift 8266392
  have htrace : WordTrace (prefixWord ++ tailWord_8266392) baseStart_8266392 baseEnd_8266392 := by
    simpa [prefixWord, tailWord_8266392, baseEnd_8266392] using wordTrace_append hprefix tailTrace_8266392
  have hstable : (prefixWord ++ tailWord_8266392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266392).length < 2 ^ (prefixWord ++ tailWord_8266392).sum := by decide
  have hdescent : baseEnd_8266392 < baseStart_8266392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266410 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_8266410 : Nat := 118140960795 + 8266410 * 2 ^ 59
def prefixEnd_8266410 : Nat := 4983230072969 + 3 ^ 40 * 8266410 * 2
def baseEnd_8266410 : Nat := 4244641617133107866558479

theorem tailTrace_8266410 : CollatzResearch.WordTrace tailWord_8266410 prefixEnd_8266410 4244641617133107866558479 := by
  unfold tailWord_8266410
  simp only [CollatzResearch.WordTrace]
  refine ⟨75375185495553958818683171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201000494654810556849821789 75375185495553958818683171)
  ·
    refine ⟨113062778243330938228024757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75375185495553958818683171 113062778243330938228024757)
    ·
      refine ⟨10599635460312275458877321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113062778243330938228024757 10599635460312275458877321)
      ·
        refine ⟨7949726595234206594157991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10599635460312275458877321 7949726595234206594157991)
        ·
          refine ⟨11924589892851309891236987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949726595234206594157991 11924589892851309891236987)
          ·
            refine ⟨17886884839276964836855481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924589892851309891236987 17886884839276964836855481)
            ·
              refine ⟨13415163629457723627641611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17886884839276964836855481 13415163629457723627641611)
              ·
                refine ⟨20122745444186585441462417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13415163629457723627641611 20122745444186585441462417)
                ·
                  refine ⟨15092059083139939081096813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20122745444186585441462417 15092059083139939081096813)
                  ·
                    refine ⟨5659522156177477155411305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15092059083139939081096813 5659522156177477155411305)
                    ·
                      refine ⟨4244641617133107866558479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659522156177477155411305 4244641617133107866558479)
                      ·
                        rfl

theorem cell23_8266410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_8266410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266410 prefixEnd_8266410 := by exact prefixLift 8266410
  have htrace : WordTrace (prefixWord ++ tailWord_8266410) baseStart_8266410 baseEnd_8266410 := by
    simpa [prefixWord, tailWord_8266410, baseEnd_8266410] using wordTrace_append hprefix tailTrace_8266410
  have hstable : (prefixWord ++ tailWord_8266410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266410).length < 2 ^ (prefixWord ++ tailWord_8266410).sum := by decide
  have hdescent : baseEnd_8266410 < baseStart_8266410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266426 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3]
def baseStart_8266426 : Nat := 118140960795 + 8266426 * 2 ^ 59
def prefixEnd_8266426 : Nat := 4983230072969 + 3 ^ 40 * 8266426 * 2
def baseEnd_8266426 : Nat := 4244649832823579803958405

theorem tailTrace_8266426 : CollatzResearch.WordTrace tailWord_8266426 prefixEnd_8266426 4244649832823579803958405 := by
  unfold tailWord_8266426
  simp only [CollatzResearch.WordTrace]
  refine ⟨75375331387539467501828783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201000883700105246671543421 75375331387539467501828783)
  ·
    refine ⟨113062997081309201252743175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75375331387539467501828783 113062997081309201252743175)
    ·
      refine ⟨169594495621963801879114763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113062997081309201252743175 169594495621963801879114763)
      ·
        refine ⟨254391743432945702818672145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169594495621963801879114763 254391743432945702818672145)
        ·
          refine ⟨190793807574709277114004109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254391743432945702818672145 190793807574709277114004109)
          ·
            refine ⟨71547677840515978917751541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190793807574709277114004109 71547677840515978917751541)
            ·
              refine ⟨6707594797548373023539207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71547677840515978917751541 6707594797548373023539207)
              ·
                refine ⟨10061392196322559535308811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6707594797548373023539207 10061392196322559535308811)
                ·
                  refine ⟨15092088294483839302963217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10061392196322559535308811 15092088294483839302963217)
                  ·
                    refine ⟨11319066220862879477222413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15092088294483839302963217 11319066220862879477222413)
                    ·
                      refine ⟨4244649832823579803958405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11319066220862879477222413 4244649832823579803958405)
                      ·
                        rfl

theorem cell23_8266426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_8266426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266426 prefixEnd_8266426 := by exact prefixLift 8266426
  have htrace : WordTrace (prefixWord ++ tailWord_8266426) baseStart_8266426 baseEnd_8266426 := by
    simpa [prefixWord, tailWord_8266426, baseEnd_8266426] using wordTrace_append hprefix tailTrace_8266426
  have hstable : (prefixWord ++ tailWord_8266426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266426).length < 2 ^ (prefixWord ++ tailWord_8266426).sum := by decide
  have hdescent : baseEnd_8266426 < baseStart_8266426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266435 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_8266435 : Nat := 118140960795 + 8266435 * 2 ^ 59
def prefixEnd_8266435 : Nat := 4983230072969 + 3 ^ 40 * 8266435 * 2
def baseEnd_8266435 : Nat := 4244654454149470268745863

theorem tailTrace_8266435 : CollatzResearch.WordTrace tailWord_8266435 prefixEnd_8266435 4244654454149470268745863 := by
  unfold tailWord_8266435
  simp only [CollatzResearch.WordTrace]
  refine ⟨301501653807125264544392759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201001102538083509696261839 301501653807125264544392759)
  ·
    refine ⟨452252480710687896816589139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301501653807125264544392759 452252480710687896816589139)
    ·
      refine ⟨678378721066031845224883709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452252480710687896816589139 678378721066031845224883709)
      ·
        refine ⟨254392020399761941959331391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678378721066031845224883709 254392020399761941959331391)
        ·
          refine ⟨381588030599642912938997087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254392020399761941959331391 381588030599642912938997087)
          ·
            refine ⟨572382045899464369408495631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381588030599642912938997087 572382045899464369408495631)
            ·
              refine ⟨858573068849196554112743447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572382045899464369408495631 858573068849196554112743447)
              ·
                refine ⟨1287859603273794831169115171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858573068849196554112743447 1287859603273794831169115171)
                ·
                  refine ⟨1931789404910692246753672757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287859603273794831169115171 1931789404910692246753672757)
                  ·
                    refine ⟨181105256710377398133156821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1931789404910692246753672757 181105256710377398133156821)
                    ·
                      refine ⟨4244654454149470268745863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181105256710377398133156821 4244654454149470268745863)
                      ·
                        rfl

theorem cell23_8266435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_8266435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266435 prefixEnd_8266435 := by exact prefixLift 8266435
  have htrace : WordTrace (prefixWord ++ tailWord_8266435) baseStart_8266435 baseEnd_8266435 := by
    simpa [prefixWord, tailWord_8266435, baseEnd_8266435] using wordTrace_append hprefix tailTrace_8266435
  have hstable : (prefixWord ++ tailWord_8266435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266435).length < 2 ^ (prefixWord ++ tailWord_8266435).sum := by decide
  have hdescent : baseEnd_8266435 < baseStart_8266435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266440 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_8266440 : Nat := 118140960795 + 8266440 * 2 ^ 59
def prefixEnd_8266440 : Nat := 4983230072969 + 3 ^ 40 * 8266440 * 2
def baseEnd_8266440 : Nat := 4244657021552742749183341

theorem tailTrace_8266440 : CollatzResearch.WordTrace tailWord_8266440 prefixEnd_8266440 4244657021552742749183341 := by
  unfold tailWord_8266440
  simp only [CollatzResearch.WordTrace]
  refine ⟨150750918086053575199162387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201001224114738100265549849 150750918086053575199162387)
  ·
    refine ⟨226126377129080362798743581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150750918086053575199162387 226126377129080362798743581)
    ·
      refine ⟨84797391423405136049528843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226126377129080362798743581 84797391423405136049528843)
      ·
        refine ⟨127196087135107704074293265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84797391423405136049528843 127196087135107704074293265)
        ·
          refine ⟨95397065351330778055719949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127196087135107704074293265 95397065351330778055719949)
          ·
            refine ⟨35773899506749041770894981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95397065351330778055719949 35773899506749041770894981)
            ·
              refine ⟨6707606157515445332042809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35773899506749041770894981 6707606157515445332042809)
              ·
                refine ⟨5030704618136583999032107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707606157515445332042809 5030704618136583999032107)
                ·
                  refine ⟨7546056927204875998548161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030704618136583999032107 7546056927204875998548161)
                  ·
                    refine ⟨5659542695403656998911121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546056927204875998548161 5659542695403656998911121)
                    ·
                      refine ⟨4244657021552742749183341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659542695403656998911121 4244657021552742749183341)
                      ·
                        rfl

theorem cell23_8266440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_8266440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266440 prefixEnd_8266440 := by exact prefixLift 8266440
  have htrace : WordTrace (prefixWord ++ tailWord_8266440) baseStart_8266440 baseEnd_8266440 := by
    simpa [prefixWord, tailWord_8266440, baseEnd_8266440] using wordTrace_append hprefix tailTrace_8266440
  have hstable : (prefixWord ++ tailWord_8266440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266440).length < 2 ^ (prefixWord ++ tailWord_8266440).sum := by decide
  have hdescent : baseEnd_8266440 < baseStart_8266440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266442 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_8266442 : Nat := 118140960795 + 8266442 * 2 ^ 59
def prefixEnd_8266442 : Nat := 4983230072969 + 3 ^ 40 * 8266442 * 2
def baseEnd_8266442 : Nat := 1414886016171350580452777

theorem tailTrace_8266442 : CollatzResearch.WordTrace tailWord_8266442 prefixEnd_8266442 1414886016171350580452777 := by
  unfold tailWord_8266442
  simp only [CollatzResearch.WordTrace]
  refine ⟨75375477279524976184974395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201001272745399936493265053 75375477279524976184974395)
  ·
    refine ⟨113063215919287464277461593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75375477279524976184974395 113063215919287464277461593)
    ·
      refine ⟨84797411939465598208096195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113063215919287464277461593 84797411939465598208096195)
      ·
        refine ⟨127196117909198397312144293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84797411939465598208096195 127196117909198397312144293)
        ·
          refine ⟨23849272107974699496027055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127196117909198397312144293 23849272107974699496027055)
          ·
            refine ⟨35773908161962049244040583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23849272107974699496027055 35773908161962049244040583)
            ·
              refine ⟨53660862242943073866060875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35773908161962049244040583 53660862242943073866060875)
              ·
                refine ⟨80491293364414610799091313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53660862242943073866060875 80491293364414610799091313)
                ·
                  refine ⟨60368470023310958099318485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80491293364414610799091313 60368470023310958099318485)
                  ·
                    refine ⟨1414886016171350580452777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60368470023310958099318485 1414886016171350580452777)
                    ·
                      rfl

theorem cell23_8266442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_8266442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266442 prefixEnd_8266442 := by exact prefixLift 8266442
  have htrace : WordTrace (prefixWord ++ tailWord_8266442) baseStart_8266442 baseEnd_8266442 := by
    simpa [prefixWord, tailWord_8266442, baseEnd_8266442] using wordTrace_append hprefix tailTrace_8266442
  have hstable : (prefixWord ++ tailWord_8266442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266442).length < 2 ^ (prefixWord ++ tailWord_8266442).sum := by decide
  have hdescent : baseEnd_8266442 < baseStart_8266442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266449 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 5, 3, 2]
def baseStart_8266449 : Nat := 118140960795 + 8266449 * 2 ^ 59
def prefixEnd_8266449 : Nat := 4983230072969 + 3 ^ 40 * 8266449 * 2
def baseEnd_8266449 : Nat := 4244661642878633213970799

theorem tailTrace_8266449 : CollatzResearch.WordTrace tailWord_8266449 prefixEnd_8266449 4244661642878633213970799 := by
  unfold tailWord_8266449
  simp only [CollatzResearch.WordTrace]
  refine ⟨301502164429074544935402401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201001442952716363290268267 301502164429074544935402401)
  ·
    refine ⟨226126623321805908701551801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301502164429074544935402401 226126623321805908701551801)
    ·
      refine ⟨169594967491354431526163851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226126623321805908701551801 169594967491354431526163851)
      ·
        refine ⟨254392451237031647289245777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169594967491354431526163851 254392451237031647289245777)
        ·
          refine ⟨190794338427773735466934333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254392451237031647289245777 190794338427773735466934333)
          ·
            refine ⟨71547876910415150800100375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190794338427773735466934333 71547876910415150800100375)
            ·
              refine ⟨107321815365622726200150563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71547876910415150800100375 107321815365622726200150563)
              ·
                refine ⟨160982723048434089300225845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107321815365622726200150563 160982723048434089300225845)
                ·
                  refine ⟨15092130285790695871896173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160982723048434089300225845 15092130285790695871896173)
                  ·
                    refine ⟨5659548857171510951961065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15092130285790695871896173 5659548857171510951961065)
                    ·
                      refine ⟨4244661642878633213970799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659548857171510951961065 4244661642878633213970799)
                      ·
                        rfl

theorem cell23_8266449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_8266449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266449 prefixEnd_8266449 := by exact prefixLift 8266449
  have htrace : WordTrace (prefixWord ++ tailWord_8266449) baseStart_8266449 baseEnd_8266449 := by
    simpa [prefixWord, tailWord_8266449, baseEnd_8266449] using wordTrace_append hprefix tailTrace_8266449
  have hstable : (prefixWord ++ tailWord_8266449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266449).length < 2 ^ (prefixWord ++ tailWord_8266449).sum := by decide
  have hdescent : baseEnd_8266449 < baseStart_8266449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266456 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_8266456 : Nat := 118140960795 + 8266456 * 2 ^ 59
def prefixEnd_8266456 : Nat := 4983230072969 + 3 ^ 40 * 8266456 * 2
def baseEnd_8266456 : Nat := 4244665237243214686583267

theorem tailTrace_8266456 : CollatzResearch.WordTrace tailWord_8266456 prefixEnd_8266456 4244665237243214686583267 := by
  unfold tailWord_8266456
  simp only [CollatzResearch.WordTrace]
  refine ⟨150751209870024592565453611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201001613160032790087271481 150751209870024592565453611)
  ·
    refine ⟨226126814805036888848180417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150751209870024592565453611 226126814805036888848180417)
    ·
      refine ⟨169595111103777666636135313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226126814805036888848180417 169595111103777666636135313)
      ·
        refine ⟨127196333327833249977101485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169595111103777666636135313 127196333327833249977101485)
        ·
          refine ⟨47698624997937468741413057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127196333327833249977101485 47698624997937468741413057)
          ·
            refine ⟨35773968748453101556059793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47698624997937468741413057 35773968748453101556059793)
            ·
              refine ⟨26830476561339826167044845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35773968748453101556059793 26830476561339826167044845)
              ·
                refine ⟨10061428710502434812641817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26830476561339826167044845 10061428710502434812641817)
                ·
                  refine ⟨7546071532876826109481363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10061428710502434812641817 7546071532876826109481363)
                  ·
                    refine ⟨11319107299315239164222045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7546071532876826109481363 11319107299315239164222045)
                    ·
                      refine ⟨4244665237243214686583267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11319107299315239164222045 4244665237243214686583267)
                      ·
                        rfl

theorem cell23_8266456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_8266456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266456 prefixEnd_8266456 := by exact prefixLift 8266456
  have htrace : WordTrace (prefixWord ++ tailWord_8266456) baseStart_8266456 baseEnd_8266456 := by
    simpa [prefixWord, tailWord_8266456, baseEnd_8266456] using wordTrace_append hprefix tailTrace_8266456
  have hstable : (prefixWord ++ tailWord_8266456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266456).length < 2 ^ (prefixWord ++ tailWord_8266456).sum := by decide
  have hdescent : baseEnd_8266456 < baseStart_8266456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266549 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_8266549 : Nat := 118140960795 + 8266549 * 2 ^ 59
def prefixEnd_8266549 : Nat := 4983230072969 + 3 ^ 40 * 8266549 * 2
def baseEnd_8266549 : Nat := 1414904330314694274240113

theorem tailTrace_8266549 : CollatzResearch.WordTrace tailWord_8266549 prefixEnd_8266549 1414904330314694274240113 := by
  unfold tailWord_8266549
  simp only [CollatzResearch.WordTrace]
  refine ⟨301505811728712262014042701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201003874485808174676028467 301505811728712262014042701)
  ·
    refine ⟨113064679398267098255266013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301505811728712262014042701 113064679398267098255266013)
    ·
      refine ⟨42399254774350161845724755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113064679398267098255266013 42399254774350161845724755)
      ·
        refine ⟨63598882161525242768587133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42399254774350161845724755 63598882161525242768587133)
        ·
          refine ⟨23849580810571966038220175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63598882161525242768587133 23849580810571966038220175)
          ·
            refine ⟨35774371215857949057330263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23849580810571966038220175 35774371215857949057330263)
            ·
              refine ⟨53661556823786923585995395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35774371215857949057330263 53661556823786923585995395)
              ·
                refine ⟨80492335235680385378993093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53661556823786923585995395 80492335235680385378993093)
                ·
                  refine ⟨15092312856690072258561205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80492335235680385378993093 15092312856690072258561205)
                  ·
                    refine ⟨1414904330314694274240113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15092312856690072258561205 1414904330314694274240113)
                    ·
                      rfl

theorem cell23_8266549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_8266549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266549 prefixEnd_8266549 := by exact prefixLift 8266549
  have htrace : WordTrace (prefixWord ++ tailWord_8266549) baseStart_8266549 baseEnd_8266549 := by
    simpa [prefixWord, tailWord_8266549, baseEnd_8266549] using wordTrace_append hprefix tailTrace_8266549
  have hstable : (prefixWord ++ tailWord_8266549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266549).length < 2 ^ (prefixWord ++ tailWord_8266549).sum := by decide
  have hdescent : baseEnd_8266549 < baseStart_8266549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266559 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_8266559 : Nat := 118140960795 + 8266559 * 2 ^ 59
def prefixEnd_8266559 : Nat := 4983230072969 + 3 ^ 40 * 8266559 * 2
def baseEnd_8266559 : Nat := 4244718125750627783595293

theorem tailTrace_8266559 : CollatzResearch.WordTrace tailWord_8266559 prefixEnd_8266559 4244718125750627783595293 := by
  unfold tailWord_8266559
  simp only [CollatzResearch.WordTrace]
  refine ⟨301506176458676033721906731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201004117639117355814604487 301506176458676033721906731)
  ·
    refine ⟨452259264688014050582860097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301506176458676033721906731 452259264688014050582860097)
    ·
      refine ⟨339194448516010537937145073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452259264688014050582860097 339194448516010537937145073)
      ·
        refine ⟨254395836387007903452858805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339194448516010537937145073 254395836387007903452858805)
        ·
          refine ⟨23849609661281990948705513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254395836387007903452858805 23849609661281990948705513)
          ·
            refine ⟨17887207245961493211529135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23849609661281990948705513 17887207245961493211529135)
            ·
              refine ⟨26830810868942239817293703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17887207245961493211529135 26830810868942239817293703)
              ·
                refine ⟨40246216303413359725940555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26830810868942239817293703 40246216303413359725940555)
                ·
                  refine ⟨60369324455120039588910833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40246216303413359725940555 60369324455120039588910833)
                  ·
                    refine ⟨45276993341340029691683125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60369324455120039588910833 45276993341340029691683125)
                    ·
                      refine ⟨4244718125750627783595293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45276993341340029691683125 4244718125750627783595293)
                      ·
                        rfl

theorem cell23_8266559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_8266559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266559 prefixEnd_8266559 := by exact prefixLift 8266559
  have htrace : WordTrace (prefixWord ++ tailWord_8266559) baseStart_8266559 baseEnd_8266559 := by
    simpa [prefixWord, tailWord_8266559, baseEnd_8266559] using wordTrace_append hprefix tailTrace_8266559
  have hstable : (prefixWord ++ tailWord_8266559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266559).length < 2 ^ (prefixWord ++ tailWord_8266559).sum := by decide
  have hdescent : baseEnd_8266559 < baseStart_8266559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266579 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 3, 4]
def baseStart_8266579 : Nat := 118140960795 + 8266579 * 2 ^ 59
def prefixEnd_8266579 : Nat := 4983230072969 + 3 ^ 40 * 8266579 * 2
def baseEnd_8266579 : Nat := 1414909465121239235115067

theorem tailTrace_8266579 : CollatzResearch.WordTrace tailWord_8266579 prefixEnd_8266579 1414909465121239235115067 := by
  unfold tailWord_8266579
  simp only [CollatzResearch.WordTrace]
  refine ⟨301506905918603577137634791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201004603945735718091756527 301506905918603577137634791)
  ·
    refine ⟨452260358877905365706452187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301506905918603577137634791 452260358877905365706452187)
    ·
      refine ⟨678390538316858048559678281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452260358877905365706452187 678390538316858048559678281)
      ·
        refine ⟨508792903737643536419758711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678390538316858048559678281 508792903737643536419758711)
        ·
          refine ⟨763189355606465304629638067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508792903737643536419758711 763189355606465304629638067)
          ·
            refine ⟨1144784033409697956944457101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763189355606465304629638067 1144784033409697956944457101)
            ·
              refine ⟨429294012528636733854171413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144784033409697956944457101 429294012528636733854171413)
              ·
                refine ⟨20123156837279846899414285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 429294012528636733854171413 20123156837279846899414285)
                ·
                  refine ⟨7546183813979942587280357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20123156837279846899414285 7546183813979942587280357)
                  ·
                    refine ⟨1414909465121239235115067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546183813979942587280357 1414909465121239235115067)
                    ·
                      rfl

theorem cell23_8266579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 4].length) (baseStart_8266579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266579 prefixEnd_8266579 := by exact prefixLift 8266579
  have htrace : WordTrace (prefixWord ++ tailWord_8266579) baseStart_8266579 baseEnd_8266579 := by
    simpa [prefixWord, tailWord_8266579, baseEnd_8266579] using wordTrace_append hprefix tailTrace_8266579
  have hstable : (prefixWord ++ tailWord_8266579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266579).length < 2 ^ (prefixWord ++ tailWord_8266579).sum := by decide
  have hdescent : baseEnd_8266579 < baseStart_8266579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266586 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_8266586 : Nat := 118140960795 + 8266586 * 2 ^ 59
def prefixEnd_8266586 : Nat := 4983230072969 + 3 ^ 40 * 8266586 * 2
def baseEnd_8266586 : Nat := 4244731989728299177957669

theorem tailTrace_8266586 : CollatzResearch.WordTrace tailWord_8266586 prefixEnd_8266586 4244731989728299177957669 := by
  unfold tailWord_8266586
  simp only [CollatzResearch.WordTrace]
  refine ⟨75376790307394554333284903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201004774153052144888759741 75376790307394554333284903)
  ·
    refine ⟨113065185461091831499927355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75376790307394554333284903 113065185461091831499927355)
    ·
      refine ⟨169597778191637747249891033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113065185461091831499927355 169597778191637747249891033)
      ·
        refine ⟨127198333643728310437418275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169597778191637747249891033 127198333643728310437418275)
        ·
          refine ⟨190797500465592465656127413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127198333643728310437418275 190797500465592465656127413)
          ·
            refine ⟨17887265668649293655261945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190797500465592465656127413 17887265668649293655261945)
            ·
              refine ⟨13415449251486970241446459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17887265668649293655261945 13415449251486970241446459)
              ·
                refine ⟨20123173877230455362169689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13415449251486970241446459 20123173877230455362169689)
                ·
                  refine ⟨15092380407922841521627267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20123173877230455362169689 15092380407922841521627267)
                  ·
                    refine ⟨22638570611884262282440901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15092380407922841521627267 22638570611884262282440901)
                    ·
                      refine ⟨4244731989728299177957669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22638570611884262282440901 4244731989728299177957669)
                      ·
                        rfl

theorem cell23_8266586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_8266586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266586 prefixEnd_8266586 := by exact prefixLift 8266586
  have htrace : WordTrace (prefixWord ++ tailWord_8266586) baseStart_8266586 baseEnd_8266586 := by
    simpa [prefixWord, tailWord_8266586, baseEnd_8266586] using wordTrace_append hprefix tailTrace_8266586
  have hstable : (prefixWord ++ tailWord_8266586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266586).length < 2 ^ (prefixWord ++ tailWord_8266586).sum := by decide
  have hdescent : baseEnd_8266586 < baseStart_8266586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266609 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 6]
def baseStart_8266609 : Nat := 118140960795 + 8266609 * 2 ^ 59
def prefixEnd_8266609 : Nat := 4983230072969 + 3 ^ 40 * 8266609 * 2
def baseEnd_8266609 : Nat := 471638199975928065330007

theorem tailTrace_8266609 : CollatzResearch.WordTrace tailWord_8266609 prefixEnd_8266609 471638199975928065330007 := by
  unfold tailWord_8266609
  simp only [CollatzResearch.WordTrace]
  refine ⟨301508000108494892261226881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201005333405663261507484587 301508000108494892261226881)
  ·
    refine ⟨226131000081371169195920161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301508000108494892261226881 226131000081371169195920161)
    ·
      refine ⟨169598250061028376896940121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226131000081371169195920161 169598250061028376896940121)
      ·
        refine ⟨127198687545771282672705091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169598250061028376896940121 127198687545771282672705091)
        ·
          refine ⟨190798031318656924009057637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127198687545771282672705091 190798031318656924009057637)
          ·
            refine ⟨35774630872248173251698307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190798031318656924009057637 35774630872248173251698307)
            ·
              refine ⟨53661946308372259877547461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35774630872248173251698307 53661946308372259877547461)
              ·
                refine ⟨10061614932819798727040149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53661946308372259877547461 10061614932819798727040149)
                ·
                  refine ⟨471638199975928065330007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10061614932819798727040149 471638199975928065330007)
                  ·
                    rfl

theorem cell23_8266609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 6].length) (baseStart_8266609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266609 prefixEnd_8266609 := by exact prefixLift 8266609
  have htrace : WordTrace (prefixWord ++ tailWord_8266609) baseStart_8266609 baseEnd_8266609 := by
    simpa [prefixWord, tailWord_8266609, baseEnd_8266609] using wordTrace_append hprefix tailTrace_8266609
  have hstable : (prefixWord ++ tailWord_8266609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266609).length < 2 ^ (prefixWord ++ tailWord_8266609).sum := by decide
  have hdescent : baseEnd_8266609 < baseStart_8266609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266636 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_8266636 : Nat := 118140960795 + 8266636 * 2 ^ 59
def prefixEnd_8266636 : Nat := 4983230072969 + 3 ^ 40 * 8266636 * 2
def baseEnd_8266636 : Nat := 4244757663761023982332439

theorem tailTrace_8266636 : CollatzResearch.WordTrace tailWord_8266636 prefixEnd_8266636 4244757663761023982332439 := by
  unfold tailWord_8266636
  simp only [CollatzResearch.WordTrace]
  refine ⟨150754492439698537936229881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201005989919598050581639841 150754492439698537936229881)
  ·
    refine ⟨113065869329773903452172411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150754492439698537936229881 113065869329773903452172411)
    ·
      refine ⟨169598803994660855178258617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113065869329773903452172411 169598803994660855178258617)
      ·
        refine ⟨127199102995995641383693963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169598803994660855178258617 127199102995995641383693963)
        ·
          refine ⟨190798654493993462075540945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127199102995995641383693963 190798654493993462075540945)
          ·
            refine ⟨143098990870495096556655709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190798654493993462075540945 143098990870495096556655709)
            ·
              refine ⟨53662121576435661208745891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143098990870495096556655709 53662121576435661208745891)
              ·
                refine ⟨80493182364653491813118837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53662121576435661208745891 80493182364653491813118837)
                ·
                  refine ⟨7546235846686264857479891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80493182364653491813118837 7546235846686264857479891)
                  ·
                    refine ⟨11319353770029397286219837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7546235846686264857479891 11319353770029397286219837)
                    ·
                      refine ⟨4244757663761023982332439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11319353770029397286219837 4244757663761023982332439)
                      ·
                        rfl

theorem cell23_8266636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_8266636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266636 prefixEnd_8266636 := by exact prefixLift 8266636
  have htrace : WordTrace (prefixWord ++ tailWord_8266636) baseStart_8266636 baseEnd_8266636 := by
    simpa [prefixWord, tailWord_8266636, baseEnd_8266636] using wordTrace_append hprefix tailTrace_8266636
  have hstable : (prefixWord ++ tailWord_8266636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266636).length < 2 ^ (prefixWord ++ tailWord_8266636).sum := by decide
  have hdescent : baseEnd_8266636 < baseStart_8266636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266679 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_8266679 : Nat := 118140960795 + 8266679 * 2 ^ 59
def prefixEnd_8266679 : Nat := 4983230072969 + 3 ^ 40 * 8266679 * 2
def baseEnd_8266679 : Nat := 4244779743429167314094741

theorem tailTrace_8266679 : CollatzResearch.WordTrace tailWord_8266679 prefixEnd_8266679 4244779743429167314094741 := by
  unfold tailWord_8266679
  simp only [CollatzResearch.WordTrace]
  refine ⟨301510553218241294216275091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201007035478827529477516727 301510553218241294216275091)
  ·
    refine ⟨452265829827361941324412637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301510553218241294216275091 452265829827361941324412637)
    ·
      refine ⟨169599686185260727996654739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452265829827361941324412637 169599686185260727996654739)
      ·
        refine ⟨254399529277891091994982109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169599686185260727996654739 254399529277891091994982109)
        ·
          refine ⟨95399823479209159498118291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254399529277891091994982109 95399823479209159498118291)
          ·
            refine ⟨143099735218813739247177437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95399823479209159498118291 143099735218813739247177437)
            ·
              refine ⟨53662400707055152217691539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143099735218813739247177437 53662400707055152217691539)
              ·
                refine ⟨80493601060582728326537309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53662400707055152217691539 80493601060582728326537309)
                ·
                  refine ⟨30185100397718523122451491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80493601060582728326537309 30185100397718523122451491)
                  ·
                    refine ⟨45277650596577784683677237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30185100397718523122451491 45277650596577784683677237)
                    ·
                      refine ⟨4244779743429167314094741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45277650596577784683677237 4244779743429167314094741)
                      ·
                        rfl

theorem cell23_8266679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_8266679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266679 prefixEnd_8266679 := by exact prefixLift 8266679
  have htrace : WordTrace (prefixWord ++ tailWord_8266679) baseStart_8266679 baseEnd_8266679 := by
    simpa [prefixWord, tailWord_8266679, baseEnd_8266679] using wordTrace_append hprefix tailTrace_8266679
  have hstable : (prefixWord ++ tailWord_8266679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266679).length < 2 ^ (prefixWord ++ tailWord_8266679).sum := by decide
  have hdescent : baseEnd_8266679 < baseStart_8266679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266699 : List Nat := [1, 1, 1, 1, 3, 6, 1, 9]
def baseStart_8266699 : Nat := 118140960795 + 8266699 * 2 ^ 59
def prefixEnd_8266699 : Nat := 4983230072969 + 3 ^ 40 * 8266699 * 2
def baseEnd_8266699 : Nat := 157214444927491008734987

theorem tailTrace_8266699 : CollatzResearch.WordTrace tailWord_8266699 prefixEnd_8266699 157214444927491008734987 := by
  unfold tailWord_8266699
  simp only [CollatzResearch.WordTrace]
  refine ⟨301511282678168837632003151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201007521785445891754668767 301511282678168837632003151)
  ·
    refine ⟨452266924017253256448004727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301511282678168837632003151 452266924017253256448004727)
    ·
      refine ⟨678400386025879884672007091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452266924017253256448004727 678400386025879884672007091)
      ·
        refine ⟨1017600579038819827008010637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678400386025879884672007091 1017600579038819827008010637)
        ·
          refine ⟨381600217139557435128003989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1017600579038819827008010637 381600217139557435128003989)
          ·
            refine ⟨17887510178416754771625187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381600217139557435128003989 17887510178416754771625187)
            ·
              refine ⟨26831265267625132157437781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17887510178416754771625187 26831265267625132157437781)
              ·
                refine ⟨157214444927491008734987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26831265267625132157437781 157214444927491008734987)
                ·
                  rfl

theorem cell23_8266699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 9].length) (baseStart_8266699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266699 prefixEnd_8266699 := by exact prefixLift 8266699
  have htrace : WordTrace (prefixWord ++ tailWord_8266699) baseStart_8266699 baseEnd_8266699 := by
    simpa [prefixWord, tailWord_8266699, baseEnd_8266699] using wordTrace_append hprefix tailTrace_8266699
  have hstable : (prefixWord ++ tailWord_8266699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266699).length < 2 ^ (prefixWord ++ tailWord_8266699).sum := by decide
  have hdescent : baseEnd_8266699 < baseStart_8266699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266710 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_8266710 : Nat := 118140960795 + 8266710 * 2 ^ 59
def prefixEnd_8266710 : Nat := 4983230072969 + 3 ^ 40 * 8266710 * 2
def baseEnd_8266710 : Nat := 4244795661329456692807099

theorem tailTrace_8266710 : CollatzResearch.WordTrace tailWord_8266710 prefixEnd_8266710 4244795661329456692807099 := by
  unfold tailWord_8266710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18844480242570561656915849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201007789254085991007102389 18844480242570561656915849)
  ·
    refine ⟨14133360181927921242686887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18844480242570561656915849 14133360181927921242686887)
    ·
      refine ⟨21200040272891881864030331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14133360181927921242686887 21200040272891881864030331)
      ·
        refine ⟨31800060409337822796045497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21200040272891881864030331 31800060409337822796045497)
        ·
          refine ⟨23850045307003367097034123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31800060409337822796045497 23850045307003367097034123)
          ·
            refine ⟨35775067960505050645551185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23850045307003367097034123 35775067960505050645551185)
            ·
              refine ⟨26831300970378787984163389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35775067960505050645551185 26831300970378787984163389)
              ·
                refine ⟨10061737863892045494061271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26831300970378787984163389 10061737863892045494061271)
                ·
                  refine ⟨15092606795838068241091907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10061737863892045494061271 15092606795838068241091907)
                  ·
                    refine ⟨22638910193757102361637861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15092606795838068241091907 22638910193757102361637861)
                    ·
                      refine ⟨4244795661329456692807099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22638910193757102361637861 4244795661329456692807099)
                      ·
                        rfl

theorem cell23_8266710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_8266710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266710 prefixEnd_8266710 := by exact prefixLift 8266710
  have htrace : WordTrace (prefixWord ++ tailWord_8266710) baseStart_8266710 baseEnd_8266710 := by
    simpa [prefixWord, tailWord_8266710, baseEnd_8266710] using wordTrace_append hprefix tailTrace_8266710
  have hstable : (prefixWord ++ tailWord_8266710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266710).length < 2 ^ (prefixWord ++ tailWord_8266710).sum := by decide
  have hdescent : baseEnd_8266710 < baseStart_8266710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266713 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 3]
def baseStart_8266713 : Nat := 118140960795 + 8266713 * 2 ^ 59
def prefixEnd_8266713 : Nat := 4983230072969 + 3 ^ 40 * 8266713 * 2
def baseEnd_8266713 : Nat := 4244797201771420181069585

theorem tailTrace_8266713 : CollatzResearch.WordTrace tailWord_8266713 prefixEnd_8266713 4244797201771420181069585 := by
  unfold tailWord_8266713
  simp only [CollatzResearch.WordTrace]
  refine ⟨301511793300118118023012793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201007862200078745348675195 301511793300118118023012793)
  ·
    refine ⟨226133844975088588517259595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301511793300118118023012793 226133844975088588517259595)
    ·
      refine ⟨339200767462632882775889393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226133844975088588517259595 339200767462632882775889393)
      ·
        refine ⟨254400575596974662081917045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339200767462632882775889393 254400575596974662081917045)
        ·
          refine ⟨23850053962216374570179723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254400575596974662081917045 23850053962216374570179723)
          ·
            refine ⟨35775080943324561855269585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23850053962216374570179723 35775080943324561855269585)
            ·
              refine ⟨26831310707493421391452189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35775080943324561855269585 26831310707493421391452189)
              ·
                refine ⟨10061741515310033021794571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26831310707493421391452189 10061741515310033021794571)
                ·
                  refine ⟨15092612272965049532691857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10061741515310033021794571 15092612272965049532691857)
                  ·
                    refine ⟨11319459204723787149518893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15092612272965049532691857 11319459204723787149518893)
                    ·
                      refine ⟨4244797201771420181069585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11319459204723787149518893 4244797201771420181069585)
                      ·
                        rfl

theorem cell23_8266713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_8266713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266713 prefixEnd_8266713 := by exact prefixLift 8266713
  have htrace : WordTrace (prefixWord ++ tailWord_8266713) baseStart_8266713 baseEnd_8266713 := by
    simpa [prefixWord, tailWord_8266713, baseEnd_8266713] using wordTrace_append hprefix tailTrace_8266713
  have hstable : (prefixWord ++ tailWord_8266713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266713).length < 2 ^ (prefixWord ++ tailWord_8266713).sum := by decide
  have hdescent : baseEnd_8266713 < baseStart_8266713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266727 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_8266727 : Nat := 118140960795 + 8266727 * 2 ^ 59
def prefixEnd_8266727 : Nat := 4983230072969 + 3 ^ 40 * 8266727 * 2
def baseEnd_8266727 : Nat := 4244804390500583126294521

theorem tailTrace_8266727 : CollatzResearch.WordTrace tailWord_8266727 prefixEnd_8266727 4244804390500583126294521 := by
  unfold tailWord_8266727
  simp only [CollatzResearch.WordTrace]
  refine ⟨301512303922067398414022435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201008202614711598942681623 301512303922067398414022435)
  ·
    refine ⟨452268455883101097621033653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301512303922067398414022435 452268455883101097621033653)
    ·
      refine ⟨42400167739040727901971905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452268455883101097621033653 42400167739040727901971905)
      ·
        refine ⟨31800125804280545926478929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42400167739040727901971905 31800125804280545926478929)
        ·
          refine ⟨23850094353210409444859197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31800125804280545926478929 23850094353210409444859197)
          ·
            refine ⟨8943785382453903541822199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23850094353210409444859197 8943785382453903541822199)
            ·
              refine ⟨13415678073680855312733299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8943785382453903541822199 13415678073680855312733299)
              ·
                refine ⟨20123517110521282969099949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13415678073680855312733299 20123517110521282969099949)
                ·
                  refine ⟨7546318916445481113412481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20123517110521282969099949 7546318916445481113412481)
                  ·
                    refine ⟨5659739187334110835059361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546318916445481113412481 5659739187334110835059361)
                    ·
                      refine ⟨4244804390500583126294521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659739187334110835059361 4244804390500583126294521)
                      ·
                        rfl

theorem cell23_8266727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_8266727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266727 prefixEnd_8266727 := by exact prefixLift 8266727
  have htrace : WordTrace (prefixWord ++ tailWord_8266727) baseStart_8266727 baseEnd_8266727 := by
    simpa [prefixWord, tailWord_8266727, baseEnd_8266727] using wordTrace_append hprefix tailTrace_8266727
  have hstable : (prefixWord ++ tailWord_8266727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266727).length < 2 ^ (prefixWord ++ tailWord_8266727).sum := by decide
  have hdescent : baseEnd_8266727 < baseStart_8266727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266736 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 7, 2]
def baseStart_8266736 : Nat := 118140960795 + 8266736 * 2 ^ 59
def prefixEnd_8266736 : Nat := 4983230072969 + 3 ^ 40 * 8266736 * 2
def baseEnd_8266736 : Nat := 4244809011826473591081979

theorem tailTrace_8266736 : CollatzResearch.WordTrace tailWord_8266736 prefixEnd_8266736 4244809011826473591081979 := by
  unfold tailWord_8266736
  simp only [CollatzResearch.WordTrace]
  refine ⟨150756316089517396475550031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201008421452689861967400041 150756316089517396475550031)
  ·
    refine ⟨226134474134276094713325047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150756316089517396475550031 226134474134276094713325047)
    ·
      refine ⟨339201711201414142069987571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226134474134276094713325047 339201711201414142069987571)
      ·
        refine ⟨508802566802121213104981357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339201711201414142069987571 508802566802121213104981357)
        ·
          refine ⟨190800962550795454914368009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508802566802121213104981357 190800962550795454914368009)
          ·
            refine ⟨143100721913096591185776007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190800962550795454914368009 143100721913096591185776007)
            ·
              refine ⟨214651082869644886778664011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143100721913096591185776007 214651082869644886778664011)
              ·
                refine ⟨321976624304467330167996017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214651082869644886778664011 321976624304467330167996017)
                ·
                  refine ⟨241482468228350497625997013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321976624304467330167996017 241482468228350497625997013)
                  ·
                    refine ⟨5659745349101964788109305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 241482468228350497625997013 5659745349101964788109305)
                    ·
                      refine ⟨4244809011826473591081979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659745349101964788109305 4244809011826473591081979)
                      ·
                        rfl

theorem cell23_8266736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 7, 2].length) (baseStart_8266736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266736 prefixEnd_8266736 := by exact prefixLift 8266736
  have htrace : WordTrace (prefixWord ++ tailWord_8266736) baseStart_8266736 baseEnd_8266736 := by
    simpa [prefixWord, tailWord_8266736, baseEnd_8266736] using wordTrace_append hprefix tailTrace_8266736
  have hstable : (prefixWord ++ tailWord_8266736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266736).length < 2 ^ (prefixWord ++ tailWord_8266736).sum := by decide
  have hdescent : baseEnd_8266736 < baseStart_8266736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266749 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_8266749 : Nat := 118140960795 + 8266749 * 2 ^ 59
def prefixEnd_8266749 : Nat := 4983230072969 + 3 ^ 40 * 8266749 * 2
def baseEnd_8266749 : Nat := 4244815687074982040219419

theorem tailTrace_8266749 : CollatzResearch.WordTrace tailWord_8266749 prefixEnd_8266749 4244815687074982040219419 := by
  unfold tailWord_8266749
  simp only [CollatzResearch.WordTrace]
  refine ⟨301513106327987696171323301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201008737551991797447548867 301513106327987696171323301)
  ·
    refine ⟨56533707436497693032123119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301513106327987696171323301 56533707436497693032123119)
    ·
      refine ⟨84800561154746539548184679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56533707436497693032123119 84800561154746539548184679)
      ·
        refine ⟨127200841732119809322277019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84800561154746539548184679 127200841732119809322277019)
        ·
          refine ⟨190801262598179713983415529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127200841732119809322277019 190801262598179713983415529)
          ·
            refine ⟨143100946948634785487561647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190801262598179713983415529 143100946948634785487561647)
            ·
              refine ⟨214651420422952178231342471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143100946948634785487561647 214651420422952178231342471)
              ·
                refine ⟨321977130634428267347013707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214651420422952178231342471 321977130634428267347013707)
                ·
                  refine ⟨482965695951642401020520561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321977130634428267347013707 482965695951642401020520561)
                  ·
                    refine ⟨362224271963731800765390421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482965695951642401020520561 362224271963731800765390421)
                    ·
                      refine ⟨4244815687074982040219419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 362224271963731800765390421 4244815687074982040219419)
                      ·
                        rfl

theorem cell23_8266749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_8266749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266749 prefixEnd_8266749 := by exact prefixLift 8266749
  have htrace : WordTrace (prefixWord ++ tailWord_8266749) baseStart_8266749 baseEnd_8266749 := by
    simpa [prefixWord, tailWord_8266749, baseEnd_8266749] using wordTrace_append hprefix tailTrace_8266749
  have hstable : (prefixWord ++ tailWord_8266749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266749).length < 2 ^ (prefixWord ++ tailWord_8266749).sum := by decide
  have hdescent : baseEnd_8266749 < baseStart_8266749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266796 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_8266796 : Nat := 118140960795 + 8266796 * 2 ^ 59
def prefixEnd_8266796 : Nat := 4983230072969 + 3 ^ 40 * 8266796 * 2
def baseEnd_8266796 : Nat := 4244839820665743356331703

theorem tailTrace_8266796 : CollatzResearch.WordTrace tailWord_8266796 prefixEnd_8266796 4244839820665743356331703 := by
  unfold tailWord_8266796
  simp only [CollatzResearch.WordTrace]
  refine ⟨150757410279408711599142121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201009880372544948798856161 150757410279408711599142121)
  ·
    refine ⟨113068057709556533699356591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150757410279408711599142121 113068057709556533699356591)
    ·
      refine ⟨169602086564334800549034887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113068057709556533699356591 169602086564334800549034887)
      ·
        refine ⟨254403129846502200823552331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169602086564334800549034887 254403129846502200823552331)
        ·
          refine ⟨381604694769753301235328497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254403129846502200823552331 381604694769753301235328497)
          ·
            refine ⟨286203521077314975926496373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381604694769753301235328497 286203521077314975926496373)
            ·
              refine ⟨26831580100998278993109035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286203521077314975926496373 26831580100998278993109035)
              ·
                refine ⟨40247370151497418489663553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26831580100998278993109035 40247370151497418489663553)
                ·
                  refine ⟨30185527613623063867247665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40247370151497418489663553 30185527613623063867247665)
                  ·
                    refine ⟨22639145710217297900435749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30185527613623063867247665 22639145710217297900435749)
                    ·
                      refine ⟨4244839820665743356331703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22639145710217297900435749 4244839820665743356331703)
                      ·
                        rfl

theorem cell23_8266796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_8266796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266796 prefixEnd_8266796 := by exact prefixLift 8266796
  have htrace : WordTrace (prefixWord ++ tailWord_8266796) baseStart_8266796 baseEnd_8266796 := by
    simpa [prefixWord, tailWord_8266796, baseEnd_8266796] using wordTrace_append hprefix tailTrace_8266796
  have hstable : (prefixWord ++ tailWord_8266796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266796).length < 2 ^ (prefixWord ++ tailWord_8266796).sum := by decide
  have hdescent : baseEnd_8266796 < baseStart_8266796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266799 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_8266799 : Nat := 118140960795 + 8266799 * 2 ^ 59
def prefixEnd_8266799 : Nat := 4983230072969 + 3 ^ 40 * 8266799 * 2
def baseEnd_8266799 : Nat := 4244841361107706844594189

theorem tailTrace_8266799 : CollatzResearch.WordTrace tailWord_8266799 prefixEnd_8266799 4244841361107706844594189 := by
  unfold tailWord_8266799
  simp only [CollatzResearch.WordTrace]
  refine ⟨301514929977806554710643451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201009953318537703140428967 301514929977806554710643451)
  ·
    refine ⟨452272394966709832065965177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301514929977806554710643451 452272394966709832065965177)
    ·
      refine ⟨339204296225032374049473883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452272394966709832065965177 339204296225032374049473883)
      ·
        refine ⟨508806444337548561074210825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339204296225032374049473883 508806444337548561074210825)
        ·
          refine ⟨381604833253161420805658119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508806444337548561074210825 381604833253161420805658119)
          ·
            refine ⟨572407249879742131208487179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381604833253161420805658119 572407249879742131208487179)
            ·
              refine ⟨858610874819613196812730769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572407249879742131208487179 858610874819613196812730769)
              ·
                refine ⟨643958156114709897609548077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858610874819613196812730769 643958156114709897609548077)
                ·
                  refine ⟨241484308543016211603580529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643958156114709897609548077 241484308543016211603580529)
                  ·
                    refine ⟨181113231407262158702685397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241484308543016211603580529 181113231407262158702685397)
                    ·
                      refine ⟨4244841361107706844594189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181113231407262158702685397 4244841361107706844594189)
                      ·
                        rfl

theorem cell23_8266799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_8266799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266799 prefixEnd_8266799 := by exact prefixLift 8266799
  have htrace : WordTrace (prefixWord ++ tailWord_8266799) baseStart_8266799 baseEnd_8266799 := by
    simpa [prefixWord, tailWord_8266799, baseEnd_8266799] using wordTrace_append hprefix tailTrace_8266799
  have hstable : (prefixWord ++ tailWord_8266799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266799).length < 2 ^ (prefixWord ++ tailWord_8266799).sum := by decide
  have hdescent : baseEnd_8266799 < baseStart_8266799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266800 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 2, 2, 2]
def baseStart_8266800 : Nat := 118140960795 + 8266800 * 2 ^ 59
def prefixEnd_8266800 : Nat := 4983230072969 + 3 ^ 40 * 8266800 * 2
def baseEnd_8266800 : Nat := 4244841874588361340681685

theorem tailTrace_8266800 : CollatzResearch.WordTrace tailWord_8266800 prefixEnd_8266800 4244841874588361340681685 := by
  unfold tailWord_8266800
  simp only [CollatzResearch.WordTrace]
  refine ⟨150757483225401465940714927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201009977633868621254286569 150757483225401465940714927)
  ·
    refine ⟨226136224838102198911072391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150757483225401465940714927 226136224838102198911072391)
    ·
      refine ⟨339204337257153298366608587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226136224838102198911072391 339204337257153298366608587)
      ·
        refine ⟨508806505885729947549912881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339204337257153298366608587 508806505885729947549912881)
        ·
          refine ⟨381604879414297460662434661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508806505885729947549912881 381604879414297460662434661)
          ·
            refine ⟨71550914890180773874206499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381604879414297460662434661 71550914890180773874206499)
            ·
              refine ⟨107326372335271160811309749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71550914890180773874206499 107326372335271160811309749)
              ·
                refine ⟨10061847406431671326060289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107326372335271160811309749 10061847406431671326060289)
                ·
                  refine ⟨7546385554823753494545217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10061847406431671326060289 7546385554823753494545217)
                  ·
                    refine ⟨5659789166117815120908913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546385554823753494545217 5659789166117815120908913)
                    ·
                      refine ⟨4244841874588361340681685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659789166117815120908913 4244841874588361340681685)
                      ·
                        rfl

theorem cell23_8266800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 2, 2].length) (baseStart_8266800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266800 prefixEnd_8266800 := by exact prefixLift 8266800
  have htrace : WordTrace (prefixWord ++ tailWord_8266800) baseStart_8266800 baseEnd_8266800 := by
    simpa [prefixWord, tailWord_8266800, baseEnd_8266800] using wordTrace_append hprefix tailTrace_8266800
  have hstable : (prefixWord ++ tailWord_8266800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266800).length < 2 ^ (prefixWord ++ tailWord_8266800).sum := by decide
  have hdescent : baseEnd_8266800 < baseStart_8266800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266816 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_8266816 : Nat := 118140960795 + 8266816 * 2 ^ 59
def prefixEnd_8266816 : Nat := 4983230072969 + 3 ^ 40 * 8266816 * 2
def baseEnd_8266816 : Nat := 4244850090278833278081611

theorem tailTrace_8266816 : CollatzResearch.WordTrace tailWord_8266816 prefixEnd_8266816 4244850090278833278081611 := by
  unfold tailWord_8266816
  simp only [CollatzResearch.WordTrace]
  refine ⟨150757775009372483307006151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201010366679163311076008201 150757775009372483307006151)
  ·
    refine ⟨226136662514058724960509227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150757775009372483307006151 226136662514058724960509227)
    ·
      refine ⟨339204993771088087440763841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226136662514058724960509227 339204993771088087440763841)
      ·
        refine ⟨254403745328316065580572881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339204993771088087440763841 254403745328316065580572881)
        ·
          refine ⟨190802808996237049185429661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254403745328316065580572881 190802808996237049185429661)
          ·
            refine ⟨71551053373588893444536123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190802808996237049185429661 71551053373588893444536123)
            ·
              refine ⟨107326580060383340166804185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71551053373588893444536123 107326580060383340166804185)
              ·
                refine ⟨80494935045287505125103139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107326580060383340166804185 80494935045287505125103139)
                ·
                  refine ⟨120742402567931257687654709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80494935045287505125103139 120742402567931257687654709)
                  ·
                    refine ⟨11319600240743555408217629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120742402567931257687654709 11319600240743555408217629)
                    ·
                      refine ⟨4244850090278833278081611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11319600240743555408217629 4244850090278833278081611)
                      ·
                        rfl

theorem cell23_8266816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_8266816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266816 prefixEnd_8266816 := by exact prefixLift 8266816
  have htrace : WordTrace (prefixWord ++ tailWord_8266816) baseStart_8266816 baseEnd_8266816 := by
    simpa [prefixWord, tailWord_8266816, baseEnd_8266816] using wordTrace_append hprefix tailTrace_8266816
  have hstable : (prefixWord ++ tailWord_8266816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266816).length < 2 ^ (prefixWord ++ tailWord_8266816).sum := by decide
  have hdescent : baseEnd_8266816 < baseStart_8266816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266823 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 5]
def baseStart_8266823 : Nat := 118140960795 + 8266823 * 2 ^ 59
def prefixEnd_8266823 : Nat := 4983230072969 + 3 ^ 40 * 8266823 * 2
def baseEnd_8266823 : Nat := 471650409404823861188231

theorem tailTrace_8266823 : CollatzResearch.WordTrace tailWord_8266823 prefixEnd_8266823 471650409404823861188231 := by
  unfold tailWord_8266823
  simp only [CollatzResearch.WordTrace]
  refine ⟨301515805329719606809517123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201010536886479737873011415 301515805329719606809517123)
  ·
    refine ⟨452273707994579410214275685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301515805329719606809517123 452273707994579410214275685)
    ·
      refine ⟨84801320248983639415176691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452273707994579410214275685 84801320248983639415176691)
      ·
        refine ⟨127201980373475459122765037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84801320248983639415176691 127201980373475459122765037)
        ·
          refine ⟨47700742640053297171036889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127201980373475459122765037 47700742640053297171036889)
          ·
            refine ⟨35775556980039972878277667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47700742640053297171036889 35775556980039972878277667)
            ·
              refine ⟨53663335470059959317416501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35775556980039972878277667 53663335470059959317416501)
              ·
                refine ⟨5030937700318121186007797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53663335470059959317416501 5030937700318121186007797)
                ·
                  refine ⟨471650409404823861188231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5030937700318121186007797 471650409404823861188231)
                  ·
                    rfl

theorem cell23_8266823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 5].length) (baseStart_8266823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266823 prefixEnd_8266823 := by exact prefixLift 8266823
  have htrace : WordTrace (prefixWord ++ tailWord_8266823) baseStart_8266823 baseEnd_8266823 := by
    simpa [prefixWord, tailWord_8266823, baseEnd_8266823] using wordTrace_append hprefix tailTrace_8266823
  have hstable : (prefixWord ++ tailWord_8266823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266823).length < 2 ^ (prefixWord ++ tailWord_8266823).sum := by decide
  have hdescent : baseEnd_8266823 < baseStart_8266823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266834 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_8266834 : Nat := 118140960795 + 8266834 * 2 ^ 59
def prefixEnd_8266834 : Nat := 4983230072969 + 3 ^ 40 * 8266834 * 2
def baseEnd_8266834 : Nat := 4244859332930614207656529

theorem tailTrace_8266834 : CollatzResearch.WordTrace tailWord_8266834 prefixEnd_8266834 4244859332930614207656529 := by
  unfold tailWord_8266834
  simp only [CollatzResearch.WordTrace]
  refine ⟨75379051633169938922041889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201010804355119837125445037 75379051633169938922041889)
  ·
    refine ⟨56534288724877454191531417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75379051633169938922041889 56534288724877454191531417)
    ·
      refine ⟨42400716543658090643648563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56534288724877454191531417 42400716543658090643648563)
      ·
        refine ⟨63601074815487135965472845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42400716543658090643648563 63601074815487135965472845)
        ·
          refine ⟨23850403055807675987052317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63601074815487135965472845 23850403055807675987052317)
          ·
            refine ⟨8943901145927878495144619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23850403055807675987052317 8943901145927878495144619)
            ·
              refine ⟨13415851718891817742716929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8943901145927878495144619 13415851718891817742716929)
              ·
                refine ⟨10061888789168863307037697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13415851718891817742716929 10061888789168863307037697)
                ·
                  refine ⟨7546416591876647480278273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10061888789168863307037697 7546416591876647480278273)
                  ·
                    refine ⟨5659812443907485610208705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546416591876647480278273 5659812443907485610208705)
                    ·
                      refine ⟨4244859332930614207656529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659812443907485610208705 4244859332930614207656529)
                      ·
                        rfl

theorem cell23_8266834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_8266834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266834 prefixEnd_8266834 := by exact prefixLift 8266834
  have htrace : WordTrace (prefixWord ++ tailWord_8266834) baseStart_8266834 baseEnd_8266834 := by
    simpa [prefixWord, tailWord_8266834, baseEnd_8266834] using wordTrace_append hprefix tailTrace_8266834
  have hstable : (prefixWord ++ tailWord_8266834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266834).length < 2 ^ (prefixWord ++ tailWord_8266834).sum := by decide
  have hdescent : baseEnd_8266834 < baseStart_8266834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266850 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_8266850 : Nat := 118140960795 + 8266850 * 2 ^ 59
def prefixEnd_8266850 : Nat := 4983230072969 + 3 ^ 40 * 8266850 * 2
def baseEnd_8266850 : Nat := 4244867548621086145056455

theorem tailTrace_8266850 : CollatzResearch.WordTrace tailWord_8266850 prefixEnd_8266850 4244867548621086145056455 := by
  unfold tailWord_8266850
  simp only [CollatzResearch.WordTrace]
  refine ⟨75379197525155447605187501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201011193400414526947166669 75379197525155447605187501)
  ·
    refine ⟨28267199071933292851945313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75379197525155447605187501 28267199071933292851945313)
    ·
      refine ⟨21200399303949969638958985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28267199071933292851945313 21200399303949969638958985)
      ·
        refine ⟨15900299477962477229219239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21200399303949969638958985 15900299477962477229219239)
        ·
          refine ⟨23850449216943715843828859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900299477962477229219239 23850449216943715843828859)
          ·
            refine ⟨35775673825415573765743289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23850449216943715843828859 35775673825415573765743289)
            ·
              refine ⟨26831755369061680324307467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35775673825415573765743289 26831755369061680324307467)
              ·
                refine ⟨40247633053592520486461201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26831755369061680324307467 40247633053592520486461201)
                ·
                  refine ⟨30185724790194390364845901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40247633053592520486461201 30185724790194390364845901)
                  ·
                    refine ⟨11319646796322896386817213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30185724790194390364845901 11319646796322896386817213)
                    ·
                      refine ⟨4244867548621086145056455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11319646796322896386817213 4244867548621086145056455)
                      ·
                        rfl

theorem cell23_8266850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_8266850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266850 prefixEnd_8266850 := by exact prefixLift 8266850
  have htrace : WordTrace (prefixWord ++ tailWord_8266850) baseStart_8266850 baseEnd_8266850 := by
    simpa [prefixWord, tailWord_8266850, baseEnd_8266850] using wordTrace_append hprefix tailTrace_8266850
  have hstable : (prefixWord ++ tailWord_8266850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266850).length < 2 ^ (prefixWord ++ tailWord_8266850).sum := by decide
  have hdescent : baseEnd_8266850 < baseStart_8266850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266866 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_8266866 : Nat := 118140960795 + 8266866 * 2 ^ 59
def prefixEnd_8266866 : Nat := 4983230072969 + 3 ^ 40 * 8266866 * 2
def baseEnd_8266866 : Nat := 1414958588103852694152127

theorem tailTrace_8266866 : CollatzResearch.WordTrace tailWord_8266866 prefixEnd_8266866 1414958588103852694152127 := by
  unfold tailWord_8266866
  simp only [CollatzResearch.WordTrace]
  refine ⟨75379343417140956288333113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201011582445709216768888301 75379343417140956288333113)
  ·
    refine ⟨56534507562855717216249835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75379343417140956288333113 56534507562855717216249835)
    ·
      refine ⟨84801761344283575824374753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56534507562855717216249835 84801761344283575824374753)
      ·
        refine ⟨63601321008212681868281065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84801761344283575824374753 63601321008212681868281065)
        ·
          refine ⟨47700990756159511401210799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63601321008212681868281065 47700990756159511401210799)
          ·
            refine ⟨71551486134239267101816199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47700990756159511401210799 71551486134239267101816199)
            ·
              refine ⟨107327229201358900652724299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71551486134239267101816199 107327229201358900652724299)
              ·
                refine ⟨160990843802038350979086449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107327229201358900652724299 160990843802038350979086449)
                ·
                  refine ⟨120743132851528763234314837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160990843802038350979086449 120743132851528763234314837)
                  ·
                    refine ⟨1414958588103852694152127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120743132851528763234314837 1414958588103852694152127)
                    ·
                      rfl

theorem cell23_8266866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_8266866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266866 prefixEnd_8266866 := by exact prefixLift 8266866
  have htrace : WordTrace (prefixWord ++ tailWord_8266866) baseStart_8266866 baseEnd_8266866 := by
    simpa [prefixWord, tailWord_8266866, baseEnd_8266866] using wordTrace_append hprefix tailTrace_8266866
  have hstable : (prefixWord ++ tailWord_8266866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266866).length < 2 ^ (prefixWord ++ tailWord_8266866).sum := by decide
  have hdescent : baseEnd_8266866 < baseStart_8266866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266913 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 6]
def baseStart_8266913 : Nat := 118140960795 + 8266913 * 2 ^ 59
def prefixEnd_8266913 : Nat := 4983230072969 + 3 ^ 40 * 8266913 * 2
def baseEnd_8266913 : Nat := 471655544211368822063185

theorem tailTrace_8266913 : CollatzResearch.WordTrace tailWord_8266913 prefixEnd_8266913 471655544211368822063185 := by
  unfold tailWord_8266913
  simp only [CollatzResearch.WordTrace]
  refine ⟨301519087899393552180293393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201012725266262368120195595 301519087899393552180293393)
  ·
    refine ⟨226139315924545164135220045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301519087899393552180293393 226139315924545164135220045)
    ·
      refine ⟨84802243471704436550707517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226139315924545164135220045 84802243471704436550707517)
      ·
        refine ⟨31800841301889163706515319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84802243471704436550707517 31800841301889163706515319)
        ·
          refine ⟨47701261952833745559772979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31800841301889163706515319 47701261952833745559772979)
          ·
            refine ⟨71551892929250618339659469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47701261952833745559772979 71551892929250618339659469)
            ·
              refine ⟨26831959848468981877372301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71551892929250618339659469 26831959848468981877372301)
              ·
                refine ⟨10061984943175868204014613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26831959848468981877372301 10061984943175868204014613)
                ·
                  refine ⟨471655544211368822063185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10061984943175868204014613 471655544211368822063185)
                  ·
                    rfl

theorem cell23_8266913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 6].length) (baseStart_8266913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266913 prefixEnd_8266913 := by exact prefixLift 8266913
  have htrace : WordTrace (prefixWord ++ tailWord_8266913) baseStart_8266913 baseEnd_8266913 := by
    simpa [prefixWord, tailWord_8266913, baseEnd_8266913] using wordTrace_append hprefix tailTrace_8266913
  have hstable : (prefixWord ++ tailWord_8266913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266913).length < 2 ^ (prefixWord ++ tailWord_8266913).sum := by decide
  have hdescent : baseEnd_8266913 < baseStart_8266913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266936 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_8266936 : Nat := 118140960795 + 8266936 * 2 ^ 59
def prefixEnd_8266936 : Nat := 4983230072969 + 3 ^ 40 * 8266936 * 2
def baseEnd_8266936 : Nat := 4244911707957372808581059

theorem tailTrace_8266936 : CollatzResearch.WordTrace tailWord_8266936 prefixEnd_8266936 4244911707957372808581059 := by
  unfold tailWord_8266936
  simp only [CollatzResearch.WordTrace]
  refine ⟨150759963389155113554190331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201013284518873484738920441 150759963389155113554190331)
  ·
    refine ⟨226139945083732670331285497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150759963389155113554190331 226139945083732670331285497)
    ·
      refine ⟨169604958812799502748464123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226139945083732670331285497 169604958812799502748464123)
      ·
        refine ⟨254407438219199254122696185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169604958812799502748464123 254407438219199254122696185)
        ·
          refine ⟨190805578664399440592022139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254407438219199254122696185 190805578664399440592022139)
          ·
            refine ⟨286208367996599160888033209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190805578664399440592022139 286208367996599160888033209)
            ·
              refine ⟨214656275997449370666024907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286208367996599160888033209 214656275997449370666024907)
              ·
                refine ⟨321984413996174055999037361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214656275997449370666024907 321984413996174055999037361)
                ·
                  refine ⟨241488310497130541999278021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321984413996174055999037361 241488310497130541999278021)
                  ·
                    refine ⟨45279058218211976624864629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241488310497130541999278021 45279058218211976624864629)
                    ·
                      refine ⟨4244911707957372808581059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45279058218211976624864629 4244911707957372808581059)
                      ·
                        rfl

theorem cell23_8266936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_8266936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266936 prefixEnd_8266936 := by exact prefixLift 8266936
  have htrace : WordTrace (prefixWord ++ tailWord_8266936) baseStart_8266936 baseEnd_8266936 := by
    simpa [prefixWord, tailWord_8266936, baseEnd_8266936] using wordTrace_append hprefix tailTrace_8266936
  have hstable : (prefixWord ++ tailWord_8266936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266936).length < 2 ^ (prefixWord ++ tailWord_8266936).sum := by decide
  have hdescent : baseEnd_8266936 < baseStart_8266936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266943 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 1, 5]
def baseStart_8266943 : Nat := 118140960795 + 8266943 * 2 ^ 59
def prefixEnd_8266943 : Nat := 4983230072969 + 3 ^ 40 * 8266943 * 2
def baseEnd_8266943 : Nat := 1414971767440651427064509

theorem tailTrace_8266943 : CollatzResearch.WordTrace tailWord_8266943 prefixEnd_8266943 1414971767440651427064509 := by
  unfold tailWord_8266943
  simp only [CollatzResearch.WordTrace]
  refine ⟨301520182089284867303885483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201013454726189911535923655 301520182089284867303885483)
  ·
    refine ⟨452280273133927300955828225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301520182089284867303885483 452280273133927300955828225)
    ·
      refine ⟨339210204850445475716871169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452280273133927300955828225 339210204850445475716871169)
      ·
        refine ⟨254407653637834106787653377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339210204850445475716871169 254407653637834106787653377)
        ·
          refine ⟨190805740228375580090740033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254407653637834106787653377 190805740228375580090740033)
          ·
            refine ⟨143104305171281685068055025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190805740228375580090740033 143104305171281685068055025)
            ·
              refine ⟨107328228878461263801041269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143104305171281685068055025 107328228878461263801041269)
              ·
                refine ⟨10062021457355743481347619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107328228878461263801041269 10062021457355743481347619)
                ·
                  refine ⟨15093032186033615222021429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062021457355743481347619 15093032186033615222021429)
                  ·
                    refine ⟨1414971767440651427064509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15093032186033615222021429 1414971767440651427064509)
                    ·
                      rfl

theorem cell23_8266943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_8266943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266943 prefixEnd_8266943 := by exact prefixLift 8266943
  have htrace : WordTrace (prefixWord ++ tailWord_8266943) baseStart_8266943 baseEnd_8266943 := by
    simpa [prefixWord, tailWord_8266943, baseEnd_8266943] using wordTrace_append hprefix tailTrace_8266943
  have hstable : (prefixWord ++ tailWord_8266943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266943).length < 2 ^ (prefixWord ++ tailWord_8266943).sum := by decide
  have hdescent : baseEnd_8266943 < baseStart_8266943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8266994 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_8266994 : Nat := 118140960795 + 8266994 * 2 ^ 59
def prefixEnd_8266994 : Nat := 4983230072969 + 3 ^ 40 * 8266994 * 2
def baseEnd_8266994 : Nat := 1414980496611777860551931

theorem tailTrace_8266994 : CollatzResearch.WordTrace tailWord_8266994 prefixEnd_8266994 1414980496611777860551931 := by
  unfold tailWord_8266994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75380510553025025753498009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201014694808066735342661357 75380510553025025753498009)
  ·
    refine ⟨56535382914768769315123507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75380510553025025753498009 56535382914768769315123507)
    ·
      refine ⟨84803074372153153972685261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56535382914768769315123507 84803074372153153972685261)
      ·
        refine ⟨31801152889557432739756973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84803074372153153972685261 31801152889557432739756973)
        ·
          refine ⟨11925432333584037277408865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31801152889557432739756973 11925432333584037277408865)
          ·
            refine ⟨8944074250188027958056649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925432333584037277408865 8944074250188027958056649)
            ·
              refine ⟨6708055687641020968542487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8944074250188027958056649 6708055687641020968542487)
              ·
                refine ⟨10062083531461531452813731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708055687641020968542487 10062083531461531452813731)
                ·
                  refine ⟨15093125297192297179220597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062083531461531452813731 15093125297192297179220597)
                  ·
                    refine ⟨1414980496611777860551931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15093125297192297179220597 1414980496611777860551931)
                    ·
                      rfl

theorem cell23_8266994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_8266994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8266994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8266994 prefixEnd_8266994 := by exact prefixLift 8266994
  have htrace : WordTrace (prefixWord ++ tailWord_8266994) baseStart_8266994 baseEnd_8266994 := by
    simpa [prefixWord, tailWord_8266994, baseEnd_8266994] using wordTrace_append hprefix tailTrace_8266994
  have hstable : (prefixWord ++ tailWord_8266994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8266994).length < 2 ^ (prefixWord ++ tailWord_8266994).sum := by decide
  have hdescent : baseEnd_8266994 < baseStart_8266994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8266994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267007 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 2, 4]
def baseStart_8267007 : Nat := 118140960795 + 8267007 * 2 ^ 59
def prefixEnd_8267007 : Nat := 4983230072969 + 3 ^ 40 * 8267007 * 2
def baseEnd_8267007 : Nat := 1414982721694614010264411

theorem tailTrace_8267007 : CollatzResearch.WordTrace tailWord_8267007 prefixEnd_8267007 1414982721694614010264411 := by
  unfold tailWord_8267007
  simp only [CollatzResearch.WordTrace]
  refine ⟨301522516361053006234215275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201015010907368670822810183 301522516361053006234215275)
  ·
    refine ⟨452283774541579509351322913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301522516361053006234215275 452283774541579509351322913)
    ·
      refine ⟨339212830906184632013492185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452283774541579509351322913 339212830906184632013492185)
      ·
        refine ⟨254409623179638474010119139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339212830906184632013492185 254409623179638474010119139)
        ·
          refine ⟨381614434769457711015178709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254409623179638474010119139 381614434769457711015178709)
          ·
            refine ⟨8944088314909165101918251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 381614434769457711015178709 8944088314909165101918251)
            ·
              refine ⟨13416132472363747652877377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944088314909165101918251 13416132472363747652877377)
              ·
                refine ⟨10062099354272810739658033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13416132472363747652877377 10062099354272810739658033)
                ·
                  refine ⟨7546574515704608054743525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062099354272810739658033 7546574515704608054743525)
                  ·
                    refine ⟨1414982721694614010264411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546574515704608054743525 1414982721694614010264411)
                    ·
                      rfl

theorem cell23_8267007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_8267007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267007 prefixEnd_8267007 := by exact prefixLift 8267007
  have htrace : WordTrace (prefixWord ++ tailWord_8267007) baseStart_8267007 baseEnd_8267007 := by
    simpa [prefixWord, tailWord_8267007, baseEnd_8267007] using wordTrace_append hprefix tailTrace_8267007
  have hstable : (prefixWord ++ tailWord_8267007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267007).length < 2 ^ (prefixWord ++ tailWord_8267007).sum := by decide
  have hdescent : baseEnd_8267007 < baseStart_8267007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267037 : List Nat := [1, 4, 2, 3, 1, 3, 2, 7]
def baseStart_8267037 : Nat := 118140960795 + 8267037 * 2 ^ 59
def prefixEnd_8267037 : Nat := 4983230072969 + 3 ^ 40 * 8267037 * 2
def baseEnd_8267037 : Nat := 157220872944573219015485

theorem tailTrace_8267037 : CollatzResearch.WordTrace tailWord_8267037 prefixEnd_8267037 157220872944573219015485 := by
  unfold tailWord_8267037
  simp only [CollatzResearch.WordTrace]
  refine ⟨301523610550944321357807365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201015740367296214238538243 301523610550944321357807365)
  ·
    refine ⟨56535676978302060254588881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301523610550944321357807365 56535676978302060254588881)
    ·
      refine ⟨42401757733726545190941661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56535676978302060254588881 42401757733726545190941661)
      ·
        refine ⟨15900659150147454446603123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42401757733726545190941661 15900659150147454446603123)
        ·
          refine ⟨23850988725221181669904685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900659150147454446603123 23850988725221181669904685)
          ·
            refine ⟨8944120771957943126214257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23850988725221181669904685 8944120771957943126214257)
            ·
              refine ⟨6708090578968457344660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8944120771957943126214257 6708090578968457344660693)
              ·
                refine ⟨157220872944573219015485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6708090578968457344660693 157220872944573219015485)
                ·
                  rfl

theorem cell23_8267037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 7].length) (baseStart_8267037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267037 prefixEnd_8267037 := by exact prefixLift 8267037
  have htrace : WordTrace (prefixWord ++ tailWord_8267037) baseStart_8267037 baseEnd_8267037 := by
    simpa [prefixWord, tailWord_8267037, baseEnd_8267037] using wordTrace_append hprefix tailTrace_8267037
  have hstable : (prefixWord ++ tailWord_8267037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267037).length < 2 ^ (prefixWord ++ tailWord_8267037).sum := by decide
  have hdescent : baseEnd_8267037 < baseStart_8267037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267043 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5]
def baseStart_8267043 : Nat := 118140960795 + 8267043 * 2 ^ 59
def prefixEnd_8267043 : Nat := 4983230072969 + 3 ^ 40 * 8267043 * 2
def baseEnd_8267043 : Nat := 4244966650387403889943067

theorem tailTrace_8267043 : CollatzResearch.WordTrace tailWord_8267043 prefixEnd_8267043 4244966650387403889943067 := by
  unfold tailWord_8267043
  simp only [CollatzResearch.WordTrace]
  refine ⟨301523829388922584382525783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201015886259281722921683855 301523829388922584382525783)
  ·
    refine ⟨452285744083383876573788675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301523829388922584382525783 452285744083383876573788675)
    ·
      refine ⟨678428616125075814860683013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452285744083383876573788675 678428616125075814860683013)
      ·
        refine ⟨127205365523451715286378065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678428616125075814860683013 127205365523451715286378065)
        ·
          refine ⟨95404024142588786464783549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127205365523451715286378065 95404024142588786464783549)
          ·
            refine ⟨35776509053470794924293831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95404024142588786464783549 35776509053470794924293831)
            ·
              refine ⟨53664763580206192386440747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35776509053470794924293831 53664763580206192386440747)
              ·
                refine ⟨80497145370309288579661121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53664763580206192386440747 80497145370309288579661121)
                ·
                  refine ⟨60372859027731966434745841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80497145370309288579661121 60372859027731966434745841)
                  ·
                    refine ⟨45279644270798974826059381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60372859027731966434745841 45279644270798974826059381)
                    ·
                      refine ⟨4244966650387403889943067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45279644270798974826059381 4244966650387403889943067)
                      ·
                        rfl

theorem cell23_8267043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_8267043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267043 prefixEnd_8267043 := by exact prefixLift 8267043
  have htrace : WordTrace (prefixWord ++ tailWord_8267043) baseStart_8267043 baseEnd_8267043 := by
    simpa [prefixWord, tailWord_8267043, baseEnd_8267043] using wordTrace_append hprefix tailTrace_8267043
  have hstable : (prefixWord ++ tailWord_8267043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267043).length < 2 ^ (prefixWord ++ tailWord_8267043).sum := by decide
  have hdescent : baseEnd_8267043 < baseStart_8267043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267048 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_8267048 : Nat := 118140960795 + 8267048 * 2 ^ 59
def prefixEnd_8267048 : Nat := 4983230072969 + 3 ^ 40 * 8267048 * 2
def baseEnd_8267048 : Nat := 4244969217790676370380545

theorem tailTrace_8267048 : CollatzResearch.WordTrace tailWord_8267048 prefixEnd_8267048 4244969217790676370380545 := by
  unfold tailWord_8267048
  simp only [CollatzResearch.WordTrace]
  refine ⟨150762005876952235118228899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201016007835936313490971865 150762005876952235118228899)
  ·
    refine ⟨226143008815428352677343349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150762005876952235118228899 226143008815428352677343349)
    ·
      refine ⟨21200907076446408063500939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226143008815428352677343349 21200907076446408063500939)
      ·
        refine ⟨31801360614669612095251409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21200907076446408063500939 31801360614669612095251409)
        ·
          refine ⟨23851020461002209071438557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31801360614669612095251409 23851020461002209071438557)
          ·
            refine ⟨8944132672875828401789459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23851020461002209071438557 8944132672875828401789459)
            ·
              refine ⟨13416199009313742602684189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944132672875828401789459 13416199009313742602684189)
              ·
                refine ⟨5031074628492653476006571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13416199009313742602684189 5031074628492653476006571)
                ·
                  refine ⟨7546611942738980214009857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031074628492653476006571 7546611942738980214009857)
                  ·
                    refine ⟨5659958957054235160507393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546611942738980214009857 5659958957054235160507393)
                    ·
                      refine ⟨4244969217790676370380545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5659958957054235160507393 4244969217790676370380545)
                      ·
                        rfl

theorem cell23_8267048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_8267048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267048 prefixEnd_8267048 := by exact prefixLift 8267048
  have htrace : WordTrace (prefixWord ++ tailWord_8267048) baseStart_8267048 baseEnd_8267048 := by
    simpa [prefixWord, tailWord_8267048, baseEnd_8267048] using wordTrace_append hprefix tailTrace_8267048
  have hstable : (prefixWord ++ tailWord_8267048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267048).length < 2 ^ (prefixWord ++ tailWord_8267048).sum := by decide
  have hdescent : baseEnd_8267048 < baseStart_8267048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267060 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_8267060 : Nat := 118140960795 + 8267060 * 2 ^ 59
def prefixEnd_8267060 : Nat := 4983230072969 + 3 ^ 40 * 8267060 * 2
def baseEnd_8267060 : Nat := 4244975379558530323430489

theorem tailTrace_8267060 : CollatzResearch.WordTrace tailWord_8267060 prefixEnd_8267060 4244975379558530323430489 := by
  unfold tailWord_8267060
  simp only [CollatzResearch.WordTrace]
  refine ⟨150762224714930498142947317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201016299619907330857263089 150762224714930498142947317)
  ·
    refine ⟨14133958567024734200901311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150762224714930498142947317 14133958567024734200901311)
    ·
      refine ⟨21200937850537101301351967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14133958567024734200901311 21200937850537101301351967)
      ·
        refine ⟨31801406775805651952027951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21200937850537101301351967 31801406775805651952027951)
        ·
          refine ⟨47702110163708477928041927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31801406775805651952027951 47702110163708477928041927)
          ·
            refine ⟨71553165245562716892062891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47702110163708477928041927 71553165245562716892062891)
            ·
              refine ⟨107329747868344075338094337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71553165245562716892062891 107329747868344075338094337)
              ·
                refine ⟨80497310901258056503570753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107329747868344075338094337 80497310901258056503570753)
                ·
                  refine ⟨60372983175943542377678065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80497310901258056503570753 60372983175943542377678065)
                  ·
                    refine ⟨45279737381957656783258549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60372983175943542377678065 45279737381957656783258549)
                    ·
                      refine ⟨4244975379558530323430489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45279737381957656783258549 4244975379558530323430489)
                      ·
                        rfl

theorem cell23_8267060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_8267060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267060 prefixEnd_8267060 := by exact prefixLift 8267060
  have htrace : WordTrace (prefixWord ++ tailWord_8267060) baseStart_8267060 baseEnd_8267060 := by
    simpa [prefixWord, tailWord_8267060, baseEnd_8267060] using wordTrace_append hprefix tailTrace_8267060
  have hstable : (prefixWord ++ tailWord_8267060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267060).length < 2 ^ (prefixWord ++ tailWord_8267060).sum := by decide
  have hdescent : baseEnd_8267060 < baseStart_8267060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267070 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_8267070 : Nat := 118140960795 + 8267070 * 2 ^ 59
def prefixEnd_8267070 : Nat := 4983230072969 + 3 ^ 40 * 8267070 * 2
def baseEnd_8267070 : Nat := 4244980514365075284305443

theorem tailTrace_8267070 : CollatzResearch.WordTrace tailWord_8267070 prefixEnd_8267070 4244980514365075284305443 := by
  unfold tailWord_8267070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37690601769978095999219833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201016542773216511995839109 37690601769978095999219833)
  ·
    refine ⟨28267951327483571999414875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37690601769978095999219833 28267951327483571999414875)
    ·
      refine ⟨42401926991225357999122313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28267951327483571999414875 42401926991225357999122313)
      ·
        refine ⟨31801445243419018499341735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42401926991225357999122313 31801445243419018499341735)
        ·
          refine ⟨47702167865128527749012603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31801445243419018499341735 47702167865128527749012603)
          ·
            refine ⟨71553251797692791623518905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47702167865128527749012603 71553251797692791623518905)
            ·
              refine ⟨53664938848269593717639179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71553251797692791623518905 53664938848269593717639179)
              ·
                refine ⟨80497408272404390576458769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53664938848269593717639179 80497408272404390576458769)
                ·
                  refine ⟨60373056204303292932344077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80497408272404390576458769 60373056204303292932344077)
                  ·
                    refine ⟨22639896076613734849629029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60373056204303292932344077 22639896076613734849629029)
                    ·
                      refine ⟨4244980514365075284305443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22639896076613734849629029 4244980514365075284305443)
                      ·
                        rfl

theorem cell23_8267070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_8267070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267070 prefixEnd_8267070 := by exact prefixLift 8267070
  have htrace : WordTrace (prefixWord ++ tailWord_8267070) baseStart_8267070 baseEnd_8267070 := by
    simpa [prefixWord, tailWord_8267070, baseEnd_8267070] using wordTrace_append hprefix tailTrace_8267070
  have hstable : (prefixWord ++ tailWord_8267070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267070).length < 2 ^ (prefixWord ++ tailWord_8267070).sum := by decide
  have hdescent : baseEnd_8267070 < baseStart_8267070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267083 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4]
def baseStart_8267083 : Nat := 118140960795 + 8267083 * 2 ^ 59
def prefixEnd_8267083 : Nat := 4983230072969 + 3 ^ 40 * 8267083 * 2
def baseEnd_8267083 : Nat := 4244987189613583733442883

theorem tailTrace_8267083 : CollatzResearch.WordTrace tailWord_8267083 prefixEnd_8267083 4244987189613583733442883 := by
  unfold tailWord_8267083
  simp only [CollatzResearch.WordTrace]
  refine ⟨301525288308777671213981903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201016858872518447475987935 301525288308777671213981903)
  ·
    refine ⟨452287932463166506820972855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301525288308777671213981903 452287932463166506820972855)
    ·
      refine ⟨678431898694749760231459283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452287932463166506820972855 678431898694749760231459283)
      ·
        refine ⟨1017647848042124640347188925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678431898694749760231459283 1017647848042124640347188925)
        ·
          refine ⟨381617943015796740130195847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1017647848042124640347188925 381617943015796740130195847)
          ·
            refine ⟨572426914523695110195293771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381617943015796740130195847 572426914523695110195293771)
            ·
              refine ⟨858640371785542665292940657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572426914523695110195293771 858640371785542665292940657)
              ·
                refine ⟨643980278839156998969705493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858640371785542665292940657 643980278839156998969705493)
                ·
                  refine ⟨30186575570585484326704945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 643980278839156998969705493 30186575570585484326704945)
                  ·
                    refine ⟨22639931677939113245028709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30186575570585484326704945 22639931677939113245028709)
                    ·
                      refine ⟨4244987189613583733442883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22639931677939113245028709 4244987189613583733442883)
                      ·
                        rfl

theorem cell23_8267083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_8267083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267083 prefixEnd_8267083 := by exact prefixLift 8267083
  have htrace : WordTrace (prefixWord ++ tailWord_8267083) baseStart_8267083 baseEnd_8267083 := by
    simpa [prefixWord, tailWord_8267083, baseEnd_8267083] using wordTrace_append hprefix tailTrace_8267083
  have hstable : (prefixWord ++ tailWord_8267083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267083).length < 2 ^ (prefixWord ++ tailWord_8267083).sum := by decide
  have hdescent : baseEnd_8267083 < baseStart_8267083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267120 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_8267120 : Nat := 118140960795 + 8267120 * 2 ^ 59
def prefixEnd_8267120 : Nat := 4983230072969 + 3 ^ 40 * 8267120 * 2
def baseEnd_8267120 : Nat := 4245006188397800088680213

theorem tailTrace_8267120 : CollatzResearch.WordTrace tailWord_8267120 prefixEnd_8267120 4245006188397800088680213 := by
  unfold tailWord_8267120
  simp only [CollatzResearch.WordTrace]
  refine ⟨150763318904821813266539407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201017758539762417688719209 150763318904821813266539407)
  ·
    refine ⟨226144978357232719899809111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150763318904821813266539407 226144978357232719899809111)
    ·
      refine ⟨339217467535849079849713667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226144978357232719899809111 339217467535849079849713667)
      ·
        refine ⟨508826201303773619774570501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339217467535849079849713667 508826201303773619774570501)
        ·
          refine ⟨95404912744457553707731969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508826201303773619774570501 95404912744457553707731969)
          ·
            refine ⟨71553684558343165280798977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95404912744457553707731969 71553684558343165280798977)
            ·
              refine ⟨53665263418757373960599233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71553684558343165280798977 53665263418757373960599233)
              ·
                refine ⟨40248947564068030470449425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53665263418757373960599233 40248947564068030470449425)
                ·
                  refine ⟨30186710673051022852837069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40248947564068030470449425 30186710673051022852837069)
                  ·
                    refine ⟨11320016502394133569813901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30186710673051022852837069 11320016502394133569813901)
                    ·
                      refine ⟨4245006188397800088680213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320016502394133569813901 4245006188397800088680213)
                      ·
                        rfl

theorem cell23_8267120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_8267120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267120 prefixEnd_8267120 := by exact prefixLift 8267120
  have htrace : WordTrace (prefixWord ++ tailWord_8267120) baseStart_8267120 baseEnd_8267120 := by
    simpa [prefixWord, tailWord_8267120, baseEnd_8267120] using wordTrace_append hprefix tailTrace_8267120
  have hstable : (prefixWord ++ tailWord_8267120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267120).length < 2 ^ (prefixWord ++ tailWord_8267120).sum := by decide
  have hdescent : baseEnd_8267120 < baseStart_8267120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267138 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_8267138 : Nat := 118140960795 + 8267138 * 2 ^ 59
def prefixEnd_8267138 : Nat := 4983230072969 + 3 ^ 40 * 8267138 * 2
def baseEnd_8267138 : Nat := 4245015431049581018255131

theorem tailTrace_8267138 : CollatzResearch.WordTrace tailWord_8267138 prefixEnd_8267138 4245015431049581018255131 := by
  unfold tailWord_8267138
  simp only [CollatzResearch.WordTrace]
  refine ⟨75381823580894603901808517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201018196215718943738156045 75381823580894603901808517)
  ·
    refine ⟨14134091921417738231589097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75381823580894603901808517 14134091921417738231589097)
    ·
      refine ⟨10600568941063303673691823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14134091921417738231589097 10600568941063303673691823)
      ·
        refine ⟨15900853411594955510537735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600568941063303673691823 15900853411594955510537735)
        ·
          refine ⟨23851280117392433265806603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900853411594955510537735 23851280117392433265806603)
          ·
            refine ⟨35776920176088649898709905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23851280117392433265806603 35776920176088649898709905)
            ·
              refine ⟨26832690132066487424032429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35776920176088649898709905 26832690132066487424032429)
              ·
                refine ⟨10062258799524932784012161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26832690132066487424032429 10062258799524932784012161)
                ·
                  refine ⟨7546694099643699588009121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062258799524932784012161 7546694099643699588009121)
                  ·
                    refine ⟨5660020574732774691006841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546694099643699588009121 5660020574732774691006841)
                    ·
                      refine ⟨4245015431049581018255131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660020574732774691006841 4245015431049581018255131)
                      ·
                        rfl

theorem cell23_8267138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_8267138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267138 prefixEnd_8267138 := by exact prefixLift 8267138
  have htrace : WordTrace (prefixWord ++ tailWord_8267138) baseStart_8267138 baseEnd_8267138 := by
    simpa [prefixWord, tailWord_8267138, baseEnd_8267138] using wordTrace_append hprefix tailTrace_8267138
  have hstable : (prefixWord ++ tailWord_8267138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267138).length < 2 ^ (prefixWord ++ tailWord_8267138).sum := by decide
  have hdescent : baseEnd_8267138 < baseStart_8267138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267153 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_8267153 : Nat := 118140960795 + 8267153 * 2 ^ 59
def prefixEnd_8267153 : Nat := 4983230072969 + 3 ^ 40 * 8267153 * 2
def baseEnd_8267153 : Nat := 1415007711086466153189187

theorem tailTrace_8267153 : CollatzResearch.WordTrace tailWord_8267153 prefixEnd_8267153 1415007711086466153189187 := by
  unfold tailWord_8267153
  simp only [CollatzResearch.WordTrace]
  refine ⟨301527841418524073169030113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201018560945682715446020075 301527841418524073169030113)
  ·
    refine ⟨226145881063893054876772585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301527841418524073169030113 226145881063893054876772585)
    ·
      refine ⟨169609410797919791157579439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226145881063893054876772585 169609410797919791157579439)
      ·
        refine ⟨254414116196879686736369159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169609410797919791157579439 254414116196879686736369159)
        ·
          refine ⟨381621174295319530104553739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254414116196879686736369159 381621174295319530104553739)
          ·
            refine ⟨572431761442979295156830609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381621174295319530104553739 572431761442979295156830609)
            ·
              refine ⟨429323821082234471367622957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572431761442979295156830609 429323821082234471367622957)
              ·
                refine ⟨160996432905837926762858609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429323821082234471367622957 160996432905837926762858609)
                ·
                  refine ⟨120747324679378445072143957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160996432905837926762858609 120747324679378445072143957)
                  ·
                    refine ⟨1415007711086466153189187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120747324679378445072143957 1415007711086466153189187)
                    ·
                      rfl

theorem cell23_8267153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_8267153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267153 prefixEnd_8267153 := by exact prefixLift 8267153
  have htrace : WordTrace (prefixWord ++ tailWord_8267153) baseStart_8267153 baseEnd_8267153 := by
    simpa [prefixWord, tailWord_8267153, baseEnd_8267153] using wordTrace_append hprefix tailTrace_8267153
  have hstable : (prefixWord ++ tailWord_8267153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267153).length < 2 ^ (prefixWord ++ tailWord_8267153).sum := by decide
  have hdescent : baseEnd_8267153 < baseStart_8267153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267200 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 6]
def baseStart_8267200 : Nat := 118140960795 + 8267200 * 2 ^ 59
def prefixEnd_8267200 : Nat := 4983230072969 + 3 ^ 40 * 8267200 * 2
def baseEnd_8267200 : Nat := 471671918538906641742205

theorem tailTrace_8267200 : CollatzResearch.WordTrace tailWord_8267200 prefixEnd_8267200 471671918538906641742205 := by
  unfold tailWord_8267200
  simp only [CollatzResearch.WordTrace]
  refine ⟨150764777824676900097995527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201019703766235866797327369 150764777824676900097995527)
  ·
    refine ⟨226147166737015350146993291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150764777824676900097995527 226147166737015350146993291)
    ·
      refine ⟨339220750105523025220489937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226147166737015350146993291 339220750105523025220489937)
      ·
        refine ⟨254415562579142268915367453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339220750105523025220489937 254415562579142268915367453)
        ·
          refine ⟨95405835967178350843262795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254415562579142268915367453 95405835967178350843262795)
          ·
            refine ⟨143108753950767526264894193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95405835967178350843262795 143108753950767526264894193)
            ·
              refine ⟨107331565463075644698670645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143108753950767526264894193 107331565463075644698670645)
              ·
                refine ⟨10062334262163341690500373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107331565463075644698670645 10062334262163341690500373)
                ·
                  refine ⟨471671918538906641742205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10062334262163341690500373 471671918538906641742205)
                  ·
                    rfl

theorem cell23_8267200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_8267200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267200 prefixEnd_8267200 := by exact prefixLift 8267200
  have htrace : WordTrace (prefixWord ++ tailWord_8267200) baseStart_8267200 baseEnd_8267200 := by
    simpa [prefixWord, tailWord_8267200, baseEnd_8267200] using wordTrace_append hprefix tailTrace_8267200
  have hstable : (prefixWord ++ tailWord_8267200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267200).length < 2 ^ (prefixWord ++ tailWord_8267200).sum := by decide
  have hdescent : baseEnd_8267200 < baseStart_8267200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267204 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_8267204 : Nat := 118140960795 + 8267204 * 2 ^ 59
def prefixEnd_8267204 : Nat := 4983230072969 + 3 ^ 40 * 8267204 * 2
def baseEnd_8267204 : Nat := 1415016440257592586676609

theorem tailTrace_8267204 : CollatzResearch.WordTrace tailWord_8267204 prefixEnd_8267204 1415016440257592586676609 := by
  unfold tailWord_8267204
  simp only [CollatzResearch.WordTrace]
  refine ⟨150764850770669654439568333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201019801027559539252757777 150764850770669654439568333)
  ·
    refine ⟨56536819039001120414838125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150764850770669654439568333 56536819039001120414838125)
    ·
      refine ⟨21201307139625420155564297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56536819039001120414838125 21201307139625420155564297)
      ·
        refine ⟨15900980354719065116673223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21201307139625420155564297 15900980354719065116673223)
        ·
          refine ⟨23851470532078597675009835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900980354719065116673223 23851470532078597675009835)
          ·
            refine ⟨35777205798117896512514753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23851470532078597675009835 35777205798117896512514753)
            ·
              refine ⟨26832904348588422384386065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35777205798117896512514753 26832904348588422384386065)
              ·
                refine ⟨20124678261441316788289549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26832904348588422384386065 20124678261441316788289549)
                ·
                  refine ⟨7546754348040493795608581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20124678261441316788289549 7546754348040493795608581)
                  ·
                    refine ⟨1415016440257592586676609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546754348040493795608581 1415016440257592586676609)
                    ·
                      rfl

theorem cell23_8267204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_8267204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267204 prefixEnd_8267204 := by exact prefixLift 8267204
  have htrace : WordTrace (prefixWord ++ tailWord_8267204) baseStart_8267204 baseEnd_8267204 := by
    simpa [prefixWord, tailWord_8267204, baseEnd_8267204] using wordTrace_append hprefix tailTrace_8267204
  have hstable : (prefixWord ++ tailWord_8267204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267204).length < 2 ^ (prefixWord ++ tailWord_8267204).sum := by decide
  have hdescent : baseEnd_8267204 < baseStart_8267204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267267 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 4]
def baseStart_8267267 : Nat := 118140960795 + 8267267 * 2 ^ 59
def prefixEnd_8267267 : Nat := 4983230072969 + 3 ^ 40 * 8267267 * 2
def baseEnd_8267267 : Nat := 4245081670054011013542037

theorem tailTrace_8267267 : CollatzResearch.WordTrace tailWord_8267267 prefixEnd_8267267 4245081670054011013542037 := by
  unfold tailWord_8267267
  simp only [CollatzResearch.WordTrace]
  refine ⟨301531999340111070638680055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201021332893407380425786703 301531999340111070638680055)
  ·
    refine ⟨452297999010166605958020083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301531999340111070638680055 452297999010166605958020083)
    ·
      refine ⟨678446998515249908937030125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452297999010166605958020083 678446998515249908937030125)
      ·
        refine ⟨254417624443218715851386297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678446998515249908937030125 254417624443218715851386297)
        ·
          refine ⟨190813218332414036888539723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254417624443218715851386297 190813218332414036888539723)
          ·
            refine ⟨286219827498621055332809585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190813218332414036888539723 286219827498621055332809585)
            ·
              refine ⟨214664870623965791499607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286219827498621055332809585 214664870623965791499607189)
              ·
                refine ⟨10062415810498396476544087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214664870623965791499607189 10062415810498396476544087)
                ·
                  refine ⟨15093623715747594714816131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062415810498396476544087 15093623715747594714816131)
                  ·
                    refine ⟨22640435573621392072224197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15093623715747594714816131 22640435573621392072224197)
                    ·
                      refine ⟨4245081670054011013542037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22640435573621392072224197 4245081670054011013542037)
                      ·
                        rfl

theorem cell23_8267267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_8267267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267267 prefixEnd_8267267 := by exact prefixLift 8267267
  have htrace : WordTrace (prefixWord ++ tailWord_8267267) baseStart_8267267 baseEnd_8267267 := by
    simpa [prefixWord, tailWord_8267267, baseEnd_8267267] using wordTrace_append hprefix tailTrace_8267267
  have hstable : (prefixWord ++ tailWord_8267267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267267).length < 2 ^ (prefixWord ++ tailWord_8267267).sum := by decide
  have hdescent : baseEnd_8267267 < baseStart_8267267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267271 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_8267271 : Nat := 118140960795 + 8267271 * 2 ^ 59
def prefixEnd_8267271 : Nat := 4983230072969 + 3 ^ 40 * 8267271 * 2
def baseEnd_8267271 : Nat := 4245083723976628997892019

theorem tailTrace_8267271 : CollatzResearch.WordTrace tailWord_8267271 prefixEnd_8267271 4245083723976628997892019 := by
  unfold tailWord_8267271
  simp only [CollatzResearch.WordTrace]
  refine ⟨301532145232096579321825667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201021430154731052881217111 301532145232096579321825667)
  ·
    refine ⟨452298217848144868982738501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301532145232096579321825667 452298217848144868982738501)
    ·
      refine ⟨84805915846527162934263469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452298217848144868982738501 84805915846527162934263469)
      ·
        refine ⟨31802218442447686100348801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84805915846527162934263469 31802218442447686100348801)
        ·
          refine ⟨23851663831835764575261601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31802218442447686100348801 23851663831835764575261601)
          ·
            refine ⟨17888747873876823431446201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23851663831835764575261601 17888747873876823431446201)
            ·
              refine ⟨13416560905407617573584651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17888747873876823431446201 13416560905407617573584651)
              ·
                refine ⟨20124841358111426360376977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13416560905407617573584651 20124841358111426360376977)
                ·
                  refine ⟨15093631018583569770282733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20124841358111426360376977 15093631018583569770282733)
                  ·
                    refine ⟨5660111631968838663856025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15093631018583569770282733 5660111631968838663856025)
                    ·
                      refine ⟨4245083723976628997892019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660111631968838663856025 4245083723976628997892019)
                      ·
                        rfl

theorem cell23_8267271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_8267271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267271 prefixEnd_8267271 := by exact prefixLift 8267271
  have htrace : WordTrace (prefixWord ++ tailWord_8267271) baseStart_8267271 baseEnd_8267271 := by
    simpa [prefixWord, tailWord_8267271, baseEnd_8267271] using wordTrace_append hprefix tailTrace_8267271
  have hstable : (prefixWord ++ tailWord_8267271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267271).length < 2 ^ (prefixWord ++ tailWord_8267271).sum := by decide
  have hdescent : baseEnd_8267271 < baseStart_8267271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267324 : List Nat := [2, 2, 2, 2, 4, 1, 3, 7]
def baseStart_8267324 : Nat := 118140960795 + 8267324 * 2 ^ 59
def prefixEnd_8267324 : Nat := 4983230072969 + 3 ^ 40 * 8267324 * 2
def baseEnd_8267324 : Nat := 157226331053752492241825

theorem tailTrace_8267324 : CollatzResearch.WordTrace tailWord_8267324 prefixEnd_8267324 157226331053752492241825 := by
  unfold tailWord_8267324
  simp only [CollatzResearch.WordTrace]
  refine ⟨150767039150452284686752513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201022718867269712915670017 150767039150452284686752513)
  ·
    refine ⟨113075279362839213515064385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150767039150452284686752513 113075279362839213515064385)
    ·
      refine ⟨84806459522129410136298289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113075279362839213515064385 84806459522129410136298289)
      ·
        refine ⟨63604844641597057602223717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84806459522129410136298289 63604844641597057602223717)
        ·
          refine ⟨11925908370299448300416947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63604844641597057602223717 11925908370299448300416947)
          ·
            refine ⟨17888862555449172450625421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11925908370299448300416947 17888862555449172450625421)
            ·
              refine ⟨6708323458293439668984533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17888862555449172450625421 6708323458293439668984533)
              ·
                refine ⟨157226331053752492241825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6708323458293439668984533 157226331053752492241825)
                ·
                  rfl

theorem cell23_8267324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 7].length) (baseStart_8267324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267324 prefixEnd_8267324 := by exact prefixLift 8267324
  have htrace : WordTrace (prefixWord ++ tailWord_8267324) baseStart_8267324 baseEnd_8267324 := by
    simpa [prefixWord, tailWord_8267324, baseEnd_8267324] using wordTrace_append hprefix tailTrace_8267324
  have hstable : (prefixWord ++ tailWord_8267324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267324).length < 2 ^ (prefixWord ++ tailWord_8267324).sum := by decide
  have hdescent : baseEnd_8267324 < baseStart_8267324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267335 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_8267335 : Nat := 118140960795 + 8267335 * 2 ^ 59
def prefixEnd_8267335 : Nat := 4983230072969 + 3 ^ 40 * 8267335 * 2
def baseEnd_8267335 : Nat := 4245116586738516747491725

theorem tailTrace_8267335 : CollatzResearch.WordTrace tailWord_8267335 prefixEnd_8267335 4245116586738516747491725 := by
  unfold tailWord_8267335
  simp only [CollatzResearch.WordTrace]
  refine ⟨301534479503864718252155459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201022986335909812168103639 301534479503864718252155459)
  ·
    refine ⟨452301719255797077378233189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301534479503864718252155459 452301719255797077378233189)
    ·
      refine ⟨84806572360461952008418723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452301719255797077378233189 84806572360461952008418723)
      ·
        refine ⟨127209858540692928012628085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84806572360461952008418723 127209858540692928012628085)
        ·
          refine ⟨11925924238189962001183883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127209858540692928012628085 11925924238189962001183883)
          ·
            refine ⟨17888886357284943001775825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11925924238189962001183883 17888886357284943001775825)
            ·
              refine ⟨13416664767963707251331869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17888886357284943001775825 13416664767963707251331869)
              ·
                refine ⟨5031249287986390219249451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13416664767963707251331869 5031249287986390219249451)
                ·
                  refine ⟨7546873931979585328874177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031249287986390219249451 7546873931979585328874177)
                  ·
                    refine ⟨5660155448984688996655633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546873931979585328874177 5660155448984688996655633)
                    ·
                      refine ⟨4245116586738516747491725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660155448984688996655633 4245116586738516747491725)
                      ·
                        rfl

theorem cell23_8267335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_8267335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267335 prefixEnd_8267335 := by exact prefixLift 8267335
  have htrace : WordTrace (prefixWord ++ tailWord_8267335) baseStart_8267335 baseEnd_8267335 := by
    simpa [prefixWord, tailWord_8267335, baseEnd_8267335] using wordTrace_append hprefix tailTrace_8267335
  have hstable : (prefixWord ++ tailWord_8267335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267335).length < 2 ^ (prefixWord ++ tailWord_8267335).sum := by decide
  have hdescent : baseEnd_8267335 < baseStart_8267335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267351 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_8267351 : Nat := 118140960795 + 8267351 * 2 ^ 59
def prefixEnd_8267351 : Nat := 4983230072969 + 3 ^ 40 * 8267351 * 2
def baseEnd_8267351 : Nat := 4245124802428988684891651

theorem tailTrace_8267351 : CollatzResearch.WordTrace tailWord_8267351 prefixEnd_8267351 4245124802428988684891651 := by
  unfold tailWord_8267351
  simp only [CollatzResearch.WordTrace]
  refine ⟨301535063071806752984737907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201023375381204501989825271 301535063071806752984737907)
  ·
    refine ⟨452302594607710129477106861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301535063071806752984737907 452302594607710129477106861)
    ·
      refine ⟨169613472977891298553915073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452302594607710129477106861 169613472977891298553915073)
      ·
        refine ⟨127210104733418473915436305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169613472977891298553915073 127210104733418473915436305)
        ·
          refine ⟨95407578550063855436577229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127210104733418473915436305 95407578550063855436577229)
          ·
            refine ⟨35777841956273945788716461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95407578550063855436577229 35777841956273945788716461)
            ·
              refine ⟨13416690733602729670768673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35777841956273945788716461 13416690733602729670768673)
              ·
                refine ⟨10062518050202047253076505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13416690733602729670768673 10062518050202047253076505)
                ·
                  refine ⟨7546888537651535439807379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062518050202047253076505 7546888537651535439807379)
                  ·
                    refine ⟨11320332806477303159711069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7546888537651535439807379 11320332806477303159711069)
                    ·
                      refine ⟨4245124802428988684891651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320332806477303159711069 4245124802428988684891651)
                      ·
                        rfl

theorem cell23_8267351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_8267351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267351 prefixEnd_8267351 := by exact prefixLift 8267351
  have htrace : WordTrace (prefixWord ++ tailWord_8267351) baseStart_8267351 baseEnd_8267351 := by
    simpa [prefixWord, tailWord_8267351, baseEnd_8267351] using wordTrace_append hprefix tailTrace_8267351
  have hstable : (prefixWord ++ tailWord_8267351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267351).length < 2 ^ (prefixWord ++ tailWord_8267351).sum := by decide
  have hdescent : baseEnd_8267351 < baseStart_8267351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267367 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 2, 6]
def baseStart_8267367 : Nat := 118140960795 + 8267367 * 2 ^ 59
def prefixEnd_8267367 : Nat := 4983230072969 + 3 ^ 40 * 8267367 * 2
def baseEnd_8267367 : Nat := 1415044339373153540763859

theorem tailTrace_8267367 : CollatzResearch.WordTrace tailWord_8267367 prefixEnd_8267367 1415044339373153540763859 := by
  unfold tailWord_8267367
  simp only [CollatzResearch.WordTrace]
  refine ⟨301535646639748787717320355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201023764426499191811546903 301535646639748787717320355)
  ·
    refine ⟨452303469959623181575980533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301535646639748787717320355 452303469959623181575980533)
    ·
      refine ⟨42403450308714673272748175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452303469959623181575980533 42403450308714673272748175)
      ·
        refine ⟨63605175463072009909122263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42403450308714673272748175 63605175463072009909122263)
        ·
          refine ⟨95407763194608014863683395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63605175463072009909122263 95407763194608014863683395)
          ·
            refine ⟨143111644791912022295525093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95407763194608014863683395 143111644791912022295525093)
            ·
              refine ⟨26833433398483504180410955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143111644791912022295525093 26833433398483504180410955)
              ·
                refine ⟨40250150097725256270616433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26833433398483504180410955 40250150097725256270616433)
                ·
                  refine ⟨30187612573293942202962325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40250150097725256270616433 30187612573293942202962325)
                  ·
                    refine ⟨1415044339373153540763859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30187612573293942202962325 1415044339373153540763859)
                    ·
                      rfl

theorem cell23_8267367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_8267367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267367 prefixEnd_8267367 := by exact prefixLift 8267367
  have htrace : WordTrace (prefixWord ++ tailWord_8267367) baseStart_8267367 baseEnd_8267367 := by
    simpa [prefixWord, tailWord_8267367, baseEnd_8267367] using wordTrace_append hprefix tailTrace_8267367
  have hstable : (prefixWord ++ tailWord_8267367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267367).length < 2 ^ (prefixWord ++ tailWord_8267367).sum := by decide
  have hdescent : baseEnd_8267367 < baseStart_8267367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267377 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_8267377 : Nat := 118140960795 + 8267377 * 2 ^ 59
def prefixEnd_8267377 : Nat := 4983230072969 + 3 ^ 40 * 8267377 * 2
def baseEnd_8267377 : Nat := 4245138152926005583166531

theorem tailTrace_8267377 : CollatzResearch.WordTrace tailWord_8267377 prefixEnd_8267377 4245138152926005583166531 := by
  unfold tailWord_8267377
  simp only [CollatzResearch.WordTrace]
  refine ⟨301536011369712559425184385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201024007579808372950122923 301536011369712559425184385)
  ·
    refine ⟨226152008527284419568888289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301536011369712559425184385 226152008527284419568888289)
    ·
      refine ⟨169614006395463314676666217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226152008527284419568888289 169614006395463314676666217)
      ·
        refine ⟨127210504796597486007499663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169614006395463314676666217 127210504796597486007499663)
        ·
          refine ⟨190815757194896229011249495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127210504796597486007499663 190815757194896229011249495)
          ·
            refine ⟨286223635792344343516874243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190815757194896229011249495 286223635792344343516874243)
            ·
              refine ⟨429335453688516515275311365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286223635792344343516874243 429335453688516515275311365)
              ·
                refine ⟨80500397566596846614120881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429335453688516515275311365 80500397566596846614120881)
                ·
                  refine ⟨60375298174947634960590661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80500397566596846614120881 60375298174947634960590661)
                  ·
                    refine ⟨11320368407802681555110749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60375298174947634960590661 11320368407802681555110749)
                    ·
                      refine ⟨4245138152926005583166531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320368407802681555110749 4245138152926005583166531)
                      ·
                        rfl

theorem cell23_8267377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_8267377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267377 prefixEnd_8267377 := by exact prefixLift 8267377
  have htrace : WordTrace (prefixWord ++ tailWord_8267377) baseStart_8267377 baseEnd_8267377 := by
    simpa [prefixWord, tailWord_8267377, baseEnd_8267377] using wordTrace_append hprefix tailTrace_8267377
  have hstable : (prefixWord ++ tailWord_8267377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267377).length < 2 ^ (prefixWord ++ tailWord_8267377).sum := by decide
  have hdescent : baseEnd_8267377 < baseStart_8267377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267378 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_8267378 : Nat := 118140960795 + 8267378 * 2 ^ 59
def prefixEnd_8267378 : Nat := 4983230072969 + 3 ^ 40 * 8267378 * 2
def baseEnd_8267378 : Nat := 4245138666406660079254027

theorem tailTrace_8267378 : CollatzResearch.WordTrace tailWord_8267378 prefixEnd_8267378 4245138666406660079254027 := by
  unfold tailWord_8267378
  simp only [CollatzResearch.WordTrace]
  refine ⟨75384011960677234148992697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201024031895139291063980525 75384011960677234148992697)
  ·
    refine ⟨56538008970507925611744523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75384011960677234148992697 56538008970507925611744523)
    ·
      refine ⟨84807013455761888417616785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56538008970507925611744523 84807013455761888417616785)
      ·
        refine ⟨63605260091821416313212589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84807013455761888417616785 63605260091821416313212589)
        ·
          refine ⟨23851972534433031117454721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63605260091821416313212589 23851972534433031117454721)
          ·
            refine ⟨17888979400824773338091041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23851972534433031117454721 17888979400824773338091041)
            ·
              refine ⟨13416734550618580003568281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17888979400824773338091041 13416734550618580003568281)
              ·
                refine ⟨10062550912963935002676211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13416734550618580003568281 10062550912963935002676211)
                ·
                  refine ⟨15093826369445902504014317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062550912963935002676211 15093826369445902504014317)
                  ·
                    refine ⟨5660184888542213439005369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15093826369445902504014317 5660184888542213439005369)
                    ·
                      refine ⟨4245138666406660079254027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660184888542213439005369 4245138666406660079254027)
                      ·
                        rfl

theorem cell23_8267378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_8267378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267378 prefixEnd_8267378 := by exact prefixLift 8267378
  have htrace : WordTrace (prefixWord ++ tailWord_8267378) baseStart_8267378 baseEnd_8267378 := by
    simpa [prefixWord, tailWord_8267378, baseEnd_8267378] using wordTrace_append hprefix tailTrace_8267378
  have hstable : (prefixWord ++ tailWord_8267378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267378).length < 2 ^ (prefixWord ++ tailWord_8267378).sum := by decide
  have hdescent : baseEnd_8267378 < baseStart_8267378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267425 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_8267425 : Nat := 118140960795 + 8267425 * 2 ^ 59
def prefixEnd_8267425 : Nat := 4983230072969 + 3 ^ 40 * 8267425 * 2
def baseEnd_8267425 : Nat := 4245162799997421395366311

theorem tailTrace_8267425 : CollatzResearch.WordTrace tailWord_8267425 prefixEnd_8267425 4245162799997421395366311 := by
  unfold tailWord_8267425
  simp only [CollatzResearch.WordTrace]
  refine ⟨301537762073538663622931729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201025174715692442415287819 301537762073538663622931729)
  ·
    refine ⟨226153321555153997717198797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301537762073538663622931729 226153321555153997717198797)
    ·
      refine ⟨84807495583182749143949549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226153321555153997717198797 84807495583182749143949549)
      ·
        refine ⟨31802810843693530928981081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84807495583182749143949549 31802810843693530928981081)
        ·
          refine ⟨23852108132770148196735811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31802810843693530928981081 23852108132770148196735811)
          ·
            refine ⟨35778162199155222295103717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23852108132770148196735811 35778162199155222295103717)
            ·
              refine ⟨6708405412341604180331947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35778162199155222295103717 6708405412341604180331947)
              ·
                refine ⟨10062608118512406270497921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708405412341604180331947 10062608118512406270497921)
                ·
                  refine ⟨7546956088884304702873441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062608118512406270497921 7546956088884304702873441)
                  ·
                    refine ⟨5660217066663228527155081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7546956088884304702873441 5660217066663228527155081)
                    ·
                      refine ⟨4245162799997421395366311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660217066663228527155081 4245162799997421395366311)
                      ·
                        rfl

theorem cell23_8267425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_8267425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267425 prefixEnd_8267425 := by exact prefixLift 8267425
  have htrace : WordTrace (prefixWord ++ tailWord_8267425) baseStart_8267425 baseEnd_8267425 := by
    simpa [prefixWord, tailWord_8267425, baseEnd_8267425] using wordTrace_append hprefix tailTrace_8267425
  have hstable : (prefixWord ++ tailWord_8267425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267425).length < 2 ^ (prefixWord ++ tailWord_8267425).sum := by decide
  have hdescent : baseEnd_8267425 < baseStart_8267425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267427 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 4, 5]
def baseStart_8267427 : Nat := 118140960795 + 8267427 * 2 ^ 59
def prefixEnd_8267427 : Nat := 4983230072969 + 3 ^ 40 * 8267427 * 2
def baseEnd_8267427 : Nat := 1415054608986243462513767

theorem tailTrace_8267427 : CollatzResearch.WordTrace tailWord_8267427 prefixEnd_8267427 1415054608986243462513767 := by
  unfold tailWord_8267427
  simp only [CollatzResearch.WordTrace]
  refine ⟨301537835019531417964504535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201025223346354278643003023 301537835019531417964504535)
  ·
    refine ⟨452306752529297126946756803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301537835019531417964504535 452306752529297126946756803)
    ·
      refine ⟨678460128793945690420135205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452306752529297126946756803 678460128793945690420135205)
      ·
        refine ⟨127211274148864816953775351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678460128793945690420135205 127211274148864816953775351)
        ·
          refine ⟨190816911223297225430663027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127211274148864816953775351 190816911223297225430663027)
          ·
            refine ⟨286225366834945838145994541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190816911223297225430663027 286225366834945838145994541)
            ·
              refine ⟨107334512563104689304747953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286225366834945838145994541 107334512563104689304747953)
              ·
                refine ⟨80500884422328516978560965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107334512563104689304747953 80500884422328516978560965)
                ·
                  refine ⟨15093915829186596933480181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80500884422328516978560965 15093915829186596933480181)
                  ·
                    refine ⟨1415054608986243462513767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15093915829186596933480181 1415054608986243462513767)
                    ·
                      rfl

theorem cell23_8267427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 5].length) (baseStart_8267427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267427 prefixEnd_8267427 := by exact prefixLift 8267427
  have htrace : WordTrace (prefixWord ++ tailWord_8267427) baseStart_8267427 baseEnd_8267427 := by
    simpa [prefixWord, tailWord_8267427, baseEnd_8267427] using wordTrace_append hprefix tailTrace_8267427
  have hstable : (prefixWord ++ tailWord_8267427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267427).length < 2 ^ (prefixWord ++ tailWord_8267427).sum := by decide
  have hdescent : baseEnd_8267427 < baseStart_8267427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267454 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_8267454 : Nat := 118140960795 + 8267454 * 2 ^ 59
def prefixEnd_8267454 : Nat := 4983230072969 + 3 ^ 40 * 8267454 * 2
def baseEnd_8267454 : Nat := 4245177690936401781903677

theorem tailTrace_8267454 : CollatzResearch.WordTrace tailWord_8267454 prefixEnd_8267454 4245177690936401781903677 := by
  unfold tailWord_8267454
  simp only [CollatzResearch.WordTrace]
  refine ⟨37692352473804200196967177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201025879860289067717158277 37692352473804200196967177)
  ·
    refine ⟨28269264355353150147725383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37692352473804200196967177 28269264355353150147725383)
    ·
      refine ⟨42403896533029725221588075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28269264355353150147725383 42403896533029725221588075)
      ·
        refine ⟨63605844799544587832382113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42403896533029725221588075 63605844799544587832382113)
        ·
          refine ⟨47704383599658440874286585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63605844799544587832382113 47704383599658440874286585)
          ·
            refine ⟨35778287699743830655714939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47704383599658440874286585 35778287699743830655714939)
            ·
              refine ⟨53667431549615745983572409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35778287699743830655714939 53667431549615745983572409)
              ·
                refine ⟨40250573662211809487679307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53667431549615745983572409 40250573662211809487679307)
                ·
                  refine ⟨60375860493317714231518961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40250573662211809487679307 60375860493317714231518961)
                  ·
                    refine ⟨45281895369988285673639221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60375860493317714231518961 45281895369988285673639221)
                    ·
                      refine ⟨4245177690936401781903677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45281895369988285673639221 4245177690936401781903677)
                      ·
                        rfl

theorem cell23_8267454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_8267454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267454 prefixEnd_8267454 := by exact prefixLift 8267454
  have htrace : WordTrace (prefixWord ++ tailWord_8267454) baseStart_8267454 baseEnd_8267454 := by
    simpa [prefixWord, tailWord_8267454, baseEnd_8267454] using wordTrace_append hprefix tailTrace_8267454
  have hstable : (prefixWord ++ tailWord_8267454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267454).length < 2 ^ (prefixWord ++ tailWord_8267454).sum := by decide
  have hdescent : baseEnd_8267454 < baseStart_8267454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267464 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_8267464 : Nat := 118140960795 + 8267464 * 2 ^ 59
def prefixEnd_8267464 : Nat := 4983230072969 + 3 ^ 40 * 8267464 * 2
def baseEnd_8267464 : Nat := 4245182825742946742778631

theorem tailTrace_8267464 : CollatzResearch.WordTrace tailWord_8267464 prefixEnd_8267464 4245182825742946742778631 := by
  unfold tailWord_8267464
  simp only [CollatzResearch.WordTrace]
  refine ⟨150769592260198686641800723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201026123013598248855734297 150769592260198686641800723)
  ·
    refine ⟨226154388390298029962701085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150769592260198686641800723 226154388390298029962701085)
    ·
      refine ⟨84807895646361761236012907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226154388390298029962701085 84807895646361761236012907)
      ·
        refine ⟨127211843469542641854019361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84807895646361761236012907 127211843469542641854019361)
        ·
          refine ⟨95408882602156981390514521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127211843469542641854019361 95408882602156981390514521)
          ·
            refine ⟨71556661951617736042885891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95408882602156981390514521 71556661951617736042885891)
            ·
              refine ⟨107334992927426604064328837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71556661951617736042885891 107334992927426604064328837)
              ·
                refine ⟨20125311173892488262061657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107334992927426604064328837 20125311173892488262061657)
                ·
                  refine ⟨15093983380419366196546243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20125311173892488262061657 15093983380419366196546243)
                  ·
                    refine ⟨22640975070629049294819365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15093983380419366196546243 22640975070629049294819365)
                    ·
                      refine ⟨4245182825742946742778631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22640975070629049294819365 4245182825742946742778631)
                      ·
                        rfl

theorem cell23_8267464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_8267464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267464 prefixEnd_8267464 := by exact prefixLift 8267464
  have htrace : WordTrace (prefixWord ++ tailWord_8267464) baseStart_8267464 baseEnd_8267464 := by
    simpa [prefixWord, tailWord_8267464, baseEnd_8267464] using wordTrace_append hprefix tailTrace_8267464
  have hstable : (prefixWord ++ tailWord_8267464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267464).length < 2 ^ (prefixWord ++ tailWord_8267464).sum := by decide
  have hdescent : baseEnd_8267464 < baseStart_8267464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267481 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 2, 4, 2]
def baseStart_8267481 : Nat := 118140960795 + 8267481 * 2 ^ 59
def prefixEnd_8267481 : Nat := 4983230072969 + 3 ^ 40 * 8267481 * 2
def baseEnd_8267481 : Nat := 4245191554914073176266053

theorem tailTrace_8267481 : CollatzResearch.WordTrace tailWord_8267481 prefixEnd_8267481 4245191554914073176266053 := by
  unfold tailWord_8267481
  simp only [CollatzResearch.WordTrace]
  refine ⟨301539804561335785186970297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201026536374223856791313531 301539804561335785186970297)
  ·
    refine ⟨226154853421001838890227723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301539804561335785186970297 226154853421001838890227723)
    ·
      refine ⟨339232280131502758335341585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226154853421001838890227723 339232280131502758335341585)
      ·
        refine ⟨254424210098627068751506189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339232280131502758335341585 254424210098627068751506189)
        ·
          refine ⟨95409078786985150781814821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254424210098627068751506189 95409078786985150781814821)
          ·
            refine ⟨17889202272559715771590279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95409078786985150781814821 17889202272559715771590279)
            ·
              refine ⟨26833803408839573657385419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889202272559715771590279 26833803408839573657385419)
              ·
                refine ⟨40250705113259360486078129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26833803408839573657385419 40250705113259360486078129)
                ·
                  refine ⟨30188028834944520364558597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40250705113259360486078129 30188028834944520364558597)
                  ·
                    refine ⟨5660255406552097568354737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30188028834944520364558597 5660255406552097568354737)
                    ·
                      refine ⟨4245191554914073176266053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660255406552097568354737 4245191554914073176266053)
                      ·
                        rfl

theorem cell23_8267481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_8267481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267481 prefixEnd_8267481 := by exact prefixLift 8267481
  have htrace : WordTrace (prefixWord ++ tailWord_8267481) baseStart_8267481 baseEnd_8267481 := by
    simpa [prefixWord, tailWord_8267481, baseEnd_8267481] using wordTrace_append hprefix tailTrace_8267481
  have hstable : (prefixWord ++ tailWord_8267481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267481).length < 2 ^ (prefixWord ++ tailWord_8267481).sum := by decide
  have hdescent : baseEnd_8267481 < baseStart_8267481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267495 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 2, 5]
def baseStart_8267495 : Nat := 118140960795 + 8267495 * 2 ^ 59
def prefixEnd_8267495 : Nat := 4983230072969 + 3 ^ 40 * 8267495 * 2
def baseEnd_8267495 : Nat := 1415066247881078707163663

theorem tailTrace_8267495 : CollatzResearch.WordTrace tailWord_8267495 prefixEnd_8267495 1415066247881078707163663 := by
  unfold tailWord_8267495
  simp only [CollatzResearch.WordTrace]
  refine ⟨301540315183285065577979939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201026876788856710385319959 301540315183285065577979939)
  ·
    refine ⟨452310472774927598366969909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301540315183285065577979939 452310472774927598366969909)
    ·
      refine ⟨42404106822649462346903429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452310472774927598366969909 42404106822649462346903429)
      ·
        refine ⟨7950770029246774190044393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42404106822649462346903429 7950770029246774190044393)
        ·
          refine ⟨5963077521935080642533295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7950770029246774190044393 5963077521935080642533295)
          ·
            refine ⟨8944616282902620963799943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963077521935080642533295 8944616282902620963799943)
            ·
              refine ⟨13416924424353931445699915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944616282902620963799943 13416924424353931445699915)
              ·
                refine ⟨20125386636530897168549873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13416924424353931445699915 20125386636530897168549873)
                ·
                  refine ⟨15094039977398172876412405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20125386636530897168549873 15094039977398172876412405)
                  ·
                    refine ⟨1415066247881078707163663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15094039977398172876412405 1415066247881078707163663)
                    ·
                      rfl

theorem cell23_8267495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_8267495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267495 prefixEnd_8267495 := by exact prefixLift 8267495
  have htrace : WordTrace (prefixWord ++ tailWord_8267495) baseStart_8267495 baseEnd_8267495 := by
    simpa [prefixWord, tailWord_8267495, baseEnd_8267495] using wordTrace_append hprefix tailTrace_8267495
  have hstable : (prefixWord ++ tailWord_8267495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267495).length < 2 ^ (prefixWord ++ tailWord_8267495).sum := by decide
  have hdescent : baseEnd_8267495 < baseStart_8267495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267501 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_8267501 : Nat := 118140960795 + 8267501 * 2 ^ 59
def prefixEnd_8267501 : Nat := 4983230072969 + 3 ^ 40 * 8267501 * 2
def baseEnd_8267501 : Nat := 4245201824527163098015961

theorem tailTrace_8267501 : CollatzResearch.WordTrace tailWord_8267501 prefixEnd_8267501 4245201824527163098015961 := by
  unfold tailWord_8267501
  simp only [CollatzResearch.WordTrace]
  refine ⟨301540534021263328602698357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201027022680842219068465571 301540534021263328602698357)
  ·
    refine ⟨28269425064493437056502971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301540534021263328602698357 28269425064493437056502971)
    ·
      refine ⟨42404137596740155584754457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28269425064493437056502971 42404137596740155584754457)
      ·
        refine ⟨31803103197555116688565843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42404137596740155584754457 31803103197555116688565843)
        ·
          refine ⟨47704654796332675032848765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31803103197555116688565843 47704654796332675032848765)
          ·
            refine ⟨17889245548624753137318287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47704654796332675032848765 17889245548624753137318287)
            ·
              refine ⟨26833868322937129705977431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889245548624753137318287 26833868322937129705977431)
              ·
                refine ⟨40250802484405694558966147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26833868322937129705977431 40250802484405694558966147)
                ·
                  refine ⟨60376203726608541838449221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40250802484405694558966147 60376203726608541838449221)
                  ·
                    refine ⟨11320538198739101594709229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60376203726608541838449221 11320538198739101594709229)
                    ·
                      refine ⟨4245201824527163098015961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320538198739101594709229 4245201824527163098015961)
                      ·
                        rfl

theorem cell23_8267501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_8267501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267501 prefixEnd_8267501 := by exact prefixLift 8267501
  have htrace : WordTrace (prefixWord ++ tailWord_8267501) baseStart_8267501 baseEnd_8267501 := by
    simpa [prefixWord, tailWord_8267501, baseEnd_8267501] using wordTrace_append hprefix tailTrace_8267501
  have hstable : (prefixWord ++ tailWord_8267501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267501).length < 2 ^ (prefixWord ++ tailWord_8267501).sum := by decide
  have hdescent : baseEnd_8267501 < baseStart_8267501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267524 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_8267524 : Nat := 118140960795 + 8267524 * 2 ^ 59
def prefixEnd_8267524 : Nat := 4983230072969 + 3 ^ 40 * 8267524 * 2
def baseEnd_8267524 : Nat := 4245213634582216508028355

theorem tailTrace_8267524 : CollatzResearch.WordTrace tailWord_8267524 prefixEnd_8267524 4245213634582216508028355 := by
  unfold tailWord_8267524
  simp only [CollatzResearch.WordTrace]
  refine ⟨150770686450090001765392813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201027581933453335687190417 150770686450090001765392813)
  ·
    refine ⟨56539007418783750662022305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150770686450090001765392813 56539007418783750662022305)
    ·
      refine ⟨42404255564087812996516729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56539007418783750662022305 42404255564087812996516729)
      ·
        refine ⟨31803191673065859747387547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42404255564087812996516729 31803191673065859747387547)
        ·
          refine ⟨47704787509598789621081321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31803191673065859747387547 47704787509598789621081321)
          ·
            refine ⟨35778590632199092215810991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47704787509598789621081321 35778590632199092215810991)
            ·
              refine ⟨53667885948298638323716487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35778590632199092215810991 53667885948298638323716487)
              ·
                refine ⟨80501828922447957485574731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53667885948298638323716487 80501828922447957485574731)
                ·
                  refine ⟨120752743383671936228362097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80501828922447957485574731 120752743383671936228362097)
                  ·
                    refine ⟨90564557537753952171271573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120752743383671936228362097 90564557537753952171271573)
                    ·
                      refine ⟨4245213634582216508028355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90564557537753952171271573 4245213634582216508028355)
                      ·
                        rfl

theorem cell23_8267524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_8267524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267524 prefixEnd_8267524 := by exact prefixLift 8267524
  have htrace : WordTrace (prefixWord ++ tailWord_8267524) baseStart_8267524 baseEnd_8267524 := by
    simpa [prefixWord, tailWord_8267524, baseEnd_8267524] using wordTrace_append hprefix tailTrace_8267524
  have hstable : (prefixWord ++ tailWord_8267524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267524).length < 2 ^ (prefixWord ++ tailWord_8267524).sum := by decide
  have hdescent : baseEnd_8267524 < baseStart_8267524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267531 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 3]
def baseStart_8267531 : Nat := 118140960795 + 8267531 * 2 ^ 59
def prefixEnd_8267531 : Nat := 4983230072969 + 3 ^ 40 * 8267531 * 2
def baseEnd_8267531 : Nat := 4245217228946797980640823

theorem tailTrace_8267531 : CollatzResearch.WordTrace tailWord_8267531 prefixEnd_8267531 4245217228946797980640823 := by
  unfold tailWord_8267531
  simp only [CollatzResearch.WordTrace]
  refine ⟨301541628211154643726290447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201027752140769762484193631 301541628211154643726290447)
  ·
    refine ⟨452312442316731965589435671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301541628211154643726290447 452312442316731965589435671)
    ·
      refine ⟨678468663475097948384153507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452312442316731965589435671 678468663475097948384153507)
      ·
        refine ⟨1017702995212646922576230261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678468663475097948384153507 1017702995212646922576230261)
        ·
          refine ⟨95409655801185648991521587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1017702995212646922576230261 95409655801185648991521587)
          ·
            refine ⟨143114483701778473487282381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95409655801185648991521587 143114483701778473487282381)
            ·
              refine ⟨53667931388166927557730893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143114483701778473487282381 53667931388166927557730893)
              ·
                refine ⟨20125474270562597834149085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53667931388166927557730893 20125474270562597834149085)
                ·
                  refine ⟨7547052851460974187805907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20125474270562597834149085 7547052851460974187805907)
                  ·
                    refine ⟨11320579277191461281708861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547052851460974187805907 11320579277191461281708861)
                    ·
                      refine ⟨4245217228946797980640823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320579277191461281708861 4245217228946797980640823)
                      ·
                        rfl

theorem cell23_8267531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 1, 3].length) (baseStart_8267531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267531 prefixEnd_8267531 := by exact prefixLift 8267531
  have htrace : WordTrace (prefixWord ++ tailWord_8267531) baseStart_8267531 baseEnd_8267531 := by
    simpa [prefixWord, tailWord_8267531, baseEnd_8267531] using wordTrace_append hprefix tailTrace_8267531
  have hstable : (prefixWord ++ tailWord_8267531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267531).length < 2 ^ (prefixWord ++ tailWord_8267531).sum := by decide
  have hdescent : baseEnd_8267531 < baseStart_8267531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267534 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_8267534 : Nat := 118140960795 + 8267534 * 2 ^ 59
def prefixEnd_8267534 : Nat := 4983230072969 + 3 ^ 40 * 8267534 * 2
def baseEnd_8267534 : Nat := 1415072923129587156301103

theorem tailTrace_8267534 : CollatzResearch.WordTrace tailWord_8267534 prefixEnd_8267534 1415072923129587156301103 := by
  unfold tailWord_8267534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37692717203767971904831207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201027825086762516825766437 37692717203767971904831207)
  ·
    refine ⟨56539075805651957857246811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37692717203767971904831207 56539075805651957857246811)
    ·
      refine ⟨84808613708477936785870217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56539075805651957857246811 84808613708477936785870217)
      ·
        refine ⟨63606460281358452589402663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84808613708477936785870217 63606460281358452589402663)
        ·
          refine ⟨95409690422037678884103995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63606460281358452589402663 95409690422037678884103995)
          ·
            refine ⟨143114535633056518326155993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95409690422037678884103995 143114535633056518326155993)
            ·
              refine ⟨107335901724792388744616995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143114535633056518326155993 107335901724792388744616995)
              ·
                refine ⟨161003852587188583116925493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107335901724792388744616995 161003852587188583116925493)
                ·
                  refine ⟨15094111180048929667211765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161003852587188583116925493 15094111180048929667211765)
                  ·
                    refine ⟨1415072923129587156301103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15094111180048929667211765 1415072923129587156301103)
                    ·
                      rfl

theorem cell23_8267534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_8267534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267534 prefixEnd_8267534 := by exact prefixLift 8267534
  have htrace : WordTrace (prefixWord ++ tailWord_8267534) baseStart_8267534 baseEnd_8267534 := by
    simpa [prefixWord, tailWord_8267534, baseEnd_8267534] using wordTrace_append hprefix tailTrace_8267534
  have hstable : (prefixWord ++ tailWord_8267534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267534).length < 2 ^ (prefixWord ++ tailWord_8267534).sum := by decide
  have hdescent : baseEnd_8267534 < baseStart_8267534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267541 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_8267541 : Nat := 118140960795 + 8267541 * 2 ^ 59
def prefixEnd_8267541 : Nat := 4983230072969 + 3 ^ 40 * 8267541 * 2
def baseEnd_8267541 : Nat := 4245222363753342941515777

theorem tailTrace_8267541 : CollatzResearch.WordTrace tailWord_8267541 prefixEnd_8267541 4245222363753342941515777 := by
  unfold tailWord_8267541
  simp only [CollatzResearch.WordTrace]
  refine ⟨301541992941118415434154477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201027995294078943622769651 301541992941118415434154477)
  ·
    refine ⟨113078247352919405787807929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301541992941118415434154477 113078247352919405787807929)
    ·
      refine ⟨84808685514689554340855947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113078247352919405787807929 84808685514689554340855947)
      ·
        refine ⟨127213028272034331511283921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84808685514689554340855947 127213028272034331511283921)
        ·
          refine ⟨95409771204025748633462941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127213028272034331511283921 95409771204025748633462941)
          ·
            refine ⟨35778664201509655737548603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95409771204025748633462941 35778664201509655737548603)
            ·
              refine ⟨53667996302264483606322905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35778664201509655737548603 53667996302264483606322905)
              ·
                refine ⟨40250997226698362704742179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53667996302264483606322905 40250997226698362704742179)
                ·
                  refine ⟨60376495840047544057113269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40250997226698362704742179 60376495840047544057113269)
                  ·
                    refine ⟨5660296485004457255354369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60376495840047544057113269 5660296485004457255354369)
                    ·
                      refine ⟨4245222363753342941515777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660296485004457255354369 4245222363753342941515777)
                      ·
                        rfl

theorem cell23_8267541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_8267541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267541 prefixEnd_8267541 := by exact prefixLift 8267541
  have htrace : WordTrace (prefixWord ++ tailWord_8267541) baseStart_8267541 baseEnd_8267541 := by
    simpa [prefixWord, tailWord_8267541, baseEnd_8267541] using wordTrace_append hprefix tailTrace_8267541
  have hstable : (prefixWord ++ tailWord_8267541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267541).length < 2 ^ (prefixWord ++ tailWord_8267541).sum := by decide
  have hdescent : baseEnd_8267541 < baseStart_8267541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267551 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 1, 5]
def baseStart_8267551 : Nat := 118140960795 + 8267551 * 2 ^ 59
def prefixEnd_8267551 : Nat := 4983230072969 + 3 ^ 40 * 8267551 * 2
def baseEnd_8267551 : Nat := 1415075832853295967463577

theorem tailTrace_8267551 : CollatzResearch.WordTrace tailWord_8267551 prefixEnd_8267551 1415075832853295967463577 := by
  unfold tailWord_8267551
  simp only [CollatzResearch.WordTrace]
  refine ⟨301542357671082187142018507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201028238447388124761345671 301542357671082187142018507)
  ·
    refine ⟨452313536506623280713027761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301542357671082187142018507 452313536506623280713027761)
    ·
      refine ⟨339235152379967460534770821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452313536506623280713027761 339235152379967460534770821)
      ·
        refine ⟨63606591071243898850269529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339235152379967460534770821 63606591071243898850269529)
        ·
          refine ⟨47704943303432924137702147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63606591071243898850269529 47704943303432924137702147)
          ·
            refine ⟨71557414955149386206553221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47704943303432924137702147 71557414955149386206553221)
            ·
              refine ⟨13417015304090509913728729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71557414955149386206553221 13417015304090509913728729)
              ·
                refine ⟨10062761478067882435296547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13417015304090509913728729 10062761478067882435296547)
                ·
                  refine ⟨15094142217101823652944821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062761478067882435296547 15094142217101823652944821)
                  ·
                    refine ⟨1415075832853295967463577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15094142217101823652944821 1415075832853295967463577)
                    ·
                      rfl

theorem cell23_8267551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_8267551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267551 prefixEnd_8267551 := by exact prefixLift 8267551
  have htrace : WordTrace (prefixWord ++ tailWord_8267551) baseStart_8267551 baseEnd_8267551 := by
    simpa [prefixWord, tailWord_8267551, baseEnd_8267551] using wordTrace_append hprefix tailTrace_8267551
  have hstable : (prefixWord ++ tailWord_8267551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267551).length < 2 ^ (prefixWord ++ tailWord_8267551).sum := by decide
  have hdescent : baseEnd_8267551 < baseStart_8267551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267594 : List Nat := [3, 1, 2, 1, 1, 1, 6, 8]
def baseStart_8267594 : Nat := 118140960795 + 8267594 * 2 ^ 59
def prefixEnd_8267594 : Nat := 4983230072969 + 3 ^ 40 * 8267594 * 2
def baseEnd_8267594 : Nat := 157231465860297453116779

theorem tailTrace_8267594 : CollatzResearch.WordTrace tailWord_8267594 prefixEnd_8267594 157231465860297453116779 := by
  unfold tailWord_8267594
  simp only [CollatzResearch.WordTrace]
  refine ⟨75385981502481601371458459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201029284006617603657222557 75385981502481601371458459)
  ·
    refine ⟨113078972253722402057187689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75385981502481601371458459 113078972253722402057187689)
    ·
      refine ⟨84809229190291801542890767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113078972253722402057187689 84809229190291801542890767)
      ·
        refine ⟨127213843785437702314336151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84809229190291801542890767 127213843785437702314336151)
        ·
          refine ⟨190820765678156553471504227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127213843785437702314336151 190820765678156553471504227)
          ·
            refine ⟨286231148517234830207256341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190820765678156553471504227 286231148517234830207256341)
            ·
              refine ⟨13417085086745382665965141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286231148517234830207256341 13417085086745382665965141)
              ·
                refine ⟨157231465860297453116779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13417085086745382665965141 157231465860297453116779)
                ·
                  rfl

theorem cell23_8267594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_8267594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267594 prefixEnd_8267594 := by exact prefixLift 8267594
  have htrace : WordTrace (prefixWord ++ tailWord_8267594) baseStart_8267594 baseEnd_8267594 := by
    simpa [prefixWord, tailWord_8267594, baseEnd_8267594] using wordTrace_append hprefix tailTrace_8267594
  have hstable : (prefixWord ++ tailWord_8267594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267594).length < 2 ^ (prefixWord ++ tailWord_8267594).sum := by decide
  have hdescent : baseEnd_8267594 < baseStart_8267594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267618 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_8267618 : Nat := 118140960795 + 8267618 * 2 ^ 59
def prefixEnd_8267618 : Nat := 4983230072969 + 3 ^ 40 * 8267618 * 2
def baseEnd_8267618 : Nat := 4245261901763739140252923

theorem tailTrace_8267618 : CollatzResearch.WordTrace tailWord_8267618 prefixEnd_8267618 4245261901763739140252923 := by
  unfold tailWord_8267618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75386200340459864396176877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201029867574559638389805005 75386200340459864396176877)
  ·
    refine ⟨28269825127672449148566329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75386200340459864396176877 28269825127672449148566329)
    ·
      refine ⟨21202368845754336861424747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28269825127672449148566329 21202368845754336861424747)
      ·
        refine ⟨31803553268631505292137121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21202368845754336861424747 31803553268631505292137121)
        ·
          refine ⟨23852664951473628969102841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31803553268631505292137121 23852664951473628969102841)
          ·
            refine ⟨17889498713605221726827131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23852664951473628969102841 17889498713605221726827131)
            ·
              refine ⟨26834248070407832590240697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889498713605221726827131 26834248070407832590240697)
              ·
                refine ⟨20125686052805874442680523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26834248070407832590240697 20125686052805874442680523)
                ·
                  refine ⟨30188529079208811664020785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20125686052805874442680523 30188529079208811664020785)
                  ·
                    refine ⟨22641396809406608748015589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30188529079208811664020785 22641396809406608748015589)
                    ·
                      refine ⟨4245261901763739140252923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22641396809406608748015589 4245261901763739140252923)
                      ·
                        rfl

theorem cell23_8267618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_8267618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267618 prefixEnd_8267618 := by exact prefixLift 8267618
  have htrace : WordTrace (prefixWord ++ tailWord_8267618) baseStart_8267618 baseEnd_8267618 := by
    simpa [prefixWord, tailWord_8267618, baseEnd_8267618] using wordTrace_append hprefix tailTrace_8267618
  have hstable : (prefixWord ++ tailWord_8267618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267618).length < 2 ^ (prefixWord ++ tailWord_8267618).sum := by decide
  have hdescent : baseEnd_8267618 < baseStart_8267618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267682 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_8267682 : Nat := 118140960795 + 8267682 * 2 ^ 59
def prefixEnd_8267682 : Nat := 4983230072969 + 3 ^ 40 * 8267682 * 2
def baseEnd_8267682 : Nat := 4245294764525626889852629

theorem tailTrace_8267682 : CollatzResearch.WordTrace tailWord_8267682 prefixEnd_8267682 4245294764525626889852629 := by
  unfold tailWord_8267682
  simp only [CollatzResearch.WordTrace]
  refine ⟨75386783908401899128759325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201031423755738397676691533 75386783908401899128759325)
  ·
    refine ⟨28270043965650712173284747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75386783908401899128759325 28270043965650712173284747)
    ·
      refine ⟨42405065948476068259927121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28270043965650712173284747 42405065948476068259927121)
      ·
        refine ⟨31803799461357051194945341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42405065948476068259927121 31803799461357051194945341)
        ·
          refine ⟨11926424798008894198104503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31803799461357051194945341 11926424798008894198104503)
          ·
            refine ⟨17889637197013341297156755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11926424798008894198104503 17889637197013341297156755)
            ·
              refine ⟨26834455795520011945735133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889637197013341297156755 26834455795520011945735133)
              ·
                refine ⟨10062920923320004479650675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26834455795520011945735133 10062920923320004479650675)
                ·
                  refine ⟨15094381384980006719476013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062920923320004479650675 15094381384980006719476013)
                  ·
                    refine ⟨5660393019367502519803505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15094381384980006719476013 5660393019367502519803505)
                    ·
                      refine ⟨4245294764525626889852629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660393019367502519803505 4245294764525626889852629)
                      ·
                        rfl

theorem cell23_8267682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_8267682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267682 prefixEnd_8267682 := by exact prefixLift 8267682
  have htrace : WordTrace (prefixWord ++ tailWord_8267682) baseStart_8267682 baseEnd_8267682 := by
    simpa [prefixWord, tailWord_8267682, baseEnd_8267682] using wordTrace_append hprefix tailTrace_8267682
  have hstable : (prefixWord ++ tailWord_8267682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267682).length < 2 ^ (prefixWord ++ tailWord_8267682).sum := by decide
  have hdescent : baseEnd_8267682 < baseStart_8267682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267701 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 7]
def baseStart_8267701 : Nat := 118140960795 + 8267701 * 2 ^ 59
def prefixEnd_8267701 : Nat := 4983230072969 + 3 ^ 40 * 8267701 * 2
def baseEnd_8267701 : Nat := 471700502295340257279449

theorem tailTrace_8267701 : CollatzResearch.WordTrace tailWord_8267701 prefixEnd_8267701 471700502295340257279449 := by
  unfold tailWord_8267701
  simp only [CollatzResearch.WordTrace]
  refine ⟨301547828620538762759978957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201031885747025841839985971 301547828620538762759978957)
  ·
    refine ⟨113080435732702036034992109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301547828620538762759978957 113080435732702036034992109)
    ·
      refine ⟨42405163399763263513122041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113080435732702036034992109 42405163399763263513122041)
      ·
        refine ⟨31803872549822447634841531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42405163399763263513122041 31803872549822447634841531)
        ·
          refine ⟨47705808824733671452262297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31803872549822447634841531 47705808824733671452262297)
          ·
            refine ⟨35779356618550253589196723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47705808824733671452262297 35779356618550253589196723)
            ·
              refine ⟨53669034927825380383795085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35779356618550253589196723 53669034927825380383795085)
              ·
                refine ⟨20125888097934517643923157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53669034927825380383795085 20125888097934517643923157)
                ·
                  refine ⟨471700502295340257279449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20125888097934517643923157 471700502295340257279449)
                  ·
                    rfl

theorem cell23_8267701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_8267701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267701 prefixEnd_8267701 := by exact prefixLift 8267701
  have htrace : WordTrace (prefixWord ++ tailWord_8267701) baseStart_8267701 baseEnd_8267701 := by
    simpa [prefixWord, tailWord_8267701, baseEnd_8267701] using wordTrace_append hprefix tailTrace_8267701
  have hstable : (prefixWord ++ tailWord_8267701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267701).length < 2 ^ (prefixWord ++ tailWord_8267701).sum := by decide
  have hdescent : baseEnd_8267701 < baseStart_8267701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267711 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_8267711 : Nat := 118140960795 + 8267711 * 2 ^ 59
def prefixEnd_8267711 : Nat := 4983230072969 + 3 ^ 40 * 8267711 * 2
def baseEnd_8267711 : Nat := 4245309655464607276389995

theorem tailTrace_8267711 : CollatzResearch.WordTrace tailWord_8267711 prefixEnd_8267711 4245309655464607276389995 := by
  unfold tailWord_8267711
  simp only [CollatzResearch.WordTrace]
  refine ⟨301548193350502534467842987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201032128900335022978561991 301548193350502534467842987)
  ·
    refine ⟨452322290025753801701764481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301548193350502534467842987 452322290025753801701764481)
    ·
      refine ⟨339241717519315351276323361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452322290025753801701764481 339241717519315351276323361)
      ·
        refine ⟨254431288139486513457242521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339241717519315351276323361 254431288139486513457242521)
        ·
          refine ⟨190823466104614885092931891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254431288139486513457242521 190823466104614885092931891)
          ·
            refine ⟨286235199156922327639397837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190823466104614885092931891 286235199156922327639397837)
            ·
              refine ⟨107338199683845872864774189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286235199156922327639397837 107338199683845872864774189)
              ·
                refine ⟨40251824881442202324290321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107338199683845872864774189 40251824881442202324290321)
                ·
                  refine ⟨30188868661081651743217741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40251824881442202324290321 30188868661081651743217741)
                  ·
                    refine ⟨11320825747905619403706653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30188868661081651743217741 11320825747905619403706653)
                    ·
                      refine ⟨4245309655464607276389995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320825747905619403706653 4245309655464607276389995)
                      ·
                        rfl

theorem cell23_8267711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_8267711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267711 prefixEnd_8267711 := by exact prefixLift 8267711
  have htrace : WordTrace (prefixWord ++ tailWord_8267711) baseStart_8267711 baseEnd_8267711 := by
    simpa [prefixWord, tailWord_8267711, baseEnd_8267711] using wordTrace_append hprefix tailTrace_8267711
  have hstable : (prefixWord ++ tailWord_8267711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267711).length < 2 ^ (prefixWord ++ tailWord_8267711).sum := by decide
  have hdescent : baseEnd_8267711 < baseStart_8267711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267712 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 2, 2, 2]
def baseStart_8267712 : Nat := 118140960795 + 8267712 * 2 ^ 59
def prefixEnd_8267712 : Nat := 4983230072969 + 3 ^ 40 * 8267712 * 2
def baseEnd_8267712 : Nat := 4245310168945261772477491

theorem tailTrace_8267712 : CollatzResearch.WordTrace tailWord_8267712 prefixEnd_8267712 4245310168945261772477491 := by
  unfold tailWord_8267712
  simp only [CollatzResearch.WordTrace]
  refine ⟨150774114911749455819314695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201032153215665941092419593 150774114911749455819314695)
  ·
    refine ⟨226161172367624183728972043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150774114911749455819314695 226161172367624183728972043)
    ·
      refine ⟨339241758551436275593458065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226161172367624183728972043 339241758551436275593458065)
      ·
        refine ⟨254431318913577206695093549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339241758551436275593458065 254431318913577206695093549)
        ·
          refine ⟨95411744592591452510660081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254431318913577206695093549 95411744592591452510660081)
          ·
            refine ⟨71558808444443589382995061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95411744592591452510660081 71558808444443589382995061)
            ·
              refine ⟨6708638291666586504655787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71558808444443589382995061 6708638291666586504655787)
              ·
                refine ⟨10062957437499879756983681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708638291666586504655787 10062957437499879756983681)
                ·
                  refine ⟨7547218078124909817737761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062957437499879756983681 7547218078124909817737761)
                  ·
                    refine ⟨5660413558593682363303321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7547218078124909817737761 5660413558593682363303321)
                    ·
                      refine ⟨4245310168945261772477491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660413558593682363303321 4245310168945261772477491)
                      ·
                        rfl

theorem cell23_8267712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_8267712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267712 prefixEnd_8267712 := by exact prefixLift 8267712
  have htrace : WordTrace (prefixWord ++ tailWord_8267712) baseStart_8267712 baseEnd_8267712 := by
    simpa [prefixWord, tailWord_8267712, baseEnd_8267712] using wordTrace_append hprefix tailTrace_8267712
  have hstable : (prefixWord ++ tailWord_8267712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267712).length < 2 ^ (prefixWord ++ tailWord_8267712).sum := by decide
  have hdescent : baseEnd_8267712 < baseStart_8267712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267758 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_8267758 : Nat := 118140960795 + 8267758 * 2 ^ 59
def prefixEnd_8267758 : Nat := 4983230072969 + 3 ^ 40 * 8267758 * 2
def baseEnd_8267758 : Nat := 4245333789055368592502279

theorem tailTrace_8267758 : CollatzResearch.WordTrace tailWord_8267758 prefixEnd_8267758 4245333789055368592502279 := by
  unfold tailWord_8267758
  simp only [CollatzResearch.WordTrace]
  refine ⟨37693738447666532686850491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201033271720888174329869285 37693738447666532686850491)
  ·
    refine ⟨56540607671499799030275737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37693738447666532686850491 56540607671499799030275737)
    ·
      refine ⟨42405455753624849272706803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56540607671499799030275737 42405455753624849272706803)
      ·
        refine ⟨63608183630437273909060205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42405455753624849272706803 63608183630437273909060205)
        ·
          refine ⟨23853068861413977715897577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63608183630437273909060205 23853068861413977715897577)
          ·
            refine ⟨17889801646060483286923183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23853068861413977715897577 17889801646060483286923183)
            ·
              refine ⟨26834702469090724930384775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889801646060483286923183 26834702469090724930384775)
              ·
                refine ⟨40252053703636087395577163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26834702469090724930384775 40252053703636087395577163)
                ·
                  refine ⟨60378080555454131093365745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40252053703636087395577163 60378080555454131093365745)
                  ·
                    refine ⟨45283560416590598320024309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60378080555454131093365745 45283560416590598320024309)
                    ·
                      refine ⟨4245333789055368592502279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45283560416590598320024309 4245333789055368592502279)
                      ·
                        rfl

theorem cell23_8267758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_8267758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267758 prefixEnd_8267758 := by exact prefixLift 8267758
  have htrace : WordTrace (prefixWord ++ tailWord_8267758) baseStart_8267758 baseEnd_8267758 := by
    simpa [prefixWord, tailWord_8267758, baseEnd_8267758] using wordTrace_append hprefix tailTrace_8267758
  have hstable : (prefixWord ++ tailWord_8267758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267758).length < 2 ^ (prefixWord ++ tailWord_8267758).sum := by decide
  have hdescent : baseEnd_8267758 < baseStart_8267758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267768 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 2, 4, 2]
def baseStart_8267768 : Nat := 118140960795 + 8267768 * 2 ^ 59
def prefixEnd_8267768 : Nat := 4983230072969 + 3 ^ 40 * 8267768 * 2
def baseEnd_8267768 : Nat := 4245338923861913553377233

theorem tailTrace_8267768 : CollatzResearch.WordTrace tailWord_8267768 prefixEnd_8267768 4245338923861913553377233 := by
  unfold tailWord_8267768
  simp only [CollatzResearch.WordTrace]
  refine ⟨150775136155648016601333979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201033514874197355468445305 150775136155648016601333979)
  ·
    refine ⟨226162704233472024902000969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150775136155648016601333979 226162704233472024902000969)
    ·
      refine ⟨169622028175104018676500727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226162704233472024902000969 169622028175104018676500727)
      ·
        refine ⟨254433042262656028014751091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169622028175104018676500727 254433042262656028014751091)
        ·
          refine ⟨381649563393984042022126637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254433042262656028014751091 381649563393984042022126637)
          ·
            refine ⟨143118586272744015758297489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381649563393984042022126637 143118586272744015758297489)
            ·
              refine ⟨107338939704558011818723117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143118586272744015758297489 107338939704558011818723117)
              ·
                refine ⟨40252102389209254432021169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107338939704558011818723117 40252102389209254432021169)
                ·
                  refine ⟨30189076791906940824015877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40252102389209254432021169 30189076791906940824015877)
                  ·
                    refine ⟨5660451898482551404502977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30189076791906940824015877 5660451898482551404502977)
                    ·
                      refine ⟨4245338923861913553377233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660451898482551404502977 4245338923861913553377233)
                      ·
                        rfl

theorem cell23_8267768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_8267768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267768 prefixEnd_8267768 := by exact prefixLift 8267768
  have htrace : WordTrace (prefixWord ++ tailWord_8267768) baseStart_8267768 baseEnd_8267768 := by
    simpa [prefixWord, tailWord_8267768, baseEnd_8267768] using wordTrace_append hprefix tailTrace_8267768
  have hstable : (prefixWord ++ tailWord_8267768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267768).length < 2 ^ (prefixWord ++ tailWord_8267768).sum := by decide
  have hdescent : baseEnd_8267768 < baseStart_8267768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267771 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 3]
def baseStart_8267771 : Nat := 118140960795 + 8267771 * 2 ^ 59
def prefixEnd_8267771 : Nat := 4983230072969 + 3 ^ 40 * 8267771 * 2
def baseEnd_8267771 : Nat := 4245340464303877041639719

theorem tailTrace_8267771 : CollatzResearch.WordTrace tailWord_8267771 prefixEnd_8267771 4245340464303877041639719 := by
  unfold tailWord_8267771
  simp only [CollatzResearch.WordTrace]
  refine ⟨301550381730285164715027167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201033587820190109810018111 301550381730285164715027167)
  ·
    refine ⟨452325572595427747072540751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301550381730285164715027167 452325572595427747072540751)
    ·
      refine ⟨678488358893141620608811127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452325572595427747072540751 678488358893141620608811127)
      ·
        refine ⟨1017732538339712430913216691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678488358893141620608811127 1017732538339712430913216691)
        ·
          refine ⟨1526598807509568646369825037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017732538339712430913216691 1526598807509568646369825037)
          ·
            refine ⟨572474552816088242388684389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1526598807509568646369825037 572474552816088242388684389)
            ·
              refine ⟨107338978653016545447878323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 572474552816088242388684389 107338978653016545447878323)
              ·
                refine ⟨161008467979524818171817485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107338978653016545447878323 161008467979524818171817485)
                ·
                  refine ⟨60378175492321806814431557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161008467979524818171817485 60378175492321806814431557)
                  ·
                    refine ⟨11320907904810338777705917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60378175492321806814431557 11320907904810338777705917)
                    ·
                      refine ⟨4245340464303877041639719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320907904810338777705917 4245340464303877041639719)
                      ·
                        rfl

theorem cell23_8267771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 3].length) (baseStart_8267771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267771 prefixEnd_8267771 := by exact prefixLift 8267771
  have htrace : WordTrace (prefixWord ++ tailWord_8267771) baseStart_8267771 baseEnd_8267771 := by
    simpa [prefixWord, tailWord_8267771, baseEnd_8267771] using wordTrace_append hprefix tailTrace_8267771
  have hstable : (prefixWord ++ tailWord_8267771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267771).length < 2 ^ (prefixWord ++ tailWord_8267771).sum := by decide
  have hdescent : baseEnd_8267771 < baseStart_8267771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267805 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_8267805 : Nat := 118140960795 + 8267805 * 2 ^ 59
def prefixEnd_8267805 : Nat := 4983230072969 + 3 ^ 40 * 8267805 * 2
def baseEnd_8267805 : Nat := 4245357922646129908614563

theorem tailTrace_8267805 : CollatzResearch.WordTrace tailWord_8267805 prefixEnd_8267805 4245357922646129908614563 := by
  unfold tailWord_8267805
  simp only [CollatzResearch.WordTrace]
  refine ⟨301551621812161988521764869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201034414541441325681176579 301551621812161988521764869)
  ·
    refine ⟨56540929089780372847830913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301551621812161988521764869 56540929089780372847830913)
    ·
      refine ⟨42405696817335279635873185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56540929089780372847830913 42405696817335279635873185)
      ·
        refine ⟨31804272613001459726904889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42405696817335279635873185 31804272613001459726904889)
        ·
          refine ⟨23853204459751094795178667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31804272613001459726904889 23853204459751094795178667)
          ·
            refine ⟨35779806689626642192768001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23853204459751094795178667 35779806689626642192768001)
            ·
              refine ⟨26834855017219981644576001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35779806689626642192768001 26834855017219981644576001)
              ·
                refine ⟨20126141262914986233432001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26834855017219981644576001 20126141262914986233432001)
                ·
                  refine ⟨15094605947186239675074001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20126141262914986233432001 15094605947186239675074001)
                  ·
                    refine ⟨11320954460389679756305501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15094605947186239675074001 11320954460389679756305501)
                    ·
                      refine ⟨4245357922646129908614563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11320954460389679756305501 4245357922646129908614563)
                      ·
                        rfl

theorem cell23_8267805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_8267805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267805 prefixEnd_8267805 := by exact prefixLift 8267805
  have htrace : WordTrace (prefixWord ++ tailWord_8267805) baseStart_8267805 baseEnd_8267805 := by
    simpa [prefixWord, tailWord_8267805, baseEnd_8267805] using wordTrace_append hprefix tailTrace_8267805
  have hstable : (prefixWord ++ tailWord_8267805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267805).length < 2 ^ (prefixWord ++ tailWord_8267805).sum := by decide
  have hdescent : baseEnd_8267805 < baseStart_8267805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267811 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_8267811 : Nat := 118140960795 + 8267811 * 2 ^ 59
def prefixEnd_8267811 : Nat := 4983230072969 + 3 ^ 40 * 8267811 * 2
def baseEnd_8267811 : Nat := 4245361003530056885139535

theorem tailTrace_8267811 : CollatzResearch.WordTrace tailWord_8267811 prefixEnd_8267811 4245361003530056885139535 := by
  unfold tailWord_8267811
  simp only [CollatzResearch.WordTrace]
  refine ⟨301551840650140251546483287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201034560433426834364322191 301551840650140251546483287)
  ·
    refine ⟨452327760975210377319724931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301551840650140251546483287 452327760975210377319724931)
    ·
      refine ⟨678491641462815565979587397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452327760975210377319724931 678491641462815565979587397)
      ·
        refine ⟨127217182774277918621172637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678491641462815565979587397 127217182774277918621172637)
        ·
          refine ⟨47706443540354219482939739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127217182774277918621172637 47706443540354219482939739)
          ·
            refine ⟨71559665310531329224409609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47706443540354219482939739 71559665310531329224409609)
            ·
              refine ⟨53669748982898496918307207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71559665310531329224409609 53669748982898496918307207)
              ·
                refine ⟨80504623474347745377460811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53669748982898496918307207 80504623474347745377460811)
                ·
                  refine ⟨120756935211521618066191217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80504623474347745377460811 120756935211521618066191217)
                  ·
                    refine ⟨90567701408641213549643413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120756935211521618066191217 90567701408641213549643413)
                    ·
                      refine ⟨4245361003530056885139535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90567701408641213549643413 4245361003530056885139535)
                      ·
                        rfl

theorem cell23_8267811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_8267811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267811 prefixEnd_8267811 := by exact prefixLift 8267811
  have htrace : WordTrace (prefixWord ++ tailWord_8267811) baseStart_8267811 baseEnd_8267811 := by
    simpa [prefixWord, tailWord_8267811, baseEnd_8267811] using wordTrace_append hprefix tailTrace_8267811
  have hstable : (prefixWord ++ tailWord_8267811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267811).length < 2 ^ (prefixWord ++ tailWord_8267811).sum := by decide
  have hdescent : baseEnd_8267811 < baseStart_8267811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267852 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 1, 1, 3]
def baseStart_8267852 : Nat := 118140960795 + 8267852 * 2 ^ 59
def prefixEnd_8267852 : Nat := 4983230072969 + 3 ^ 40 * 8267852 * 2
def baseEnd_8267852 : Nat := 4245382056236891224726847

theorem tailTrace_8267852 : CollatzResearch.WordTrace tailWord_8267852 prefixEnd_8267852 4245382056236891224726847 := by
  unfold tailWord_8267852
  simp only [CollatzResearch.WordTrace]
  refine ⟨150776668021495857774362905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201035557361994477032483873 150776668021495857774362905)
  ·
    refine ⟨113082501016121893330772179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150776668021495857774362905 113082501016121893330772179)
    ·
      refine ⟨169623751524182839996158269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113082501016121893330772179 169623751524182839996158269)
      ·
        refine ⟨63608906821568564998559351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169623751524182839996158269 63608906821568564998559351)
        ·
          refine ⟨95413360232352847497839027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63608906821568564998559351 95413360232352847497839027)
          ·
            refine ⟨143120040348529271246758541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95413360232352847497839027 143120040348529271246758541)
            ·
              refine ⟨53670015130698476717534453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143120040348529271246758541 53670015130698476717534453)
              ·
                refine ⟨5031563918502982192268855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53670015130698476717534453 5031563918502982192268855)
                ·
                  refine ⟨7547345877754473288403283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031563918502982192268855 7547345877754473288403283)
                  ·
                    refine ⟨11321018816631709932604925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547345877754473288403283 11321018816631709932604925)
                    ·
                      refine ⟨4245382056236891224726847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321018816631709932604925 4245382056236891224726847)
                      ·
                        rfl

theorem cell23_8267852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_8267852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267852 prefixEnd_8267852 := by exact prefixLift 8267852
  have htrace : WordTrace (prefixWord ++ tailWord_8267852) baseStart_8267852 baseEnd_8267852 := by
    simpa [prefixWord, tailWord_8267852, baseEnd_8267852] using wordTrace_append hprefix tailTrace_8267852
  have hstable : (prefixWord ++ tailWord_8267852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267852).length < 2 ^ (prefixWord ++ tailWord_8267852).sum := by decide
  have hdescent : baseEnd_8267852 < baseStart_8267852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267869 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8267869 : Nat := 118140960795 + 8267869 * 2 ^ 59
def prefixEnd_8267869 : Nat := 4983230072969 + 3 ^ 40 * 8267869 * 2
def baseEnd_8267869 : Nat := 4245390785408017658214269

theorem tailTrace_8267869 : CollatzResearch.WordTrace tailWord_8267869 prefixEnd_8267869 4245390785408017658214269 := by
  unfold tailWord_8267869
  simp only [CollatzResearch.WordTrace]
  refine ⟨301553956083930127452094661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201035970722620084968063107 301553956083930127452094661)
  ·
    refine ⟨56541366765736898897267749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301553956083930127452094661 56541366765736898897267749)
    ·
      refine ⟨10601506268575668543237703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56541366765736898897267749 10601506268575668543237703)
      ·
        refine ⟨15902259402863502814856555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10601506268575668543237703 15902259402863502814856555)
        ·
          refine ⟨23853389104295254222284833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15902259402863502814856555 23853389104295254222284833)
          ·
            refine ⟨17890041828221440666713625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23853389104295254222284833 17890041828221440666713625)
            ·
              refine ⟨13417531371166080500035219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17890041828221440666713625 13417531371166080500035219)
              ·
                refine ⟨20126297056749120750052829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13417531371166080500035219 20126297056749120750052829)
                ·
                  refine ⟨7547361396280920281269811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20126297056749120750052829 7547361396280920281269811)
                  ·
                    refine ⟨11321042094421380421904717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547361396280920281269811 11321042094421380421904717)
                    ·
                      refine ⟨4245390785408017658214269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321042094421380421904717 4245390785408017658214269)
                      ·
                        rfl

theorem cell23_8267869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8267869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267869 prefixEnd_8267869 := by exact prefixLift 8267869
  have htrace : WordTrace (prefixWord ++ tailWord_8267869) baseStart_8267869 baseEnd_8267869 := by
    simpa [prefixWord, tailWord_8267869, baseEnd_8267869] using wordTrace_append hprefix tailTrace_8267869
  have hstable : (prefixWord ++ tailWord_8267869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267869).length < 2 ^ (prefixWord ++ tailWord_8267869).sum := by decide
  have hdescent : baseEnd_8267869 < baseStart_8267869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267881 : List Nat := [1, 2, 1, 1, 1, 5, 2, 10]
def baseStart_8267881 : Nat := 118140960795 + 8267881 * 2 ^ 59
def prefixEnd_8267881 : Nat := 4983230072969 + 3 ^ 40 * 8267881 * 2
def baseEnd_8267881 : Nat := 157236923969476726343119

theorem tailTrace_8267881 : CollatzResearch.WordTrace tailWord_8267881 prefixEnd_8267881 157236923969476726343119 := by
  unfold tailWord_8267881
  simp only [CollatzResearch.WordTrace]
  refine ⟨301554393759886653501531497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201036262506591102334354331 301554393759886653501531497)
  ·
    refine ⟨226165795319914990126148623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301554393759886653501531497 226165795319914990126148623)
    ·
      refine ⟨339248692979872485189222935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226165795319914990126148623 339248692979872485189222935)
      ·
        refine ⟨508873039469808727783834403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339248692979872485189222935 508873039469808727783834403)
        ·
          refine ⟨763309559204713091675751605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508873039469808727783834403 763309559204713091675751605)
          ·
            refine ⟨71560271175441852344601713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 763309559204713091675751605 71560271175441852344601713)
            ·
              refine ⟨53670203381581389258451285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71560271175441852344601713 53670203381581389258451285)
              ·
                refine ⟨157236923969476726343119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53670203381581389258451285 157236923969476726343119)
                ·
                  rfl

theorem cell23_8267881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 10].length) (baseStart_8267881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267881 prefixEnd_8267881 := by exact prefixLift 8267881
  have htrace : WordTrace (prefixWord ++ tailWord_8267881) baseStart_8267881 baseEnd_8267881 := by
    simpa [prefixWord, tailWord_8267881, baseEnd_8267881] using wordTrace_append hprefix tailTrace_8267881
  have hstable : (prefixWord ++ tailWord_8267881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267881).length < 2 ^ (prefixWord ++ tailWord_8267881).sum := by decide
  have hdescent : baseEnd_8267881 < baseStart_8267881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267888 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_8267888 : Nat := 118140960795 + 8267888 * 2 ^ 59
def prefixEnd_8267888 : Nat := 4983230072969 + 3 ^ 40 * 8267888 * 2
def baseEnd_8267888 : Nat := 4245400541540453083876681

theorem tailTrace_8267888 : CollatzResearch.WordTrace tailWord_8267888 prefixEnd_8267888 4245400541540453083876681 := by
  unfold tailWord_8267888
  simp only [CollatzResearch.WordTrace]
  refine ⟨150777324535430646848518159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201036432713907529131357545 150777324535430646848518159)
  ·
    refine ⟨226165986803145970272777239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150777324535430646848518159 226165986803145970272777239)
    ·
      refine ⟨339248980204718955409165859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226165986803145970272777239 339248980204718955409165859)
      ·
        refine ⟨508873470307078433113748789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339248980204718955409165859 508873470307078433113748789)
        ·
          refine ⟨47706887841288603104413949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 508873470307078433113748789 47706887841288603104413949)
          ·
            refine ⟨17890082940483226164155231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47706887841288603104413949 17890082940483226164155231)
            ·
              refine ⟨26835124410724839246232847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17890082940483226164155231 26835124410724839246232847)
              ·
                refine ⟨40252686616087258869349271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26835124410724839246232847 40252686616087258869349271)
                ·
                  refine ⟨60379029924130888304023907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40252686616087258869349271 60379029924130888304023907)
                  ·
                    refine ⟨90568544886196332456035861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60379029924130888304023907 90568544886196332456035861)
                    ·
                      refine ⟨4245400541540453083876681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90568544886196332456035861 4245400541540453083876681)
                      ·
                        rfl

theorem cell23_8267888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_8267888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267888 prefixEnd_8267888 := by exact prefixLift 8267888
  have htrace : WordTrace (prefixWord ++ tailWord_8267888) baseStart_8267888 baseEnd_8267888 := by
    simpa [prefixWord, tailWord_8267888, baseEnd_8267888] using wordTrace_append hprefix tailTrace_8267888
  have hstable : (prefixWord ++ tailWord_8267888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267888).length < 2 ^ (prefixWord ++ tailWord_8267888).sum := by decide
  have hdescent : baseEnd_8267888 < baseStart_8267888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267895 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_8267895 : Nat := 118140960795 + 8267895 * 2 ^ 59
def prefixEnd_8267895 : Nat := 4983230072969 + 3 ^ 40 * 8267895 * 2
def baseEnd_8267895 : Nat := 4245404135905034556489149

theorem tailTrace_8267895 : CollatzResearch.WordTrace tailWord_8267895 prefixEnd_8267895 4245404135905034556489149 := by
  unfold tailWord_8267895
  simp only [CollatzResearch.WordTrace]
  refine ⟨301554904381835933892541139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201036602921223955928360759 301554904381835933892541139)
  ·
    refine ⟨452332356572753900838811709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301554904381835933892541139 452332356572753900838811709)
    ·
      refine ⟨169624633714782712814554391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452332356572753900838811709 169624633714782712814554391)
      ·
        refine ⟨254436950572174069221831587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169624633714782712814554391 254436950572174069221831587)
        ·
          refine ⟨381655425858261103832747381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254436950572174069221831587 381655425858261103832747381)
          ·
            refine ⟨35780196174211978484320067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 381655425858261103832747381 35780196174211978484320067)
            ·
              refine ⟨53670294261317967726480101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35780196174211978484320067 53670294261317967726480101)
              ·
                refine ⟨10063180173997118948715019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53670294261317967726480101 10063180173997118948715019)
                ·
                  refine ⟨15094770260995678423072529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10063180173997118948715019 15094770260995678423072529)
                  ·
                    refine ⟨11321077695746758817304397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15094770260995678423072529 11321077695746758817304397)
                    ·
                      refine ⟨4245404135905034556489149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321077695746758817304397 4245404135905034556489149)
                      ·
                        rfl

theorem cell23_8267895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_8267895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267895 prefixEnd_8267895 := by exact prefixLift 8267895
  have htrace : WordTrace (prefixWord ++ tailWord_8267895) baseStart_8267895 baseEnd_8267895 := by
    simpa [prefixWord, tailWord_8267895, baseEnd_8267895] using wordTrace_append hprefix tailTrace_8267895
  have hstable : (prefixWord ++ tailWord_8267895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267895).length < 2 ^ (prefixWord ++ tailWord_8267895).sum := by decide
  have hdescent : baseEnd_8267895 < baseStart_8267895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267912 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_8267912 : Nat := 118140960795 + 8267912 * 2 ^ 59
def prefixEnd_8267912 : Nat := 4983230072969 + 3 ^ 40 * 8267912 * 2
def baseEnd_8267912 : Nat := 4245412865076160989976571

theorem tailTrace_8267912 : CollatzResearch.WordTrace tailWord_8267912 prefixEnd_8267912 4245412865076160989976571 := by
  unfold tailWord_8267912
  simp only [CollatzResearch.WordTrace]
  refine ⟨150777762211387172897954995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201037016281849563863939993 150777762211387172897954995)
  ·
    refine ⟨226166643317080759346932493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150777762211387172897954995 226166643317080759346932493)
    ·
      refine ⟨84812491243905284755099685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226166643317080759346932493 84812491243905284755099685)
      ·
        refine ⟨15902342108232240891581191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84812491243905284755099685 15902342108232240891581191)
        ·
          refine ⟨23853513162348361337371787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15902342108232240891581191 23853513162348361337371787)
          ·
            refine ⟨35780269743522542006057681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23853513162348361337371787 35780269743522542006057681)
            ·
              refine ⟨26835202307641906504543261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35780269743522542006057681 26835202307641906504543261)
              ·
                refine ⟨10063200865365714939203723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26835202307641906504543261 10063200865365714939203723)
                ·
                  refine ⟨15094801298048572408805585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10063200865365714939203723 15094801298048572408805585)
                  ·
                    refine ⟨11321100973536429306604189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15094801298048572408805585 11321100973536429306604189)
                    ·
                      refine ⟨4245412865076160989976571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321100973536429306604189 4245412865076160989976571)
                      ·
                        rfl

theorem cell23_8267912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_8267912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267912 prefixEnd_8267912 := by exact prefixLift 8267912
  have htrace : WordTrace (prefixWord ++ tailWord_8267912) baseStart_8267912 baseEnd_8267912 := by
    simpa [prefixWord, tailWord_8267912, baseEnd_8267912] using wordTrace_append hprefix tailTrace_8267912
  have hstable : (prefixWord ++ tailWord_8267912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267912).length < 2 ^ (prefixWord ++ tailWord_8267912).sum := by decide
  have hdescent : baseEnd_8267912 < baseStart_8267912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267925 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_8267925 : Nat := 118140960795 + 8267925 * 2 ^ 59
def prefixEnd_8267925 : Nat := 4983230072969 + 3 ^ 40 * 8267925 * 2
def baseEnd_8267925 : Nat := 4245419540324669439114011

theorem tailTrace_8267925 : CollatzResearch.WordTrace tailWord_8267925 prefixEnd_8267925 4245419540324669439114011 := by
  unfold tailWord_8267925
  simp only [CollatzResearch.WordTrace]
  refine ⟨301555998571727249016133229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201037332381151499344088819 301555998571727249016133229)
  ·
    refine ⟨113083499464397718381049961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301555998571727249016133229 113083499464397718381049961)
    ·
      refine ⟨84812624598298288785787471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113083499464397718381049961 84812624598298288785787471)
      ·
        refine ⟨127218936897447433178681207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84812624598298288785787471 127218936897447433178681207)
        ·
          refine ⟨190828405346171149768021811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127218936897447433178681207 190828405346171149768021811)
          ·
            refine ⟨286242608019256724652032717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190828405346171149768021811 286242608019256724652032717)
            ·
              refine ⟨107340978007221271744512269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286242608019256724652032717 107340978007221271744512269)
              ·
                refine ⟨40252866752707976904192101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107340978007221271744512269 40252866752707976904192101)
                ·
                  refine ⟨7547412516132745669536019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40252866752707976904192101 7547412516132745669536019)
                  ·
                    refine ⟨11321118774199118504304029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547412516132745669536019 11321118774199118504304029)
                    ·
                      refine ⟨4245419540324669439114011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321118774199118504304029 4245419540324669439114011)
                      ·
                        rfl

theorem cell23_8267925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_8267925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267925 prefixEnd_8267925 := by exact prefixLift 8267925
  have htrace : WordTrace (prefixWord ++ tailWord_8267925) baseStart_8267925 baseEnd_8267925 := by
    simpa [prefixWord, tailWord_8267925, baseEnd_8267925] using wordTrace_append hprefix tailTrace_8267925
  have hstable : (prefixWord ++ tailWord_8267925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267925).length < 2 ^ (prefixWord ++ tailWord_8267925).sum := by decide
  have hdescent : baseEnd_8267925 < baseStart_8267925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267946 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_8267946 : Nat := 118140960795 + 8267946 * 2 ^ 59
def prefixEnd_8267946 : Nat := 4983230072969 + 3 ^ 40 * 8267946 * 2
def baseEnd_8267946 : Nat := 4245430323418413856951415

theorem tailTrace_8267946 : CollatzResearch.WordTrace tailWord_8267946 prefixEnd_8267946 4245430323418413856951415 := by
  unfold tailWord_8267946
  simp only [CollatzResearch.WordTrace]
  refine ⟨75389191126162792400661923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201037843003100779735098461 75389191126162792400661923)
  ·
    refine ⟨113083786689244188600992885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75389191126162792400661923 113083786689244188600992885)
    ·
      refine ⟨10601605002116642681343083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113083786689244188600992885 10601605002116642681343083)
      ·
        refine ⟨15902407503174964022014625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10601605002116642681343083 15902407503174964022014625)
        ·
          refine ⟨11926805627381223016510969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15902407503174964022014625 11926805627381223016510969)
          ·
            refine ⟨8945104220535917262383227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11926805627381223016510969 8945104220535917262383227)
            ·
              refine ⟨13417656330803875893574841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945104220535917262383227 13417656330803875893574841)
              ·
                refine ⟨10063242248102906920181131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13417656330803875893574841 10063242248102906920181131)
                ·
                  refine ⟨15094863372154360380271697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10063242248102906920181131 15094863372154360380271697)
                  ·
                    refine ⟨11321147529115770285203773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15094863372154360380271697 11321147529115770285203773)
                    ·
                      refine ⟨4245430323418413856951415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321147529115770285203773 4245430323418413856951415)
                      ·
                        rfl

theorem cell23_8267946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_8267946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267946 prefixEnd_8267946 := by exact prefixLift 8267946
  have htrace : WordTrace (prefixWord ++ tailWord_8267946) baseStart_8267946 baseEnd_8267946 := by
    simpa [prefixWord, tailWord_8267946, baseEnd_8267946] using wordTrace_append hprefix tailTrace_8267946
  have hstable : (prefixWord ++ tailWord_8267946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267946).length < 2 ^ (prefixWord ++ tailWord_8267946).sum := by decide
  have hdescent : baseEnd_8267946 < baseStart_8267946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8267956 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_8267956 : Nat := 118140960795 + 8267956 * 2 ^ 59
def prefixEnd_8267956 : Nat := 4983230072969 + 3 ^ 40 * 8267956 * 2
def baseEnd_8267956 : Nat := 4245435458224958817826369

theorem tailTrace_8267956 : CollatzResearch.WordTrace tailWord_8267956 prefixEnd_8267956 4245435458224958817826369 := by
  unfold tailWord_8267956
  simp only [CollatzResearch.WordTrace]
  refine ⟨150778564617307470655255861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201038086156409960873674481 150778564617307470655255861)
  ·
    refine ⟨14135490432872575373930237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150778564617307470655255861 14135490432872575373930237)
    ·
      refine ⟨5300808912327215765223839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14135490432872575373930237 5300808912327215765223839)
      ·
        refine ⟨7951213368490823647835759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300808912327215765223839 7951213368490823647835759)
        ·
          refine ⟨11926820052736235471753639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951213368490823647835759 11926820052736235471753639)
          ·
            refine ⟨17890230079104353207630459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11926820052736235471753639 17890230079104353207630459)
            ·
              refine ⟨26835345118656529811445689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17890230079104353207630459 26835345118656529811445689)
              ·
                refine ⟨20126508838992397358584267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26835345118656529811445689 20126508838992397358584267)
                ·
                  refine ⟨30189763258488596037876401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20126508838992397358584267 30189763258488596037876401)
                  ·
                    refine ⟨22642322443866447028407301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30189763258488596037876401 22642322443866447028407301)
                    ·
                      refine ⟨4245435458224958817826369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22642322443866447028407301 4245435458224958817826369)
                      ·
                        rfl

theorem cell23_8267956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_8267956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8267956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8267956 prefixEnd_8267956 := by exact prefixLift 8267956
  have htrace : WordTrace (prefixWord ++ tailWord_8267956) baseStart_8267956 baseEnd_8267956 := by
    simpa [prefixWord, tailWord_8267956, baseEnd_8267956] using wordTrace_append hprefix tailTrace_8267956
  have hstable : (prefixWord ++ tailWord_8267956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8267956).length < 2 ^ (prefixWord ++ tailWord_8267956).sum := by decide
  have hdescent : baseEnd_8267956 < baseStart_8267956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8267956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268005 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 7]
def baseStart_8268005 : Nat := 118140960795 + 8268005 * 2 ^ 59
def prefixEnd_8268005 : Nat := 4983230072969 + 3 ^ 40 * 8268005 * 2
def baseEnd_8268005 : Nat := 471717846530781014012627

theorem tailTrace_8268005 : CollatzResearch.WordTrace tailWord_8268005 prefixEnd_8268005 471717846530781014012627 := by
  unfold tailWord_8268005
  simp only [CollatzResearch.WordTrace]
  refine ⟨301558916411437422679045469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201039277607624948452696979 301558916411437422679045469)
  ·
    refine ⟨113084593654289033504642051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301558916411437422679045469 113084593654289033504642051)
    ·
      refine ⟨169626890481433550256963077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113084593654289033504642051 169626890481433550256963077)
      ·
        refine ⟨31805041965268790673180577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169626890481433550256963077 31805041965268790673180577)
        ·
          refine ⟨23853781473951593004885433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31805041965268790673180577 23853781473951593004885433)
          ·
            refine ⟨17890336105463694753664075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23853781473951593004885433 17890336105463694753664075)
            ·
              refine ⟨26835504158195542130496113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17890336105463694753664075 26835504158195542130496113)
              ·
                refine ⟨20126628118646656597872085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26835504158195542130496113 20126628118646656597872085)
                ·
                  refine ⟨471717846530781014012627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20126628118646656597872085 471717846530781014012627)
                  ·
                    rfl

theorem cell23_8268005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_8268005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268005 prefixEnd_8268005 := by exact prefixLift 8268005
  have htrace : WordTrace (prefixWord ++ tailWord_8268005) baseStart_8268005 baseEnd_8268005 := by
    simpa [prefixWord, tailWord_8268005, baseEnd_8268005] using wordTrace_append hprefix tailTrace_8268005
  have hstable : (prefixWord ++ tailWord_8268005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268005).length < 2 ^ (prefixWord ++ tailWord_8268005).sum := by decide
  have hdescent : baseEnd_8268005 < baseStart_8268005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268022 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_8268022 : Nat := 118140960795 + 8268022 * 2 ^ 59
def prefixEnd_8268022 : Nat := 4983230072969 + 3 ^ 40 * 8268022 * 2
def baseEnd_8268022 : Nat := 471718816438683951066785

theorem tailTrace_8268022 : CollatzResearch.WordTrace tailWord_8268022 prefixEnd_8268022 471718816438683951066785 := by
  unfold tailWord_8268022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847471028273489661400895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201039690968250556388276213 18847471028273489661400895)
  ·
    refine ⟨28271206542410234492101343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18847471028273489661400895 28271206542410234492101343)
    ·
      refine ⟨42406809813615351738152015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28271206542410234492101343 42406809813615351738152015)
      ·
        refine ⟨63610214720423027607228023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42406809813615351738152015 63610214720423027607228023)
        ·
          refine ⟨95415322080634541410842035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63610214720423027607228023 95415322080634541410842035)
          ·
            refine ⟨143122983120951812116263053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95415322080634541410842035 143122983120951812116263053)
            ·
              refine ⟨53671118670356929543598645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143122983120951812116263053 53671118670356929543598645)
              ·
                refine ⟨5031667375345962144712373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53671118670356929543598645 5031667375345962144712373)
                ·
                  refine ⟨471718816438683951066785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5031667375345962144712373 471718816438683951066785)
                  ·
                    rfl

theorem cell23_8268022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_8268022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268022 prefixEnd_8268022 := by exact prefixLift 8268022
  have htrace : WordTrace (prefixWord ++ tailWord_8268022) baseStart_8268022 baseEnd_8268022 := by
    simpa [prefixWord, tailWord_8268022, baseEnd_8268022] using wordTrace_append hprefix tailTrace_8268022
  have hstable : (prefixWord ++ tailWord_8268022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268022).length < 2 ^ (prefixWord ++ tailWord_8268022).sum := by decide
  have hdescent : baseEnd_8268022 < baseStart_8268022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268025 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 7, 2]
def baseStart_8268025 : Nat := 118140960795 + 8268025 * 2 ^ 59
def prefixEnd_8268025 : Nat := 4983230072969 + 3 ^ 40 * 8268025 * 2
def baseEnd_8268025 : Nat := 4245470888390119047863551

theorem tailTrace_8268025 : CollatzResearch.WordTrace tailWord_8268025 prefixEnd_8268025 4245470888390119047863551 := by
  unfold tailWord_8268025
  simp only [CollatzResearch.WordTrace]
  refine ⟨301559645871364966094773529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201039763914243310729849019 301559645871364966094773529)
  ·
    refine ⟨226169734403523724571080147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301559645871364966094773529 226169734403523724571080147)
    ·
      refine ⟨339254601605285586856620221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226169734403523724571080147 339254601605285586856620221)
      ·
        refine ⟨127220475601982095071232583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339254601605285586856620221 127220475601982095071232583)
        ·
          refine ⟨190830713402973142606848875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127220475601982095071232583 190830713402973142606848875)
          ·
            refine ⟨286246070104459713910273313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190830713402973142606848875 286246070104459713910273313)
            ·
              refine ⟨214684552578344785432704985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286246070104459713910273313 214684552578344785432704985)
              ·
                refine ⟨161013414433758589074528739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214684552578344785432704985 161013414433758589074528739)
                ·
                  refine ⟨241520121650637883611793109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161013414433758589074528739 241520121650637883611793109)
                  ·
                    refine ⟨5660627851186825397151401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 241520121650637883611793109 5660627851186825397151401)
                    ·
                      refine ⟨4245470888390119047863551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660627851186825397151401 4245470888390119047863551)
                      ·
                        rfl

theorem cell23_8268025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_8268025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268025 prefixEnd_8268025 := by exact prefixLift 8268025
  have htrace : WordTrace (prefixWord ++ tailWord_8268025) baseStart_8268025 baseEnd_8268025 := by
    simpa [prefixWord, tailWord_8268025, baseEnd_8268025] using wordTrace_append hprefix tailTrace_8268025
  have hstable : (prefixWord ++ tailWord_8268025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268025).length < 2 ^ (prefixWord ++ tailWord_8268025).sum := by decide
  have hdescent : baseEnd_8268025 < baseStart_8268025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268055 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_8268055 : Nat := 118140960795 + 8268055 * 2 ^ 59
def prefixEnd_8268055 : Nat := 4983230072969 + 3 ^ 40 * 8268055 * 2
def baseEnd_8268055 : Nat := 4245486292809753930488413

theorem tailTrace_8268055 : CollatzResearch.WordTrace tailWord_8268055 prefixEnd_8268055 4245486292809753930488413 := by
  unfold tailWord_8268055
  simp only [CollatzResearch.WordTrace]
  refine ⟨301560740061256281218365619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201040493374170854145577079 301560740061256281218365619)
  ·
    refine ⟨452341110091884421827548429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301560740061256281218365619 452341110091884421827548429)
    ·
      refine ⟨169627916284456658185330661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452341110091884421827548429 169627916284456658185330661)
      ·
        refine ⟨31805234303335623409749499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169627916284456658185330661 31805234303335623409749499)
        ·
          refine ⟨47707851455003435114624249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31805234303335623409749499 47707851455003435114624249)
          ·
            refine ⟨35780888591252576335968187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47707851455003435114624249 35780888591252576335968187)
            ·
              refine ⟨53671332886878864503952281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35780888591252576335968187 53671332886878864503952281)
              ·
                refine ⟨40253499665159148377964211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53671332886878864503952281 40253499665159148377964211)
                ·
                  refine ⟨60380249497738722566946317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40253499665159148377964211 60380249497738722566946317)
                  ·
                    refine ⟨22642593561652020962604869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60380249497738722566946317 22642593561652020962604869)
                    ·
                      refine ⟨4245486292809753930488413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22642593561652020962604869 4245486292809753930488413)
                      ·
                        rfl

theorem cell23_8268055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_8268055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268055 prefixEnd_8268055 := by exact prefixLift 8268055
  have htrace : WordTrace (prefixWord ++ tailWord_8268055) baseStart_8268055 baseEnd_8268055 := by
    simpa [prefixWord, tailWord_8268055, baseEnd_8268055] using wordTrace_append hprefix tailTrace_8268055
  have hstable : (prefixWord ++ tailWord_8268055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268055).length < 2 ^ (prefixWord ++ tailWord_8268055).sum := by decide
  have hdescent : baseEnd_8268055 < baseStart_8268055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268092 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_8268092 : Nat := 118140960795 + 8268092 * 2 ^ 59
def prefixEnd_8268092 : Nat := 4983230072969 + 3 ^ 40 * 8268092 * 2
def baseEnd_8268092 : Nat := 4245505291593970285725743

theorem tailTrace_8268092 : CollatzResearch.WordTrace tailWord_8268092 prefixEnd_8268092 4245505291593970285725743 := by
  unfold tailWord_8268092
  simp only [CollatzResearch.WordTrace]
  refine ⟨150781044781061118268731265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201041393041414824358308353 150781044781061118268731265)
  ·
    refine ⟨113085783585795838701548449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150781044781061118268731265 113085783585795838701548449)
    ·
      refine ⟨84814337689346879026161337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113085783585795838701548449 84814337689346879026161337)
      ·
        refine ⟨63610753267010159269621003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84814337689346879026161337 63610753267010159269621003)
        ·
          refine ⟨95416129900515238904431505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63610753267010159269621003 95416129900515238904431505)
          ·
            refine ⟨71562097425386429178323629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95416129900515238904431505 71562097425386429178323629)
            ·
              refine ⟨26835786534519910941871361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71562097425386429178323629 26835786534519910941871361)
              ·
                refine ⟨20126839900889933206403521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26835786534519910941871361 20126839900889933206403521)
                ·
                  refine ⟨15095129925667449904802641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20126839900889933206403521 15095129925667449904802641)
                  ·
                    refine ⟨11321347444250587428601981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15095129925667449904802641 11321347444250587428601981)
                    ·
                      refine ⟨4245505291593970285725743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321347444250587428601981 4245505291593970285725743)
                      ·
                        rfl

theorem cell23_8268092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_8268092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268092 prefixEnd_8268092 := by exact prefixLift 8268092
  have htrace : WordTrace (prefixWord ++ tailWord_8268092) baseStart_8268092 baseEnd_8268092 := by
    simpa [prefixWord, tailWord_8268092, baseEnd_8268092] using wordTrace_append hprefix tailTrace_8268092
  have hstable : (prefixWord ++ tailWord_8268092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268092).length < 2 ^ (prefixWord ++ tailWord_8268092).sum := by decide
  have hdescent : baseEnd_8268092 < baseStart_8268092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268095 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 6]
def baseStart_8268095 : Nat := 118140960795 + 8268095 * 2 ^ 59
def prefixEnd_8268095 : Nat := 4983230072969 + 3 ^ 40 * 8268095 * 2
def baseEnd_8268095 : Nat := 471722981337325974887581

theorem tailTrace_8268095 : CollatzResearch.WordTrace tailWord_8268095 prefixEnd_8268095 471722981337325974887581 := by
  unfold tailWord_8268095
  simp only [CollatzResearch.WordTrace]
  refine ⟨301562198981111368049821739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201041465987407578699881159 301562198981111368049821739)
  ·
    refine ⟨452343298471667052074732609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301562198981111368049821739 452343298471667052074732609)
    ·
      refine ⟨339257473853750289056049457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452343298471667052074732609 339257473853750289056049457)
      ·
        refine ⟨254443105390312716792037093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339257473853750289056049457 254443105390312716792037093)
        ·
          refine ⟨47708082260683634398506955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254443105390312716792037093 47708082260683634398506955)
          ·
            refine ⟨71562123391025451597760433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47708082260683634398506955 71562123391025451597760433)
            ·
              refine ⟨53671592543269088698320325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71562123391025451597760433 53671592543269088698320325)
              ·
                refine ⟨10063423601862954130935061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53671592543269088698320325 10063423601862954130935061)
                ·
                  refine ⟨471722981337325974887581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10063423601862954130935061 471722981337325974887581)
                  ·
                    rfl

theorem cell23_8268095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 6].length) (baseStart_8268095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268095 prefixEnd_8268095 := by exact prefixLift 8268095
  have htrace : WordTrace (prefixWord ++ tailWord_8268095) baseStart_8268095 baseEnd_8268095 := by
    simpa [prefixWord, tailWord_8268095, baseEnd_8268095] using wordTrace_append hprefix tailTrace_8268095
  have hstable : (prefixWord ++ tailWord_8268095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268095).length < 2 ^ (prefixWord ++ tailWord_8268095).sum := by decide
  have hdescent : baseEnd_8268095 < baseStart_8268095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268112 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 6]
def baseStart_8268112 : Nat := 118140960795 + 8268112 * 2 ^ 59
def prefixEnd_8268112 : Nat := 4983230072969 + 3 ^ 40 * 8268112 * 2
def baseEnd_8268112 : Nat := 471723951245228911941739

theorem tailTrace_8268112 : CollatzResearch.WordTrace tailWord_8268112 prefixEnd_8268112 471723951245228911941739 := by
  unfold tailWord_8268112
  simp only [CollatzResearch.WordTrace]
  refine ⟨150781409511024889976595295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201041879348033186635460393 150781409511024889976595295)
  ·
    refine ⟨226172114266537334964892943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150781409511024889976595295 226172114266537334964892943)
    ·
      refine ⟨339258171399806002447339415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226172114266537334964892943 339258171399806002447339415)
      ·
        refine ⟨508887257099709003671009123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339258171399806002447339415 508887257099709003671009123)
        ·
          refine ⟨763330885649563505506513685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508887257099709003671009123 763330885649563505506513685)
          ·
            refine ⟨35781135264823289320617829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 763330885649563505506513685 35781135264823289320617829)
            ·
              refine ⟨6708962862154366747615843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35781135264823289320617829 6708962862154366747615843)
              ·
                refine ⟨10063444293231550121423765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708962862154366747615843 10063444293231550121423765)
                ·
                  refine ⟨471723951245228911941739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10063444293231550121423765 471723951245228911941739)
                  ·
                    rfl

theorem cell23_8268112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 6].length) (baseStart_8268112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268112 prefixEnd_8268112 := by exact prefixLift 8268112
  have htrace : WordTrace (prefixWord ++ tailWord_8268112) baseStart_8268112 baseEnd_8268112 := by
    simpa [prefixWord, tailWord_8268112, baseEnd_8268112] using wordTrace_append hprefix tailTrace_8268112
  have hstable : (prefixWord ++ tailWord_8268112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268112).length < 2 ^ (prefixWord ++ tailWord_8268112).sum := by decide
  have hdescent : baseEnd_8268112 < baseStart_8268112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268122 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_8268122 : Nat := 118140960795 + 8268122 * 2 ^ 59
def prefixEnd_8268122 : Nat := 4983230072969 + 3 ^ 40 * 8268122 * 2
def baseEnd_8268122 : Nat := 4245520696013605168350605

theorem tailTrace_8268122 : CollatzResearch.WordTrace tailWord_8268122 prefixEnd_8268122 4245520696013605168350605 := by
  unfold tailWord_8268122
  simp only [CollatzResearch.WordTrace]
  refine ⟨75390795938003387915263655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201042122501342367774036413 75390795938003387915263655)
  ·
    refine ⟨113086193907005081872895483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75390795938003387915263655 113086193907005081872895483)
    ·
      refine ⟨169629290860507622809343225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113086193907005081872895483 169629290860507622809343225)
      ·
        refine ⟨127221968145380717107007419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169629290860507622809343225 127221968145380717107007419)
        ·
          refine ⟨190832952218071075660511129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127221968145380717107007419 190832952218071075660511129)
          ·
            refine ⟨143124714163553306745383347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190832952218071075660511129 143124714163553306745383347)
            ·
              refine ⟨214687071245329960118075021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143124714163553306745383347 214687071245329960118075021)
              ·
                refine ⟨80507651716998735044278133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214687071245329960118075021 80507651716998735044278133)
                ·
                  refine ⟨7547592348468631410401075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80507651716998735044278133 7547592348468631410401075)
                  ·
                    refine ⟨11321388522702947115601613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547592348468631410401075 11321388522702947115601613)
                    ·
                      refine ⟨4245520696013605168350605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321388522702947115601613 4245520696013605168350605)
                      ·
                        rfl

theorem cell23_8268122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_8268122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268122 prefixEnd_8268122 := by exact prefixLift 8268122
  have htrace : WordTrace (prefixWord ++ tailWord_8268122) baseStart_8268122 baseEnd_8268122 := by
    simpa [prefixWord, tailWord_8268122, baseEnd_8268122] using wordTrace_append hprefix tailTrace_8268122
  have hstable : (prefixWord ++ tailWord_8268122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268122).length < 2 ^ (prefixWord ++ tailWord_8268122).sum := by decide
  have hdescent : baseEnd_8268122 < baseStart_8268122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268165 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_8268165 : Nat := 118140960795 + 8268165 * 2 ^ 59
def prefixEnd_8268165 : Nat := 4983230072969 + 3 ^ 40 * 8268165 * 2
def baseEnd_8268165 : Nat := 4245542775681748500112907

theorem tailTrace_8268165 : CollatzResearch.WordTrace tailWord_8268165 prefixEnd_8268165 4245542775681748500112907 := by
  unfold tailWord_8268165
  simp only [CollatzResearch.WordTrace]
  refine ⟨301564752090857770004869949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201043168060571846669913299 301564752090857770004869949)
  ·
    refine ⟨113086782034071663751826231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301564752090857770004869949 113086782034071663751826231)
    ·
      refine ⟨169630173051107495627739347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113086782034071663751826231 169630173051107495627739347)
      ·
        refine ⟨254445259576661243441609021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169630173051107495627739347 254445259576661243441609021)
        ·
          refine ⟨95416972341247966290603383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254445259576661243441609021 95416972341247966290603383)
          ·
            refine ⟨143125458511871949435905075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95416972341247966290603383 143125458511871949435905075)
            ·
              refine ⟨214688187767807924153857613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143125458511871949435905075 214688187767807924153857613)
              ·
                refine ⟨80508070412927971557696605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214688187767807924153857613 80508070412927971557696605)
                ·
                  refine ⟨30190526404847989334136227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80508070412927971557696605 30190526404847989334136227)
                  ·
                    refine ⟨45285789607271984001204341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30190526404847989334136227 45285789607271984001204341)
                    ·
                      refine ⟨4245542775681748500112907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45285789607271984001204341 4245542775681748500112907)
                      ·
                        rfl

theorem cell23_8268165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_8268165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268165 prefixEnd_8268165 := by exact prefixLift 8268165
  have htrace : WordTrace (prefixWord ++ tailWord_8268165) baseStart_8268165 baseEnd_8268165 := by
    simpa [prefixWord, tailWord_8268165, baseEnd_8268165] using wordTrace_append hprefix tailTrace_8268165
  have hstable : (prefixWord ++ tailWord_8268165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268165).length < 2 ^ (prefixWord ++ tailWord_8268165).sum := by decide
  have hdescent : baseEnd_8268165 < baseStart_8268165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268172 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_8268172 : Nat := 118140960795 + 8268172 * 2 ^ 59
def prefixEnd_8268172 : Nat := 4983230072969 + 3 ^ 40 * 8268172 * 2
def baseEnd_8268172 : Nat := 1415182123348776657575125

theorem tailTrace_8268172 : CollatzResearch.WordTrace tailWord_8268172 prefixEnd_8268172 1415182123348776657575125 := by
  unfold tailWord_8268172
  simp only [CollatzResearch.WordTrace]
  refine ⟨150782503700916205100187385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201043338267888273466916513 150782503700916205100187385)
  ·
    refine ⟨113086877775687153825140539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150782503700916205100187385 113086877775687153825140539)
    ·
      refine ⟨169630316663530730737710809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113086877775687153825140539 169630316663530730737710809)
      ·
        refine ⟨127222737497648048053283107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169630316663530730737710809 127222737497648048053283107)
        ·
          refine ⟨190834106246472072079924661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127222737497648048053283107 190834106246472072079924661)
          ·
            refine ⟨17890697460606756757492937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190834106246472072079924661 17890697460606756757492937)
            ·
              refine ⟨13418023095455067568119703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17890697460606756757492937 13418023095455067568119703)
              ·
                refine ⟨20127034643182601352179555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13418023095455067568119703 20127034643182601352179555)
                ·
                  refine ⟨30190551964773902028269333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20127034643182601352179555 30190551964773902028269333)
                  ·
                    refine ⟨1415182123348776657575125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30190551964773902028269333 1415182123348776657575125)
                    ·
                      rfl

theorem cell23_8268172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_8268172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268172 prefixEnd_8268172 := by exact prefixLift 8268172
  have htrace : WordTrace (prefixWord ++ tailWord_8268172) baseStart_8268172 baseEnd_8268172 := by
    simpa [prefixWord, tailWord_8268172, baseEnd_8268172] using wordTrace_append hprefix tailTrace_8268172
  have hstable : (prefixWord ++ tailWord_8268172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268172).length < 2 ^ (prefixWord ++ tailWord_8268172).sum := by decide
  have hdescent : baseEnd_8268172 < baseStart_8268172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268190 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_8268190 : Nat := 118140960795 + 8268190 * 2 ^ 59
def prefixEnd_8268190 : Nat := 4983230072969 + 3 ^ 40 * 8268190 * 2
def baseEnd_8268190 : Nat := 4245555612698110902300293

theorem tailTrace_8268190 : CollatzResearch.WordTrace tailWord_8268190 prefixEnd_8268190 4245555612698110902300293 := by
  unfold tailWord_8268190
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695707989470899909316253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201043775943844799516353349 37695707989470899909316253)
  ·
    refine ⟨14135890496051587465993595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37695707989470899909316253 14135890496051587465993595)
    ·
      refine ⟨21203835744077381198990393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14135890496051587465993595 21203835744077381198990393)
      ·
        refine ⟨15902876808058035899242795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21203835744077381198990393 15902876808058035899242795)
        ·
          refine ⟨23854315212087053848864193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15902876808058035899242795 23854315212087053848864193)
          ·
            refine ⟨17890736409065290386648145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23854315212087053848864193 17890736409065290386648145)
            ·
              refine ⟨13418052306798967789986109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17890736409065290386648145 13418052306798967789986109)
              ·
                refine ⟨5031769615049612921244791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13418052306798967789986109 5031769615049612921244791)
                ·
                  refine ⟨7547654422574419381867187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031769615049612921244791 7547654422574419381867187)
                  ·
                    refine ⟨11321481633861629072800781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547654422574419381867187 11321481633861629072800781)
                    ·
                      refine ⟨4245555612698110902300293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321481633861629072800781 4245555612698110902300293)
                      ·
                        rfl

theorem cell23_8268190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_8268190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268190 prefixEnd_8268190 := by exact prefixLift 8268190
  have htrace : WordTrace (prefixWord ++ tailWord_8268190) baseStart_8268190 baseEnd_8268190 := by
    simpa [prefixWord, tailWord_8268190, baseEnd_8268190] using wordTrace_append hprefix tailTrace_8268190
  have hstable : (prefixWord ++ tailWord_8268190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268190).length < 2 ^ (prefixWord ++ tailWord_8268190).sum := by decide
  have hdescent : baseEnd_8268190 < baseStart_8268190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268192 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_8268192 : Nat := 118140960795 + 8268192 * 2 ^ 59
def prefixEnd_8268192 : Nat := 4983230072969 + 3 ^ 40 * 8268192 * 2
def baseEnd_8268192 : Nat := 4245556639659419894475283

theorem tailTrace_8268192 : CollatzResearch.WordTrace tailWord_8268192 prefixEnd_8268192 4245556639659419894475283 := by
  unfold tailWord_8268192
  simp only [CollatzResearch.WordTrace]
  refine ⟨150782868430879976808051415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201043824574506635744068553 150782868430879976808051415)
  ·
    refine ⟨226174302646319965212077123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150782868430879976808051415 226174302646319965212077123)
    ·
      refine ⟨339261453969479947818115685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226174302646319965212077123 339261453969479947818115685)
      ·
        refine ⟨63611522619277490215896691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339261453969479947818115685 63611522619277490215896691)
        ·
          refine ⟨95417283928916235323845037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63611522619277490215896691 95417283928916235323845037)
          ·
            refine ⟨35781481473343588246441889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95417283928916235323845037 35781481473343588246441889)
            ·
              refine ⟨26836111105007691184831417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35781481473343588246441889 26836111105007691184831417)
              ·
                refine ⟨20127083328755768388623563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26836111105007691184831417 20127083328755768388623563)
                ·
                  refine ⟨30190624993133652582935345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20127083328755768388623563 30190624993133652582935345)
                  ·
                    refine ⟨22642968744850239437201509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30190624993133652582935345 22642968744850239437201509)
                    ·
                      refine ⟨4245556639659419894475283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22642968744850239437201509 4245556639659419894475283)
                      ·
                        rfl

theorem cell23_8268192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_8268192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268192 prefixEnd_8268192 := by exact prefixLift 8268192
  have htrace : WordTrace (prefixWord ++ tailWord_8268192) baseStart_8268192 baseEnd_8268192 := by
    simpa [prefixWord, tailWord_8268192, baseEnd_8268192] using wordTrace_append hprefix tailTrace_8268192
  have hstable : (prefixWord ++ tailWord_8268192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268192).length < 2 ^ (prefixWord ++ tailWord_8268192).sum := by decide
  have hdescent : baseEnd_8268192 < baseStart_8268192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268193 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 1, 5]
def baseStart_8268193 : Nat := 118140960795 + 8268193 * 2 ^ 59
def prefixEnd_8268193 : Nat := 4983230072969 + 3 ^ 40 * 8268193 * 2
def baseEnd_8268193 : Nat := 1415185717713358130187593

theorem tailTrace_8268193 : CollatzResearch.WordTrace tailWord_8268193 prefixEnd_8268193 1415185717713358130187593 := by
  unfold tailWord_8268193
  simp only [CollatzResearch.WordTrace]
  refine ⟨301565773334756330786889233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201043848889837553857926155 301565773334756330786889233)
  ·
    refine ⟨226174330001067248090166925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301565773334756330786889233 226174330001067248090166925)
    ·
      refine ⟨84815373750400218033812597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226174330001067248090166925 84815373750400218033812597)
      ·
        refine ⟨7951441289100020440669931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84815373750400218033812597 7951441289100020440669931)
        ·
          refine ⟨11927161933650030661004897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951441289100020440669931 11927161933650030661004897)
          ·
            refine ⟨8945371450237522995753673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11927161933650030661004897 8945371450237522995753673)
            ·
              refine ⟨6709028587678142246815255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8945371450237522995753673 6709028587678142246815255)
              ·
                refine ⟨10063542881517213370222883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709028587678142246815255 10063542881517213370222883)
                ·
                  refine ⟨15095314322275820055334325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10063542881517213370222883 15095314322275820055334325)
                  ·
                    refine ⟨1415185717713358130187593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15095314322275820055334325 1415185717713358130187593)
                    ·
                      rfl

theorem cell23_8268193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_8268193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268193 prefixEnd_8268193 := by exact prefixLift 8268193
  have htrace : WordTrace (prefixWord ++ tailWord_8268193) baseStart_8268193 baseEnd_8268193 := by
    simpa [prefixWord, tailWord_8268193, baseEnd_8268193] using wordTrace_append hprefix tailTrace_8268193
  have hstable : (prefixWord ++ tailWord_8268193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268193).length < 2 ^ (prefixWord ++ tailWord_8268193).sum := by decide
  have hdescent : baseEnd_8268193 < baseStart_8268193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268213 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_8268213 : Nat := 118140960795 + 8268213 * 2 ^ 59
def prefixEnd_8268213 : Nat := 4983230072969 + 3 ^ 40 * 8268213 * 2
def baseEnd_8268213 : Nat := 4245567422753164312312687

theorem tailTrace_8268213 : CollatzResearch.WordTrace tailWord_8268213 prefixEnd_8268213 4245567422753164312312687 := by
  unfold tailWord_8268213
  simp only [CollatzResearch.WordTrace]
  refine ⟨301566502794683874202617293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201044335196455916135078195 301566502794683874202617293)
  ·
    refine ⟨113087438548006452825981485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301566502794683874202617293 113087438548006452825981485)
    ·
      refine ⟨42407789455502419809743057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113087438548006452825981485 42407789455502419809743057)
      ·
        refine ⟨31805842091626814857307293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42407789455502419809743057 31805842091626814857307293)
        ·
          refine ⟨11927190784360055571490235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31805842091626814857307293 11927190784360055571490235)
          ·
            refine ⟨17890786176540083357235353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927190784360055571490235 17890786176540083357235353)
            ·
              refine ⟨13418089632405062517926515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17890786176540083357235353 13418089632405062517926515)
              ·
                refine ⟨20127134448607593776889773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13418089632405062517926515 20127134448607593776889773)
                ·
                  refine ⟨7547675418227847666333665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20127134448607593776889773 7547675418227847666333665)
                  ·
                    refine ⟨5660756563670885749750249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7547675418227847666333665 5660756563670885749750249)
                    ·
                      refine ⟨4245567422753164312312687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660756563670885749750249 4245567422753164312312687)
                      ·
                        rfl

theorem cell23_8268213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_8268213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268213 prefixEnd_8268213 := by exact prefixLift 8268213
  have htrace : WordTrace (prefixWord ++ tailWord_8268213) baseStart_8268213 baseEnd_8268213 := by
    simpa [prefixWord, tailWord_8268213, baseEnd_8268213] using wordTrace_append hprefix tailTrace_8268213
  have hstable : (prefixWord ++ tailWord_8268213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268213).length < 2 ^ (prefixWord ++ tailWord_8268213).sum := by decide
  have hdescent : baseEnd_8268213 < baseStart_8268213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268236 : List Nat := [2, 2, 1, 4, 4, 1, 2, 7]
def baseStart_8268236 : Nat := 118140960795 + 8268236 * 2 ^ 59
def prefixEnd_8268236 : Nat := 4983230072969 + 3 ^ 40 * 8268236 * 2
def baseEnd_8268236 : Nat := 157243675289193248975003

theorem tailTrace_8268236 : CollatzResearch.WordTrace tailWord_8268236 prefixEnd_8268236 157243675289193248975003 := by
  unfold tailWord_8268236
  simp only [CollatzResearch.WordTrace]
  refine ⟨150783670836800274565352281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201044894449067032753803041 150783670836800274565352281)
  ·
    refine ⟨113087753127600205924014211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150783670836800274565352281 113087753127600205924014211)
    ·
      refine ⟨169631629691400308886021317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113087753127600205924014211 169631629691400308886021317)
      ·
        refine ⟨31805930567137557916128997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169631629691400308886021317 31805930567137557916128997)
        ·
          refine ⟨5963611981338292109274187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31805930567137557916128997 5963611981338292109274187)
          ·
            refine ⟨8945417972007438163911281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963611981338292109274187 8945417972007438163911281)
            ·
              refine ⟨6709063479005578622933461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8945417972007438163911281 6709063479005578622933461)
              ·
                refine ⟨157243675289193248975003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6709063479005578622933461 157243675289193248975003)
                ·
                  rfl

theorem cell23_8268236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 7].length) (baseStart_8268236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268236 prefixEnd_8268236 := by exact prefixLift 8268236
  have htrace : WordTrace (prefixWord ++ tailWord_8268236) baseStart_8268236 baseEnd_8268236 := by
    simpa [prefixWord, tailWord_8268236, baseEnd_8268236] using wordTrace_append hprefix tailTrace_8268236
  have hstable : (prefixWord ++ tailWord_8268236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268236).length < 2 ^ (prefixWord ++ tailWord_8268236).sum := by decide
  have hdescent : baseEnd_8268236 < baseStart_8268236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268246 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_8268246 : Nat := 118140960795 + 8268246 * 2 ^ 59
def prefixEnd_8268246 : Nat := 4983230072969 + 3 ^ 40 * 8268246 * 2
def baseEnd_8268246 : Nat := 4245584367614762683200035

theorem tailTrace_8268246 : CollatzResearch.WordTrace tailWord_8268246 prefixEnd_8268246 4245584367614762683200035 := by
  unfold tailWord_8268246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847981650222770052410537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201045137602376213892379061 18847981650222770052410537)
  ·
    refine ⟨14135986237667077539307903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18847981650222770052410537 14135986237667077539307903)
    ·
      refine ⟨21203979356500616308961855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14135986237667077539307903 21203979356500616308961855)
      ·
        refine ⟨31805969034750924463442783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21203979356500616308961855 31805969034750924463442783)
        ·
          refine ⟨47708953552126386695164175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31805969034750924463442783 47708953552126386695164175)
          ·
            refine ⟨71563430328189580042746263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47708953552126386695164175 71563430328189580042746263)
            ·
              refine ⟨107345145492284370064119395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71563430328189580042746263 107345145492284370064119395)
              ·
                refine ⟨161017718238426555096179093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107345145492284370064119395 161017718238426555096179093)
                ·
                  refine ⟨7547705542426244770133395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161017718238426555096179093 7547705542426244770133395)
                  ·
                    refine ⟨11321558313639367155200093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547705542426244770133395 11321558313639367155200093)
                    ·
                      refine ⟨4245584367614762683200035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321558313639367155200093 4245584367614762683200035)
                      ·
                        rfl

theorem cell23_8268246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_8268246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268246 prefixEnd_8268246 := by exact prefixLift 8268246
  have htrace : WordTrace (prefixWord ++ tailWord_8268246) baseStart_8268246 baseEnd_8268246 := by
    simpa [prefixWord, tailWord_8268246, baseEnd_8268246] using wordTrace_append hprefix tailTrace_8268246
  have hstable : (prefixWord ++ tailWord_8268246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268246).length < 2 ^ (prefixWord ++ tailWord_8268246).sum := by decide
  have hdescent : baseEnd_8268246 < baseStart_8268246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268265 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_8268265 : Nat := 118140960795 + 8268265 * 2 ^ 59
def prefixEnd_8268265 : Nat := 4983230072969 + 3 ^ 40 * 8268265 * 2
def baseEnd_8268265 : Nat := 4245594123747198108862447

theorem tailTrace_8268265 : CollatzResearch.WordTrace tailWord_8268265 prefixEnd_8268265 4245594123747198108862447 := by
  unfold tailWord_8268265
  simp only [CollatzResearch.WordTrace]
  refine ⟨301568399390495487083510249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201045599593663658055673499 301568399390495487083510249)
  ·
    refine ⟨226176299542871615312632687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301568399390495487083510249 226176299542871615312632687)
    ·
      refine ⟨339264449314307422968949031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226176299542871615312632687 339264449314307422968949031)
      ·
        refine ⟨508896673971461134453423547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339264449314307422968949031 508896673971461134453423547)
        ·
          refine ⟨763345010957191701680135321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508896673971461134453423547 763345010957191701680135321)
          ·
            refine ⟨572508758217893776260101491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763345010957191701680135321 572508758217893776260101491)
            ·
              refine ⟨858763137326840664390152237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572508758217893776260101491 858763137326840664390152237)
              ·
                refine ⟨322036176497565249146307089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858763137326840664390152237 322036176497565249146307089)
                ·
                  refine ⟨241527132373173936859730317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322036176497565249146307089 241527132373173936859730317)
                  ·
                    refine ⟨90572674639940226322398869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241527132373173936859730317 90572674639940226322398869)
                    ·
                      refine ⟨4245594123747198108862447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90572674639940226322398869 4245594123747198108862447)
                      ·
                        rfl

theorem cell23_8268265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_8268265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268265 prefixEnd_8268265 := by exact prefixLift 8268265
  have htrace : WordTrace (prefixWord ++ tailWord_8268265) baseStart_8268265 baseEnd_8268265 := by
    simpa [prefixWord, tailWord_8268265, baseEnd_8268265] using wordTrace_append hprefix tailTrace_8268265
  have hstable : (prefixWord ++ tailWord_8268265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268265).length < 2 ^ (prefixWord ++ tailWord_8268265).sum := by decide
  have hdescent : baseEnd_8268265 < baseStart_8268265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268272 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_8268272 : Nat := 118140960795 + 8268272 * 2 ^ 59
def prefixEnd_8268272 : Nat := 4983230072969 + 3 ^ 40 * 8268272 * 2
def baseEnd_8268272 : Nat := 4245597718111779581474915

theorem tailTrace_8268272 : CollatzResearch.WordTrace tailWord_8268272 prefixEnd_8268272 4245597718111779581474915 := by
  unfold tailWord_8268272
  simp only [CollatzResearch.WordTrace]
  refine ⟨150784327350735063639507535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201045769800980084852676713 150784327350735063639507535)
  ·
    refine ⟨226176491026102595459261303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150784327350735063639507535 226176491026102595459261303)
    ·
      refine ⟨339264736539153893188891955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226176491026102595459261303 339264736539153893188891955)
      ·
        refine ⟨508897104808730839783337933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339264736539153893188891955 508897104808730839783337933)
        ·
          refine ⟨190836414303274064918751725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508897104808730839783337933 190836414303274064918751725)
          ·
            refine ⟨71563655363727774344531897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190836414303274064918751725 71563655363727774344531897)
            ·
              refine ⟨53672741522795830758398923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71563655363727774344531897 53672741522795830758398923)
              ·
                refine ⟨80509112284193746137598385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53672741522795830758398923 80509112284193746137598385)
                ·
                  refine ⟨60381834213145309603198789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80509112284193746137598385 60381834213145309603198789)
                  ·
                    refine ⟨11321593914964745550599773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60381834213145309603198789 11321593914964745550599773)
                    ·
                      refine ⟨4245597718111779581474915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321593914964745550599773 4245597718111779581474915)
                      ·
                        rfl

theorem cell23_8268272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_8268272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268272 prefixEnd_8268272 := by exact prefixLift 8268272
  have htrace : WordTrace (prefixWord ++ tailWord_8268272) baseStart_8268272 baseEnd_8268272 := by
    simpa [prefixWord, tailWord_8268272, baseEnd_8268272] using wordTrace_append hprefix tailTrace_8268272
  have hstable : (prefixWord ++ tailWord_8268272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268272).length < 2 ^ (prefixWord ++ tailWord_8268272).sum := by decide
  have hdescent : baseEnd_8268272 < baseStart_8268272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268309 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 5]
def baseStart_8268309 : Nat := 118140960795 + 8268309 * 2 ^ 59
def prefixEnd_8268309 : Nat := 4983230072969 + 3 ^ 40 * 8268309 * 2
def baseEnd_8268309 : Nat := 471735190766221770745805

theorem tailTrace_8268309 : CollatzResearch.WordTrace tailWord_8268309 prefixEnd_8268309 471735190766221770745805 := by
  unfold tailWord_8268309
  simp only [CollatzResearch.WordTrace]
  refine ⟨301570004202336082598111981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201046669468224055065407987 301570004202336082598111981)
  ·
    refine ⟨113088751575876030974291993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301570004202336082598111981 113088751575876030974291993)
    ·
      refine ⟨84816563681907023230718995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113088751575876030974291993 84816563681907023230718995)
      ·
        refine ⟨127224845522860534846078493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84816563681907023230718995 127224845522860534846078493)
        ·
          refine ⟨47709317071072700567279435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127224845522860534846078493 47709317071072700567279435)
          ·
            refine ⟨71563975606609050850919153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47709317071072700567279435 71563975606609050850919153)
            ·
              refine ⟨53672981704956788138189365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71563975606609050850919153 53672981704956788138189365)
              ·
                refine ⟨5031842034839698887955253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53672981704956788138189365 5031842034839698887955253)
                ·
                  refine ⟨471735190766221770745805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5031842034839698887955253 471735190766221770745805)
                  ·
                    rfl

theorem cell23_8268309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_8268309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268309 prefixEnd_8268309 := by exact prefixLift 8268309
  have htrace : WordTrace (prefixWord ++ tailWord_8268309) baseStart_8268309 baseEnd_8268309 := by
    simpa [prefixWord, tailWord_8268309, baseEnd_8268309] using wordTrace_append hprefix tailTrace_8268309
  have hstable : (prefixWord ++ tailWord_8268309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268309).length < 2 ^ (prefixWord ++ tailWord_8268309).sum := by decide
  have hdescent : baseEnd_8268309 < baseStart_8268309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268320 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8268320 : Nat := 118140960795 + 8268320 * 2 ^ 59
def prefixEnd_8268320 : Nat := 4983230072969 + 3 ^ 40 * 8268320 * 2
def baseEnd_8268320 : Nat := 4245622365183195393674695

theorem tailTrace_8268320 : CollatzResearch.WordTrace tailWord_8268320 prefixEnd_8268320 4245622365183195393674695 := by
  unfold tailWord_8268320
  simp only [CollatzResearch.WordTrace]
  refine ⟨150785202702648115738381207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201046936936864154317841609 150785202702648115738381207)
  ·
    refine ⟨226177804053972173607571811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150785202702648115738381207 226177804053972173607571811)
    ·
      refine ⟨339266706080958260411357717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226177804053972173607571811 339266706080958260411357717)
      ·
        refine ⟨15903126847544918456782393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 339266706080958260411357717 15903126847544918456782393)
        ·
          refine ⟨11927345135658688842586795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15903126847544918456782393 11927345135658688842586795)
          ·
            refine ⟨17891017703488033263880193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927345135658688842586795 17891017703488033263880193)
            ·
              refine ⟨13418263277616024947910145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17891017703488033263880193 13418263277616024947910145)
              ·
                refine ⟨10063697458212018710932609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13418263277616024947910145 10063697458212018710932609)
                ·
                  refine ⟨7547773093659014033199457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10063697458212018710932609 7547773093659014033199457)
                  ·
                    refine ⟨5660829820244260524899593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7547773093659014033199457 5660829820244260524899593)
                    ·
                      refine ⟨4245622365183195393674695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5660829820244260524899593 4245622365183195393674695)
                      ·
                        rfl

theorem cell23_8268320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8268320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268320 prefixEnd_8268320 := by exact prefixLift 8268320
  have htrace : WordTrace (prefixWord ++ tailWord_8268320) baseStart_8268320 baseEnd_8268320 := by
    simpa [prefixWord, tailWord_8268320, baseEnd_8268320] using wordTrace_append hprefix tailTrace_8268320
  have hstable : (prefixWord ++ tailWord_8268320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268320).length < 2 ^ (prefixWord ++ tailWord_8268320).sum := by decide
  have hdescent : baseEnd_8268320 < baseStart_8268320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268322 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_8268322 : Nat := 118140960795 + 8268322 * 2 ^ 59
def prefixEnd_8268322 : Nat := 4983230072969 + 3 ^ 40 * 8268322 * 2
def baseEnd_8268322 : Nat := 1415207797381501461949895

theorem tailTrace_8268322 : CollatzResearch.WordTrace tailWord_8268322 prefixEnd_8268322 1415207797381501461949895 := by
  unfold tailWord_8268322
  simp only [CollatzResearch.WordTrace]
  refine ⟨75392619587822246454583805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201046985567525990545556813 75392619587822246454583805)
  ·
    refine ⟨28272232345433342420468927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75392619587822246454583805 28272232345433342420468927)
    ·
      refine ⟨42408348518150013630703391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28272232345433342420468927 42408348518150013630703391)
      ·
        refine ⟨63612522777225020446055087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42408348518150013630703391 63612522777225020446055087)
        ·
          refine ⟨95418784165837530669082631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63612522777225020446055087 95418784165837530669082631)
          ·
            refine ⟨143128176248756296003623947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95418784165837530669082631 143128176248756296003623947)
            ·
              refine ⟨214692264373134444005435921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143128176248756296003623947 214692264373134444005435921)
              ·
                refine ⟨161019198279850833004076941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214692264373134444005435921 161019198279850833004076941)
                ·
                  refine ⟨60382199354944062376528853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161019198279850833004076941 60382199354944062376528853)
                  ·
                    refine ⟨1415207797381501461949895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60382199354944062376528853 1415207797381501461949895)
                    ·
                      rfl

theorem cell23_8268322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_8268322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268322 prefixEnd_8268322 := by exact prefixLift 8268322
  have htrace : WordTrace (prefixWord ++ tailWord_8268322) baseStart_8268322 baseEnd_8268322 := by
    simpa [prefixWord, tailWord_8268322, baseEnd_8268322] using wordTrace_append hprefix tailTrace_8268322
  have hstable : (prefixWord ++ tailWord_8268322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268322).length < 2 ^ (prefixWord ++ tailWord_8268322).sum := by decide
  have hdescent : baseEnd_8268322 < baseStart_8268322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268359 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_8268359 : Nat := 118140960795 + 8268359 * 2 ^ 59
def prefixEnd_8268359 : Nat := 4983230072969 + 3 ^ 40 * 8268359 * 2
def baseEnd_8268359 : Nat := 4245642390928720741087015

theorem tailTrace_8268359 : CollatzResearch.WordTrace tailWord_8268359 prefixEnd_8268359 4245642390928720741087015 := by
  unfold tailWord_8268359
  simp only [CollatzResearch.WordTrace]
  refine ⟨301571827852154941137432131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201047885234769960758288087 301571827852154941137432131)
  ·
    refine ⟨452357741778232411706148197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301571827852154941137432131 452357741778232411706148197)
    ·
      refine ⟨84817076583418577194902787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452357741778232411706148197 84817076583418577194902787)
      ·
        refine ⟨127225614875127865792354181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84817076583418577194902787 127225614875127865792354181)
        ·
          refine ⟨23854802789086474836066409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127225614875127865792354181 23854802789086474836066409)
          ·
            refine ⟨17891102091814856127049807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23854802789086474836066409 17891102091814856127049807)
            ·
              refine ⟨26836653137722284190574711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891102091814856127049807 26836653137722284190574711)
              ·
                refine ⟨40254979706583426285862067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26836653137722284190574711 40254979706583426285862067)
                ·
                  refine ⟨60382469559875139428793101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40254979706583426285862067 60382469559875139428793101)
                  ·
                    refine ⟨22643426084953177285797413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60382469559875139428793101 22643426084953177285797413)
                    ·
                      refine ⟨4245642390928720741087015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22643426084953177285797413 4245642390928720741087015)
                      ·
                        rfl

theorem cell23_8268359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_8268359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268359 prefixEnd_8268359 := by exact prefixLift 8268359
  have htrace : WordTrace (prefixWord ++ tailWord_8268359) baseStart_8268359 baseEnd_8268359 := by
    simpa [prefixWord, tailWord_8268359, baseEnd_8268359] using wordTrace_append hprefix tailTrace_8268359
  have hstable : (prefixWord ++ tailWord_8268359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268359).length < 2 ^ (prefixWord ++ tailWord_8268359).sum := by decide
  have hdescent : baseEnd_8268359 < baseStart_8268359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268420 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_8268420 : Nat := 118140960795 + 8268420 * 2 ^ 59
def prefixEnd_8268420 : Nat := 4983230072969 + 3 ^ 40 * 8268420 * 2
def baseEnd_8268420 : Nat := 1415224571082881667474745

theorem tailTrace_8268420 : CollatzResearch.WordTrace tailWord_8268420 prefixEnd_8268420 1415224571082881667474745 := by
  unfold tailWord_8268420
  simp only [CollatzResearch.WordTrace]
  refine ⟨150787026352466974277701357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201049368469955965703601809 150787026352466974277701357)
  ·
    refine ⟨56545134882175115354138009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150787026352466974277701357 56545134882175115354138009)
    ·
      refine ⟨42408851161631336515603507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56545134882175115354138009 42408851161631336515603507)
      ·
        refine ⟨63613276742447004773405261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42408851161631336515603507 63613276742447004773405261)
        ·
          refine ⟨23854978778417626790026973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63613276742447004773405261 23854978778417626790026973)
          ·
            refine ⟨8945617041906610046260115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23854978778417626790026973 8945617041906610046260115)
            ·
              refine ⟨13418425562859915069390173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945617041906610046260115 13418425562859915069390173)
              ·
                refine ⟨5031909586072468151021315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13418425562859915069390173 5031909586072468151021315)
                ·
                  refine ⟨7547864379108702226531973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031909586072468151021315 7547864379108702226531973)
                  ·
                    refine ⟨1415224571082881667474745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7547864379108702226531973 1415224571082881667474745)
                    ·
                      rfl

theorem cell23_8268420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_8268420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268420 prefixEnd_8268420 := by exact prefixLift 8268420
  have htrace : WordTrace (prefixWord ++ tailWord_8268420) baseStart_8268420 baseEnd_8268420 := by
    simpa [prefixWord, tailWord_8268420, baseEnd_8268420] using wordTrace_append hprefix tailTrace_8268420
  have hstable : (prefixWord ++ tailWord_8268420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268420).length < 2 ^ (prefixWord ++ tailWord_8268420).sum := by decide
  have hdescent : baseEnd_8268420 < baseStart_8268420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268446 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_8268446 : Nat := 118140960795 + 8268446 * 2 ^ 59
def prefixEnd_8268446 : Nat := 4983230072969 + 3 ^ 40 * 8268446 * 2
def baseEnd_8268446 : Nat := 1415229021248553966899705

theorem tailTrace_8268446 : CollatzResearch.WordTrace tailWord_8268446 prefixEnd_8268446 1415229021248553966899705 := by
  unfold tailWord_8268446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37696875125354969374481149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201050000668559836663899461 37696875125354969374481149)
  ·
    refine ⟨14136328172008113515430431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37696875125354969374481149 14136328172008113515430431)
    ·
      refine ⟨21204492258012170273145647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14136328172008113515430431 21204492258012170273145647)
      ·
        refine ⟨31806738387018255409718471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21204492258012170273145647 31806738387018255409718471)
        ·
          refine ⟨47710107580527383114577707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31806738387018255409718471 47710107580527383114577707)
          ·
            refine ⟨71565161370791074671866561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47710107580527383114577707 71565161370791074671866561)
            ·
              refine ⟨53673871028093306003899921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71565161370791074671866561 53673871028093306003899921)
              ·
                refine ⟨40255403271069979502924941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53673871028093306003899921 40255403271069979502924941)
                ·
                  refine ⟨15095776226651242313596853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40255403271069979502924941 15095776226651242313596853)
                  ·
                    refine ⟨1415229021248553966899705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15095776226651242313596853 1415229021248553966899705)
                    ·
                      rfl

theorem cell23_8268446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_8268446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268446 prefixEnd_8268446 := by exact prefixLift 8268446
  have htrace : WordTrace (prefixWord ++ tailWord_8268446) baseStart_8268446 baseEnd_8268446 := by
    simpa [prefixWord, tailWord_8268446, baseEnd_8268446] using wordTrace_append hprefix tailTrace_8268446
  have hstable : (prefixWord ++ tailWord_8268446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268446).length < 2 ^ (prefixWord ++ tailWord_8268446).sum := by decide
  have hdescent : baseEnd_8268446 < baseStart_8268446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268479 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_8268479 : Nat := 118140960795 + 8268479 * 2 ^ 59
def prefixEnd_8268479 : Nat := 4983230072969 + 3 ^ 40 * 8268479 * 2
def baseEnd_8268479 : Nat := 4245704008607260271586463

theorem tailTrace_8268479 : CollatzResearch.WordTrace tailWord_8268479 prefixEnd_8268479 4245704008607260271586463 := by
  unfold tailWord_8268479
  simp only [CollatzResearch.WordTrace]
  refine ⟨301576204611720201631800491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201050803074480134421200327 301576204611720201631800491)
  ·
    refine ⟨452364306917580302447700737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301576204611720201631800491 452364306917580302447700737)
    ·
      refine ⟨339273230188185226835775553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452364306917580302447700737 339273230188185226835775553)
      ·
        refine ⟨254454922641138920126831665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339273230188185226835775553 254454922641138920126831665)
        ·
          refine ⟨190841191980854190095123749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254454922641138920126831665 190841191980854190095123749)
          ·
            refine ⟨35782723496410160642835703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190841191980854190095123749 35782723496410160642835703)
            ·
              refine ⟨53674085244615240964253555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35782723496410160642835703 53674085244615240964253555)
              ·
                refine ⟨80511127866922861446380333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53674085244615240964253555 80511127866922861446380333)
                ·
                  refine ⟨30191672950096073042392625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80511127866922861446380333 30191672950096073042392625)
                  ·
                    refine ⟨22643754712572054781794469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30191672950096073042392625 22643754712572054781794469)
                    ·
                      refine ⟨4245704008607260271586463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22643754712572054781794469 4245704008607260271586463)
                      ·
                        rfl

theorem cell23_8268479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_8268479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268479 prefixEnd_8268479 := by exact prefixLift 8268479
  have htrace : WordTrace (prefixWord ++ tailWord_8268479) baseStart_8268479 baseEnd_8268479 := by
    simpa [prefixWord, tailWord_8268479, baseEnd_8268479] using wordTrace_append hprefix tailTrace_8268479
  have hstable : (prefixWord ++ tailWord_8268479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268479).length < 2 ^ (prefixWord ++ tailWord_8268479).sum := by decide
  have hdescent : baseEnd_8268479 < baseStart_8268479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268516 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_8268516 : Nat := 118140960795 + 8268516 * 2 ^ 59
def prefixEnd_8268516 : Nat := 4983230072969 + 3 ^ 40 * 8268516 * 2
def baseEnd_8268516 : Nat := 4245723007391476626823793

theorem tailTrace_8268516 : CollatzResearch.WordTrace tailWord_8268516 prefixEnd_8268516 4245723007391476626823793 := by
  unfold tailWord_8268516
  simp only [CollatzResearch.WordTrace]
  refine ⟨150788777056293078475448701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201051702741724104633931601 150788777056293078475448701)
  ·
    refine ⟨56545791396109904428293263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150788777056293078475448701 56545791396109904428293263)
    ·
      refine ⟨84818687094164856642439895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56545791396109904428293263 84818687094164856642439895)
      ·
        refine ⟨127228030641247284963659843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84818687094164856642439895 127228030641247284963659843)
        ·
          refine ⟨190842045961870927445489765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127228030641247284963659843 190842045961870927445489765)
          ·
            refine ⟨35782883617850798896029331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190842045961870927445489765 35782883617850798896029331)
            ·
              refine ⟨53674325426776198344043997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35782883617850798896029331 53674325426776198344043997)
              ·
                refine ⟨20127872035041074379016499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53674325426776198344043997 20127872035041074379016499)
                ·
                  refine ⟨30191808052561611568524749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20127872035041074379016499 30191808052561611568524749)
                  ·
                    refine ⟨11321928019710604338196781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30191808052561611568524749 11321928019710604338196781)
                    ·
                      refine ⟨4245723007391476626823793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321928019710604338196781 4245723007391476626823793)
                      ·
                        rfl

theorem cell23_8268516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_8268516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268516 prefixEnd_8268516 := by exact prefixLift 8268516
  have htrace : WordTrace (prefixWord ++ tailWord_8268516) baseStart_8268516 baseEnd_8268516 := by
    simpa [prefixWord, tailWord_8268516, baseEnd_8268516] using wordTrace_append hprefix tailTrace_8268516
  have hstable : (prefixWord ++ tailWord_8268516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268516).length < 2 ^ (prefixWord ++ tailWord_8268516).sum := by decide
  have hdescent : baseEnd_8268516 < baseStart_8268516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268529 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_8268529 : Nat := 118140960795 + 8268529 * 2 ^ 59
def prefixEnd_8268529 : Nat := 4983230072969 + 3 ^ 40 * 8268529 * 2
def baseEnd_8268529 : Nat := 4245729682639985075961233

theorem tailTrace_8268529 : CollatzResearch.WordTrace tailWord_8268529 prefixEnd_8268529 4245729682639985075961233 := by
  unfold tailWord_8268529
  simp only [CollatzResearch.WordTrace]
  refine ⟨301578028261539060171120641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201052018841026040114080427 301578028261539060171120641)
  ·
    refine ⟨226183521196154295128340481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301578028261539060171120641 226183521196154295128340481)
    ·
      refine ⟨169637640897115721346255361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226183521196154295128340481 169637640897115721346255361)
      ·
        refine ⟨127228230672836791009691521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169637640897115721346255361 127228230672836791009691521)
        ·
          refine ⟨95421173004627593257268641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127228230672836791009691521 95421173004627593257268641)
          ·
            refine ⟨71565879753470694942951481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95421173004627593257268641 71565879753470694942951481)
            ·
              refine ⟨53674409815103021207213611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71565879753470694942951481 53674409815103021207213611)
              ·
                refine ⟨80511614722654531810820417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53674409815103021207213611 80511614722654531810820417)
                ·
                  refine ⟨60383711041990898858115313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80511614722654531810820417 60383711041990898858115313)
                  ·
                    refine ⟨45287783281493174143586485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60383711041990898858115313 45287783281493174143586485)
                    ·
                      refine ⟨4245729682639985075961233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45287783281493174143586485 4245729682639985075961233)
                      ·
                        rfl

theorem cell23_8268529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_8268529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268529 prefixEnd_8268529 := by exact prefixLift 8268529
  have htrace : WordTrace (prefixWord ++ tailWord_8268529) baseStart_8268529 baseEnd_8268529 := by
    simpa [prefixWord, tailWord_8268529, baseEnd_8268529] using wordTrace_append hprefix tailTrace_8268529
  have hstable : (prefixWord ++ tailWord_8268529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268529).length < 2 ^ (prefixWord ++ tailWord_8268529).sum := by decide
  have hdescent : baseEnd_8268529 < baseStart_8268529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
