import V185TrunkScan23Chunk0969

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5742016 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_5742016 : Nat := 118140960795 + 5742016 * 2 ^ 59
def prefixEnd_5742016 : Nat := 4983230072969 + 3 ^ 40 * 5742016 * 2
def baseEnd_5742016 : Nat := 2948414133807111569692955

theorem tailTrace_5742016 : CollatzResearch.WordTrace tailWord_5742016 prefixEnd_5742016 2948414133807111569692955 := by
  unfold tailWord_5742016
  simp only [CollatzResearch.WordTrace]
  refine ⟨104714264382832082551858951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139619019177109443402478601 104714264382832082551858951)
  ·
    refine ⟨157071396574248123827788427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104714264382832082551858951 157071396574248123827788427)
    ·
      refine ⟨235607094861372185741682641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157071396574248123827788427 235607094861372185741682641)
      ·
        refine ⟨176705321146029139306261981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235607094861372185741682641 176705321146029139306261981)
        ·
          refine ⟨66264495429760927239848243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176705321146029139306261981 66264495429760927239848243)
          ·
            refine ⟨99396743144641390859772365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66264495429760927239848243 99396743144641390859772365)
            ·
              refine ⟨37273778679240521572414637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99396743144641390859772365 37273778679240521572414637)
              ·
                refine ⟨13977667004715195589655489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37273778679240521572414637 13977667004715195589655489)
                ·
                  refine ⟨10483250253536396692241617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13977667004715195589655489 10483250253536396692241617)
                  ·
                    refine ⟨7862437690152297519181213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10483250253536396692241617 7862437690152297519181213)
                    ·
                      refine ⟨2948414133807111569692955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862437690152297519181213 2948414133807111569692955)
                      ·
                        rfl

theorem cell23_5742016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_5742016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742016 prefixEnd_5742016 := by exact prefixLift 5742016
  have htrace : WordTrace (prefixWord ++ tailWord_5742016) baseStart_5742016 baseEnd_5742016 := by
    simpa [prefixWord, tailWord_5742016, baseEnd_5742016] using wordTrace_append hprefix tailTrace_5742016
  have hstable : (prefixWord ++ tailWord_5742016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742016).length < 2 ^ (prefixWord ++ tailWord_5742016).sum := by decide
  have hdescent : baseEnd_5742016 < baseStart_5742016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742023 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 1, 4]
def baseStart_5742023 : Nat := 118140960795 + 5742023 * 2 ^ 59
def prefixEnd_5742023 : Nat := 4983230072969 + 3 ^ 40 * 5742023 * 2
def baseEnd_5742023 : Nat := 982805909390564347435141

theorem tailTrace_5742023 : CollatzResearch.WordTrace tailWord_5742023 prefixEnd_5742023 982805909390564347435141 := by
  unfold tailWord_5742023
  simp only [CollatzResearch.WordTrace]
  refine ⟨209428784076638805299222723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139619189384425870199481815 209428784076638805299222723)
  ·
    refine ⟨314143176114958207948834085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209428784076638805299222723 314143176114958207948834085)
    ·
      refine ⟨58901845521554663990406391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314143176114958207948834085 58901845521554663990406391)
      ·
        refine ⟨88352768282331995985609587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58901845521554663990406391 88352768282331995985609587)
        ·
          refine ⟨132529152423497993978414381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88352768282331995985609587 132529152423497993978414381)
          ·
            refine ⟨49698432158811747741905393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132529152423497993978414381 49698432158811747741905393)
            ·
              refine ⟨37273824119108810806429045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49698432158811747741905393 37273824119108810806429045)
              ·
                refine ⟨3494421011166451013102723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37273824119108810806429045 3494421011166451013102723)
                ·
                  refine ⟨5241631516749676519654085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494421011166451013102723 5241631516749676519654085)
                  ·
                    refine ⟨982805909390564347435141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241631516749676519654085 982805909390564347435141)
                    ·
                      rfl

theorem cell23_5742023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_5742023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742023 prefixEnd_5742023 := by exact prefixLift 5742023
  have htrace : WordTrace (prefixWord ++ tailWord_5742023) baseStart_5742023 baseEnd_5742023 := by
    simpa [prefixWord, tailWord_5742023, baseEnd_5742023] using wordTrace_append hprefix tailTrace_5742023
  have hstable : (prefixWord ++ tailWord_5742023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742023).length < 2 ^ (prefixWord ++ tailWord_5742023).sum := by decide
  have hdescent : baseEnd_5742023 < baseStart_5742023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742040 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 1, 4]
def baseStart_5742040 : Nat := 118140960795 + 5742040 * 2 ^ 59
def prefixEnd_5742040 : Nat := 4983230072969 + 3 ^ 40 * 5742040 * 2
def baseEnd_5742040 : Nat := 982808819114273158597615

theorem tailTrace_5742040 : CollatzResearch.WordTrace tailWord_5742040 prefixEnd_5742040 982808819114273158597615 := by
  unfold tailWord_5742040
  simp only [CollatzResearch.WordTrace]
  refine ⟨104714702058788608601295787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139619602745051478135061049 104714702058788608601295787)
  ·
    refine ⟨157072053088182912901943681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104714702058788608601295787 157072053088182912901943681)
    ·
      refine ⟨117804039816137184676457761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157072053088182912901943681 117804039816137184676457761)
      ·
        refine ⟨88353029862102888507343321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117804039816137184676457761 88353029862102888507343321)
        ·
          refine ⟨66264772396577166380507491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88353029862102888507343321 66264772396577166380507491)
          ·
            refine ⟨99397158594865749570761237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66264772396577166380507491 99397158594865749570761237)
            ·
              refine ⟨4659241809134332011129433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99397158594865749570761237 4659241809134332011129433)
              ·
                refine ⟨3494431356850749008347075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4659241809134332011129433 3494431356850749008347075)
                ·
                  refine ⟨5241647035276123512520613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494431356850749008347075 5241647035276123512520613)
                  ·
                    refine ⟨982808819114273158597615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241647035276123512520613 982808819114273158597615)
                    ·
                      rfl

theorem cell23_5742040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_5742040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742040 prefixEnd_5742040 := by exact prefixLift 5742040
  have htrace : WordTrace (prefixWord ++ tailWord_5742040) baseStart_5742040 baseEnd_5742040 := by
    simpa [prefixWord, tailWord_5742040, baseEnd_5742040] using wordTrace_append hprefix tailTrace_5742040
  have hstable : (prefixWord ++ tailWord_5742040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742040).length < 2 ^ (prefixWord ++ tailWord_5742040).sum := by decide
  have hdescent : baseEnd_5742040 < baseStart_5742040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742079 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 3, 6]
def baseStart_5742079 : Nat := 118140960795 + 5742079 * 2 ^ 59
def prefixEnd_5742079 : Nat := 4983230072969 + 3 ^ 40 * 5742079 * 2
def baseEnd_5742079 : Nat := 982815494362781607735055

theorem tailTrace_5742079 : CollatzResearch.WordTrace tailWord_5742079 prefixEnd_5742079 982815494362781607735055 := by
  unfold tailWord_5742079
  simp only [CollatzResearch.WordTrace]
  refine ⟨209430826564435926863261291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139620551042957284575507527 209430826564435926863261291)
  ·
    refine ⟨314146239846653890294891937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209430826564435926863261291 314146239846653890294891937)
    ·
      refine ⟨235609679884990417721168953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314146239846653890294891937 235609679884990417721168953)
      ·
        refine ⟨176707259913742813290876715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235609679884990417721168953 176707259913742813290876715)
        ·
          refine ⟨265060889870614219936315073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176707259913742813290876715 265060889870614219936315073)
          ·
            refine ⟨198795667402960664952236305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265060889870614219936315073 198795667402960664952236305)
            ·
              refine ⟨149096750552220498714177229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198795667402960664952236305 149096750552220498714177229)
              ·
                refine ⟨55911281457082687017816461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149096750552220498714177229 55911281457082687017816461)
                ·
                  refine ⟨20966730546406007631681173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55911281457082687017816461 20966730546406007631681173)
                  ·
                    refine ⟨982815494362781607735055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20966730546406007631681173 982815494362781607735055)
                    ·
                      rfl

theorem cell23_5742079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_5742079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742079 prefixEnd_5742079 := by exact prefixLift 5742079
  have htrace : WordTrace (prefixWord ++ tailWord_5742079) baseStart_5742079 baseEnd_5742079 := by
    simpa [prefixWord, tailWord_5742079, baseEnd_5742079] using wordTrace_append hprefix tailTrace_5742079
  have hstable : (prefixWord ++ tailWord_5742079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742079).length < 2 ^ (prefixWord ++ tailWord_5742079).sum := by decide
  have hdescent : baseEnd_5742079 < baseStart_5742079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742113 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 1, 6]
def baseStart_5742113 : Nat := 118140960795 + 5742113 * 2 ^ 59
def prefixEnd_5742113 : Nat := 4983230072969 + 3 ^ 40 * 5742113 * 2
def baseEnd_5742113 : Nat := 982821313810199230060003

theorem tailTrace_5742113 : CollatzResearch.WordTrace tailWord_5742113 prefixEnd_5742113 982821313810199230060003 := by
  unfold tailWord_5742113
  simp only [CollatzResearch.WordTrace]
  refine ⟨209432066646312750669998993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139621377764208500446665995 209432066646312750669998993)
  ·
    refine ⟨157074049984734563002499245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209432066646312750669998993 157074049984734563002499245)
    ·
      refine ⟨58902768744275461125937217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157074049984734563002499245 58902768744275461125937217)
      ·
        refine ⟨44177076558206595844452913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58902768744275461125937217 44177076558206595844452913)
        ·
          refine ⟨33132807418654946883339685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44177076558206595844452913 33132807418654946883339685)
          ·
            refine ⟨6212401390997802540626191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33132807418654946883339685 6212401390997802540626191)
            ·
              refine ⟨9318602086496703810939287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212401390997802540626191 9318602086496703810939287)
              ·
                refine ⟨13977903129745055716408931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9318602086496703810939287 13977903129745055716408931)
                ·
                  refine ⟨20966854694617583574613397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13977903129745055716408931 20966854694617583574613397)
                  ·
                    refine ⟨982821313810199230060003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20966854694617583574613397 982821313810199230060003)
                    ·
                      rfl

theorem cell23_5742113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_5742113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742113 prefixEnd_5742113 := by exact prefixLift 5742113
  have htrace : WordTrace (prefixWord ++ tailWord_5742113) baseStart_5742113 baseEnd_5742113 := by
    simpa [prefixWord, tailWord_5742113, baseEnd_5742113] using wordTrace_append hprefix tailTrace_5742113
  have hstable : (prefixWord ++ tailWord_5742113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742113).length < 2 ^ (prefixWord ++ tailWord_5742113).sum := by decide
  have hdescent : baseEnd_5742113 < baseStart_5742113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742154 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_5742154 : Nat := 118140960795 + 5742154 * 2 ^ 59
def prefixEnd_5742154 : Nat := 4983230072969 + 3 ^ 40 * 5742154 * 2
def baseEnd_5742154 : Nat := 2948484994137432029767321

theorem tailTrace_5742154 : CollatzResearch.WordTrace tailWord_5742154 prefixEnd_5742154 2948484994137432029767321 := by
  unfold tailWord_5742154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52358390509791053668060379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139622374692776143114827677 52358390509791053668060379)
  ·
    refine ⟨78537585764686580502090569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52358390509791053668060379 78537585764686580502090569)
    ·
      refine ⟨58903189323514935376567927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78537585764686580502090569 58903189323514935376567927)
      ·
        refine ⟨88354783985272403064851891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58903189323514935376567927 88354783985272403064851891)
        ·
          refine ⟨132532175977908604597277837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88354783985272403064851891 132532175977908604597277837)
          ·
            refine ⟨49699565991715726723979189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132532175977908604597277837 49699565991715726723979189)
            ·
              refine ⟨4659334311723349380373049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49699565991715726723979189 4659334311723349380373049)
              ·
                refine ⟨3494500733792512035279787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4659334311723349380373049 3494500733792512035279787)
                ·
                  refine ⟨5241751100688768052919681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494500733792512035279787 5241751100688768052919681)
                  ·
                    refine ⟨3931313325516576039689761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5241751100688768052919681 3931313325516576039689761)
                    ·
                      refine ⟨2948484994137432029767321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931313325516576039689761 2948484994137432029767321)
                      ·
                        rfl

theorem cell23_5742154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_5742154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742154 prefixEnd_5742154 := by exact prefixLift 5742154
  have htrace : WordTrace (prefixWord ++ tailWord_5742154) baseStart_5742154 baseEnd_5742154 := by
    simpa [prefixWord, tailWord_5742154, baseEnd_5742154] using wordTrace_append hprefix tailTrace_5742154
  have hstable : (prefixWord ++ tailWord_5742154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742154).length < 2 ^ (prefixWord ++ tailWord_5742154).sum := by decide
  have hdescent : baseEnd_5742154 < baseStart_5742154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742180 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_5742180 : Nat := 118140960795 + 5742180 * 2 ^ 59
def prefixEnd_5742180 : Nat := 4983230072969 + 3 ^ 40 * 5742180 * 2
def baseEnd_5742180 : Nat := 2948498344634448928042201

theorem tailTrace_5742180 : CollatzResearch.WordTrace tailWord_5742180 prefixEnd_5742180 2948498344634448928042201 := by
  unfold tailWord_5742180
  simp only [CollatzResearch.WordTrace]
  refine ⟨104717255168535010556343997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139623006891380014075125329 104717255168535010556343997)
  ·
    refine ⟨39268970688200628958628999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104717255168535010556343997 39268970688200628958628999)
    ·
      refine ⟨58903456032300943437943499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39268970688200628958628999 58903456032300943437943499)
      ·
        refine ⟨88355184048451415156915249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58903456032300943437943499 88355184048451415156915249)
        ·
          refine ⟨66266388036338561367686437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88355184048451415156915249 66266388036338561367686437)
          ·
            refine ⟨12424947756813480256441207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66266388036338561367686437 12424947756813480256441207)
            ·
              refine ⟨18637421635220220384661811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12424947756813480256441207 18637421635220220384661811)
              ·
                refine ⟨27956132452830330576992717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18637421635220220384661811 27956132452830330576992717)
                ·
                  refine ⟨10483549669811373966372269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27956132452830330576992717 10483549669811373966372269)
                  ·
                    refine ⟨3931331126179265237389601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10483549669811373966372269 3931331126179265237389601)
                    ·
                      refine ⟨2948498344634448928042201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931331126179265237389601 2948498344634448928042201)
                      ·
                        rfl

theorem cell23_5742180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_5742180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742180 prefixEnd_5742180 := by exact prefixLift 5742180
  have htrace : WordTrace (prefixWord ++ tailWord_5742180) baseStart_5742180 baseEnd_5742180 := by
    simpa [prefixWord, tailWord_5742180, baseEnd_5742180] using wordTrace_append hprefix tailTrace_5742180
  have hstable : (prefixWord ++ tailWord_5742180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742180).length < 2 ^ (prefixWord ++ tailWord_5742180).sum := by decide
  have hdescent : baseEnd_5742180 < baseStart_5742180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742256 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_5742256 : Nat := 118140960795 + 5742256 * 2 ^ 59
def prefixEnd_5742256 : Nat := 4983230072969 + 3 ^ 40 * 5742256 * 2
def baseEnd_5742256 : Nat := 2948537369164190630691851

theorem tailTrace_5742256 : CollatzResearch.WordTrace tailWord_5742256 prefixEnd_5742256 2948537369164190630691851 := by
  unfold tailWord_5742256
  simp only [CollatzResearch.WordTrace]
  refine ⟨104718641142397343046227311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139624854856529790728303081 104718641142397343046227311)
  ·
    refine ⟨157077961713596014569340967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104718641142397343046227311 157077961713596014569340967)
    ·
      refine ⟨235616942570394021854011451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157077961713596014569340967 235616942570394021854011451)
      ·
        refine ⟨353425413855591032781017177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235616942570394021854011451 353425413855591032781017177)
        ·
          refine ⟨265069060391693274585762883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353425413855591032781017177 265069060391693274585762883)
          ·
            refine ⟨397603590587539911878644325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265069060391693274585762883 397603590587539911878644325)
            ·
              refine ⟨74550673235163733477245811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397603590587539911878644325 74550673235163733477245811)
              ·
                refine ⟨111826009852745600215868717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74550673235163733477245811 111826009852745600215868717)
                ·
                  refine ⟨41934753694779600080950769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111826009852745600215868717 41934753694779600080950769)
                  ·
                    refine ⟨31451065271084700060713077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41934753694779600080950769 31451065271084700060713077)
                    ·
                      refine ⟨2948537369164190630691851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31451065271084700060713077 2948537369164190630691851)
                      ·
                        rfl

theorem cell23_5742256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_5742256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742256 prefixEnd_5742256 := by exact prefixLift 5742256
  have htrace : WordTrace (prefixWord ++ tailWord_5742256) baseStart_5742256 baseEnd_5742256 := by
    simpa [prefixWord, tailWord_5742256, baseEnd_5742256] using wordTrace_append hprefix tailTrace_5742256
  have hstable : (prefixWord ++ tailWord_5742256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742256).length < 2 ^ (prefixWord ++ tailWord_5742256).sum := by decide
  have hdescent : baseEnd_5742256 < baseStart_5742256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742261 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_5742261 : Nat := 118140960795 + 5742261 * 2 ^ 59
def prefixEnd_5742261 : Nat := 4983230072969 + 3 ^ 40 * 5742261 * 2
def baseEnd_5742261 : Nat := 2948539936567463111129329

theorem tailTrace_5742261 : CollatzResearch.WordTrace tailWord_5742261 prefixEnd_5742261 2948539936567463111129329 := by
  unfold tailWord_5742261
  simp only [CollatzResearch.WordTrace]
  refine ⟨209437464649776571946386637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139624976433184381297591091 209437464649776571946386637)
  ·
    refine ⟨78539049243666214479894989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209437464649776571946386637 78539049243666214479894989)
    ·
      refine ⟨29452143466374830429960621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78539049243666214479894989 29452143466374830429960621)
      ·
        refine ⟨11044553799890561411235233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29452143466374830429960621 11044553799890561411235233)
        ·
          refine ⟨8283415349917921058426425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11044553799890561411235233 8283415349917921058426425)
          ·
            refine ⟨6212561512438440793819819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8283415349917921058426425 6212561512438440793819819)
            ·
              refine ⟨9318842268657661190729729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212561512438440793819819 9318842268657661190729729)
              ·
                refine ⟨6989131701493245893047297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9318842268657661190729729 6989131701493245893047297)
                ·
                  refine ⟨5241848776119934419785473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6989131701493245893047297 5241848776119934419785473)
                  ·
                    refine ⟨3931386582089950814839105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5241848776119934419785473 3931386582089950814839105)
                    ·
                      refine ⟨2948539936567463111129329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931386582089950814839105 2948539936567463111129329)
                      ·
                        rfl

theorem cell23_5742261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_5742261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742261 prefixEnd_5742261 := by exact prefixLift 5742261
  have htrace : WordTrace (prefixWord ++ tailWord_5742261) baseStart_5742261 baseEnd_5742261 := by
    simpa [prefixWord, tailWord_5742261, baseEnd_5742261] using wordTrace_append hprefix tailTrace_5742261
  have hstable : (prefixWord ++ tailWord_5742261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742261).length < 2 ^ (prefixWord ++ tailWord_5742261).sum := by decide
  have hdescent : baseEnd_5742261 < baseStart_5742261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742301 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 5]
def baseStart_5742301 : Nat := 118140960795 + 5742301 * 2 ^ 59
def prefixEnd_5742301 : Nat := 4983230072969 + 3 ^ 40 * 5742301 * 2
def baseEnd_5742301 : Nat := 327617830643738106069905

theorem tailTrace_5742301 : CollatzResearch.WordTrace tailWord_5742301 prefixEnd_5742301 327617830643738106069905 := by
  unfold tailWord_5742301
  simp only [CollatzResearch.WordTrace]
  refine ⟨209438923569631658777842757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139625949046421105851895171 209438923569631658777842757)
  ·
    refine ⟨39269798169305936020845517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209438923569631658777842757 39269798169305936020845517)
    ·
      refine ⟨14726174313489726007817069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39269798169305936020845517 14726174313489726007817069)
      ·
        refine ⟨5522315367558647252931401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14726174313489726007817069 5522315367558647252931401)
        ·
          refine ⟨4141736525668985439698551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522315367558647252931401 4141736525668985439698551)
          ·
            refine ⟨6212604788503478159547827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141736525668985439698551 6212604788503478159547827)
            ·
              refine ⟨9318907182755217239321741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212604788503478159547827 9318907182755217239321741)
              ·
                refine ⟨3494590193533206464745653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9318907182755217239321741 3494590193533206464745653)
                ·
                  refine ⟨327617830643738106069905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494590193533206464745653 327617830643738106069905)
                  ·
                    rfl

theorem cell23_5742301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_5742301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742301 prefixEnd_5742301 := by exact prefixLift 5742301
  have htrace : WordTrace (prefixWord ++ tailWord_5742301) baseStart_5742301 baseEnd_5742301 := by
    simpa [prefixWord, tailWord_5742301, baseEnd_5742301] using wordTrace_append hprefix tailTrace_5742301
  have hstable : (prefixWord ++ tailWord_5742301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742301).length < 2 ^ (prefixWord ++ tailWord_5742301).sum := by decide
  have hdescent : baseEnd_5742301 < baseStart_5742301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742303 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_5742303 : Nat := 118140960795 + 5742303 * 2 ^ 59
def prefixEnd_5742303 : Nat := 4983230072969 + 3 ^ 40 * 5742303 * 2
def baseEnd_5742303 : Nat := 2948561502754951946804135

theorem tailTrace_5742303 : CollatzResearch.WordTrace tailWord_5742303 prefixEnd_5742303 2948561502754951946804135 := by
  unfold tailWord_5742303
  simp only [CollatzResearch.WordTrace]
  refine ⟨209438996515624413119415563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139625997677082942079610375 209438996515624413119415563)
  ·
    refine ⟨314158494773436619679123345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209438996515624413119415563 314158494773436619679123345)
    ·
      refine ⟨235618871080077464759342509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314158494773436619679123345 235618871080077464759342509)
      ·
        refine ⟨88357076655029049284753441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235618871080077464759342509 88357076655029049284753441)
        ·
          refine ⟨66267807491271786963565081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88357076655029049284753441 66267807491271786963565081)
          ·
            refine ⟨49700855618453840222673811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66267807491271786963565081 49700855618453840222673811)
            ·
              refine ⟨74551283427680760334010717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49700855618453840222673811 74551283427680760334010717)
              ·
                refine ⟨27956731285380285125254019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74551283427680760334010717 27956731285380285125254019)
                ·
                  refine ⟨41935096928070427687881029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27956731285380285125254019 41935096928070427687881029)
                  ·
                    refine ⟨7862830674013205191477693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41935096928070427687881029 7862830674013205191477693)
                    ·
                      refine ⟨2948561502754951946804135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862830674013205191477693 2948561502754951946804135)
                      ·
                        rfl

theorem cell23_5742303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_5742303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742303 prefixEnd_5742303 := by exact prefixLift 5742303
  have htrace : WordTrace (prefixWord ++ tailWord_5742303) baseStart_5742303 baseEnd_5742303 := by
    simpa [prefixWord, tailWord_5742303, baseEnd_5742303] using wordTrace_append hprefix tailTrace_5742303
  have hstable : (prefixWord ++ tailWord_5742303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742303).length < 2 ^ (prefixWord ++ tailWord_5742303).sum := by decide
  have hdescent : baseEnd_5742303 < baseStart_5742303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742333 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_5742333 : Nat := 118140960795 + 5742333 * 2 ^ 59
def prefixEnd_5742333 : Nat := 4983230072969 + 3 ^ 40 * 5742333 * 2
def baseEnd_5742333 : Nat := 2948576907174586829428997

theorem tailTrace_5742333 : CollatzResearch.WordTrace tailWord_5742333 prefixEnd_5742333 2948576907174586829428997 := by
  unfold tailWord_5742333
  simp only [CollatzResearch.WordTrace]
  refine ⟨209440090705515728243007653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139626727137010485495338435 209440090705515728243007653)
  ·
    refine ⟨39270017007284199045563935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209440090705515728243007653 39270017007284199045563935)
    ·
      refine ⟨58905025510926298568345903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39270017007284199045563935 58905025510926298568345903)
      ·
        refine ⟨88357538266389447852518855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58905025510926298568345903 88357538266389447852518855)
        ·
          refine ⟨132536307399584171778778283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88357538266389447852518855 132536307399584171778778283)
          ·
            refine ⟨198804461099376257668167425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132536307399584171778778283 198804461099376257668167425)
            ·
              refine ⟨149103345824532193251125569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198804461099376257668167425 149103345824532193251125569)
              ·
                refine ⟨111827509368399144938344177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149103345824532193251125569 111827509368399144938344177)
                ·
                  refine ⟨83870632026299358703758133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111827509368399144938344177 83870632026299358703758133)
                  ·
                    refine ⟨7862871752465564878477325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83870632026299358703758133 7862871752465564878477325)
                    ·
                      refine ⟨2948576907174586829428997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862871752465564878477325 2948576907174586829428997)
                      ·
                        rfl

theorem cell23_5742333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_5742333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742333 prefixEnd_5742333 := by exact prefixLift 5742333
  have htrace : WordTrace (prefixWord ++ tailWord_5742333) baseStart_5742333 baseEnd_5742333 := by
    simpa [prefixWord, tailWord_5742333, baseEnd_5742333] using wordTrace_append hprefix tailTrace_5742333
  have hstable : (prefixWord ++ tailWord_5742333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742333).length < 2 ^ (prefixWord ++ tailWord_5742333).sum := by decide
  have hdescent : baseEnd_5742333 < baseStart_5742333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742340 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 6]
def baseStart_5742340 : Nat := 118140960795 + 5742340 * 2 ^ 59
def prefixEnd_5742340 : Nat := 4983230072969 + 3 ^ 40 * 5742340 * 2
def baseEnd_5742340 : Nat := 327620055726574255782385

theorem tailTrace_5742340 : CollatzResearch.WordTrace tailWord_5742340 prefixEnd_5742340 327620055726574255782385 := by
  unfold tailWord_5742340
  simp only [CollatzResearch.WordTrace]
  refine ⟨104720173008245184219256237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139626897344326912292341649 104720173008245184219256237)
  ·
    refine ⟨39270064878091944082221089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104720173008245184219256237 39270064878091944082221089)
    ·
      refine ⟨29452548658568958061665817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39270064878091944082221089 29452548658568958061665817)
      ·
        refine ⟨22089411493926718546249363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29452548658568958061665817 22089411493926718546249363)
        ·
          refine ⟨33134117240890077819374045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22089411493926718546249363 33134117240890077819374045)
          ·
            refine ⟨12425293965333779182265267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33134117240890077819374045 12425293965333779182265267)
            ·
              refine ⟨18637940948000668773397901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12425293965333779182265267 18637940948000668773397901)
              ·
                refine ⟨6989227855500250790024213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18637940948000668773397901 6989227855500250790024213)
                ·
                  refine ⟨327620055726574255782385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6989227855500250790024213 327620055726574255782385)
                  ·
                    rfl

theorem cell23_5742340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_5742340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742340 prefixEnd_5742340 := by exact prefixLift 5742340
  have htrace : WordTrace (prefixWord ++ tailWord_5742340) baseStart_5742340 baseEnd_5742340 := by
    simpa [prefixWord, tailWord_5742340, baseEnd_5742340] using wordTrace_append hprefix tailTrace_5742340
  have hstable : (prefixWord ++ tailWord_5742340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742340).length < 2 ^ (prefixWord ++ tailWord_5742340).sum := by decide
  have hdescent : baseEnd_5742340 < baseStart_5742340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742354 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5742354 : Nat := 118140960795 + 5742354 * 2 ^ 59
def prefixEnd_5742354 : Nat := 4983230072969 + 3 ^ 40 * 5742354 * 2
def baseEnd_5742354 : Nat := 2948587690268331247266401

theorem tailTrace_5742354 : CollatzResearch.WordTrace tailWord_5742354 prefixEnd_5742354 2948587690268331247266401 := by
  unfold tailWord_5742354
  simp only [CollatzResearch.WordTrace]
  refine ⟨52360214159609912207380529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139627237758959765886348077 52360214159609912207380529)
  ·
    refine ⟨39270160619707434155535397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52360214159609912207380529 39270160619707434155535397)
    ·
      refine ⟨7363155116195143904162887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39270160619707434155535397 7363155116195143904162887)
      ·
        refine ⟨11044732674292715856244331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363155116195143904162887 11044732674292715856244331)
        ·
          refine ⟨16567099011439073784366497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11044732674292715856244331 16567099011439073784366497)
          ·
            refine ⟨12425324258579305338274873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16567099011439073784366497 12425324258579305338274873)
            ·
              refine ⟨9318993193934479003706155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12425324258579305338274873 9318993193934479003706155)
              ·
                refine ⟨13978489790901718505559233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9318993193934479003706155 13978489790901718505559233)
                ·
                  refine ⟨10483867343176288879169425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13978489790901718505559233 10483867343176288879169425)
                  ·
                    refine ⟨7862900507382216659377069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10483867343176288879169425 7862900507382216659377069)
                    ·
                      refine ⟨2948587690268331247266401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862900507382216659377069 2948587690268331247266401)
                      ·
                        rfl

theorem cell23_5742354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5742354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742354 prefixEnd_5742354 := by exact prefixLift 5742354
  have htrace : WordTrace (prefixWord ++ tailWord_5742354) baseStart_5742354 baseEnd_5742354 := by
    simpa [prefixWord, tailWord_5742354, baseEnd_5742354] using wordTrace_append hprefix tailTrace_5742354
  have hstable : (prefixWord ++ tailWord_5742354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742354).length < 2 ^ (prefixWord ++ tailWord_5742354).sum := by decide
  have hdescent : baseEnd_5742354 < baseStart_5742354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742360 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 1, 5, 2]
def baseStart_5742360 : Nat := 118140960795 + 5742360 * 2 ^ 59
def prefixEnd_5742360 : Nat := 4983230072969 + 3 ^ 40 * 5742360 * 2
def baseEnd_5742360 : Nat := 2948590771152258223791373

theorem tailTrace_5742360 : CollatzResearch.WordTrace tailWord_5742360 prefixEnd_5742360 2948590771152258223791373 := by
  unfold tailWord_5742360
  simp only [CollatzResearch.WordTrace]
  refine ⟨104720537738208955927120267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139627383650945274569493689 104720537738208955927120267)
  ·
    refine ⟨157080806607313433890680401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104720537738208955927120267 157080806607313433890680401)
    ·
      refine ⟨117810604955485075418010301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157080806607313433890680401 117810604955485075418010301)
      ·
        refine ⟨44178976858306903281753863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117810604955485075418010301 44178976858306903281753863)
        ·
          refine ⟨66268465287460354922630795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44178976858306903281753863 66268465287460354922630795)
          ·
            refine ⟨99402697931190532383946193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66268465287460354922630795 99402697931190532383946193)
            ·
              refine ⟨74552023448392899287959645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99402697931190532383946193 74552023448392899287959645)
              ·
                refine ⟨27957008793147337232984867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74552023448392899287959645 27957008793147337232984867)
                ·
                  refine ⟨41935513189721005849477301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27957008793147337232984867 41935513189721005849477301)
                  ·
                    refine ⟨3931454361536344298388497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41935513189721005849477301 3931454361536344298388497)
                    ·
                      refine ⟨2948590771152258223791373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931454361536344298388497 2948590771152258223791373)
                      ·
                        rfl

theorem cell23_5742360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_5742360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742360 prefixEnd_5742360 := by exact prefixLift 5742360
  have htrace : WordTrace (prefixWord ++ tailWord_5742360) baseStart_5742360 baseEnd_5742360 := by
    simpa [prefixWord, tailWord_5742360, baseEnd_5742360] using wordTrace_append hprefix tailTrace_5742360
  have hstable : (prefixWord ++ tailWord_5742360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742360).length < 2 ^ (prefixWord ++ tailWord_5742360).sum := by decide
  have hdescent : baseEnd_5742360 < baseStart_5742360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742407 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_5742407 : Nat := 118140960795 + 5742407 * 2 ^ 59
def prefixEnd_5742407 : Nat := 4983230072969 + 3 ^ 40 * 5742407 * 2
def baseEnd_5742407 : Nat := 2948614904743019539903657

theorem tailTrace_5742407 : CollatzResearch.WordTrace tailWord_5742407 prefixEnd_5742407 2948614904743019539903657 := by
  unfold tailWord_5742407
  simp only [CollatzResearch.WordTrace]
  refine ⟨209442789707247638881201475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139628526471498425920800983 209442789707247638881201475)
  ·
    refine ⟨314164184560871458321802213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209442789707247638881201475 314164184560871458321802213)
    ·
      refine ⟨58905784605163398435337915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314164184560871458321802213 58905784605163398435337915)
      ·
        refine ⟨88358676907745097653006873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58905784605163398435337915 88358676907745097653006873)
        ·
          refine ⟨66269007680808823239755155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88358676907745097653006873 66269007680808823239755155)
          ·
            refine ⟨99403511521213234859632733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66269007680808823239755155 99403511521213234859632733)
            ·
              refine ⟨37276316820454963072362275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99403511521213234859632733 37276316820454963072362275)
              ·
                refine ⟨55914475230682444608543413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37276316820454963072362275 55914475230682444608543413)
                ·
                  refine ⟨5241982052876479182050945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55914475230682444608543413 5241982052876479182050945)
                  ·
                    refine ⟨3931486539657359386538209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5241982052876479182050945 3931486539657359386538209)
                    ·
                      refine ⟨2948614904743019539903657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931486539657359386538209 2948614904743019539903657)
                      ·
                        rfl

theorem cell23_5742407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_5742407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742407 prefixEnd_5742407 := by exact prefixLift 5742407
  have htrace : WordTrace (prefixWord ++ tailWord_5742407) baseStart_5742407 baseEnd_5742407 := by
    simpa [prefixWord, tailWord_5742407, baseEnd_5742407] using wordTrace_append hprefix tailTrace_5742407
  have hstable : (prefixWord ++ tailWord_5742407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742407).length < 2 ^ (prefixWord ++ tailWord_5742407).sum := by decide
  have hdescent : baseEnd_5742407 < baseStart_5742407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742410 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_5742410 : Nat := 118140960795 + 5742410 * 2 ^ 59
def prefixEnd_5742410 : Nat := 4983230072969 + 3 ^ 40 * 5742410 * 2
def baseEnd_5742410 : Nat := 2948616445184983028166143

theorem tailTrace_5742410 : CollatzResearch.WordTrace tailWord_5742410 prefixEnd_5742410 2948616445184983028166143 := by
  unfold tailWord_5742410
  simp only [CollatzResearch.WordTrace]
  refine ⟨52360724781559192598390171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139628599417491180262373789 52360724781559192598390171)
  ·
    refine ⟨78541087172338788897585257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52360724781559192598390171 78541087172338788897585257)
    ·
      refine ⟨58905815379254091673188943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78541087172338788897585257 58905815379254091673188943)
      ·
        refine ⟨88358723068881137509783415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58905815379254091673188943 88358723068881137509783415)
        ·
          refine ⟨132538084603321706264675123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88358723068881137509783415 132538084603321706264675123)
          ·
            refine ⟨198807126904982559397012685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132538084603321706264675123 198807126904982559397012685)
            ·
              refine ⟨74552672589368459773879757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198807126904982559397012685 74552672589368459773879757)
              ·
                refine ⟨27957252221013172415204909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74552672589368459773879757 27957252221013172415204909)
                ·
                  refine ⟨10483969582879939655701841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27957252221013172415204909 10483969582879939655701841)
                  ·
                    refine ⟨7862977187159954741776381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10483969582879939655701841 7862977187159954741776381)
                    ·
                      refine ⟨2948616445184983028166143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862977187159954741776381 2948616445184983028166143)
                      ·
                        rfl

theorem cell23_5742410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_5742410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742410 prefixEnd_5742410 := by exact prefixLift 5742410
  have htrace : WordTrace (prefixWord ++ tailWord_5742410) baseStart_5742410 baseEnd_5742410 := by
    simpa [prefixWord, tailWord_5742410, baseEnd_5742410] using wordTrace_append hprefix tailTrace_5742410
  have hstable : (prefixWord ++ tailWord_5742410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742410).length < 2 ^ (prefixWord ++ tailWord_5742410).sum := by decide
  have hdescent : baseEnd_5742410 < baseStart_5742410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742434 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5742434 : Nat := 118140960795 + 5742434 * 2 ^ 59
def prefixEnd_5742434 : Nat := 4983230072969 + 3 ^ 40 * 5742434 * 2
def baseEnd_5742434 : Nat := 982876256240230311422011

theorem tailTrace_5742434 : CollatzResearch.WordTrace tailWord_5742434 prefixEnd_5742434 982876256240230311422011 := by
  unfold tailWord_5742434
  simp only [CollatzResearch.WordTrace]
  refine ⟨52360943619537455623108589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139629182985433214994956237 52360943619537455623108589)
  ·
    refine ⟨19635353857326545858665721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52360943619537455623108589 19635353857326545858665721)
    ·
      refine ⟨14726515392994909393999291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19635353857326545858665721 14726515392994909393999291)
      ·
        refine ⟨22089773089492364090998937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14726515392994909393999291 22089773089492364090998937)
        ·
          refine ⟨16567329817119273068249203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22089773089492364090998937 16567329817119273068249203)
          ·
            refine ⟨24850994725678909602373805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16567329817119273068249203 24850994725678909602373805)
            ·
              refine ⟨9319123022129591100890177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24850994725678909602373805 9319123022129591100890177)
              ·
                refine ⟨6989342266597193325667633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9319123022129591100890177 6989342266597193325667633)
                ·
                  refine ⟨5242006699947894994250725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6989342266597193325667633 5242006699947894994250725)
                  ·
                    refine ⟨982876256240230311422011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242006699947894994250725 982876256240230311422011)
                    ·
                      rfl

theorem cell23_5742434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5742434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742434 prefixEnd_5742434 := by exact prefixLift 5742434
  have htrace : WordTrace (prefixWord ++ tailWord_5742434) baseStart_5742434 baseEnd_5742434 := by
    simpa [prefixWord, tailWord_5742434, baseEnd_5742434] using wordTrace_append hprefix tailTrace_5742434
  have hstable : (prefixWord ++ tailWord_5742434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742434).length < 2 ^ (prefixWord ++ tailWord_5742434).sum := by decide
  have hdescent : baseEnd_5742434 < baseStart_5742434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742554 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_5742554 : Nat := 118140960795 + 5742554 * 2 ^ 59
def prefixEnd_5742554 : Nat := 4983230072969 + 3 ^ 40 * 5742554 * 2
def baseEnd_5742554 : Nat := 327632265155470051640609

theorem tailTrace_5742554 : CollatzResearch.WordTrace tailWord_5742554 prefixEnd_5742554 327632265155470051640609 := by
  unfold tailWord_5742554
  simp only [CollatzResearch.WordTrace]
  refine ⟨52362037809428770746700679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139632100825143388657868477 52362037809428770746700679)
  ·
    refine ⟨78543056714143156120051019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52362037809428770746700679 78543056714143156120051019)
    ·
      refine ⟨117814585071214734180076529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78543056714143156120051019 117814585071214734180076529)
      ·
        refine ⟨88360938803411050635057397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117814585071214734180076529 88360938803411050635057397)
        ·
          refine ⟨8283838012819785997036631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88360938803411050635057397 8283838012819785997036631)
          ·
            refine ⟨12425757019229678995554947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8283838012819785997036631 12425757019229678995554947)
            ·
              refine ⟨18638635528844518493332421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12425757019229678995554947 18638635528844518493332421)
              ·
                refine ⟨3494744161658347217499829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18638635528844518493332421 3494744161658347217499829)
                ·
                  refine ⟨327632265155470051640609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494744161658347217499829 327632265155470051640609)
                  ·
                    rfl

theorem cell23_5742554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_5742554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742554 prefixEnd_5742554 := by exact prefixLift 5742554
  have htrace : WordTrace (prefixWord ++ tailWord_5742554) baseStart_5742554 baseEnd_5742554 := by
    simpa [prefixWord, tailWord_5742554, baseEnd_5742554] using wordTrace_append hprefix tailTrace_5742554
  have hstable : (prefixWord ++ tailWord_5742554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742554).length < 2 ^ (prefixWord ++ tailWord_5742554).sum := by decide
  have hdescent : baseEnd_5742554 < baseStart_5742554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742587 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 4]
def baseStart_5742587 : Nat := 118140960795 + 5742587 * 2 ^ 59
def prefixEnd_5742587 : Nat := 4983230072969 + 3 ^ 40 * 5742587 * 2
def baseEnd_5742587 : Nat := 2948707331260828835652829

theorem tailTrace_5742587 : CollatzResearch.WordTrace tailWord_5742587 prefixEnd_5742587 2948707331260828835652829 := by
  unfold tailWord_5742587
  simp only [CollatzResearch.WordTrace]
  refine ⟨209449354846595529622754015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139632903231063686415169343 209449354846595529622754015)
  ·
    refine ⟨314174032269893294434131023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209449354846595529622754015 314174032269893294434131023)
    ·
      refine ⟨471261048404839941651196535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314174032269893294434131023 471261048404839941651196535)
      ·
        refine ⟨706891572607259912476794803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471261048404839941651196535 706891572607259912476794803)
        ·
          refine ⟨1060337358910889868715192205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706891572607259912476794803 1060337358910889868715192205)
          ·
            refine ⟨397626509591583700768197077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060337358910889868715192205 397626509591583700768197077)
            ·
              refine ⟨9319371318552742986754619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 397626509591583700768197077 9319371318552742986754619)
              ·
                refine ⟨13979056977829114480131929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319371318552742986754619 13979056977829114480131929)
                ·
                  refine ⟨10484292733371835860098947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13979056977829114480131929 10484292733371835860098947)
                  ·
                    refine ⟨15726439100057753790148421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10484292733371835860098947 15726439100057753790148421)
                    ·
                      refine ⟨2948707331260828835652829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15726439100057753790148421 2948707331260828835652829)
                      ·
                        rfl

theorem cell23_5742587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 4].length) (baseStart_5742587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742587 prefixEnd_5742587 := by exact prefixLift 5742587
  have htrace : WordTrace (prefixWord ++ tailWord_5742587) baseStart_5742587 baseEnd_5742587 := by
    simpa [prefixWord, tailWord_5742587, baseEnd_5742587] using wordTrace_append hprefix tailTrace_5742587
  have hstable : (prefixWord ++ tailWord_5742587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742587).length < 2 ^ (prefixWord ++ tailWord_5742587).sum := by decide
  have hdescent : baseEnd_5742587 < baseStart_5742587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742600 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5742600 : Nat := 118140960795 + 5742600 * 2 ^ 59
def prefixEnd_5742600 : Nat := 4983230072969 + 3 ^ 40 * 5742600 * 2
def baseEnd_5742600 : Nat := 2948714006509337284790269

theorem tailTrace_5742600 : CollatzResearch.WordTrace tailWord_5742600 prefixEnd_5742600 2948714006509337284790269 := by
  unfold tailWord_5742600
  simp only [CollatzResearch.WordTrace]
  refine ⟨104724914497774216421488627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139633219330365621895318169 104724914497774216421488627)
  ·
    refine ⟨157087371746661324632232941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104724914497774216421488627 157087371746661324632232941)
    ·
      refine ⟨58907764404997996737087353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157087371746661324632232941 58907764404997996737087353)
      ·
        refine ⟨44180823303748497552815515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58907764404997996737087353 44180823303748497552815515)
        ·
          refine ⟨66271234955622746329223273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44180823303748497552815515 66271234955622746329223273)
          ·
            refine ⟨49703426216717059746917455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66271234955622746329223273 49703426216717059746917455)
            ·
              refine ⟨74555139325075589620376183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49703426216717059746917455 74555139325075589620376183)
              ·
                refine ⟨111832708987613384430564275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74555139325075589620376183 111832708987613384430564275)
                ·
                  refine ⟨167749063481420076645846413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111832708987613384430564275 167749063481420076645846413)
                  ·
                    refine ⟨62905898805532528742192405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167749063481420076645846413 62905898805532528742192405)
                    ·
                      refine ⟨2948714006509337284790269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62905898805532528742192405 2948714006509337284790269)
                      ·
                        rfl

theorem cell23_5742600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5742600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742600 prefixEnd_5742600 := by exact prefixLift 5742600
  have htrace : WordTrace (prefixWord ++ tailWord_5742600) baseStart_5742600 baseEnd_5742600 := by
    simpa [prefixWord, tailWord_5742600, baseEnd_5742600] using wordTrace_append hprefix tailTrace_5742600
  have hstable : (prefixWord ++ tailWord_5742600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742600).length < 2 ^ (prefixWord ++ tailWord_5742600).sum := by decide
  have hdescent : baseEnd_5742600 < baseStart_5742600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742648 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 1, 4]
def baseStart_5742648 : Nat := 118140960795 + 5742648 * 2 ^ 59
def prefixEnd_5742648 : Nat := 4983230072969 + 3 ^ 40 * 5742648 * 2
def baseEnd_5742648 : Nat := 982912884526917698996683

theorem tailTrace_5742648 : CollatzResearch.WordTrace tailWord_5742648 prefixEnd_5742648 982912884526917698996683 := by
  unfold tailWord_5742648
  simp only [CollatzResearch.WordTrace]
  refine ⟨104725789849687268520362299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139634386466249691360483065 104725789849687268520362299)
  ·
    refine ⟨157088684774530902780543449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104725789849687268520362299 157088684774530902780543449)
    ·
      refine ⟨117816513580898177085407587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157088684774530902780543449 117816513580898177085407587)
      ·
        refine ⟨176724770371347265628111381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117816513580898177085407587 176724770371347265628111381)
        ·
          refine ⟨8283973611156903076317721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176724770371347265628111381 8283973611156903076317721)
          ·
            refine ⟨6212980208367677307238291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8283973611156903076317721 6212980208367677307238291)
            ·
              refine ⟨9319470312551515960857437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212980208367677307238291 9319470312551515960857437)
              ·
                refine ⟨3494801367206818485321539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9319470312551515960857437 3494801367206818485321539)
                ·
                  refine ⟨5242202050810227727982309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494801367206818485321539 5242202050810227727982309)
                  ·
                    refine ⟨982912884526917698996683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242202050810227727982309 982912884526917698996683)
                    ·
                      rfl

theorem cell23_5742648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_5742648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742648 prefixEnd_5742648 := by exact prefixLift 5742648
  have htrace : WordTrace (prefixWord ++ tailWord_5742648) baseStart_5742648 baseEnd_5742648 := by
    simpa [prefixWord, tailWord_5742648, baseEnd_5742648] using wordTrace_append hprefix tailTrace_5742648
  have hstable : (prefixWord ++ tailWord_5742648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742648).length < 2 ^ (prefixWord ++ tailWord_5742648).sum := by decide
  have hdescent : baseEnd_5742648 < baseStart_5742648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742678 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_5742678 : Nat := 118140960795 + 5742678 * 2 ^ 59
def prefixEnd_5742678 : Nat := 4983230072969 + 3 ^ 40 * 5742678 * 2
def baseEnd_5742678 : Nat := 327639339777820886623879

theorem tailTrace_5742678 : CollatzResearch.WordTrace tailWord_5742678 prefixEnd_5742678 327639339777820886623879 := by
  unfold tailWord_5742678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13090792118079115760269793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139635115926177234776211125 13090792118079115760269793)
  ·
    refine ⟨9818094088559336820202345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13090792118079115760269793 9818094088559336820202345)
    ·
      refine ⟨7363570566419502615151759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9818094088559336820202345 7363570566419502615151759)
      ·
        refine ⟨11045355849629253922727639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363570566419502615151759 11045355849629253922727639)
        ·
          refine ⟨16568033774443880884091459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11045355849629253922727639 16568033774443880884091459)
          ·
            refine ⟨24852050661665821326137189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16568033774443880884091459 24852050661665821326137189)
            ·
              refine ⟨4659759499062341498650723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24852050661665821326137189 4659759499062341498650723)
              ·
                refine ⟨6989639248593512247976085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659759499062341498650723 6989639248593512247976085)
                ·
                  refine ⟨327639339777820886623879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6989639248593512247976085 327639339777820886623879)
                  ·
                    rfl

theorem cell23_5742678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_5742678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742678 prefixEnd_5742678 := by exact prefixLift 5742678
  have htrace : WordTrace (prefixWord ++ tailWord_5742678) baseStart_5742678 baseEnd_5742678 := by
    simpa [prefixWord, tailWord_5742678, baseEnd_5742678] using wordTrace_append hprefix tailTrace_5742678
  have hstable : (prefixWord ++ tailWord_5742678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742678).length < 2 ^ (prefixWord ++ tailWord_5742678).sum := by decide
  have hdescent : baseEnd_5742678 < baseStart_5742678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742687 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 6, 4]
def baseStart_5742687 : Nat := 118140960795 + 5742687 * 2 ^ 59
def prefixEnd_5742687 : Nat := 4983230072969 + 3 ^ 40 * 5742687 * 2
def baseEnd_5742687 : Nat := 982919559775426148134123

theorem tailTrace_5742687 : CollatzResearch.WordTrace tailWord_5742687 prefixEnd_5742687 982919559775426148134123 := by
  unfold tailWord_5742687
  simp only [CollatzResearch.WordTrace]
  refine ⟨209453002146233246701394315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139635334764155497800929543 209453002146233246701394315)
  ·
    refine ⟨314179503219349870052091473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209453002146233246701394315 314179503219349870052091473)
    ·
      refine ⟨235634627414512402539068605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314179503219349870052091473 235634627414512402539068605)
      ·
        refine ⟨88362985280442150952150727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235634627414512402539068605 88362985280442150952150727)
        ·
          refine ⟨132544477920663226428226091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88362985280442150952150727 132544477920663226428226091)
          ·
            refine ⟨198816716880994839642339137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132544477920663226428226091 198816716880994839642339137)
            ·
              refine ⟨149112537660746129731754353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198816716880994839642339137 149112537660746129731754353)
              ·
                refine ⟨111834403245559597298815765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149112537660746129731754353 111834403245559597298815765)
                ·
                  refine ⟨5242237652135606123381989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111834403245559597298815765 5242237652135606123381989)
                  ·
                    refine ⟨982919559775426148134123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242237652135606123381989 982919559775426148134123)
                    ·
                      rfl

theorem cell23_5742687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_5742687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742687 prefixEnd_5742687 := by exact prefixLift 5742687
  have htrace : WordTrace (prefixWord ++ tailWord_5742687) baseStart_5742687 baseEnd_5742687 := by
    simpa [prefixWord, tailWord_5742687, baseEnd_5742687] using wordTrace_append hprefix tailTrace_5742687
  have hstable : (prefixWord ++ tailWord_5742687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742687).length < 2 ^ (prefixWord ++ tailWord_5742687).sum := by decide
  have hdescent : baseEnd_5742687 < baseStart_5742687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742698 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_5742698 : Nat := 118140960795 + 5742698 * 2 ^ 59
def prefixEnd_5742698 : Nat := 4983230072969 + 3 ^ 40 * 5742698 * 2
def baseEnd_5742698 : Nat := 2948764327613477901364819

theorem tailTrace_5742698 : CollatzResearch.WordTrace tailWord_5742698 prefixEnd_5742698 2948764327613477901364819 := by
  unfold tailWord_5742698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52363350837298348895011187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139635602232795597053363165 52363350837298348895011187)
  ·
    refine ⟨78545026255947523342516781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52363350837298348895011187 78545026255947523342516781)
    ·
      refine ⟨29454384845980321253443793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78545026255947523342516781 29454384845980321253443793)
      ·
        refine ⟨22090788634485240940082845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29454384845980321253443793 22090788634485240940082845)
        ·
          refine ⟨8284045737931965352531067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22090788634485240940082845 8284045737931965352531067)
          ·
            refine ⟨12426068606897948028796601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8284045737931965352531067 12426068606897948028796601)
            ·
              refine ⟨9319551455173461021597451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12426068606897948028796601 9319551455173461021597451)
              ·
                refine ⟨13979327182760191532396177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319551455173461021597451 13979327182760191532396177)
                ·
                  refine ⟨10484495387070143649297133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13979327182760191532396177 10484495387070143649297133)
                  ·
                    refine ⟨3931685770151303868486425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10484495387070143649297133 3931685770151303868486425)
                    ·
                      refine ⟨2948764327613477901364819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931685770151303868486425 2948764327613477901364819)
                      ·
                        rfl

theorem cell23_5742698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_5742698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742698 prefixEnd_5742698 := by exact prefixLift 5742698
  have htrace : WordTrace (prefixWord ++ tailWord_5742698) baseStart_5742698 baseEnd_5742698 := by
    simpa [prefixWord, tailWord_5742698, baseEnd_5742698] using wordTrace_append hprefix tailTrace_5742698
  have hstable : (prefixWord ++ tailWord_5742698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742698).length < 2 ^ (prefixWord ++ tailWord_5742698).sum := by decide
  have hdescent : baseEnd_5742698 < baseStart_5742698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742711 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 1, 1, 4]
def baseStart_5742711 : Nat := 118140960795 + 5742711 * 2 ^ 59
def prefixEnd_5742711 : Nat := 4983230072969 + 3 ^ 40 * 5742711 * 2
def baseEnd_5742711 : Nat := 2948771002861986350502259

theorem tailTrace_5742711 : CollatzResearch.WordTrace tailWord_5742711 prefixEnd_5742711 2948771002861986350502259 := by
  unfold tailWord_5742711
  simp only [CollatzResearch.WordTrace]
  refine ⟨209453877498146298800267987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139635918332097532533511991 209453877498146298800267987)
  ·
    refine ⟨314180816247219448200401981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209453877498146298800267987 314180816247219448200401981)
    ·
      refine ⟨117817806092707293075150743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314180816247219448200401981 117817806092707293075150743)
      ·
        refine ⟨176726709139060939612726115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117817806092707293075150743 176726709139060939612726115)
        ·
          refine ⟨265090063708591409419089173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176726709139060939612726115 265090063708591409419089173)
          ·
            refine ⟨12426096736340222316519805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265090063708591409419089173 12426096736340222316519805)
            ·
              refine ⟨4659786276127583368694927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12426096736340222316519805 4659786276127583368694927)
              ·
                refine ⟨6989679414191375053042391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659786276127583368694927 6989679414191375053042391)
                ·
                  refine ⟨10484519121287062579563587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989679414191375053042391 10484519121287062579563587)
                  ·
                    refine ⟨15726778681930593869345381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10484519121287062579563587 15726778681930593869345381)
                    ·
                      refine ⟨2948771002861986350502259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15726778681930593869345381 2948771002861986350502259)
                      ·
                        rfl

theorem cell23_5742711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_5742711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742711 prefixEnd_5742711 := by exact prefixLift 5742711
  have htrace : WordTrace (prefixWord ++ tailWord_5742711) baseStart_5742711 baseEnd_5742711 := by
    simpa [prefixWord, tailWord_5742711, baseEnd_5742711] using wordTrace_append hprefix tailTrace_5742711
  have hstable : (prefixWord ++ tailWord_5742711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742711).length < 2 ^ (prefixWord ++ tailWord_5742711).sum := by decide
  have hdescent : baseEnd_5742711 < baseStart_5742711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742757 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_5742757 : Nat := 118140960795 + 5742757 * 2 ^ 59
def prefixEnd_5742757 : Nat := 4983230072969 + 3 ^ 40 * 5742757 * 2
def baseEnd_5742757 : Nat := 2948794622972093170527047

theorem tailTrace_5742757 : CollatzResearch.WordTrace tailWord_5742757 prefixEnd_5742757 2948794622972093170527047 := by
  unfold tailWord_5742757
  simp only [CollatzResearch.WordTrace]
  refine ⟨209455555255979648656442525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139637036837319765770961683 209455555255979648656442525)
  ·
    refine ⟨78545833220992368246165947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209455555255979648656442525 78545833220992368246165947)
    ·
      refine ⟨117818749831488552369248921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78545833220992368246165947 117818749831488552369248921)
      ·
        refine ⟨88364062373616414276936691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117818749831488552369248921 88364062373616414276936691)
        ·
          refine ⟨132546093560424621415405037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88364062373616414276936691 132546093560424621415405037)
          ·
            refine ⟨49704785085159233030776889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132546093560424621415405037 49704785085159233030776889)
            ·
              refine ⟨37278588813869424773082667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49704785085159233030776889 37278588813869424773082667)
              ·
                refine ⟨55917883220804137159624001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37278588813869424773082667 55917883220804137159624001)
                ·
                  refine ⟨41938412415603102869718001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55917883220804137159624001 41938412415603102869718001)
                  ·
                    refine ⟨31453809311702327152288501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41938412415603102869718001 31453809311702327152288501)
                    ·
                      refine ⟨2948794622972093170527047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31453809311702327152288501 2948794622972093170527047)
                      ·
                        rfl

theorem cell23_5742757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_5742757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742757 prefixEnd_5742757 := by exact prefixLift 5742757
  have htrace : WordTrace (prefixWord ++ tailWord_5742757) baseStart_5742757 baseEnd_5742757 := by
    simpa [prefixWord, tailWord_5742757, baseEnd_5742757] using wordTrace_append hprefix tailTrace_5742757
  have hstable : (prefixWord ++ tailWord_5742757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742757).length < 2 ^ (prefixWord ++ tailWord_5742757).sum := by decide
  have hdescent : baseEnd_5742757 < baseStart_5742757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742762 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5742762 : Nat := 118140960795 + 5742762 * 2 ^ 59
def prefixEnd_5742762 : Nat := 4983230072969 + 3 ^ 40 * 5742762 * 2
def baseEnd_5742762 : Nat := 2948797190375365650964525

theorem tailTrace_5742762 : CollatzResearch.WordTrace tailWord_5742762 prefixEnd_5742762 2948797190375365650964525 := by
  unfold tailWord_5742762
  simp only [CollatzResearch.WordTrace]
  refine ⟨52363934405240383627593635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139637158413974356340249693 52363934405240383627593635)
  ·
    refine ⟨78545901607860575441390453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52363934405240383627593635 78545901607860575441390453)
    ·
      refine ⟨7363678275736928947630355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78545901607860575441390453 7363678275736928947630355)
      ·
        refine ⟨11045517413605393421445533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363678275736928947630355 11045517413605393421445533)
        ·
          refine ⟨4142069030102022533042075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11045517413605393421445533 4142069030102022533042075)
          ·
            refine ⟨6213103545153033799563113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142069030102022533042075 6213103545153033799563113)
            ·
              refine ⟨4659827658864775349672335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6213103545153033799563113 4659827658864775349672335)
              ·
                refine ⟨6989741488297163024508503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659827658864775349672335 6989741488297163024508503)
                ·
                  refine ⟨10484612232445744536762755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989741488297163024508503 10484612232445744536762755)
                  ·
                    refine ⟨15726918348668616805144133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10484612232445744536762755 15726918348668616805144133)
                    ·
                      refine ⟨2948797190375365650964525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15726918348668616805144133 2948797190375365650964525)
                      ·
                        rfl

theorem cell23_5742762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5742762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742762 prefixEnd_5742762 := by exact prefixLift 5742762
  have htrace : WordTrace (prefixWord ++ tailWord_5742762) baseStart_5742762 baseEnd_5742762 := by
    simpa [prefixWord, tailWord_5742762, baseEnd_5742762] using wordTrace_append hprefix tailTrace_5742762
  have hstable : (prefixWord ++ tailWord_5742762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742762).length < 2 ^ (prefixWord ++ tailWord_5742762).sum := by decide
  have hdescent : baseEnd_5742762 < baseStart_5742762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742765 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_5742765 : Nat := 118140960795 + 5742765 * 2 ^ 59
def prefixEnd_5742765 : Nat := 4983230072969 + 3 ^ 40 * 5742765 * 2
def baseEnd_5742765 : Nat := 2948798730817329139227011

theorem tailTrace_5742765 : CollatzResearch.WordTrace tailWord_5742765 prefixEnd_5742765 2948798730817329139227011 := by
  unfold tailWord_5742765
  simp only [CollatzResearch.WordTrace]
  refine ⟨209455847039950666022733749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139637231359967110681822499 209455847039950666022733749)
  ·
    refine ⟨19636485659995374939631289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209455847039950666022733749 19636485659995374939631289)
    ·
      refine ⟨14727364244996531204723467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19636485659995374939631289 14727364244996531204723467)
      ·
        refine ⟨22091046367494796807085201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14727364244996531204723467 22091046367494796807085201)
        ·
          refine ⟨16568284775621097605313901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22091046367494796807085201 16568284775621097605313901)
          ·
            refine ⟨6213106790857911601992713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16568284775621097605313901 6213106790857911601992713)
            ·
              refine ⟨4659830093143433701494535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6213106790857911601992713 4659830093143433701494535)
              ·
                refine ⟨6989745139715150552241803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4659830093143433701494535 6989745139715150552241803)
                ·
                  refine ⟨10484617709572725828362705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989745139715150552241803 10484617709572725828362705)
                  ·
                    refine ⟨7863463282179544371272029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10484617709572725828362705 7863463282179544371272029)
                    ·
                      refine ⟨2948798730817329139227011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7863463282179544371272029 2948798730817329139227011)
                      ·
                        rfl

theorem cell23_5742765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_5742765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742765 prefixEnd_5742765 := by exact prefixLift 5742765
  have htrace : WordTrace (prefixWord ++ tailWord_5742765) baseStart_5742765 baseEnd_5742765 := by
    simpa [prefixWord, tailWord_5742765, baseEnd_5742765] using wordTrace_append hprefix tailTrace_5742765
  have hstable : (prefixWord ++ tailWord_5742765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742765).length < 2 ^ (prefixWord ++ tailWord_5742765).sum := by decide
  have hdescent : baseEnd_5742765 < baseStart_5742765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742777 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_5742777 : Nat := 118140960795 + 5742777 * 2 ^ 59
def prefixEnd_5742777 : Nat := 4983230072969 + 3 ^ 40 * 5742777 * 2
def baseEnd_5742777 : Nat := 982934964195061030758985

theorem tailTrace_5742777 : CollatzResearch.WordTrace tailWord_5742777 prefixEnd_5742777 982934964195061030758985 := by
  unfold tailWord_5742777
  simp only [CollatzResearch.WordTrace]
  refine ⟨209456284715907192072170585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139637523143938128048113723 209456284715907192072170585)
  ·
    refine ⟨157092213536930394054127939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209456284715907192072170585 157092213536930394054127939)
    ·
      refine ⟨235638320305395591081191909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157092213536930394054127939 235638320305395591081191909)
      ·
        refine ⟨44182185057261673327723483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235638320305395591081191909 44182185057261673327723483)
        ·
          refine ⟨66273277585892509991585225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44182185057261673327723483 66273277585892509991585225)
          ·
            refine ⟨49704958189419382493688919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66273277585892509991585225 49704958189419382493688919)
            ·
              refine ⟨74557437284129073740533379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49704958189419382493688919 74557437284129073740533379)
              ·
                refine ⟨111836155926193610610800069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74557437284129073740533379 111836155926193610610800069)
                ·
                  refine ⟨20969279236161301989525013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111836155926193610610800069 20969279236161301989525013)
                  ·
                    refine ⟨982934964195061030758985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20969279236161301989525013 982934964195061030758985)
                    ·
                      rfl

theorem cell23_5742777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_5742777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742777 prefixEnd_5742777 := by exact prefixLift 5742777
  have htrace : WordTrace (prefixWord ++ tailWord_5742777) baseStart_5742777 baseEnd_5742777 := by
    simpa [prefixWord, tailWord_5742777, baseEnd_5742777] using wordTrace_append hprefix tailTrace_5742777
  have hstable : (prefixWord ++ tailWord_5742777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742777).length < 2 ^ (prefixWord ++ tailWord_5742777).sum := by decide
  have hdescent : baseEnd_5742777 < baseStart_5742777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742801 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 1, 4, 2]
def baseStart_5742801 : Nat := 118140960795 + 5742801 * 2 ^ 59
def prefixEnd_5742801 : Nat := 4983230072969 + 3 ^ 40 * 5742801 * 2
def baseEnd_5742801 : Nat := 2948817216120890998376845

theorem tailTrace_5742801 : CollatzResearch.WordTrace tailWord_5742801 prefixEnd_5742801 2948817216120890998376845 := by
  unfold tailWord_5742801
  simp only [CollatzResearch.WordTrace]
  refine ⟨209457160067820244171044257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139638106711880162780696171 209457160067820244171044257)
  ·
    refine ⟨157092870050865183128283193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209457160067820244171044257 157092870050865183128283193)
    ·
      refine ⟨117819652538148887346212395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157092870050865183128283193 117819652538148887346212395)
      ·
        refine ⟨176729478807223331019318593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117819652538148887346212395 176729478807223331019318593)
        ·
          refine ⟨132547109105417498264488945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176729478807223331019318593 132547109105417498264488945)
          ·
            refine ⟨99410331829063123698366709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132547109105417498264488945 99410331829063123698366709)
            ·
              refine ⟨9319718608974667846721879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99410331829063123698366709 9319718608974667846721879)
              ·
                refine ⟨13979577913462001770082819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319718608974667846721879 13979577913462001770082819)
                ·
                  refine ⟨20969366870193002655124229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13979577913462001770082819 20969366870193002655124229)
                  ·
                    refine ⟨3931756288161187997835793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20969366870193002655124229 3931756288161187997835793)
                    ·
                      refine ⟨2948817216120890998376845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931756288161187997835793 2948817216120890998376845)
                      ·
                        rfl

theorem cell23_5742801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_5742801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742801 prefixEnd_5742801 := by exact prefixLift 5742801
  have htrace : WordTrace (prefixWord ++ tailWord_5742801) baseStart_5742801 baseEnd_5742801 := by
    simpa [prefixWord, tailWord_5742801, baseEnd_5742801] using wordTrace_append hprefix tailTrace_5742801
  have hstable : (prefixWord ++ tailWord_5742801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742801).length < 2 ^ (prefixWord ++ tailWord_5742801).sum := by decide
  have hdescent : baseEnd_5742801 < baseStart_5742801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742805 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5742805 : Nat := 118140960795 + 5742805 * 2 ^ 59
def prefixEnd_5742805 : Nat := 4983230072969 + 3 ^ 40 * 5742805 * 2
def baseEnd_5742805 : Nat := 2948819270043508982726827

theorem tailTrace_5742805 : CollatzResearch.WordTrace tailWord_5742805 prefixEnd_5742805 2948819270043508982726827 := by
  unfold tailWord_5742805
  simp only [CollatzResearch.WordTrace]
  refine ⟨209457305959805752854189869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139638203973203835236126579 209457305959805752854189869)
  ·
    refine ⟨78546489734927157320321201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209457305959805752854189869 78546489734927157320321201)
    ·
      refine ⟨58909867301195367990240901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78546489734927157320321201 58909867301195367990240901)
      ·
        refine ⟨11045600118974131498170169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58909867301195367990240901 11045600118974131498170169)
        ·
          refine ⟨8284200089230598623627627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11045600118974131498170169 8284200089230598623627627)
          ·
            refine ⟨12426300133845897935441441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8284200089230598623627627 12426300133845897935441441)
            ·
              refine ⟨9319725100384423451581081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12426300133845897935441441 9319725100384423451581081)
              ·
                refine ⟨6989793825288317588685811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9319725100384423451581081 6989793825288317588685811)
                ·
                  refine ⟨10484690737932476383028717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6989793825288317588685811 10484690737932476383028717)
                  ·
                    refine ⟨3931759026724678643635769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10484690737932476383028717 3931759026724678643635769)
                    ·
                      refine ⟨2948819270043508982726827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931759026724678643635769 2948819270043508982726827)
                      ·
                        rfl

theorem cell23_5742805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5742805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742805 prefixEnd_5742805 := by exact prefixLift 5742805
  have htrace : WordTrace (prefixWord ++ tailWord_5742805) baseStart_5742805 baseEnd_5742805 := by
    simpa [prefixWord, tailWord_5742805, baseEnd_5742805] using wordTrace_append hprefix tailTrace_5742805
  have hstable : (prefixWord ++ tailWord_5742805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742805).length < 2 ^ (prefixWord ++ tailWord_5742805).sum := by decide
  have hdescent : baseEnd_5742805 < baseStart_5742805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742867 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 8]
def baseStart_5742867 : Nat := 118140960795 + 5742867 * 2 ^ 59
def prefixEnd_5742867 : Nat := 4983230072969 + 3 ^ 40 * 5742867 * 2
def baseEnd_5742867 : Nat := 982950368614695913383847

theorem tailTrace_5742867 : CollatzResearch.WordTrace tailWord_5742867 prefixEnd_5742867 982950368614695913383847 := by
  unfold tailWord_5742867
  simp only [CollatzResearch.WordTrace]
  refine ⟨209459567285581137442946855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139639711523720758295297903 209459567285581137442946855)
  ·
    refine ⟨314189350928371706164420283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209459567285581137442946855 314189350928371706164420283)
    ·
      refine ⟨471284026392557559246630425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314189350928371706164420283 471284026392557559246630425)
      ·
        refine ⟨353463019794418169434972819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471284026392557559246630425 353463019794418169434972819)
        ·
          refine ⟨530194529691627254152459229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353463019794418169434972819 530194529691627254152459229)
          ·
            refine ⟨198822948634360220307172211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530194529691627254152459229 198822948634360220307172211)
            ·
              refine ⟨298234422951540330460758317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198822948634360220307172211 298234422951540330460758317)
              ·
                refine ⟨111837908606827623922784369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298234422951540330460758317 111837908606827623922784369)
                ·
                  refine ⟨83878431455120717942088277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111837908606827623922784369 83878431455120717942088277)
                  ·
                    refine ⟨982950368614695913383847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83878431455120717942088277 982950368614695913383847)
                    ·
                      rfl

theorem cell23_5742867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_5742867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742867 prefixEnd_5742867 := by exact prefixLift 5742867
  have htrace : WordTrace (prefixWord ++ tailWord_5742867) baseStart_5742867 baseEnd_5742867 := by
    simpa [prefixWord, tailWord_5742867, baseEnd_5742867] using wordTrace_append hprefix tailTrace_5742867
  have hstable : (prefixWord ++ tailWord_5742867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742867).length < 2 ^ (prefixWord ++ tailWord_5742867).sum := by decide
  have hdescent : baseEnd_5742867 < baseStart_5742867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742871 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 2, 5]
def baseStart_5742871 : Nat := 118140960795 + 5742871 * 2 ^ 59
def prefixEnd_5742871 : Nat := 4983230072969 + 3 ^ 40 * 5742871 * 2
def baseEnd_5742871 : Nat := 982951053255568574833841

theorem tailTrace_5742871 : CollatzResearch.WordTrace tailWord_5742871 prefixEnd_5742871 982951053255568574833841 := by
  unfold tailWord_5742871
  simp only [CollatzResearch.WordTrace]
  refine ⟨209459713177566646126092467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139639808785044430750728311 209459713177566646126092467)
  ·
    refine ⟨314189569766349969189138701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209459713177566646126092467 314189569766349969189138701)
    ·
      refine ⟨117821088662381238445927013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314189569766349969189138701 117821088662381238445927013)
      ·
        refine ⟨22091454124196482208611315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117821088662381238445927013 22091454124196482208611315)
        ·
          refine ⟨33137181186294723312916973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22091454124196482208611315 33137181186294723312916973)
          ·
            refine ⟨12426442944860521242343865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33137181186294723312916973 12426442944860521242343865)
            ·
              refine ⟨9319832208645390931757899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12426442944860521242343865 9319832208645390931757899)
              ·
                refine ⟨13979748312968086397636849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319832208645390931757899 13979748312968086397636849)
                ·
                  refine ⟨10484811234726064798227637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13979748312968086397636849 10484811234726064798227637)
                  ·
                    refine ⟨982951053255568574833841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10484811234726064798227637 982951053255568574833841)
                    ·
                      rfl

theorem cell23_5742871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_5742871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742871 prefixEnd_5742871 := by exact prefixLift 5742871
  have htrace : WordTrace (prefixWord ++ tailWord_5742871) baseStart_5742871 baseEnd_5742871 := by
    simpa [prefixWord, tailWord_5742871, baseEnd_5742871] using wordTrace_append hprefix tailTrace_5742871
  have hstable : (prefixWord ++ tailWord_5742871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742871).length < 2 ^ (prefixWord ++ tailWord_5742871).sum := by decide
  have hdescent : baseEnd_5742871 < baseStart_5742871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742901 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_5742901 : Nat := 118140960795 + 5742901 * 2 ^ 59
def prefixEnd_5742901 : Nat := 4983230072969 + 3 ^ 40 * 5742901 * 2
def baseEnd_5742901 : Nat := 982956188062113535708795

theorem tailTrace_5742901 : CollatzResearch.WordTrace tailWord_5742901 prefixEnd_5742901 982956188062113535708795 := by
  unfold tailWord_5742901
  simp only [CollatzResearch.WordTrace]
  refine ⟨209460807367457961249684557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139640538244971974166456371 209460807367457961249684557)
  ·
    refine ⟨78547802762796735468631709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209460807367457961249684557 78547802762796735468631709)
    ·
      refine ⟨29455426036048775800736891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78547802762796735468631709 29455426036048775800736891)
      ·
        refine ⟨44183139054073163701105337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29455426036048775800736891 44183139054073163701105337)
        ·
          refine ⟨33137354290554872775829003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44183139054073163701105337 33137354290554872775829003)
          ·
            refine ⟨49706031435832309163743505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33137354290554872775829003 49706031435832309163743505)
            ·
              refine ⟨37279523576874231872807629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49706031435832309163743505 37279523576874231872807629)
              ·
                refine ⟨13979821341327836952302861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37279523576874231872807629 13979821341327836952302861)
                ·
                  refine ⟨5242433002997938857113573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13979821341327836952302861 5242433002997938857113573)
                  ·
                    refine ⟨982956188062113535708795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242433002997938857113573 982956188062113535708795)
                    ·
                      rfl

theorem cell23_5742901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_5742901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742901 prefixEnd_5742901 := by exact prefixLift 5742901
  have htrace : WordTrace (prefixWord ++ tailWord_5742901) baseStart_5742901 baseEnd_5742901 := by
    simpa [prefixWord, tailWord_5742901, baseEnd_5742901] using wordTrace_append hprefix tailTrace_5742901
  have hstable : (prefixWord ++ tailWord_5742901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742901).length < 2 ^ (prefixWord ++ tailWord_5742901).sum := by decide
  have hdescent : baseEnd_5742901 < baseStart_5742901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742928 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3]
def baseStart_5742928 : Nat := 118140960795 + 5742928 * 2 ^ 59
def prefixEnd_5742928 : Nat := 4983230072969 + 3 ^ 40 * 5742928 * 2
def baseEnd_5742928 : Nat := 2948882428164012001488761

theorem tailTrace_5742928 : CollatzResearch.WordTrace tailWord_5742928 prefixEnd_5742928 2948882428164012001488761 := by
  unfold tailWord_5742928
  simp only [CollatzResearch.WordTrace]
  refine ⟨104730896069180072430458719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139641194758906763240611625 104730896069180072430458719)
  ·
    refine ⟨157096344103770108645688079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104730896069180072430458719 157096344103770108645688079)
    ·
      refine ⟨235644516155655162968532119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157096344103770108645688079 235644516155655162968532119)
      ·
        refine ⟨353466774233482744452798179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235644516155655162968532119 353466774233482744452798179)
        ·
          refine ⟨530200161350224116679197269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353466774233482744452798179 530200161350224116679197269)
          ·
            refine ⟨6213283140822938867334343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 530200161350224116679197269 6213283140822938867334343)
            ·
              refine ⟨9319924711234408301001515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213283140822938867334343 9319924711234408301001515)
              ·
                refine ⟨13979887066851612451502273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319924711234408301001515 13979887066851612451502273)
                ·
                  refine ⟨10484915300138709338626705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13979887066851612451502273 10484915300138709338626705)
                  ·
                    refine ⟨7863686475104032003970029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10484915300138709338626705 7863686475104032003970029)
                    ·
                      refine ⟨2948882428164012001488761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7863686475104032003970029 2948882428164012001488761)
                      ·
                        rfl

theorem cell23_5742928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_5742928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742928 prefixEnd_5742928 := by exact prefixLift 5742928
  have htrace : WordTrace (prefixWord ++ tailWord_5742928) baseStart_5742928 baseEnd_5742928 := by
    simpa [prefixWord, tailWord_5742928, baseEnd_5742928] using wordTrace_append hprefix tailTrace_5742928
  have hstable : (prefixWord ++ tailWord_5742928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742928).length < 2 ^ (prefixWord ++ tailWord_5742928).sum := by decide
  have hdescent : baseEnd_5742928 < baseStart_5742928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5742981 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 8, 2]
def baseStart_5742981 : Nat := 118140960795 + 5742981 * 2 ^ 59
def prefixEnd_5742981 : Nat := 4983230072969 + 3 ^ 40 * 5742981 * 2
def baseEnd_5742981 : Nat := 2948909642638700294126017

theorem tailTrace_5742981 : CollatzResearch.WordTrace tailWord_5742981 prefixEnd_5742981 2948909642638700294126017 := by
  unfold tailWord_5742981
  simp only [CollatzResearch.WordTrace]
  refine ⟨209463725207168134912596797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139642483471445423275064531 209463725207168134912596797)
  ·
    refine ⟨78548896952688050592223799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209463725207168134912596797 78548896952688050592223799)
    ·
      refine ⟨117823345429032075888335699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78548896952688050592223799 117823345429032075888335699)
      ·
        refine ⟨176735018143548113832503549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117823345429032075888335699 176735018143548113832503549)
        ·
          refine ⟨66275631803830542687188831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176735018143548113832503549 66275631803830542687188831)
          ·
            refine ⟨99413447705745814030783247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66275631803830542687188831 99413447705745814030783247)
            ·
              refine ⟨149120171558618721046174871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99413447705745814030783247 149120171558618721046174871)
              ·
                refine ⟨223680257337928081569262307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149120171558618721046174871 223680257337928081569262307)
                ·
                  refine ⟨335520386006892122353893461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223680257337928081569262307 335520386006892122353893461)
                  ·
                    refine ⟨3931879523518267058834689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 335520386006892122353893461 3931879523518267058834689)
                    ·
                      refine ⟨2948909642638700294126017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931879523518267058834689 2948909642638700294126017)
                      ·
                        rfl

theorem cell23_5742981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_5742981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5742981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5742981 prefixEnd_5742981 := by exact prefixLift 5742981
  have htrace : WordTrace (prefixWord ++ tailWord_5742981) baseStart_5742981 baseEnd_5742981 := by
    simpa [prefixWord, tailWord_5742981, baseEnd_5742981] using wordTrace_append hprefix tailTrace_5742981
  have hstable : (prefixWord ++ tailWord_5742981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5742981).length < 2 ^ (prefixWord ++ tailWord_5742981).sum := by decide
  have hdescent : baseEnd_5742981 < baseStart_5742981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5742981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743001 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_5743001 : Nat := 118140960795 + 5743001 * 2 ^ 59
def prefixEnd_5743001 : Nat := 4983230072969 + 3 ^ 40 * 5743001 * 2
def baseEnd_5743001 : Nat := 2948919912251790215875925

theorem tailTrace_5743001 : CollatzResearch.WordTrace tailWord_5743001 prefixEnd_5743001 2948919912251790215875925 := by
  unfold tailWord_5743001
  simp only [CollatzResearch.WordTrace]
  refine ⟨209464454667095678328324857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139642969778063785552216571 209464454667095678328324857)
  ·
    refine ⟨157098341000321758746243643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209464454667095678328324857 157098341000321758746243643)
    ·
      refine ⟨235647511500482638119365465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157098341000321758746243643 235647511500482638119365465)
      ·
        refine ⟨176735633625361978589524099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235647511500482638119365465 176735633625361978589524099)
        ·
          refine ⟨265103450438042967884286149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176735633625361978589524099 265103450438042967884286149)
          ·
            refine ⟨49706896957133056478303653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265103450438042967884286149 49706896957133056478303653)
            ·
              refine ⟨9320043179462448089681935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49706896957133056478303653 9320043179462448089681935)
              ·
                refine ⟨13980064769193672134522903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9320043179462448089681935 13980064769193672134522903)
                ·
                  refine ⟨20970097153790508201784355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13980064769193672134522903 20970097153790508201784355)
                  ·
                    refine ⟨31455145730685762302676533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20970097153790508201784355 31455145730685762302676533)
                    ·
                      refine ⟨2948919912251790215875925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31455145730685762302676533 2948919912251790215875925)
                      ·
                        rfl

theorem cell23_5743001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_5743001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743001 prefixEnd_5743001 := by exact prefixLift 5743001
  have htrace : WordTrace (prefixWord ++ tailWord_5743001) baseStart_5743001 baseEnd_5743001 := by
    simpa [prefixWord, tailWord_5743001, baseEnd_5743001] using wordTrace_append hprefix tailTrace_5743001
  have hstable : (prefixWord ++ tailWord_5743001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743001).length < 2 ^ (prefixWord ++ tailWord_5743001).sum := by decide
  have hdescent : baseEnd_5743001 < baseStart_5743001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743009 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5743009 : Nat := 118140960795 + 5743009 * 2 ^ 59
def prefixEnd_5743009 : Nat := 4983230072969 + 3 ^ 40 * 5743009 * 2
def baseEnd_5743009 : Nat := 2948924020097026184575889

theorem tailTrace_5743009 : CollatzResearch.WordTrace tailWord_5743009 prefixEnd_5743009 2948924020097026184575889 := by
  unfold tailWord_5743009
  simp only [CollatzResearch.WordTrace]
  refine ⟨209464746451066695694616081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139643164300711130463077387 209464746451066695694616081)
  ·
    refine ⟨157098559838300021770962061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209464746451066695694616081 157098559838300021770962061)
    ·
      refine ⟨58911959939362508164110773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157098559838300021770962061 58911959939362508164110773)
      ·
        refine ⟨5522996244315235140385385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58911959939362508164110773 5522996244315235140385385)
        ·
          refine ⟨4142247183236426355289039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522996244315235140385385 4142247183236426355289039)
          ·
            refine ⟨6213370774854639532933559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142247183236426355289039 6213370774854639532933559)
            ·
              refine ⟨9320056162281959299400339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213370774854639532933559 9320056162281959299400339)
              ·
                refine ⟨13980084243422938949100509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9320056162281959299400339 13980084243422938949100509)
                ·
                  refine ⟨5242531591283602105912691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13980084243422938949100509 5242531591283602105912691)
                  ·
                    refine ⟨7863797386925403158869037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5242531591283602105912691 7863797386925403158869037)
                    ·
                      refine ⟨2948924020097026184575889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7863797386925403158869037 2948924020097026184575889)
                      ·
                        rfl

theorem cell23_5743009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5743009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743009 prefixEnd_5743009 := by exact prefixLift 5743009
  have htrace : WordTrace (prefixWord ++ tailWord_5743009) baseStart_5743009 baseEnd_5743009 := by
    simpa [prefixWord, tailWord_5743009, baseEnd_5743009] using wordTrace_append hprefix tailTrace_5743009
  have hstable : (prefixWord ++ tailWord_5743009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743009).length < 2 ^ (prefixWord ++ tailWord_5743009).sum := by decide
  have hdescent : baseEnd_5743009 < baseStart_5743009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743025 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 2, 4]
def baseStart_5743025 : Nat := 118140960795 + 5743025 * 2 ^ 59
def prefixEnd_5743025 : Nat := 4983230072969 + 3 ^ 40 * 5743025 * 2
def baseEnd_5743025 : Nat := 982977411929166040658605

theorem tailTrace_5743025 : CollatzResearch.WordTrace tailWord_5743025 prefixEnd_5743025 982977411929166040658605 := by
  unfold tailWord_5743025
  simp only [CollatzResearch.WordTrace]
  refine ⟨209465330019008730427198529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139643553346005820284799019 209465330019008730427198529)
  ·
    refine ⟨157098997514256547820398897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209465330019008730427198529 157098997514256547820398897)
    ·
      refine ⟨117824248135692410865299173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157098997514256547820398897 117824248135692410865299173)
      ·
        refine ⟨22092046525442327037243595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117824248135692410865299173 22092046525442327037243595)
        ·
          refine ⟨33138069788163490555865393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22092046525442327037243595 33138069788163490555865393)
          ·
            refine ⟨24853552341122617916899045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33138069788163490555865393 24853552341122617916899045)
            ·
              refine ⟨4660041063960490859418571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24853552341122617916899045 4660041063960490859418571)
              ·
                refine ⟨6990061595940736289127857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660041063960490859418571 6990061595940736289127857)
                ·
                  refine ⟨5242546196955552216845893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990061595940736289127857 5242546196955552216845893)
                  ·
                    refine ⟨982977411929166040658605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242546196955552216845893 982977411929166040658605)
                    ·
                      rfl

theorem cell23_5743025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_5743025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743025 prefixEnd_5743025 := by exact prefixLift 5743025
  have htrace : WordTrace (prefixWord ++ tailWord_5743025) baseStart_5743025 baseEnd_5743025 := by
    simpa [prefixWord, tailWord_5743025, baseEnd_5743025] using wordTrace_append hprefix tailTrace_5743025
  have hstable : (prefixWord ++ tailWord_5743025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743025).length < 2 ^ (prefixWord ++ tailWord_5743025).sum := by decide
  have hdescent : baseEnd_5743025 < baseStart_5743025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743048 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_5743048 : Nat := 118140960795 + 5743048 * 2 ^ 59
def prefixEnd_5743048 : Nat := 4983230072969 + 3 ^ 40 * 5743048 * 2
def baseEnd_5743048 : Nat := 2948944045842551531988209

theorem tailTrace_5743048 : CollatzResearch.WordTrace tailWord_5743048 prefixEnd_5743048 2948944045842551531988209 := by
  unfold tailWord_5743048
  simp only [CollatzResearch.WordTrace]
  refine ⟨104733084448962702677642899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139644112598616936903523865 104733084448962702677642899)
  ·
    refine ⟨157099626673444054016464349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104733084448962702677642899 157099626673444054016464349)
    ·
      refine ⟨58912360002541520256174131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157099626673444054016464349 58912360002541520256174131)
      ·
        refine ⟨88368540003812280384261197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58912360002541520256174131 88368540003812280384261197)
        ·
          refine ⟨33138202501429605144097949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88368540003812280384261197 33138202501429605144097949)
          ·
            refine ⟨12426825938036101929036731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33138202501429605144097949 12426825938036101929036731)
            ·
              refine ⟨18640238907054152893555097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12426825938036101929036731 18640238907054152893555097)
              ·
                refine ⟨13980179180290614670166323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18640238907054152893555097 13980179180290614670166323)
                ·
                  refine ⟨20970268770435922005249485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13980179180290614670166323 20970268770435922005249485)
                  ·
                    refine ⟨7863850788913470751968557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20970268770435922005249485 7863850788913470751968557)
                    ·
                      refine ⟨2948944045842551531988209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7863850788913470751968557 2948944045842551531988209)
                      ·
                        rfl

theorem cell23_5743048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_5743048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743048 prefixEnd_5743048 := by exact prefixLift 5743048
  have htrace : WordTrace (prefixWord ++ tailWord_5743048) baseStart_5743048 baseEnd_5743048 := by
    simpa [prefixWord, tailWord_5743048, baseEnd_5743048] using wordTrace_append hprefix tailTrace_5743048
  have hstable : (prefixWord ++ tailWord_5743048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743048).length < 2 ^ (prefixWord ++ tailWord_5743048).sum := by decide
  have hdescent : baseEnd_5743048 < baseStart_5743048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743052 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 1, 2, 3]
def baseStart_5743052 : Nat := 118140960795 + 5743052 * 2 ^ 59
def prefixEnd_5743052 : Nat := 4983230072969 + 3 ^ 40 * 5743052 * 2
def baseEnd_5743052 : Nat := 2948946099765169516338191

theorem tailTrace_5743052 : CollatzResearch.WordTrace tailWord_5743052 prefixEnd_5743052 2948946099765169516338191 := by
  unfold tailWord_5743052
  simp only [CollatzResearch.WordTrace]
  refine ⟨104733157394955457019215705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139644209859940609358954273 104733157394955457019215705)
  ·
    refine ⟨78549868046216592764411779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104733157394955457019215705 78549868046216592764411779)
    ·
      refine ⟨117824802069324889146617669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78549868046216592764411779 117824802069324889146617669)
      ·
        refine ⟨22092150387998416714990813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117824802069324889146617669 22092150387998416714990813)
        ·
          refine ⟨8284556395499406268121555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22092150387998416714990813 8284556395499406268121555)
          ·
            refine ⟨12426834593249109402182333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8284556395499406268121555 12426834593249109402182333)
            ·
              refine ⟨4660062972468416025818375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12426834593249109402182333 4660062972468416025818375)
              ·
                refine ⟨6990094458702624038727563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660062972468416025818375 6990094458702624038727563)
                ·
                  refine ⟨10485141688053936058091345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990094458702624038727563 10485141688053936058091345)
                  ·
                    refine ⟨7863856266040452043568509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10485141688053936058091345 7863856266040452043568509)
                    ·
                      refine ⟨2948946099765169516338191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7863856266040452043568509 2948946099765169516338191)
                      ·
                        rfl

theorem cell23_5743052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_5743052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743052 prefixEnd_5743052 := by exact prefixLift 5743052
  have htrace : WordTrace (prefixWord ++ tailWord_5743052) baseStart_5743052 baseEnd_5743052 := by
    simpa [prefixWord, tailWord_5743052, baseEnd_5743052] using wordTrace_append hprefix tailTrace_5743052
  have hstable : (prefixWord ++ tailWord_5743052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743052).length < 2 ^ (prefixWord ++ tailWord_5743052).sum := by decide
  have hdescent : baseEnd_5743052 < baseStart_5743052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743065 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 3]
def baseStart_5743065 : Nat := 118140960795 + 5743065 * 2 ^ 59
def prefixEnd_5743065 : Nat := 4983230072969 + 3 ^ 40 * 5743065 * 2
def baseEnd_5743065 : Nat := 2948952775013677965475631

theorem tailTrace_5743065 : CollatzResearch.WordTrace tailWord_5743065 prefixEnd_5743065 2948952775013677965475631 := by
  unfold tailWord_5743065
  simp only [CollatzResearch.WordTrace]
  refine ⟨209466788938863817258654649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139644525959242544839103099 209466788938863817258654649)
  ·
    refine ⟨157100091704147862943990987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209466788938863817258654649 157100091704147862943990987)
    ·
      refine ⟨235650137556221794415986481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157100091704147862943990987 235650137556221794415986481)
      ·
        refine ⟨176737603167166345811989861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235650137556221794415986481 176737603167166345811989861)
        ·
          refine ⟨33138300593843689839748099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176737603167166345811989861 33138300593843689839748099)
          ·
            refine ⟨49707450890765534759622149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33138300593843689839748099 49707450890765534759622149)
            ·
              refine ⟨9320147042018537767429153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49707450890765534759622149 9320147042018537767429153)
              ·
                refine ⟨6990110281513903325571865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9320147042018537767429153 6990110281513903325571865)
                ·
                  refine ⟨5242582711135427494178899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990110281513903325571865 5242582711135427494178899)
                  ·
                    refine ⟨7863874066703141241268349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5242582711135427494178899 7863874066703141241268349)
                    ·
                      refine ⟨2948952775013677965475631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7863874066703141241268349 2948952775013677965475631)
                      ·
                        rfl

theorem cell23_5743065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_5743065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743065 prefixEnd_5743065 := by exact prefixLift 5743065
  have htrace : WordTrace (prefixWord ++ tailWord_5743065) baseStart_5743065 baseEnd_5743065 := by
    simpa [prefixWord, tailWord_5743065, baseEnd_5743065] using wordTrace_append hprefix tailTrace_5743065
  have hstable : (prefixWord ++ tailWord_5743065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743065).length < 2 ^ (prefixWord ++ tailWord_5743065).sum := by decide
  have hdescent : baseEnd_5743065 < baseStart_5743065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743071 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_5743071 : Nat := 118140960795 + 5743071 * 2 ^ 59
def prefixEnd_5743071 : Nat := 4983230072969 + 3 ^ 40 * 5743071 * 2
def baseEnd_5743071 : Nat := 2948955855897604942000603

theorem tailTrace_5743071 : CollatzResearch.WordTrace tailWord_5743071 prefixEnd_5743071 2948955855897604942000603 := by
  unfold tailWord_5743071
  simp only [CollatzResearch.WordTrace]
  refine ⟨209467007776842080283373067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139644671851228053522248711 209467007776842080283373067)
  ·
    refine ⟨314200511665263120425059601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209467007776842080283373067 314200511665263120425059601)
    ·
      refine ⟨235650383748947340318794701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314200511665263120425059601 235650383748947340318794701)
      ·
        refine ⟨88368893905855252619548013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235650383748947340318794701 88368893905855252619548013)
        ·
          refine ⟨33138335214695719732330505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88368893905855252619548013 33138335214695719732330505)
          ·
            refine ⟨24853751411021789799247879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33138335214695719732330505 24853751411021789799247879)
            ·
              refine ⟨37280627116532684698871819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24853751411021789799247879 37280627116532684698871819)
              ·
                refine ⟨55920940674799027048307729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37280627116532684698871819 55920940674799027048307729)
                ·
                  refine ⟨41940705506099270286230797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55920940674799027048307729 41940705506099270286230797)
                  ·
                    refine ⟨15727764564787226357336549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41940705506099270286230797 15727764564787226357336549)
                    ·
                      refine ⟨2948955855897604942000603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15727764564787226357336549 2948955855897604942000603)
                      ·
                        rfl

theorem cell23_5743071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_5743071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743071 prefixEnd_5743071 := by exact prefixLift 5743071
  have htrace : WordTrace (prefixWord ++ tailWord_5743071) baseStart_5743071 baseEnd_5743071 := by
    simpa [prefixWord, tailWord_5743071, baseEnd_5743071] using wordTrace_append hprefix tailTrace_5743071
  have hstable : (prefixWord ++ tailWord_5743071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743071).length < 2 ^ (prefixWord ++ tailWord_5743071).sum := by decide
  have hdescent : baseEnd_5743071 < baseStart_5743071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743091 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 3]
def baseStart_5743091 : Nat := 118140960795 + 5743091 * 2 ^ 59
def prefixEnd_5743091 : Nat := 4983230072969 + 3 ^ 40 * 5743091 * 2
def baseEnd_5743091 : Nat := 2948966125510694863750511

theorem tailTrace_5743091 : CollatzResearch.WordTrace tailWord_5743091 prefixEnd_5743091 2948966125510694863750511 := by
  unfold tailWord_5743091
  simp only [CollatzResearch.WordTrace]
  refine ⟨209467737236769623699101127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139645158157846415799400751 209467737236769623699101127)
  ·
    refine ⟨314201605855154435548651691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209467737236769623699101127 314201605855154435548651691)
    ·
      refine ⟨471302408782731653322977537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314201605855154435548651691 471302408782731653322977537)
      ·
        refine ⟨353476806587048739992233153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471302408782731653322977537 353476806587048739992233153)
        ·
          refine ⟨265107604940286554994174865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353476806587048739992233153 265107604940286554994174865)
          ·
            refine ⟨198830703705214916245631149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265107604940286554994174865 198830703705214916245631149)
            ·
              refine ⟨74561513889455593592111681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198830703705214916245631149 74561513889455593592111681)
              ·
                refine ⟨55921135417091695194083761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74561513889455593592111681 55921135417091695194083761)
                ·
                  refine ⟨41940851562818771395562821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55921135417091695194083761 41940851562818771395562821)
                  ·
                    refine ⟨7863909668028519636668029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41940851562818771395562821 7863909668028519636668029)
                    ·
                      refine ⟨2948966125510694863750511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7863909668028519636668029 2948966125510694863750511)
                      ·
                        rfl

theorem cell23_5743091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_5743091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743091 prefixEnd_5743091 := by exact prefixLift 5743091
  have htrace : WordTrace (prefixWord ++ tailWord_5743091) baseStart_5743091 baseEnd_5743091 := by
    simpa [prefixWord, tailWord_5743091, baseEnd_5743091] using wordTrace_append hprefix tailTrace_5743091
  have hstable : (prefixWord ++ tailWord_5743091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743091).length < 2 ^ (prefixWord ++ tailWord_5743091).sum := by decide
  have hdescent : baseEnd_5743091 < baseStart_5743091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743101 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_5743101 : Nat := 118140960795 + 5743101 * 2 ^ 59
def prefixEnd_5743101 : Nat := 4983230072969 + 3 ^ 40 * 5743101 * 2
def baseEnd_5743101 : Nat := 2948971260317239824625465

theorem tailTrace_5743101 : CollatzResearch.WordTrace tailWord_5743101 prefixEnd_5743101 2948971260317239824625465 := by
  unfold tailWord_5743101
  simp only [CollatzResearch.WordTrace]
  refine ⟨209468101966733395406965157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139645401311155596937976771 209468101966733395406965157)
  ·
    refine ⟨39275269118762511638805967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209468101966733395406965157 39275269118762511638805967)
    ·
      refine ⟨58912903678143767458208951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39275269118762511638805967 58912903678143767458208951)
      ·
        refine ⟨88369355517215651187313427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58912903678143767458208951 88369355517215651187313427)
        ·
          refine ⟨132554033275823476780970141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88369355517215651187313427 132554033275823476780970141)
          ·
            refine ⟨49707762478433803792863803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132554033275823476780970141 49707762478433803792863803)
            ·
              refine ⟨74561643717650705689295705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49707762478433803792863803 74561643717650705689295705)
              ·
                refine ⟨55921232788238029266971779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74561643717650705689295705 55921232788238029266971779)
                ·
                  refine ⟨83881849182357043900457669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55921232788238029266971779 83881849182357043900457669)
                  ·
                    refine ⟨15727846721691945731335813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83881849182357043900457669 15727846721691945731335813)
                    ·
                      refine ⟨2948971260317239824625465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15727846721691945731335813 2948971260317239824625465)
                      ·
                        rfl

theorem cell23_5743101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_5743101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743101 prefixEnd_5743101 := by exact prefixLift 5743101
  have htrace : WordTrace (prefixWord ++ tailWord_5743101) baseStart_5743101 baseEnd_5743101 := by
    simpa [prefixWord, tailWord_5743101, baseEnd_5743101] using wordTrace_append hprefix tailTrace_5743101
  have hstable : (prefixWord ++ tailWord_5743101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743101).length < 2 ^ (prefixWord ++ tailWord_5743101).sum := by decide
  have hdescent : baseEnd_5743101 < baseStart_5743101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743105 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_5743105 : Nat := 118140960795 + 5743105 * 2 ^ 59
def prefixEnd_5743105 : Nat := 4983230072969 + 3 ^ 40 * 5743105 * 2
def baseEnd_5743105 : Nat := 2948973314239857808975447

theorem tailTrace_5743105 : CollatzResearch.WordTrace tailWord_5743105 prefixEnd_5743105 2948973314239857808975447 := by
  unfold tailWord_5743105
  simp only [CollatzResearch.WordTrace]
  refine ⟨209468247858718904090110769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139645498572479269393407179 209468247858718904090110769)
  ·
    refine ⟨157101185894039178067583077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209468247858718904090110769 157101185894039178067583077)
    ·
      refine ⟨29456472355132345887671827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157101185894039178067583077 29456472355132345887671827)
      ·
        refine ⟨44184708532698518831507741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29456472355132345887671827 44184708532698518831507741)
        ·
          refine ⟨16569265699761944561815403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44184708532698518831507741 16569265699761944561815403)
          ·
            refine ⟨24853898549642916842723105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16569265699761944561815403 24853898549642916842723105)
            ·
              refine ⟨18640423912232187632042329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24853898549642916842723105 18640423912232187632042329)
              ·
                refine ⟨13980317934174140724031747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18640423912232187632042329 13980317934174140724031747)
                ·
                  refine ⟨20970476901261211086047621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13980317934174140724031747 20970476901261211086047621)
                  ·
                    refine ⟨3931964418986477078633929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20970476901261211086047621 3931964418986477078633929)
                    ·
                      refine ⟨2948973314239857808975447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931964418986477078633929 2948973314239857808975447)
                      ·
                        rfl

theorem cell23_5743105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_5743105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743105 prefixEnd_5743105 := by exact prefixLift 5743105
  have htrace : WordTrace (prefixWord ++ tailWord_5743105) baseStart_5743105 baseEnd_5743105 := by
    simpa [prefixWord, tailWord_5743105, baseEnd_5743105] using wordTrace_append hprefix tailTrace_5743105
  have hstable : (prefixWord ++ tailWord_5743105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743105).length < 2 ^ (prefixWord ++ tailWord_5743105).sum := by decide
  have hdescent : baseEnd_5743105 < baseStart_5743105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743118 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5743118 : Nat := 118140960795 + 5743118 * 2 ^ 59
def prefixEnd_5743118 : Nat := 4983230072969 + 3 ^ 40 * 5743118 * 2
def baseEnd_5743118 : Nat := 2948979989488366258112887

theorem tailTrace_5743118 : CollatzResearch.WordTrace tailWord_5743118 prefixEnd_5743118 2948979989488366258112887 := by
  unfold tailWord_5743118
  simp only [CollatzResearch.WordTrace]
  refine ⟨26183590250958975913791751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139645814671781204873556005 26183590250958975913791751)
  ·
    refine ⟨39275385376438463870687627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26183590250958975913791751 39275385376438463870687627)
    ·
      refine ⟨58913078064657695806031441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39275385376438463870687627 58913078064657695806031441)
      ·
        refine ⟨44184808548493271854523581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58913078064657695806031441 44184808548493271854523581)
        ·
          refine ⟨16569303205684976945446343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44184808548493271854523581 16569303205684976945446343)
          ·
            refine ⟨24853954808527465418169515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16569303205684976945446343 24853954808527465418169515)
            ·
              refine ⟨37280932212791198127254273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24853954808527465418169515 37280932212791198127254273)
              ·
                refine ⟨27960699159593398595440705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37280932212791198127254273 27960699159593398595440705)
                ·
                  refine ⟨20970524369695048946580529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27960699159593398595440705 20970524369695048946580529)
                  ·
                    refine ⟨15727893277271286709935397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20970524369695048946580529 15727893277271286709935397)
                    ·
                      refine ⟨2948979989488366258112887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15727893277271286709935397 2948979989488366258112887)
                      ·
                        rfl

theorem cell23_5743118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5743118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743118 prefixEnd_5743118 := by exact prefixLift 5743118
  have htrace : WordTrace (prefixWord ++ tailWord_5743118) baseStart_5743118 baseEnd_5743118 := by
    simpa [prefixWord, tailWord_5743118, baseEnd_5743118] using wordTrace_append hprefix tailTrace_5743118
  have hstable : (prefixWord ++ tailWord_5743118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743118).length < 2 ^ (prefixWord ++ tailWord_5743118).sum := by decide
  have hdescent : baseEnd_5743118 < baseStart_5743118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743128 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 7]
def baseStart_5743128 : Nat := 118140960795 + 5743128 * 2 ^ 59
def prefixEnd_5743128 : Nat := 4983230072969 + 3 ^ 40 * 5743128 * 2
def baseEnd_5743128 : Nat := 327665013810545690998649

theorem tailTrace_5743128 : CollatzResearch.WordTrace tailWord_5743128 prefixEnd_5743128 327665013810545690998649 := by
  unfold tailWord_5743128
  simp only [CollatzResearch.WordTrace]
  refine ⟨104734543368817789509099019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139646057825090386012132025 104734543368817789509099019)
  ·
    refine ⟨157101815053226684263648529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104734543368817789509099019 157101815053226684263648529)
    ·
      refine ⟨117826361289920013197736397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157101815053226684263648529 117826361289920013197736397)
      ·
        refine ⟨44184885483720004949151149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117826361289920013197736397 44184885483720004949151149)
        ·
          refine ⟨16569332056395001855931681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44184885483720004949151149 16569332056395001855931681)
          ·
            refine ⟨12426999042296251391948761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16569332056395001855931681 12426999042296251391948761)
            ·
              refine ⟨9320249281722188543961571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12426999042296251391948761 9320249281722188543961571)
              ·
                refine ⟨13980373922583282815942357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9320249281722188543961571 13980373922583282815942357)
                ·
                  refine ⟨327665013810545690998649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13980373922583282815942357 327665013810545690998649)
                  ·
                    rfl

theorem cell23_5743128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 7].length) (baseStart_5743128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743128 prefixEnd_5743128 := by exact prefixLift 5743128
  have htrace : WordTrace (prefixWord ++ tailWord_5743128) baseStart_5743128 baseEnd_5743128 := by
    simpa [prefixWord, tailWord_5743128, baseEnd_5743128] using wordTrace_append hprefix tailTrace_5743128
  have hstable : (prefixWord ++ tailWord_5743128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743128).length < 2 ^ (prefixWord ++ tailWord_5743128).sum := by decide
  have hdescent : baseEnd_5743128 < baseStart_5743128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743139 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 2, 2, 2]
def baseStart_5743139 : Nat := 118140960795 + 5743139 * 2 ^ 59
def prefixEnd_5743139 : Nat := 4983230072969 + 3 ^ 40 * 5743139 * 2
def baseEnd_5743139 : Nat := 2948990772582110675950291

theorem tailTrace_5743139 : CollatzResearch.WordTrace tailWord_5743139 prefixEnd_5743139 2948990772582110675950291 := by
  unfold tailWord_5743139
  simp only [CollatzResearch.WordTrace]
  refine ⟨209469487940595727896848471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139646325293730485264565647 209469487940595727896848471)
  ·
    refine ⟨314204231910893591845272707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209469487940595727896848471 314204231910893591845272707)
    ·
      refine ⟨471306347866340387767909061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314204231910893591845272707 471306347866340387767909061)
      ·
        refine ⟨88369940224938822706482949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471306347866340387767909061 88369940224938822706482949)
        ·
          refine ⟨16569363792176029257465553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88369940224938822706482949 16569363792176029257465553)
          ·
            refine ⟨12427022844132021943099165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16569363792176029257465553 12427022844132021943099165)
            ·
              refine ⟨4660133566549508228662187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12427022844132021943099165 4660133566549508228662187)
              ·
                refine ⟨6990200349824262342993281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660133566549508228662187 6990200349824262342993281)
                ·
                  refine ⟨5242650262368196757244961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990200349824262342993281 5242650262368196757244961)
                  ·
                    refine ⟨3931987696776147567933721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5242650262368196757244961 3931987696776147567933721)
                    ·
                      refine ⟨2948990772582110675950291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931987696776147567933721 2948990772582110675950291)
                      ·
                        rfl

theorem cell23_5743139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_5743139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743139 prefixEnd_5743139 := by exact prefixLift 5743139
  have htrace : WordTrace (prefixWord ++ tailWord_5743139) baseStart_5743139 baseEnd_5743139 := by
    simpa [prefixWord, tailWord_5743139, baseEnd_5743139] using wordTrace_append hprefix tailTrace_5743139
  have hstable : (prefixWord ++ tailWord_5743139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743139).length < 2 ^ (prefixWord ++ tailWord_5743139).sum := by decide
  have hdescent : baseEnd_5743139 < baseStart_5743139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743141 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_5743141 : Nat := 118140960795 + 5743141 * 2 ^ 59
def prefixEnd_5743141 : Nat := 4983230072969 + 3 ^ 40 * 5743141 * 2
def baseEnd_5743141 : Nat := 982997266514473222708427

theorem tailTrace_5743141 : CollatzResearch.WordTrace tailWord_5743141 prefixEnd_5743141 982997266514473222708427 := by
  unfold tailWord_5743141
  simp only [CollatzResearch.WordTrace]
  refine ⟨209469560886588482238421277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139646373924392321492280851 209469560886588482238421277)
  ·
    refine ⟨78551085332470680839407979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209469560886588482238421277 78551085332470680839407979)
    ·
      refine ⟨117826627998706021259111969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78551085332470680839407979 117826627998706021259111969)
      ·
        refine ⟨88369970999029515944333977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117826627998706021259111969 88369970999029515944333977)
        ·
          refine ⟨66277478249272136958250483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88369970999029515944333977 66277478249272136958250483)
          ·
            refine ⟨99416217373908205437375725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66277478249272136958250483 99416217373908205437375725)
            ·
              refine ⟨37281081515215577039015897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99416217373908205437375725 37281081515215577039015897)
              ·
                refine ⟨27960811136411682779261923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37281081515215577039015897 27960811136411682779261923)
                ·
                  refine ⟨41941216704617524168892885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27960811136411682779261923 41941216704617524168892885)
                  ·
                    refine ⟨982997266514473222708427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41941216704617524168892885 982997266514473222708427)
                    ·
                      rfl

theorem cell23_5743141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_5743141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743141 prefixEnd_5743141 := by exact prefixLift 5743141
  have htrace : WordTrace (prefixWord ++ tailWord_5743141) baseStart_5743141 baseEnd_5743141 := by
    simpa [prefixWord, tailWord_5743141, baseEnd_5743141] using wordTrace_append hprefix tailTrace_5743141
  have hstable : (prefixWord ++ tailWord_5743141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743141).length < 2 ^ (prefixWord ++ tailWord_5743141).sum := by decide
  have hdescent : baseEnd_5743141 < baseStart_5743141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743148 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 2, 5, 2]
def baseStart_5743148 : Nat := 118140960795 + 5743148 * 2 ^ 59
def prefixEnd_5743148 : Nat := 4983230072969 + 3 ^ 40 * 5743148 * 2
def baseEnd_5743148 : Nat := 2948995393908001140737749

theorem tailTrace_5743148 : CollatzResearch.WordTrace tailWord_5743148 prefixEnd_5743148 2948995393908001140737749 := by
  unfold tailWord_5743148
  simp only [CollatzResearch.WordTrace]
  refine ⟨104734908098781561216963049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139646544131708748289284065 104734908098781561216963049)
  ·
    refine ⟨78551181074086170912722287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104734908098781561216963049 78551181074086170912722287)
    ·
      refine ⟨117826771611129256369083431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78551181074086170912722287 117826771611129256369083431)
      ·
        refine ⟨176740157416693884553625147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117826771611129256369083431 176740157416693884553625147)
        ·
          refine ⟨265110236125040826830437721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176740157416693884553625147 265110236125040826830437721)
          ·
            refine ⟨198832677093780620122828291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265110236125040826830437721 198832677093780620122828291)
            ·
              refine ⟨298249015640670930184242437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198832677093780620122828291 298249015640670930184242437)
              ·
                refine ⟨55921690432625799409545457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298249015640670930184242437 55921690432625799409545457)
                ·
                  refine ⟨41941267824469349557159093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55921690432625799409545457 41941267824469349557159093)
                  ·
                    refine ⟨3931993858544001520983665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41941267824469349557159093 3931993858544001520983665)
                    ·
                      refine ⟨2948995393908001140737749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931993858544001520983665 2948995393908001140737749)
                      ·
                        rfl

theorem cell23_5743148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_5743148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743148 prefixEnd_5743148 := by exact prefixLift 5743148
  have htrace : WordTrace (prefixWord ++ tailWord_5743148) baseStart_5743148 baseEnd_5743148 := by
    simpa [prefixWord, tailWord_5743148, baseEnd_5743148] using wordTrace_append hprefix tailTrace_5743148
  have hstable : (prefixWord ++ tailWord_5743148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743148).length < 2 ^ (prefixWord ++ tailWord_5743148).sum := by decide
  have hdescent : baseEnd_5743148 < baseStart_5743148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743178 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_5743178 : Nat := 118140960795 + 5743178 * 2 ^ 59
def prefixEnd_5743178 : Nat := 4983230072969 + 3 ^ 40 * 5743178 * 2
def baseEnd_5743178 : Nat := 2949010798327636023362611

theorem tailTrace_5743178 : CollatzResearch.WordTrace tailWord_5743178 prefixEnd_5743178 2949010798327636023362611 := by
  unfold tailWord_5743178
  simp only [CollatzResearch.WordTrace]
  refine ⟨52367727596863609389379547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139647273591636291705012125 52367727596863609389379547)
  ·
    refine ⟨78551591395295414084069321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52367727596863609389379547 78551591395295414084069321)
    ·
      refine ⟨58913693546471560563051991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78551591395295414084069321 58913693546471560563051991)
      ·
        refine ⟨88370540319707340844577987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58913693546471560563051991 88370540319707340844577987)
        ·
          refine ⟨132555810479561011266866981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88370540319707340844577987 132555810479561011266866981)
          ·
            refine ⟨24854214464917689612537559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132555810479561011266866981 24854214464917689612537559)
            ·
              refine ⟨37281321697376534418806339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24854214464917689612537559 37281321697376534418806339)
              ·
                refine ⟨55921982546064801628209509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37281321697376534418806339 55921982546064801628209509)
                ·
                  refine ⟨10485371727387150305289283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55921982546064801628209509 10485371727387150305289283)
                  ·
                    refine ⟨15728057591080725457933925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10485371727387150305289283 15728057591080725457933925)
                    ·
                      refine ⟨2949010798327636023362611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15728057591080725457933925 2949010798327636023362611)
                      ·
                        rfl

theorem cell23_5743178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_5743178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743178 prefixEnd_5743178 := by exact prefixLift 5743178
  have htrace : WordTrace (prefixWord ++ tailWord_5743178) baseStart_5743178 baseEnd_5743178 := by
    simpa [prefixWord, tailWord_5743178, baseEnd_5743178] using wordTrace_append hprefix tailTrace_5743178
  have hstable : (prefixWord ++ tailWord_5743178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743178).length < 2 ^ (prefixWord ++ tailWord_5743178).sum := by decide
  have hdescent : baseEnd_5743178 < baseStart_5743178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743255 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 1, 5, 2]
def baseStart_5743255 : Nat := 118140960795 + 5743255 * 2 ^ 59
def prefixEnd_5743255 : Nat := 4983230072969 + 3 ^ 40 * 5743255 * 2
def baseEnd_5743255 : Nat := 2949050336338032222099757

theorem tailTrace_5743255 : CollatzResearch.WordTrace tailWord_5743255 prefixEnd_5743255 2949050336338032222099757 := by
  unfold tailWord_5743255
  simp only [CollatzResearch.WordTrace]
  refine ⟨209473718808175479708071219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139649145872116986472047479 209473718808175479708071219)
  ·
    refine ⟨314210578212263219562106829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209473718808175479708071219 314210578212263219562106829)
    ·
      refine ⟨117828966829598707335790061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314210578212263219562106829 117828966829598707335790061)
      ·
        refine ⟨44185862561099515250921273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117828966829598707335790061 44185862561099515250921273)
        ·
          refine ⟨33139396920824636438190955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44185862561099515250921273 33139396920824636438190955)
          ·
            refine ⟨49709095381236954657286433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33139396920824636438190955 49709095381236954657286433)
            ·
              refine ⟨37281821535927715992964825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49709095381236954657286433 37281821535927715992964825)
              ·
                refine ⟨27961366151945786994723619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37281821535927715992964825 27961366151945786994723619)
                ·
                  refine ⟨41942049227918680492085429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27961366151945786994723619 41942049227918680492085429)
                  ·
                    refine ⟨3932067115117376296133009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41942049227918680492085429 3932067115117376296133009)
                    ·
                      refine ⟨2949050336338032222099757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932067115117376296133009 2949050336338032222099757)
                      ·
                        rfl

theorem cell23_5743255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_5743255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743255 prefixEnd_5743255 := by exact prefixLift 5743255
  have htrace : WordTrace (prefixWord ++ tailWord_5743255) baseStart_5743255 baseEnd_5743255 := by
    simpa [prefixWord, tailWord_5743255, baseEnd_5743255] using wordTrace_append hprefix tailTrace_5743255
  have hstable : (prefixWord ++ tailWord_5743255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743255).length < 2 ^ (prefixWord ++ tailWord_5743255).sum := by decide
  have hdescent : baseEnd_5743255 < baseStart_5743255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743279 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 1, 1, 3]
def baseStart_5743279 : Nat := 118140960795 + 5743279 * 2 ^ 59
def prefixEnd_5743279 : Nat := 4983230072969 + 3 ^ 40 * 5743279 * 2
def baseEnd_5743279 : Nat := 2949062659873740128199647

theorem tailTrace_5743279 : CollatzResearch.WordTrace tailWord_5743279 prefixEnd_5743279 2949062659873740128199647 := by
  unfold tailWord_5743279
  simp only [CollatzResearch.WordTrace]
  refine ⟨209474594160088531806944891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139649729440059021204629927 209474594160088531806944891)
  ·
    refine ⟨314211891240132797710417337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209474594160088531806944891 314211891240132797710417337)
    ·
      refine ⟨235658918430099598282813003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314211891240132797710417337 235658918430099598282813003)
      ·
        refine ⟨353488377645149397424219505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235658918430099598282813003 353488377645149397424219505)
        ·
          refine ⟨265116283233862048068164629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353488377645149397424219505 265116283233862048068164629)
          ·
            refine ⟨12427325776587283503195217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265116283233862048068164629 12427325776587283503195217)
            ·
              refine ⟨9320494332440462627396413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12427325776587283503195217 9320494332440462627396413)
              ·
                refine ⟨3495185374665173485273655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9320494332440462627396413 3495185374665173485273655)
                ·
                  refine ⟨5242778061997760227910483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3495185374665173485273655 5242778061997760227910483)
                  ·
                    refine ⟨7864167092996640341865725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5242778061997760227910483 7864167092996640341865725)
                    ·
                      refine ⟨2949062659873740128199647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864167092996640341865725 2949062659873740128199647)
                      ·
                        rfl

theorem cell23_5743279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 1, 3].length) (baseStart_5743279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743279 prefixEnd_5743279 := by exact prefixLift 5743279
  have htrace : WordTrace (prefixWord ++ tailWord_5743279) baseStart_5743279 baseEnd_5743279 := by
    simpa [prefixWord, tailWord_5743279, baseEnd_5743279] using wordTrace_append hprefix tailTrace_5743279
  have hstable : (prefixWord ++ tailWord_5743279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743279).length < 2 ^ (prefixWord ++ tailWord_5743279).sum := by decide
  have hdescent : baseEnd_5743279 < baseStart_5743279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743286 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_5743286 : Nat := 118140960795 + 5743286 * 2 ^ 59
def prefixEnd_5743286 : Nat := 4983230072969 + 3 ^ 40 * 5743286 * 2
def baseEnd_5743286 : Nat := 327674028248702400090235

theorem tailTrace_5743286 : CollatzResearch.WordTrace tailWord_5743286 prefixEnd_5743286 327674028248702400090235 := by
  unfold tailWord_5743286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092178091941448250153107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139649899647375448001633141 13092178091941448250153107)
  ·
    refine ⟨19638267137912172375229661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13092178091941448250153107 19638267137912172375229661)
    ·
      refine ⟨7364350176717064640711123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19638267137912172375229661 7364350176717064640711123)
      ·
        refine ⟨11046525265075596961066685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364350176717064640711123 11046525265075596961066685)
        ·
          refine ⟨4142446974403348860400007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11046525265075596961066685 4142446974403348860400007)
          ·
            refine ⟨6213670461605023290600011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142446974403348860400007 6213670461605023290600011)
            ·
              refine ⟨9320505692407534935900017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6213670461605023290600011 9320505692407534935900017)
              ·
                refine ⟨6990379269305651201925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9320505692407534935900017 6990379269305651201925013)
                ·
                  refine ⟨327674028248702400090235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6990379269305651201925013 327674028248702400090235)
                  ·
                    rfl

theorem cell23_5743286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_5743286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743286 prefixEnd_5743286 := by exact prefixLift 5743286
  have htrace : WordTrace (prefixWord ++ tailWord_5743286) baseStart_5743286 baseEnd_5743286 := by
    simpa [prefixWord, tailWord_5743286, baseEnd_5743286] using wordTrace_append hprefix tailTrace_5743286
  have hstable : (prefixWord ++ tailWord_5743286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743286).length < 2 ^ (prefixWord ++ tailWord_5743286).sum := by decide
  have hdescent : baseEnd_5743286 < baseStart_5743286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743295 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 4, 4]
def baseStart_5743295 : Nat := 118140960795 + 5743295 * 2 ^ 59
def prefixEnd_5743295 : Nat := 4983230072969 + 3 ^ 40 * 5743295 * 2
def baseEnd_5743295 : Nat := 983023625188070688533191

theorem tailTrace_5743295 : CollatzResearch.WordTrace tailWord_5743295 prefixEnd_5743295 983023625188070688533191 := by
  unfold tailWord_5743295
  simp only [CollatzResearch.WordTrace]
  refine ⟨209475177728030566539527339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139650118485353711026351559 209475177728030566539527339)
  ·
    refine ⟨314212766592045849809291009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209475177728030566539527339 314212766592045849809291009)
    ·
      refine ⟨235659574944034387356968257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314212766592045849809291009 235659574944034387356968257)
      ·
        refine ⟨176744681208025790517726193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235659574944034387356968257 176744681208025790517726193)
        ·
          refine ⟨132558510906019342888294645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176744681208025790517726193 132558510906019342888294645)
          ·
            refine ⟨12427360397439313395777623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132558510906019342888294645 12427360397439313395777623)
            ·
              refine ⟨18641040596158970093666435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12427360397439313395777623 18641040596158970093666435)
              ·
                refine ⟨27961560894238455140499653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18641040596158970093666435 27961560894238455140499653)
                ·
                  refine ⟨5242792667669710338843685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27961560894238455140499653 5242792667669710338843685)
                  ·
                    refine ⟨983023625188070688533191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242792667669710338843685 983023625188070688533191)
                    ·
                      rfl

theorem cell23_5743295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_5743295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743295 prefixEnd_5743295 := by exact prefixLift 5743295
  have htrace : WordTrace (prefixWord ++ tailWord_5743295) baseStart_5743295 baseEnd_5743295 := by
    simpa [prefixWord, tailWord_5743295, baseEnd_5743295] using wordTrace_append hprefix tailTrace_5743295
  have hstable : (prefixWord ++ tailWord_5743295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743295).length < 2 ^ (prefixWord ++ tailWord_5743295).sum := by decide
  have hdescent : baseEnd_5743295 < baseStart_5743295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743322 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_5743322 : Nat := 118140960795 + 5743322 * 2 ^ 59
def prefixEnd_5743322 : Nat := 4983230072969 + 3 ^ 40 * 5743322 * 2
def baseEnd_5743322 : Nat := 2949084739541883459961949

theorem tailTrace_5743322 : CollatzResearch.WordTrace tailWord_5743322 prefixEnd_5743322 2949084739541883459961949 := by
  unfold tailWord_5743322
  simp only [CollatzResearch.WordTrace]
  refine ⟨52369040624733187537690055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139650774999288500100506813 52369040624733187537690055)
  ·
    refine ⟨78553560937099781306535083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52369040624733187537690055 78553560937099781306535083)
    ·
      refine ⟨117830341405649671959802625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78553560937099781306535083 117830341405649671959802625)
      ·
        refine ⟨88372756054237253969851969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117830341405649671959802625 88372756054237253969851969)
        ·
          refine ⟨66279567040677940477388977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88372756054237253969851969 66279567040677940477388977)
          ·
            refine ⟨49709675280508455358041733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66279567040677940477388977 49709675280508455358041733)
            ·
              refine ⟨9320564115095335379632825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49709675280508455358041733 9320564115095335379632825)
              ·
                refine ⟨6990423086321501534724619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9320564115095335379632825 6990423086321501534724619)
                ·
                  refine ⟨10485634629482252302086929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990423086321501534724619 10485634629482252302086929)
                  ·
                    refine ⟨7864225972111689226565197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10485634629482252302086929 7864225972111689226565197)
                    ·
                      refine ⟨2949084739541883459961949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864225972111689226565197 2949084739541883459961949)
                      ·
                        rfl

theorem cell23_5743322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_5743322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743322 prefixEnd_5743322 := by exact prefixLift 5743322
  have htrace : WordTrace (prefixWord ++ tailWord_5743322) baseStart_5743322 baseEnd_5743322 := by
    simpa [prefixWord, tailWord_5743322, baseEnd_5743322] using wordTrace_append hprefix tailTrace_5743322
  have hstable : (prefixWord ++ tailWord_5743322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743322).length < 2 ^ (prefixWord ++ tailWord_5743322).sum := by decide
  have hdescent : baseEnd_5743322 < baseStart_5743322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743338 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_5743338 : Nat := 118140960795 + 5743338 * 2 ^ 59
def prefixEnd_5743338 : Nat := 4983230072969 + 3 ^ 40 * 5743338 * 2
def baseEnd_5743338 : Nat := 983030985077451799120625

theorem tailTrace_5743338 : CollatzResearch.WordTrace tailWord_5743338 prefixEnd_5743338 983030985077451799120625 := by
  unfold tailWord_5743338
  simp only [CollatzResearch.WordTrace]
  refine ⟨52369186516718696220835667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139651164044583189922228445 52369186516718696220835667)
  ·
    refine ⟨78553779775078044331253501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52369186516718696220835667 78553779775078044331253501)
    ·
      refine ⟨29457667415654266624220063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78553779775078044331253501 29457667415654266624220063)
      ·
        refine ⟨44186501123481399936330095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29457667415654266624220063 44186501123481399936330095)
        ·
          refine ⟨66279751685222099904495143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44186501123481399936330095 66279751685222099904495143)
          ·
            refine ⟨99419627527833149856742715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66279751685222099904495143 99419627527833149856742715)
            ·
              refine ⟨149129441291749724785114073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99419627527833149856742715 149129441291749724785114073)
              ·
                refine ⟨111847080968812293588835555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149129441291749724785114073 111847080968812293588835555)
                ·
                  refine ⟨167770621453218440383253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111847080968812293588835555 167770621453218440383253333)
                  ·
                    refine ⟨983030985077451799120625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 167770621453218440383253333 983030985077451799120625)
                    ·
                      rfl

theorem cell23_5743338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_5743338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743338 prefixEnd_5743338 := by exact prefixLift 5743338
  have htrace : WordTrace (prefixWord ++ tailWord_5743338) baseStart_5743338 baseEnd_5743338 := by
    simpa [prefixWord, tailWord_5743338, baseEnd_5743338] using wordTrace_append hprefix tailTrace_5743338
  have hstable : (prefixWord ++ tailWord_5743338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743338).length < 2 ^ (prefixWord ++ tailWord_5743338).sum := by decide
  have hdescent : baseEnd_5743338 < baseStart_5743338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743352 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_5743352 : Nat := 118140960795 + 5743352 * 2 ^ 59
def prefixEnd_5743352 : Nat := 4983230072969 + 3 ^ 40 * 5743352 * 2
def baseEnd_5743352 : Nat := 2949100143961518342586811

theorem tailTrace_5743352 : CollatzResearch.WordTrace tailWord_5743352 prefixEnd_5743352 2949100143961518342586811 := by
  unfold tailWord_5743352
  simp only [CollatzResearch.WordTrace]
  refine ⟨104738628344412032637176155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139651504459216043516234873 104738628344412032637176155)
  ·
    refine ⟨157107942516618048955764233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104738628344412032637176155 157107942516618048955764233)
    ·
      refine ⟨117830956887463536716823175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157107942516618048955764233 117830956887463536716823175)
      ·
        refine ⟨176746435331195305075234763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117830956887463536716823175 176746435331195305075234763)
        ·
          refine ⟨265119652996792957612852145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176746435331195305075234763 265119652996792957612852145)
          ·
            refine ⟨198839739747594718209639109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265119652996792957612852145 198839739747594718209639109)
            ·
              refine ⟨37282451202674009664307333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198839739747594718209639109 37282451202674009664307333)
              ·
                refine ⟨6990459600501376812057625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37282451202674009664307333 6990459600501376812057625)
                ·
                  refine ⟨5242844700376032609043219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990459600501376812057625 5242844700376032609043219)
                  ·
                    refine ⟨7864267050564048913564829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5242844700376032609043219 7864267050564048913564829)
                    ·
                      refine ⟨2949100143961518342586811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864267050564048913564829 2949100143961518342586811)
                      ·
                        rfl

theorem cell23_5743352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_5743352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743352 prefixEnd_5743352 := by exact prefixLift 5743352
  have htrace : WordTrace (prefixWord ++ tailWord_5743352) baseStart_5743352 baseEnd_5743352 := by
    simpa [prefixWord, tailWord_5743352, baseEnd_5743352] using wordTrace_append hprefix tailTrace_5743352
  have hstable : (prefixWord ++ tailWord_5743352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743352).length < 2 ^ (prefixWord ++ tailWord_5743352).sum := by decide
  have hdescent : baseEnd_5743352 < baseStart_5743352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743369 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 2, 1, 3]
def baseStart_5743369 : Nat := 118140960795 + 5743369 * 2 ^ 59
def prefixEnd_5743369 : Nat := 4983230072969 + 3 ^ 40 * 5743369 * 2
def baseEnd_5743369 : Nat := 2949108873132644776074233

theorem tailTrace_5743369 : CollatzResearch.WordTrace tailWord_5743369 prefixEnd_5743369 2949108873132644776074233 := by
  unfold tailWord_5743369
  simp only [CollatzResearch.WordTrace]
  refine ⟨209477876729762477177721161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139651917819841651451814107 209477876729762477177721161)
  ·
    refine ⟨157108407547321857883290871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209477876729762477177721161 157108407547321857883290871)
    ·
      refine ⟨235662611320982786824936307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157108407547321857883290871 235662611320982786824936307)
      ·
        refine ⟨353493916981474180237404461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235662611320982786824936307 353493916981474180237404461)
        ·
          refine ⟨132560218868052817589026673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353493916981474180237404461 132560218868052817589026673)
          ·
            refine ⟨99420164151039613191770005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132560218868052817589026673 99420164151039613191770005)
            ·
              refine ⟨4660320194579981868364219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99420164151039613191770005 4660320194579981868364219)
              ·
                refine ⟨6990480291869972802546329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660320194579981868364219 6990480291869972802546329)
                ·
                  refine ⟨5242860218902479601909747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990480291869972802546329 5242860218902479601909747)
                  ·
                    refine ⟨7864290328353719402864621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5242860218902479601909747 7864290328353719402864621)
                    ·
                      refine ⟨2949108873132644776074233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864290328353719402864621 2949108873132644776074233)
                      ·
                        rfl

theorem cell23_5743369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 1, 3].length) (baseStart_5743369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743369 prefixEnd_5743369 := by exact prefixLift 5743369
  have htrace : WordTrace (prefixWord ++ tailWord_5743369) baseStart_5743369 baseEnd_5743369 := by
    simpa [prefixWord, tailWord_5743369, baseEnd_5743369] using wordTrace_append hprefix tailTrace_5743369
  have hstable : (prefixWord ++ tailWord_5743369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743369).length < 2 ^ (prefixWord ++ tailWord_5743369).sum := by decide
  have hdescent : baseEnd_5743369 < baseStart_5743369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743392 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 3, 4, 2]
def baseStart_5743392 : Nat := 118140960795 + 5743392 * 2 ^ 59
def prefixEnd_5743392 : Nat := 4983230072969 + 3 ^ 40 * 5743392 * 2
def baseEnd_5743392 : Nat := 2949120683187698186086627

theorem tailTrace_5743392 : CollatzResearch.WordTrace tailWord_5743392 prefixEnd_5743392 2949120683187698186086627 := by
  unfold tailWord_5743392
  simp only [CollatzResearch.WordTrace]
  refine ⟨104739357804339576052904215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139652477072452768070538953 104739357804339576052904215)
  ·
    refine ⟨157109036706509364079356323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104739357804339576052904215 157109036706509364079356323)
    ·
      refine ⟨235663555059764046119034485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157109036706509364079356323 235663555059764046119034485)
      ·
        refine ⟨22093458286852879323659483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235663555059764046119034485 22093458286852879323659483)
        ·
          refine ⟨33140187430279318985489225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22093458286852879323659483 33140187430279318985489225)
          ·
            refine ⟨24855140572709489239116919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33140187430279318985489225 24855140572709489239116919)
            ·
              refine ⟨37282710859064233858675379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24855140572709489239116919 37282710859064233858675379)
              ·
                refine ⟨55924066288596350788013069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37282710859064233858675379 55924066288596350788013069)
                ·
                  refine ⟨20971524858223631545504901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55924066288596350788013069 20971524858223631545504901)
                  ·
                    refine ⟨3932160910916930914782169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20971524858223631545504901 3932160910916930914782169)
                    ·
                      refine ⟨2949120683187698186086627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932160910916930914782169 2949120683187698186086627)
                      ·
                        rfl

theorem cell23_5743392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_5743392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743392 prefixEnd_5743392 := by exact prefixLift 5743392
  have htrace : WordTrace (prefixWord ++ tailWord_5743392) baseStart_5743392 baseEnd_5743392 := by
    simpa [prefixWord, tailWord_5743392, baseEnd_5743392] using wordTrace_append hprefix tailTrace_5743392
  have hstable : (prefixWord ++ tailWord_5743392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743392).length < 2 ^ (prefixWord ++ tailWord_5743392).sum := by decide
  have hdescent : baseEnd_5743392 < baseStart_5743392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743408 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_5743408 : Nat := 118140960795 + 5743408 * 2 ^ 59
def prefixEnd_5743408 : Nat := 4983230072969 + 3 ^ 40 * 5743408 * 2
def baseEnd_5743408 : Nat := 2949128898878170123486553

theorem tailTrace_5743408 : CollatzResearch.WordTrace tailWord_5743408 prefixEnd_5743408 2949128898878170123486553 := by
  unfold tailWord_5743408
  simp only [CollatzResearch.WordTrace]
  refine ⟨104739649588310593419195439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139652866117747457892260585 104739649588310593419195439)
  ·
    refine ⟨157109474382465890128793159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104739649588310593419195439 157109474382465890128793159)
    ·
      refine ⟨235664211573698835193189739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157109474382465890128793159 235664211573698835193189739)
      ·
        refine ⟨353496317360548252789784609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235664211573698835193189739 353496317360548252789784609)
        ·
          refine ⟨265122238020411189592338457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353496317360548252789784609 265122238020411189592338457)
          ·
            refine ⟨198841678515308392194253843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265122238020411189592338457 198841678515308392194253843)
            ·
              refine ⟨298262517772962588291380765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198841678515308392194253843 298262517772962588291380765)
              ·
                refine ⟨111848444164860970609267787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298262517772962588291380765 111848444164860970609267787)
                ·
                  refine ⟨167772666247291455913901681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111848444164860970609267787 167772666247291455913901681)
                  ·
                    refine ⟨125829499685468591935426261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167772666247291455913901681 125829499685468591935426261)
                    ·
                      refine ⟨2949128898878170123486553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125829499685468591935426261 2949128898878170123486553)
                      ·
                        rfl

theorem cell23_5743408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_5743408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743408 prefixEnd_5743408 := by exact prefixLift 5743408
  have htrace : WordTrace (prefixWord ++ tailWord_5743408) baseStart_5743408 baseEnd_5743408 := by
    simpa [prefixWord, tailWord_5743408, baseEnd_5743408] using wordTrace_append hprefix tailTrace_5743408
  have hstable : (prefixWord ++ tailWord_5743408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743408).length < 2 ^ (prefixWord ++ tailWord_5743408).sum := by decide
  have hdescent : baseEnd_5743408 < baseStart_5743408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743445 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_5743445 : Nat := 118140960795 + 5743445 * 2 ^ 59
def prefixEnd_5743445 : Nat := 4983230072969 + 3 ^ 40 * 5743445 * 2
def baseEnd_5743445 : Nat := 983049299220795492907961

theorem tailTrace_5743445 : CollatzResearch.WordTrace tailWord_5743445 prefixEnd_5743445 983049299220795492907961 := by
  unfold tailWord_5743445
  simp only [CollatzResearch.WordTrace]
  refine ⟨209480648677487142157487789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139653765784991428104991859 209480648677487142157487789)
  ·
    refine ⟨78555243254057678309057921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209480648677487142157487789 78555243254057678309057921)
    ·
      refine ⟨58916432440543258731793441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78555243254057678309057921 58916432440543258731793441)
      ·
        refine ⟨44187324330407444048845081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58916432440543258731793441 44187324330407444048845081)
        ·
          refine ⟨33140493247805583036633811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44187324330407444048845081 33140493247805583036633811)
          ·
            refine ⟨49710739871708374554950717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33140493247805583036633811 49710739871708374554950717)
            ·
              refine ⟨18641527451890640458106519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49710739871708374554950717 18641527451890640458106519)
              ·
                refine ⟨27962291177835960687159779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18641527451890640458106519 27962291177835960687159779)
                ·
                  refine ⟨41943436766753941030739669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27962291177835960687159779 41943436766753941030739669)
                  ·
                    refine ⟨983049299220795492907961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41943436766753941030739669 983049299220795492907961)
                    ·
                      rfl

theorem cell23_5743445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_5743445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743445 prefixEnd_5743445 := by exact prefixLift 5743445
  have htrace : WordTrace (prefixWord ++ tailWord_5743445) baseStart_5743445 baseEnd_5743445 := by
    simpa [prefixWord, tailWord_5743445, baseEnd_5743445] using wordTrace_append hprefix tailTrace_5743445
  have hstable : (prefixWord ++ tailWord_5743445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743445).length < 2 ^ (prefixWord ++ tailWord_5743445).sum := by decide
  have hdescent : baseEnd_5743445 < baseStart_5743445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743519 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_5743519 : Nat := 118140960795 + 5743519 * 2 ^ 59
def prefixEnd_5743519 : Nat := 4983230072969 + 3 ^ 40 * 5743519 * 2
def baseEnd_5743519 : Nat := 2949185895230819189198543

theorem tailTrace_5743519 : CollatzResearch.WordTrace tailWord_5743519 prefixEnd_5743519 2949185895230819189198543 := by
  unfold tailWord_5743519
  simp only [CollatzResearch.WordTrace]
  refine ⟨209483347679219052795681611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139655565119479368530454407 209483347679219052795681611)
  ·
    refine ⟨314225021518828579193522417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209483347679219052795681611 314225021518828579193522417)
    ·
      refine ⟨235668766139121434395141813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314225021518828579193522417 235668766139121434395141813)
      ·
        refine ⟨22093946825542634474544545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235668766139121434395141813 22093946825542634474544545)
        ·
          refine ⟨16570460119156975855908409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22093946825542634474544545 16570460119156975855908409)
          ·
            refine ⟨12427845089367731891931307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16570460119156975855908409 12427845089367731891931307)
            ·
              refine ⟨18641767634051597837896961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12427845089367731891931307 18641767634051597837896961)
              ·
                refine ⟨13981325725538698378422721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18641767634051597837896961 13981325725538698378422721)
                ·
                  refine ⟨10485994294154023783817041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13981325725538698378422721 10485994294154023783817041)
                  ·
                    refine ⟨7864495720615517837862781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10485994294154023783817041 7864495720615517837862781)
                    ·
                      refine ⟨2949185895230819189198543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864495720615517837862781 2949185895230819189198543)
                      ·
                        rfl

theorem cell23_5743519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_5743519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743519 prefixEnd_5743519 := by exact prefixLift 5743519
  have htrace : WordTrace (prefixWord ++ tailWord_5743519) baseStart_5743519 baseEnd_5743519 := by
    simpa [prefixWord, tailWord_5743519, baseEnd_5743519] using wordTrace_append hprefix tailTrace_5743519
  have hstable : (prefixWord ++ tailWord_5743519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743519).length < 2 ^ (prefixWord ++ tailWord_5743519).sum := by decide
  have hdescent : baseEnd_5743519 < baseStart_5743519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743522 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_5743522 : Nat := 118140960795 + 5743522 * 2 ^ 59
def prefixEnd_5743522 : Nat := 4983230072969 + 3 ^ 40 * 5743522 * 2
def baseEnd_5743522 : Nat := 327687492852531408606781

theorem tailTrace_5743522 : CollatzResearch.WordTrace tailWord_5743522 prefixEnd_5743522 327687492852531408606781 := by
  unfold tailWord_5743522
  simp only [CollatzResearch.WordTrace]
  refine ⟨52370864274552046077010205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139655638065472122872027213 52370864274552046077010205)
  ·
    refine ⟨19639074102957017278878827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52370864274552046077010205 19639074102957017278878827)
    ·
      refine ⟨29458611154435525918318241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19639074102957017278878827 29458611154435525918318241)
      ·
        refine ⟨22093958365826644438738681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29458611154435525918318241 22093958365826644438738681)
        ·
          refine ⟨16570468774369983329054011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22093958365826644438738681 16570468774369983329054011)
          ·
            refine ⟨24855703161554974993581017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16570468774369983329054011 24855703161554974993581017)
            ·
              refine ⟨18641777371166231245185763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24855703161554974993581017 18641777371166231245185763)
              ·
                refine ⟨27962666056749346867778645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18641777371166231245185763 27962666056749346867778645)
                ·
                  refine ⟨327687492852531408606781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27962666056749346867778645 327687492852531408606781)
                  ·
                    rfl

theorem cell23_5743522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_5743522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743522 prefixEnd_5743522 := by exact prefixLift 5743522
  have htrace : WordTrace (prefixWord ++ tailWord_5743522) baseStart_5743522 baseEnd_5743522 := by
    simpa [prefixWord, tailWord_5743522, baseEnd_5743522] using wordTrace_append hprefix tailTrace_5743522
  have hstable : (prefixWord ++ tailWord_5743522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743522).length < 2 ^ (prefixWord ++ tailWord_5743522).sum := by decide
  have hdescent : baseEnd_5743522 < baseStart_5743522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743552 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_5743552 : Nat := 118140960795 + 5743552 * 2 ^ 59
def prefixEnd_5743552 : Nat := 4983230072969 + 3 ^ 40 * 5743552 * 2
def baseEnd_5743552 : Nat := 983067613364139186695297

theorem tailTrace_5743552 : CollatzResearch.WordTrace tailWord_5743552 prefixEnd_5743552 983067613364139186695297 := by
  unfold tailWord_5743552
  simp only [CollatzResearch.WordTrace]
  refine ⟨104742275644049749715816455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139656367525399666287755273 104742275644049749715816455)
  ·
    refine ⟨157113413466074624573724683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104742275644049749715816455 157113413466074624573724683)
    ·
      refine ⟨235670120199111936860587025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157113413466074624573724683 235670120199111936860587025)
      ·
        refine ⟨176752590149333952645440269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235670120199111936860587025 176752590149333952645440269)
        ·
          refine ⟨66282221306000232242040101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176752590149333952645440269 66282221306000232242040101)
          ·
            refine ⟨12427916494875043545382519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66282221306000232242040101 12427916494875043545382519)
            ·
              refine ⟨18641874742312565318073779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12427916494875043545382519 18641874742312565318073779)
              ·
                refine ⟨27962812113468847977110669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18641874742312565318073779 27962812113468847977110669)
                ·
                  refine ⟨10486054542550817991416501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27962812113468847977110669 10486054542550817991416501)
                  ·
                    refine ⟨983067613364139186695297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486054542550817991416501 983067613364139186695297)
                    ·
                      rfl

theorem cell23_5743552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_5743552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743552 prefixEnd_5743552 := by exact prefixLift 5743552
  have htrace : WordTrace (prefixWord ++ tailWord_5743552) baseStart_5743552 baseEnd_5743552 := by
    simpa [prefixWord, tailWord_5743552, baseEnd_5743552] using wordTrace_append hprefix tailTrace_5743552
  have hstable : (prefixWord ++ tailWord_5743552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743552).length < 2 ^ (prefixWord ++ tailWord_5743552).sum := by decide
  have hdescent : baseEnd_5743552 < baseStart_5743552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743555 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4]
def baseStart_5743555 : Nat := 118140960795 + 5743555 * 2 ^ 59
def prefixEnd_5743555 : Nat := 4983230072969 + 3 ^ 40 * 5743555 * 2
def baseEnd_5743555 : Nat := 2949204380534381048348377

theorem tailTrace_5743555 : CollatzResearch.WordTrace tailWord_5743555 prefixEnd_5743555 2949204380534381048348377 := by
  unfold tailWord_5743555
  simp only [CollatzResearch.WordTrace]
  refine ⟨209484660707088630943992119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139656440471392420629328079 209484660707088630943992119)
  ·
    refine ⟨314226991060632946415988179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209484660707088630943992119 314226991060632946415988179)
    ·
      refine ⟨471340486590949419623982269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314226991060632946415988179 471340486590949419623982269)
      ·
        refine ⟨176752682471606032358993351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471340486590949419623982269 176752682471606032358993351)
        ·
          refine ⟨265129023707409048538490027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176752682471606032358993351 265129023707409048538490027)
          ·
            refine ⟨397693535561113572807735041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265129023707409048538490027 397693535561113572807735041)
            ·
              refine ⟨298270151670835179605801281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397693535561113572807735041 298270151670835179605801281)
              ·
                refine ⟨223702613753126384704350961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298270151670835179605801281 223702613753126384704350961)
                ·
                  refine ⟨167776960314844788528263221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223702613753126384704350961 167776960314844788528263221)
                  ·
                    refine ⟨15729090029516698924524677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 167776960314844788528263221 15729090029516698924524677)
                    ·
                      refine ⟨2949204380534381048348377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15729090029516698924524677 2949204380534381048348377)
                      ·
                        rfl

theorem cell23_5743555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_5743555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743555 prefixEnd_5743555 := by exact prefixLift 5743555
  have htrace : WordTrace (prefixWord ++ tailWord_5743555) baseStart_5743555 baseEnd_5743555 := by
    simpa [prefixWord, tailWord_5743555, baseEnd_5743555] using wordTrace_append hprefix tailTrace_5743555
  have hstable : (prefixWord ++ tailWord_5743555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743555).length < 2 ^ (prefixWord ++ tailWord_5743555).sum := by decide
  have hdescent : baseEnd_5743555 < baseStart_5743555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743559 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_5743559 : Nat := 118140960795 + 5743559 * 2 ^ 59
def prefixEnd_5743559 : Nat := 4983230072969 + 3 ^ 40 * 5743559 * 2
def baseEnd_5743559 : Nat := 2949206434456999032698359

theorem tailTrace_5743559 : CollatzResearch.WordTrace tailWord_5743559 prefixEnd_5743559 2949206434456999032698359 := by
  unfold tailWord_5743559
  simp only [CollatzResearch.WordTrace]
  refine ⟨209484806599074139627137731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139656537732716093084758487 209484806599074139627137731)
  ·
    refine ⟨314227209898611209440706597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209484806599074139627137731 314227209898611209440706597)
    ·
      refine ⟨58917601855989601770132487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314227209898611209440706597 58917601855989601770132487)
      ·
        refine ⟨88376402783984402655198731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58917601855989601770132487 88376402783984402655198731)
        ·
          refine ⟨132564604175976603982798097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88376402783984402655198731 132564604175976603982798097)
          ·
            refine ⟨99423453131982452987098573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132564604175976603982798097 99423453131982452987098573)
            ·
              refine ⟨37283794924493419870161965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99423453131982452987098573 37283794924493419870161965)
              ·
                refine ⟨13981423096685032451310737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37283794924493419870161965 13981423096685032451310737)
                ·
                  refine ⟨10486067322513774338483053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13981423096685032451310737 10486067322513774338483053)
                  ·
                    refine ⟨3932275245942665376931145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10486067322513774338483053 3932275245942665376931145)
                    ·
                      refine ⟨2949206434456999032698359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932275245942665376931145 2949206434456999032698359)
                      ·
                        rfl

theorem cell23_5743559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_5743559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743559 prefixEnd_5743559 := by exact prefixLift 5743559
  have htrace : WordTrace (prefixWord ++ tailWord_5743559) baseStart_5743559 baseEnd_5743559 := by
    simpa [prefixWord, tailWord_5743559, baseEnd_5743559] using wordTrace_append hprefix tailTrace_5743559
  have hstable : (prefixWord ++ tailWord_5743559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743559).length < 2 ^ (prefixWord ++ tailWord_5743559).sum := by decide
  have hdescent : baseEnd_5743559 < baseStart_5743559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743569 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 1, 5]
def baseStart_5743569 : Nat := 118140960795 + 5743569 * 2 ^ 59
def prefixEnd_5743569 : Nat := 4983230072969 + 3 ^ 40 * 5743569 * 2
def baseEnd_5743569 : Nat := 983070523087847997857771

theorem tailTrace_5743569 : CollatzResearch.WordTrace tailWord_5743569 prefixEnd_5743569 983070523087847997857771 := by
  unfold tailWord_5743569
  simp only [CollatzResearch.WordTrace]
  refine ⟨209485171329037911335001761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139656780886025274223334507 209485171329037911335001761)
  ·
    refine ⟨157113878496778433501251321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209485171329037911335001761 157113878496778433501251321)
    ·
      refine ⟨117835408872583825125938491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157113878496778433501251321 117835408872583825125938491)
      ·
        refine ⟨176753113308875737688907737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117835408872583825125938491 176753113308875737688907737)
        ·
          refine ⟨132564834981656803266680803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176753113308875737688907737 132564834981656803266680803)
          ·
            refine ⟨198847252472485204900021205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132564834981656803266680803 198847252472485204900021205)
            ·
              refine ⟨4660482479823871989844247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198847252472485204900021205 4660482479823871989844247)
              ·
                refine ⟨6990723719735807984766371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660482479823871989844247 6990723719735807984766371)
                ·
                  refine ⟨10486085579603711977149557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990723719735807984766371 10486085579603711977149557)
                  ·
                    refine ⟨983070523087847997857771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486085579603711977149557 983070523087847997857771)
                    ·
                      rfl

theorem cell23_5743569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_5743569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743569 prefixEnd_5743569 := by exact prefixLift 5743569
  have htrace : WordTrace (prefixWord ++ tailWord_5743569) baseStart_5743569 baseEnd_5743569 := by
    simpa [prefixWord, tailWord_5743569, baseEnd_5743569] using wordTrace_append hprefix tailTrace_5743569
  have hstable : (prefixWord ++ tailWord_5743569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743569).length < 2 ^ (prefixWord ++ tailWord_5743569).sum := by decide
  have hdescent : baseEnd_5743569 < baseStart_5743569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743583 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 1, 1, 3]
def baseStart_5743583 : Nat := 118140960795 + 5743583 * 2 ^ 59
def prefixEnd_5743583 : Nat := 4983230072969 + 3 ^ 40 * 5743583 * 2
def baseEnd_5743583 : Nat := 2949218757992706938798249

theorem tailTrace_5743583 : CollatzResearch.WordTrace tailWord_5743583 prefixEnd_5743583 2949218757992706938798249 := by
  unfold tailWord_5743583
  simp only [CollatzResearch.WordTrace]
  refine ⟨209485681950987191726011403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139657121300658127817340935 209485681950987191726011403)
  ·
    refine ⟨314228522926480787589017105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209485681950987191726011403 314228522926480787589017105)
    ·
      refine ⟨235671392194860590691762829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314228522926480787589017105 235671392194860590691762829)
      ·
        refine ⟨88376772073072721509411061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235671392194860590691762829 88376772073072721509411061)
        ·
          refine ⟨8285322381850567641507287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88376772073072721509411061 8285322381850567641507287)
          ·
            refine ⟨12427983572775851462260931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8285322381850567641507287 12427983572775851462260931)
            ·
              refine ⟨18641975359163777193391397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12427983572775851462260931 18641975359163777193391397)
              ·
                refine ⟨3495370379843208223760887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18641975359163777193391397 3495370379843208223760887)
                ·
                  refine ⟨5243055569764812335641331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3495370379843208223760887 5243055569764812335641331)
                  ·
                    refine ⟨7864583354647218503461997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243055569764812335641331 7864583354647218503461997)
                    ·
                      refine ⟨2949218757992706938798249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864583354647218503461997 2949218757992706938798249)
                      ·
                        rfl

theorem cell23_5743583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_5743583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743583 prefixEnd_5743583 := by exact prefixLift 5743583
  have htrace : WordTrace (prefixWord ++ tailWord_5743583) baseStart_5743583 baseEnd_5743583 := by
    simpa [prefixWord, tailWord_5743583, baseEnd_5743583] using wordTrace_append hprefix tailTrace_5743583
  have hstable : (prefixWord ++ tailWord_5743583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743583).length < 2 ^ (prefixWord ++ tailWord_5743583).sum := by decide
  have hdescent : baseEnd_5743583 < baseStart_5743583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743592 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5743592 : Nat := 118140960795 + 5743592 * 2 ^ 59
def prefixEnd_5743592 : Nat := 4983230072969 + 3 ^ 40 * 5743592 * 2
def baseEnd_5743592 : Nat := 2949223379318597403585707

theorem tailTrace_5743592 : CollatzResearch.WordTrace tailWord_5743592 prefixEnd_5743592 2949223379318597403585707 := by
  unfold tailWord_5743592
  simp only [CollatzResearch.WordTrace]
  refine ⟨104743005103977293131544515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139657340138636390842059353 104743005103977293131544515)
  ·
    refine ⟨157114507655965939697316773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104743005103977293131544515 157114507655965939697316773)
    ·
      refine ⟨29458970185493613693246895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157114507655965939697316773 29458970185493613693246895)
      ·
        refine ⟨44188455278240420539870343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29458970185493613693246895 44188455278240420539870343)
        ·
          refine ⟨66282682917360630809805515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44188455278240420539870343 66282682917360630809805515)
          ·
            refine ⟨99424024376040946214708273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66282682917360630809805515 99424024376040946214708273)
            ·
              refine ⟨74568018282030709661031205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99424024376040946214708273 74568018282030709661031205)
              ·
                refine ⟨13981503427880758061443351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74568018282030709661031205 13981503427880758061443351)
                ·
                  refine ⟨20972255141821137092165027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13981503427880758061443351 20972255141821137092165027)
                  ·
                    refine ⟨31458382712731705638247541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20972255141821137092165027 31458382712731705638247541)
                    ·
                      refine ⟨2949223379318597403585707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31458382712731705638247541 2949223379318597403585707)
                      ·
                        rfl

theorem cell23_5743592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5743592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743592 prefixEnd_5743592 := by exact prefixLift 5743592
  have htrace : WordTrace (prefixWord ++ tailWord_5743592) baseStart_5743592 baseEnd_5743592 := by
    simpa [prefixWord, tailWord_5743592, baseEnd_5743592] using wordTrace_append hprefix tailTrace_5743592
  have hstable : (prefixWord ++ tailWord_5743592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743592).length < 2 ^ (prefixWord ++ tailWord_5743592).sum := by decide
  have hdescent : baseEnd_5743592 < baseStart_5743592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743599 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 2, 4]
def baseStart_5743599 : Nat := 118140960795 + 5743599 * 2 ^ 59
def prefixEnd_5743599 : Nat := 4983230072969 + 3 ^ 40 * 5743599 * 2
def baseEnd_5743599 : Nat := 983075657894392958732725

theorem tailTrace_5743599 : CollatzResearch.WordTrace tailWord_5743599 prefixEnd_5743599 983075657894392958732725 := by
  unfold tailWord_5743599
  simp only [CollatzResearch.WordTrace]
  refine ⟨209486265518929226458593851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139657510345952817639062567 209486265518929226458593851)
  ·
    refine ⟨314229398278393839687890777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209486265518929226458593851 314229398278393839687890777)
    ·
      refine ⟨235672048708795379765918083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314229398278393839687890777 235672048708795379765918083)
      ·
        refine ⟨353508073063193069648877125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235672048708795379765918083 353508073063193069648877125)
        ·
          refine ⟨66282763699348700559164461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353508073063193069648877125 66282763699348700559164461)
          ·
            refine ⟨24856036387255762709686673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66282763699348700559164461 24856036387255762709686673)
            ·
              refine ⟨18642027290441822032265005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24856036387255762709686673 18642027290441822032265005)
              ·
                refine ⟨6990760233915683262099377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18642027290441822032265005 6990760233915683262099377)
                ·
                  refine ⟨5243070175436762446574533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6990760233915683262099377 5243070175436762446574533)
                  ·
                    refine ⟨983075657894392958732725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243070175436762446574533 983075657894392958732725)
                    ·
                      rfl

theorem cell23_5743599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_5743599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743599 prefixEnd_5743599 := by exact prefixLift 5743599
  have htrace : WordTrace (prefixWord ++ tailWord_5743599) baseStart_5743599 baseEnd_5743599 := by
    simpa [prefixWord, tailWord_5743599, baseEnd_5743599] using wordTrace_append hprefix tailTrace_5743599
  have hstable : (prefixWord ++ tailWord_5743599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743599).length < 2 ^ (prefixWord ++ tailWord_5743599).sum := by decide
  have hdescent : baseEnd_5743599 < baseStart_5743599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743604 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5743604 : Nat := 118140960795 + 5743604 * 2 ^ 59
def prefixEnd_5743604 : Nat := 4983230072969 + 3 ^ 40 * 5743604 * 2
def baseEnd_5743604 : Nat := 2949229541086451356635653

theorem tailTrace_5743604 : CollatzResearch.WordTrace tailWord_5743604 prefixEnd_5743604 2949229541086451356635653 := by
  unfold tailWord_5743604
  simp only [CollatzResearch.WordTrace]
  refine ⟨104743223941955556156262933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139657631922607408208350577 104743223941955556156262933)
  ·
    refine ⟨4909838622279166694824825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104743223941955556156262933 4909838622279166694824825)
    ·
      refine ⟨3682378966709375021118619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4909838622279166694824825 3682378966709375021118619)
      ·
        refine ⟨5523568450064062531677929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682378966709375021118619 5523568450064062531677929)
        ·
          refine ⟨4142676337548046898758447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5523568450064062531677929 4142676337548046898758447)
          ·
            refine ⟨6214014506322070348137671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142676337548046898758447 6214014506322070348137671)
            ·
              refine ⟨9321021759483105522206507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214014506322070348137671 9321021759483105522206507)
              ·
                refine ⟨13981532639224658283309761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321021759483105522206507 13981532639224658283309761)
                ·
                  refine ⟨10486149479418493712482321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13981532639224658283309761 10486149479418493712482321)
                  ·
                    refine ⟨7864612109563870284361741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10486149479418493712482321 7864612109563870284361741)
                    ·
                      refine ⟨2949229541086451356635653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864612109563870284361741 2949229541086451356635653)
                      ·
                        rfl

theorem cell23_5743604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5743604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743604 prefixEnd_5743604 := by exact prefixLift 5743604
  have htrace : WordTrace (prefixWord ++ tailWord_5743604) baseStart_5743604 baseEnd_5743604 := by
    simpa [prefixWord, tailWord_5743604, baseEnd_5743604] using wordTrace_append hprefix tailTrace_5743604
  have hstable : (prefixWord ++ tailWord_5743604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743604).length < 2 ^ (prefixWord ++ tailWord_5743604).sum := by decide
  have hdescent : baseEnd_5743604 < baseStart_5743604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743609 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 3]
def baseStart_5743609 : Nat := 118140960795 + 5743609 * 2 ^ 59
def prefixEnd_5743609 : Nat := 4983230072969 + 3 ^ 40 * 5743609 * 2
def baseEnd_5743609 : Nat := 2949232108489723837073129

theorem tailTrace_5743609 : CollatzResearch.WordTrace tailWord_5743609 prefixEnd_5743609 2949232108489723837073129 := by
  unfold tailWord_5743609
  simp only [CollatzResearch.WordTrace]
  refine ⟨209486630248892998166457881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139657753499261998777638587 209486630248892998166457881)
  ·
    refine ⟨157114972686669748624843411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209486630248892998166457881 157114972686669748624843411)
    ·
      refine ⟨235672459030004622937265117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157114972686669748624843411 235672459030004622937265117)
      ·
        refine ⟨88377172136251733601474419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235672459030004622937265117 88377172136251733601474419)
        ·
          refine ⟨132565758204377600402211629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88377172136251733601474419 132565758204377600402211629)
          ·
            refine ⟨49712159326641600150829361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132565758204377600402211629 49712159326641600150829361)
            ·
              refine ⟨37284119494981200113122021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49712159326641600150829361 37284119494981200113122021)
              ·
                refine ⟨6990772405308975021210379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37284119494981200113122021 6990772405308975021210379)
                ·
                  refine ⟨10486158607963462531815569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990772405308975021210379 10486158607963462531815569)
                  ·
                    refine ⟨7864618955972596898861677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10486158607963462531815569 7864618955972596898861677)
                    ·
                      refine ⟨2949232108489723837073129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864618955972596898861677 2949232108489723837073129)
                      ·
                        rfl

theorem cell23_5743609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_5743609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743609 prefixEnd_5743609 := by exact prefixLift 5743609
  have htrace : WordTrace (prefixWord ++ tailWord_5743609) baseStart_5743609 baseEnd_5743609 := by
    simpa [prefixWord, tailWord_5743609, baseEnd_5743609] using wordTrace_append hprefix tailTrace_5743609
  have hstable : (prefixWord ++ tailWord_5743609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743609).length < 2 ^ (prefixWord ++ tailWord_5743609).sum := by decide
  have hdescent : baseEnd_5743609 < baseStart_5743609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743626 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_5743626 : Nat := 118140960795 + 5743626 * 2 ^ 59
def prefixEnd_5743626 : Nat := 4983230072969 + 3 ^ 40 * 5743626 * 2
def baseEnd_5743626 : Nat := 2949240837660850270560551

theorem tailTrace_5743626 : CollatzResearch.WordTrace tailWord_5743626 prefixEnd_5743626 2949240837660850270560551 := by
  unfold tailWord_5743626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52371812572457852517456683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139658166859887606713217821 52371812572457852517456683)
  ·
    refine ⟨78557718858686778776185025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52371812572457852517456683 78557718858686778776185025)
    ·
      refine ⟨58918289144015084082138769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78557718858686778776185025 58918289144015084082138769)
      ·
        refine ⟨44188716858011313061604077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58918289144015084082138769 44188716858011313061604077)
        ·
          refine ⟨16570768821754242398101529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44188716858011313061604077 16570768821754242398101529)
          ·
            refine ⟨12428076616315681798576147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16570768821754242398101529 12428076616315681798576147)
            ·
              refine ⟨18642114924473522697864221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12428076616315681798576147 18642114924473522697864221)
              ·
                refine ⟨6990793096677571011699083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18642114924473522697864221 6990793096677571011699083)
                ·
                  refine ⟨10486189645016356517548625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990793096677571011699083 10486189645016356517548625)
                  ·
                    refine ⟨7864642233762267388161469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10486189645016356517548625 7864642233762267388161469)
                    ·
                      refine ⟨2949240837660850270560551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864642233762267388161469 2949240837660850270560551)
                      ·
                        rfl

theorem cell23_5743626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_5743626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743626 prefixEnd_5743626 := by exact prefixLift 5743626
  have htrace : WordTrace (prefixWord ++ tailWord_5743626) baseStart_5743626 baseEnd_5743626 := by
    simpa [prefixWord, tailWord_5743626, baseEnd_5743626] using wordTrace_append hprefix tailTrace_5743626
  have hstable : (prefixWord ++ tailWord_5743626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743626).length < 2 ^ (prefixWord ++ tailWord_5743626).sum := by decide
  have hdescent : baseEnd_5743626 < baseStart_5743626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743679 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 3, 4, 2]
def baseStart_5743679 : Nat := 118140960795 + 5743679 * 2 ^ 59
def prefixEnd_5743679 : Nat := 4983230072969 + 3 ^ 40 * 5743679 * 2
def baseEnd_5743679 : Nat := 2949268052135538563197807

theorem tailTrace_5743679 : CollatzResearch.WordTrace tailWord_5743679 prefixEnd_5743679 2949268052135538563197807 := by
  unfold tailWord_5743679
  simp only [CollatzResearch.WordTrace]
  refine ⟨209489183358639400121506091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139659455572426266747670727 209489183358639400121506091)
  ·
    refine ⟨314233775037959100182259137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209489183358639400121506091 314233775037959100182259137)
    ·
      refine ⟨235675331278469325136694353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314233775037959100182259137 235675331278469325136694353)
      ·
        refine ⟨176756498458851993852520765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235675331278469325136694353 176756498458851993852520765)
        ·
          refine ⟨66283686922069497694695287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176756498458851993852520765 66283686922069497694695287)
          ·
            refine ⟨99425530383104246542042931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66283686922069497694695287 99425530383104246542042931)
            ·
              refine ⟨149138295574656369813064397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99425530383104246542042931 149138295574656369813064397)
              ·
                refine ⟨55926860840496138679899149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149138295574656369813064397 55926860840496138679899149)
                ·
                  refine ⟨20972572815186052004962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55926860840496138679899149 20972572815186052004962181)
                  ·
                    refine ⟨3932357402847384750930409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20972572815186052004962181 3932357402847384750930409)
                    ·
                      refine ⟨2949268052135538563197807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932357402847384750930409 2949268052135538563197807)
                      ·
                        rfl

theorem cell23_5743679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_5743679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743679 prefixEnd_5743679 := by exact prefixLift 5743679
  have htrace : WordTrace (prefixWord ++ tailWord_5743679) baseStart_5743679 baseEnd_5743679 := by
    simpa [prefixWord, tailWord_5743679, baseEnd_5743679] using wordTrace_append hprefix tailTrace_5743679
  have hstable : (prefixWord ++ tailWord_5743679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743679).length < 2 ^ (prefixWord ++ tailWord_5743679).sum := by decide
  have hdescent : baseEnd_5743679 < baseStart_5743679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743739 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 4, 5, 2]
def baseStart_5743739 : Nat := 118140960795 + 5743739 * 2 ^ 59
def prefixEnd_5743739 : Nat := 4983230072969 + 3 ^ 40 * 5743739 * 2
def baseEnd_5743739 : Nat := 2949298860974808328447531

theorem tailTrace_5743739 : CollatzResearch.WordTrace tailWord_5743739 prefixEnd_5743739 2949298860974808328447531 := by
  unfold tailWord_5743739
  simp only [CollatzResearch.WordTrace]
  refine ⟨209491371738422030368690271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139660914492281353579126847 209491371738422030368690271)
  ·
    refine ⟨314237057607633045553035407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209491371738422030368690271 314237057607633045553035407)
    ·
      refine ⟨471355586411449568329553111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314237057607633045553035407 471355586411449568329553111)
      ·
        refine ⟨707033379617174352494329667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471355586411449568329553111 707033379617174352494329667)
        ·
          refine ⟨1060550069425761528741494501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707033379617174352494329667 1060550069425761528741494501)
          ·
            refine ⟨198853138017330286639030219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1060550069425761528741494501 198853138017330286639030219)
            ·
              refine ⟨298279707025995429958545329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198853138017330286639030219 298279707025995429958545329)
              ·
                refine ⟨223709780269496572468908997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298279707025995429958545329 223709780269496572468908997)
                ·
                  refine ⟨41945583800530607337920437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223709780269496572468908997 41945583800530607337920437)
                  ·
                    refine ⟨3932398481299744437930041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41945583800530607337920437 3932398481299744437930041)
                    ·
                      refine ⟨2949298860974808328447531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932398481299744437930041 2949298860974808328447531)
                      ·
                        rfl

theorem cell23_5743739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5, 2].length) (baseStart_5743739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743739 prefixEnd_5743739 := by exact prefixLift 5743739
  have htrace : WordTrace (prefixWord ++ tailWord_5743739) baseStart_5743739 baseEnd_5743739 := by
    simpa [prefixWord, tailWord_5743739, baseEnd_5743739] using wordTrace_append hprefix tailTrace_5743739
  have hstable : (prefixWord ++ tailWord_5743739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743739).length < 2 ^ (prefixWord ++ tailWord_5743739).sum := by decide
  have hdescent : baseEnd_5743739 < baseStart_5743739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743753 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 5]
def baseStart_5743753 : Nat := 118140960795 + 5743753 * 2 ^ 59
def prefixEnd_5743753 : Nat := 4983230072969 + 3 ^ 40 * 5743753 * 2
def baseEnd_5743753 : Nat := 327700672189330141519163

theorem tailTrace_5743753 : CollatzResearch.WordTrace tailWord_5743753 prefixEnd_5743753 327700672189330141519163 := by
  unfold tailWord_5743753
  simp only [CollatzResearch.WordTrace]
  refine ⟨209491882360371310759699913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139661254906914207173133275 209491882360371310759699913)
  ·
    refine ⟨157118911770278483069774935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209491882360371310759699913 157118911770278483069774935)
    ·
      refine ⟨235678367655417724604662403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157118911770278483069774935 235678367655417724604662403)
      ·
        refine ⟨353517551483126586906993605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235678367655417724604662403 353517551483126586906993605)
        ·
          refine ⟨66284540903086235045061301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353517551483126586906993605 66284540903086235045061301)
          ·
            refine ⟨6214175709664334535474497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66284540903086235045061301 6214175709664334535474497)
            ·
              refine ⟨4660631782248250901605873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6214175709664334535474497 4660631782248250901605873)
              ·
                refine ⟨3495473836686188176204405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4660631782248250901605873 3495473836686188176204405)
                ·
                  refine ⟨327700672189330141519163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3495473836686188176204405 327700672189330141519163)
                  ·
                    rfl

theorem cell23_5743753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 5].length) (baseStart_5743753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743753 prefixEnd_5743753 := by exact prefixLift 5743753
  have htrace : WordTrace (prefixWord ++ tailWord_5743753) baseStart_5743753 baseEnd_5743753 := by
    simpa [prefixWord, tailWord_5743753, baseEnd_5743753] using wordTrace_append hprefix tailTrace_5743753
  have hstable : (prefixWord ++ tailWord_5743753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743753).length < 2 ^ (prefixWord ++ tailWord_5743753).sum := by decide
  have hdescent : baseEnd_5743753 < baseStart_5743753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743783 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 2, 5]
def baseStart_5743783 : Nat := 118140960795 + 5743783 * 2 ^ 59
def prefixEnd_5743783 : Nat := 4983230072969 + 3 ^ 40 * 5743783 * 2
def baseEnd_5743783 : Nat := 983107151374535385432443

theorem tailTrace_5743783 : CollatzResearch.WordTrace tailWord_5743783 prefixEnd_5743783 983107151374535385432443 := by
  unfold tailWord_5743783
  simp only [CollatzResearch.WordTrace]
  refine ⟨209492976550262625883292003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139661984366841750588861335 209492976550262625883292003)
  ·
    refine ⟨314239464825393938824938005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209492976550262625883292003 314239464825393938824938005)
    ·
      refine ⟨14729974913690340882418969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 314239464825393938824938005 14729974913690340882418969)
      ·
        refine ⟨11047481185267755661814227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14729974913690340882418969 11047481185267755661814227)
        ·
          refine ⟨16571221777901633492721341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11047481185267755661814227 16571221777901633492721341)
          ·
            refine ⟨6214208166713112559770503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16571221777901633492721341 6214208166713112559770503)
            ·
              refine ⟨9321312250069668839655755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214208166713112559770503 9321312250069668839655755)
              ·
                refine ⟨13981968375104503259483633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321312250069668839655755 13981968375104503259483633)
                ·
                  refine ⟨10486476281328377444612725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13981968375104503259483633 10486476281328377444612725)
                  ·
                    refine ⟨983107151374535385432443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486476281328377444612725 983107151374535385432443)
                    ·
                      rfl

theorem cell23_5743783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_5743783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743783 prefixEnd_5743783 := by exact prefixLift 5743783
  have htrace : WordTrace (prefixWord ++ tailWord_5743783) baseStart_5743783 baseEnd_5743783 := by
    simpa [prefixWord, tailWord_5743783, baseEnd_5743783] using wordTrace_append hprefix tailTrace_5743783
  have hstable : (prefixWord ++ tailWord_5743783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743783).length < 2 ^ (prefixWord ++ tailWord_5743783).sum := by decide
  have hdescent : baseEnd_5743783 < baseStart_5743783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743792 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 10]
def baseStart_5743792 : Nat := 118140960795 + 5743792 * 2 ^ 59
def prefixEnd_5743792 : Nat := 4983230072969 + 3 ^ 40 * 5743792 * 2
def baseEnd_5743792 : Nat := 327702897272166291231643

theorem tailTrace_5743792 : CollatzResearch.WordTrace tailWord_5743792 prefixEnd_5743792 327702897272166291231643 := by
  unfold tailWord_5743792
  simp only [CollatzResearch.WordTrace]
  refine ⟨104746652403615010210184815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139662203204820013613579753 104746652403615010210184815)
  ·
    refine ⟨157119978605422515315277223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104746652403615010210184815 157119978605422515315277223)
    ·
      refine ⟨235679967908133772972915835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157119978605422515315277223 235679967908133772972915835)
      ·
        refine ⟨353519951862200659459373753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235679967908133772972915835 353519951862200659459373753)
        ·
          refine ⟨265139963896650494594530315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353519951862200659459373753 265139963896650494594530315)
          ·
            refine ⟨397709945844975741891795473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265139963896650494594530315 397709945844975741891795473)
            ·
              refine ⟨298282459383731806418846605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397709945844975741891795473 298282459383731806418846605)
              ·
                refine ⟨111855922268899427407067477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298282459383731806418846605 111855922268899427407067477)
                ·
                  refine ⟨327702897272166291231643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111855922268899427407067477 327702897272166291231643)
                  ·
                    rfl

theorem cell23_5743792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_5743792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743792 prefixEnd_5743792 := by exact prefixLift 5743792
  have htrace : WordTrace (prefixWord ++ tailWord_5743792) baseStart_5743792 baseEnd_5743792 := by
    simpa [prefixWord, tailWord_5743792, baseEnd_5743792] using wordTrace_append hprefix tailTrace_5743792
  have hstable : (prefixWord ++ tailWord_5743792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743792).length < 2 ^ (prefixWord ++ tailWord_5743792).sum := by decide
  have hdescent : baseEnd_5743792 < baseStart_5743792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743839 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 3, 5]
def baseStart_5743839 : Nat := 118140960795 + 5743839 * 2 ^ 59
def prefixEnd_5743839 : Nat := 4983230072969 + 3 ^ 40 * 5743839 * 2
def baseEnd_5743839 : Nat := 983116736346752645732357

theorem tailTrace_5743839 : CollatzResearch.WordTrace tailWord_5743839 prefixEnd_5743839 983116736346752645732357 := by
  unfold tailWord_5743839
  simp only [CollatzResearch.WordTrace]
  refine ⟨209495019038059747447330571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139663346025373164964887047 209495019038059747447330571)
  ·
    refine ⟨314242528557089621170995857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209495019038059747447330571 314242528557089621170995857)
    ·
      refine ⟨235681896417817215878246893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314242528557089621170995857 235681896417817215878246893)
      ·
        refine ⟨88380711156681455954342585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235681896417817215878246893 88380711156681455954342585)
        ·
          refine ⟨66285533367511091965756939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88380711156681455954342585 66285533367511091965756939)
          ·
            refine ⟨99428300051266637948635409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66285533367511091965756939 99428300051266637948635409)
            ·
              refine ⟨74571225038449978461476557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99428300051266637948635409 74571225038449978461476557)
              ·
                refine ⟨27964209389418741923053709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74571225038449978461476557 27964209389418741923053709)
                ·
                  refine ⟨10486578521032028221145141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27964209389418741923053709 10486578521032028221145141)
                  ·
                    refine ⟨983116736346752645732357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486578521032028221145141 983116736346752645732357)
                    ·
                      rfl

theorem cell23_5743839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_5743839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743839 prefixEnd_5743839 := by exact prefixLift 5743839
  have htrace : WordTrace (prefixWord ++ tailWord_5743839) baseStart_5743839 baseEnd_5743839 := by
    simpa [prefixWord, tailWord_5743839, baseEnd_5743839] using wordTrace_append hprefix tailTrace_5743839
  have hstable : (prefixWord ++ tailWord_5743839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743839).length < 2 ^ (prefixWord ++ tailWord_5743839).sum := by decide
  have hdescent : baseEnd_5743839 < baseStart_5743839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743847 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 1, 4]
def baseStart_5743847 : Nat := 118140960795 + 5743847 * 2 ^ 59
def prefixEnd_5743847 : Nat := 4983230072969 + 3 ^ 40 * 5743847 * 2
def baseEnd_5743847 : Nat := 983118105628497968632345

theorem tailTrace_5743847 : CollatzResearch.WordTrace tailWord_5743847 prefixEnd_5743847 983118105628497968632345 := by
  unfold tailWord_5743847
  simp only [CollatzResearch.WordTrace]
  refine ⟨209495310822030764813621795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139663540548020509875747863 209495310822030764813621795)
  ·
    refine ⟨314242966233046147220432693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209495310822030764813621795 314242966233046147220432693)
    ·
      refine ⟨29460278084348076301915565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314242966233046147220432693 29460278084348076301915565)
      ·
        refine ⟨11047604281630528613218337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29460278084348076301915565 11047604281630528613218337)
        ·
          refine ⟨8285703211222896459913753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11047604281630528613218337 8285703211222896459913753)
          ·
            refine ⟨6214277408417172344935315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8285703211222896459913753 6214277408417172344935315)
            ·
              refine ⟨9321416112625758517402973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214277408417172344935315 9321416112625758517402973)
              ·
                refine ⟨3495531042234659444026115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9321416112625758517402973 3495531042234659444026115)
                ·
                  refine ⟨5243296563351989166039173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3495531042234659444026115 5243296563351989166039173)
                  ·
                    refine ⟨983118105628497968632345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243296563351989166039173 983118105628497968632345)
                    ·
                      rfl

theorem cell23_5743847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_5743847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743847 prefixEnd_5743847 := by exact prefixLift 5743847
  have htrace : WordTrace (prefixWord ++ tailWord_5743847) baseStart_5743847 baseEnd_5743847 := by
    simpa [prefixWord, tailWord_5743847, baseEnd_5743847] using wordTrace_append hprefix tailTrace_5743847
  have hstable : (prefixWord ++ tailWord_5743847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743847).length < 2 ^ (prefixWord ++ tailWord_5743847).sum := by decide
  have hdescent : baseEnd_5743847 < baseStart_5743847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743870 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5743870 : Nat := 118140960795 + 5743870 * 2 ^ 59
def prefixEnd_5743870 : Nat := 4983230072969 + 3 ^ 40 * 5743870 * 2
def baseEnd_5743870 : Nat := 2949366126940547315909429

theorem tailTrace_5743870 : CollatzResearch.WordTrace tailWord_5743870 prefixEnd_5743870 2949366126940547315909429 := by
  unfold tailWord_5743870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26187018712618429967713633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139664099800631626494472709 26187018712618429967713633)
  ·
    refine ⟨19640264034463822475785225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26187018712618429967713633 19640264034463822475785225)
    ·
      refine ⟨14730198025847866856838919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19640264034463822475785225 14730198025847866856838919)
      ·
        refine ⟨22095297038771800285258379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14730198025847866856838919 22095297038771800285258379)
        ·
          refine ⟨33142945558157700427887569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22095297038771800285258379 33142945558157700427887569)
          ·
            refine ⟨24857209168618275320915677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33142945558157700427887569 24857209168618275320915677)
            ·
              refine ⟨9321453438231853245343379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24857209168618275320915677 9321453438231853245343379)
              ·
                refine ⟨13982180157347779868015069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321453438231853245343379 13982180157347779868015069)
                ·
                  refine ⟨5243317559005417450505651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13982180157347779868015069 5243317559005417450505651)
                  ·
                    refine ⟨7864976338508126175758477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243317559005417450505651 7864976338508126175758477)
                    ·
                      refine ⟨2949366126940547315909429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7864976338508126175758477 2949366126940547315909429)
                      ·
                        rfl

theorem cell23_5743870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5743870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743870 prefixEnd_5743870 := by exact prefixLift 5743870
  have htrace : WordTrace (prefixWord ++ tailWord_5743870) baseStart_5743870 baseEnd_5743870 := by
    simpa [prefixWord, tailWord_5743870, baseEnd_5743870] using wordTrace_append hprefix tailTrace_5743870
  have hstable : (prefixWord ++ tailWord_5743870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743870).length < 2 ^ (prefixWord ++ tailWord_5743870).sum := by decide
  have hdescent : baseEnd_5743870 < baseStart_5743870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743889 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_5743889 : Nat := 118140960795 + 5743889 * 2 ^ 59
def prefixEnd_5743889 : Nat := 4983230072969 + 3 ^ 40 * 5743889 * 2
def baseEnd_5743889 : Nat := 2949375883072982741571841

theorem tailTrace_5743889 : CollatzResearch.WordTrace tailWord_5743889 prefixEnd_5743889 2949375883072982741571841 := by
  unfold tailWord_5743889
  simp only [CollatzResearch.WordTrace]
  refine ⟨209496842687878605986650721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139664561791919070657767147 209496842687878605986650721)
  ·
    refine ⟨157122632015908954489988041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209496842687878605986650721 157122632015908954489988041)
    ·
      refine ⟨117841974011931715867491031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157122632015908954489988041 117841974011931715867491031)
      ·
        refine ⟨176762961017897573801236547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117841974011931715867491031 176762961017897573801236547)
        ·
          refine ⟨265144441526846360701854821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176762961017897573801236547 265144441526846360701854821)
          ·
            refine ⟨49714582786283692631597779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265144441526846360701854821 49714582786283692631597779)
            ·
              refine ⟨74571874179425538947396669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49714582786283692631597779 74571874179425538947396669)
              ·
                refine ⟨27964452817284577105273751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74571874179425538947396669 27964452817284577105273751)
                ·
                  refine ⟨41946679225926865657910627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27964452817284577105273751 41946679225926865657910627)
                  ·
                    refine ⟨62920018838890298486865941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41946679225926865657910627 62920018838890298486865941)
                    ·
                      refine ⟨2949375883072982741571841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62920018838890298486865941 2949375883072982741571841)
                      ·
                        rfl

theorem cell23_5743889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_5743889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743889 prefixEnd_5743889 := by exact prefixLift 5743889
  have htrace : WordTrace (prefixWord ++ tailWord_5743889) baseStart_5743889 baseEnd_5743889 := by
    simpa [prefixWord, tailWord_5743889, baseEnd_5743889] using wordTrace_append hprefix tailTrace_5743889
  have hstable : (prefixWord ++ tailWord_5743889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743889).length < 2 ^ (prefixWord ++ tailWord_5743889).sum := by decide
  have hdescent : baseEnd_5743889 < baseStart_5743889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743890 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5743890 : Nat := 118140960795 + 5743890 * 2 ^ 59
def prefixEnd_5743890 : Nat := 4983230072969 + 3 ^ 40 * 5743890 * 2
def baseEnd_5743890 : Nat := 983125465517879079219779

theorem tailTrace_5743890 : CollatzResearch.WordTrace tailWord_5743890 prefixEnd_5743890 983125465517879079219779 := by
  unfold tailWord_5743890
  simp only [CollatzResearch.WordTrace]
  refine ⟨52374219790218745789359281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139664586107249988771624749 52374219790218745789359281)
  ·
    refine ⟨39280664842664059342019461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52374219790218745789359281 39280664842664059342019461)
    ·
      refine ⟨7365124657999511126628649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39280664842664059342019461 7365124657999511126628649)
      ·
        refine ⟨5523843493499633344971487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7365124657999511126628649 5523843493499633344971487)
        ·
          refine ⟨8285765240249450017457231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5523843493499633344971487 8285765240249450017457231)
          ·
            refine ⟨12428647860374175026185847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8285765240249450017457231 12428647860374175026185847)
            ·
              refine ⟨18642971790561262539278771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12428647860374175026185847 18642971790561262539278771)
              ·
                refine ⟨27964457685841893808918157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18642971790561262539278771 27964457685841893808918157)
                ·
                  refine ⟨10486671632190710178344309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27964457685841893808918157 10486671632190710178344309)
                  ·
                    refine ⟨983125465517879079219779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486671632190710178344309 983125465517879079219779)
                    ·
                      rfl

theorem cell23_5743890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5743890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743890 prefixEnd_5743890 := by exact prefixLift 5743890
  have htrace : WordTrace (prefixWord ++ tailWord_5743890) baseStart_5743890 baseEnd_5743890 := by
    simpa [prefixWord, tailWord_5743890, baseEnd_5743890] using wordTrace_append hprefix tailTrace_5743890
  have hstable : (prefixWord ++ tailWord_5743890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743890).length < 2 ^ (prefixWord ++ tailWord_5743890).sum := by decide
  have hdescent : baseEnd_5743890 < baseStart_5743890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743893 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_5743893 : Nat := 118140960795 + 5743893 * 2 ^ 59
def prefixEnd_5743893 : Nat := 4983230072969 + 3 ^ 40 * 5743893 * 2
def baseEnd_5743893 : Nat := 2949377936995600725921823

theorem tailTrace_5743893 : CollatzResearch.WordTrace tailWord_5743893 prefixEnd_5743893 2949377936995600725921823 := by
  unfold tailWord_5743893
  simp only [CollatzResearch.WordTrace]
  refine ⟨209496988579864114669796333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139664659053242743113197555 209496988579864114669796333)
  ·
    refine ⟨78561370717449043001173625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209496988579864114669796333 78561370717449043001173625)
    ·
      refine ⟨58921028038086782250880219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78561370717449043001173625 58921028038086782250880219)
      ·
        refine ⟨88381542057130173376320329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58921028038086782250880219 88381542057130173376320329)
        ·
          refine ⟨66286156542847630032240247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88381542057130173376320329 66286156542847630032240247)
          ·
            refine ⟨99429234814271445048360371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66286156542847630032240247 99429234814271445048360371)
            ·
              refine ⟨149143852221407167572540557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99429234814271445048360371 149143852221407167572540557)
              ·
                refine ⟨55928944583027687839702709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149143852221407167572540557 55928944583027687839702709)
                ·
                  refine ⟨5243338554658845734972129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55928944583027687839702709 5243338554658845734972129)
                  ·
                    refine ⟨3932503915994134301229097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5243338554658845734972129 3932503915994134301229097)
                    ·
                      refine ⟨2949377936995600725921823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932503915994134301229097 2949377936995600725921823)
                      ·
                        rfl

theorem cell23_5743893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_5743893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743893 prefixEnd_5743893 := by exact prefixLift 5743893
  have htrace : WordTrace (prefixWord ++ tailWord_5743893) baseStart_5743893 baseEnd_5743893 := by
    simpa [prefixWord, tailWord_5743893, baseEnd_5743893] using wordTrace_append hprefix tailTrace_5743893
  have hstable : (prefixWord ++ tailWord_5743893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743893).length < 2 ^ (prefixWord ++ tailWord_5743893).sum := by decide
  have hdescent : baseEnd_5743893 < baseStart_5743893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743939 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_5743939 : Nat := 118140960795 + 5743939 * 2 ^ 59
def prefixEnd_5743939 : Nat := 4983230072969 + 3 ^ 40 * 5743939 * 2
def baseEnd_5743939 : Nat := 2949401557105707545946611

theorem tailTrace_5743939 : CollatzResearch.WordTrace tailWord_5743939 prefixEnd_5743939 2949401557105707545946611 := by
  unfold tailWord_5743939
  simp only [CollatzResearch.WordTrace]
  refine ⟨209498666337697464525970871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139665777558464976350647247 209498666337697464525970871)
  ·
    refine ⟨314247999506546196788956307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209498666337697464525970871 314247999506546196788956307)
    ·
      refine ⟨471371999259819295183434461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314247999506546196788956307 471371999259819295183434461)
      ·
        refine ⟨176764499722432235693787923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471371999259819295183434461 176764499722432235693787923)
        ·
          refine ⟨265146749583648353540681885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176764499722432235693787923 265146749583648353540681885)
          ·
            refine ⟨99430031093868132577755707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265146749583648353540681885 99430031093868132577755707)
            ·
              refine ⟨149145046640802198866633561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99430031093868132577755707 149145046640802198866633561)
              ·
                refine ⟨111858784980601649149975171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149145046640802198866633561 111858784980601649149975171)
                ·
                  refine ⟨167788177470902473724962757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111858784980601649149975171 167788177470902473724962757)
                  ·
                    refine ⟨31460283275794213823430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167788177470902473724962757 31460283275794213823430517)
                    ·
                      refine ⟨2949401557105707545946611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31460283275794213823430517 2949401557105707545946611)
                      ·
                        rfl

theorem cell23_5743939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_5743939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743939 prefixEnd_5743939 := by exact prefixLift 5743939
  have htrace : WordTrace (prefixWord ++ tailWord_5743939) baseStart_5743939 baseEnd_5743939 := by
    simpa [prefixWord, tailWord_5743939, baseEnd_5743939] using wordTrace_append hprefix tailTrace_5743939
  have hstable : (prefixWord ++ tailWord_5743939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743939).length < 2 ^ (prefixWord ++ tailWord_5743939).sum := by decide
  have hdescent : baseEnd_5743939 < baseStart_5743939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743940 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5743940 : Nat := 118140960795 + 5743940 * 2 ^ 59
def prefixEnd_5743940 : Nat := 4983230072969 + 3 ^ 40 * 5743940 * 2
def baseEnd_5743940 : Nat := 2949402070586362042034107

theorem tailTrace_5743940 : CollatzResearch.WordTrace tailWord_5743940 prefixEnd_5743940 2949402070586362042034107 := by
  unfold tailWord_5743940
  simp only [CollatzResearch.WordTrace]
  refine ⟨104749351405346920848378637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139665801873795894464504849 104749351405346920848378637)
  ·
    refine ⟨39281006777005095318141989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104749351405346920848378637 39281006777005095318141989)
    ·
      refine ⟨7365188770688455372151623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39281006777005095318141989 7365188770688455372151623)
      ·
        refine ⟨11047783156032683058227435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7365188770688455372151623 11047783156032683058227435)
        ·
          refine ⟨16571674734049024587341153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11047783156032683058227435 16571674734049024587341153)
          ·
            refine ⟨12428756050536768440505865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16571674734049024587341153 12428756050536768440505865)
            ·
              refine ⟨9321567037902576330379399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12428756050536768440505865 9321567037902576330379399)
              ·
                refine ⟨13982350556853864495569099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321567037902576330379399 13982350556853864495569099)
                ·
                  refine ⟨20973525835280796743353649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13982350556853864495569099 20973525835280796743353649)
                  ·
                    refine ⟨15730144376460597557515237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20973525835280796743353649 15730144376460597557515237)
                    ·
                      refine ⟨2949402070586362042034107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15730144376460597557515237 2949402070586362042034107)
                      ·
                        rfl

theorem cell23_5743940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5743940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743940 prefixEnd_5743940 := by exact prefixLift 5743940
  have htrace : WordTrace (prefixWord ++ tailWord_5743940) baseStart_5743940 baseEnd_5743940 := by
    simpa [prefixWord, tailWord_5743940, baseEnd_5743940] using wordTrace_append hprefix tailTrace_5743940
  have hstable : (prefixWord ++ tailWord_5743940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743940).length < 2 ^ (prefixWord ++ tailWord_5743940).sum := by decide
  have hdescent : baseEnd_5743940 < baseStart_5743940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743943 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_5743943 : Nat := 118140960795 + 5743943 * 2 ^ 59
def prefixEnd_5743943 : Nat := 4983230072969 + 3 ^ 40 * 5743943 * 2
def baseEnd_5743943 : Nat := 2949403611028325530296593

theorem tailTrace_5743943 : CollatzResearch.WordTrace tailWord_5743943 prefixEnd_5743943 2949403611028325530296593 := by
  unfold tailWord_5743943
  simp only [CollatzResearch.WordTrace]
  refine ⟨209498812229682973209116483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139665874819788648806077655 209498812229682973209116483)
  ·
    refine ⟨314248218344524459813674725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209498812229682973209116483 314248218344524459813674725)
    ·
      refine ⟨58921540939598336215064011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314248218344524459813674725 58921540939598336215064011)
      ·
        refine ⟨88382311409397504322596017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58921540939598336215064011 88382311409397504322596017)
        ·
          refine ⟨66286733557048128241947013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88382311409397504322596017 66286733557048128241947013)
          ·
            refine ⟨12428762541946524045365065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66286733557048128241947013 12428762541946524045365065)
            ·
              refine ⟨9321571906459893034023799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12428762541946524045365065 9321571906459893034023799)
              ·
                refine ⟨13982357859689839551035699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321571906459893034023799 13982357859689839551035699)
                ·
                  refine ⟨20973536789534759326553549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13982357859689839551035699 20973536789534759326553549)
                  ·
                    refine ⟨7865076296075534747457581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20973536789534759326553549 7865076296075534747457581)
                    ·
                      refine ⟨2949403611028325530296593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7865076296075534747457581 2949403611028325530296593)
                      ·
                        rfl

theorem cell23_5743943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_5743943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743943 prefixEnd_5743943 := by exact prefixLift 5743943
  have htrace : WordTrace (prefixWord ++ tailWord_5743943) baseStart_5743943 baseEnd_5743943 := by
    simpa [prefixWord, tailWord_5743943, baseEnd_5743943] using wordTrace_append hprefix tailTrace_5743943
  have hstable : (prefixWord ++ tailWord_5743943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743943).length < 2 ^ (prefixWord ++ tailWord_5743943).sum := by decide
  have hdescent : baseEnd_5743943 < baseStart_5743943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743953 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 3, 3, 2]
def baseStart_5743953 : Nat := 118140960795 + 5743953 * 2 ^ 59
def prefixEnd_5743953 : Nat := 4983230072969 + 3 ^ 40 * 5743953 * 2
def baseEnd_5743953 : Nat := 2949408745834870491171547

theorem tailTrace_5743953 : CollatzResearch.WordTrace tailWord_5743953 prefixEnd_5743953 2949408745834870491171547 := by
  unfold tailWord_5743953
  simp only [CollatzResearch.WordTrace]
  refine ⟨209499176959646744916980513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139666117973097829944653675 209499176959646744916980513)
  ·
    refine ⟨157124382719735058687735385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209499176959646744916980513 157124382719735058687735385)
    ·
      refine ⟨117843287039801294015801539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157124382719735058687735385 117843287039801294015801539)
      ·
        refine ⟨176764930559701941023702309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117843287039801294015801539 176764930559701941023702309)
        ·
          refine ⟨33143424479944113941944183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176764930559701941023702309 33143424479944113941944183)
          ·
            refine ⟨49715136719916170912916275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33143424479944113941944183 49715136719916170912916275)
            ·
              refine ⟨74572705079874256369374413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49715136719916170912916275 74572705079874256369374413)
              ·
                refine ⟨27964764404952846138515405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74572705079874256369374413 27964764404952846138515405)
                ·
                  refine ⟨10486786651857317301943277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27964764404952846138515405 10486786651857317301943277)
                  ·
                    refine ⟨3932544994446493988228729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10486786651857317301943277 3932544994446493988228729)
                    ·
                      refine ⟨2949408745834870491171547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932544994446493988228729 2949408745834870491171547)
                      ·
                        rfl

theorem cell23_5743953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_5743953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743953 prefixEnd_5743953 := by exact prefixLift 5743953
  have htrace : WordTrace (prefixWord ++ tailWord_5743953) baseStart_5743953 baseEnd_5743953 := by
    simpa [prefixWord, tailWord_5743953, baseEnd_5743953] using wordTrace_append hprefix tailTrace_5743953
  have hstable : (prefixWord ++ tailWord_5743953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743953).length < 2 ^ (prefixWord ++ tailWord_5743953).sum := by decide
  have hdescent : baseEnd_5743953 < baseStart_5743953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743956 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_5743956 : Nat := 118140960795 + 5743956 * 2 ^ 59
def prefixEnd_5743956 : Nat := 4983230072969 + 3 ^ 40 * 5743956 * 2
def baseEnd_5743956 : Nat := 2949410286276833979434033

theorem tailTrace_5743956 : CollatzResearch.WordTrace tailWord_5743956 prefixEnd_5743956 2949410286276833979434033 := by
  unfold tailWord_5743956
  simp only [CollatzResearch.WordTrace]
  refine ⟨104749643189317938214669861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139666190919090584286226481 104749643189317938214669861)
  ·
    refine ⟨19640558097997113415250599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104749643189317938214669861 19640558097997113415250599)
    ·
      refine ⟨29460837146995670122875899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19640558097997113415250599 29460837146995670122875899)
      ·
        refine ⟨44191255720493505184313849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29460837146995670122875899 44191255720493505184313849)
        ·
          refine ⟨33143441790370128888235387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44191255720493505184313849 33143441790370128888235387)
          ·
            refine ⟨49715162685555193332353081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33143441790370128888235387 49715162685555193332353081)
            ·
              refine ⟨37286372014166394999264811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49715162685555193332353081 37286372014166394999264811)
              ·
                refine ⟨55929558021249592498897217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37286372014166394999264811 55929558021249592498897217)
                ·
                  refine ⟨41947168515937194374172913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55929558021249592498897217 41947168515937194374172913)
                  ·
                    refine ⟨31460376386952895780629685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41947168515937194374172913 31460376386952895780629685)
                    ·
                      refine ⟨2949410286276833979434033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31460376386952895780629685 2949410286276833979434033)
                      ·
                        rfl

theorem cell23_5743956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_5743956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743956 prefixEnd_5743956 := by exact prefixLift 5743956
  have htrace : WordTrace (prefixWord ++ tailWord_5743956) baseStart_5743956 baseEnd_5743956 := by
    simpa [prefixWord, tailWord_5743956, baseEnd_5743956] using wordTrace_append hprefix tailTrace_5743956
  have hstable : (prefixWord ++ tailWord_5743956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743956).length < 2 ^ (prefixWord ++ tailWord_5743956).sum := by decide
  have hdescent : baseEnd_5743956 < baseStart_5743956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743958 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5743958 : Nat := 118140960795 + 5743958 * 2 ^ 59
def prefixEnd_5743958 : Nat := 4983230072969 + 3 ^ 40 * 5743958 * 2
def baseEnd_5743958 : Nat := 983137104412714323869675

theorem tailTrace_5743958 : CollatzResearch.WordTrace tailWord_5743958 prefixEnd_5743958 983137104412714323869675 := by
  unfold tailWord_5743958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13093709957789289423182033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139666239549752420513941685 13093709957789289423182033)
  ·
    refine ⟨9820282468341967067386525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13093709957789289423182033 9820282468341967067386525)
    ·
      refine ⟨3682605925628237650269947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9820282468341967067386525 3682605925628237650269947)
      ·
        refine ⟨5523908888442356475404921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682605925628237650269947 5523908888442356475404921)
        ·
          refine ⟨4142931666331767356553691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5523908888442356475404921 4142931666331767356553691)
          ·
            refine ⟨6214397499497651034830537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142931666331767356553691 6214397499497651034830537)
            ·
              refine ⟨4660798124623238276122903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6214397499497651034830537 4660798124623238276122903)
              ·
                refine ⟨6991197186934857414184355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660798124623238276122903 6991197186934857414184355)
                ·
                  refine ⟨10486795780402286121276533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6991197186934857414184355 10486795780402286121276533)
                  ·
                    refine ⟨983137104412714323869675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486795780402286121276533 983137104412714323869675)
                    ·
                      rfl

theorem cell23_5743958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5743958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743958 prefixEnd_5743958 := by exact prefixLift 5743958
  have htrace : WordTrace (prefixWord ++ tailWord_5743958) baseStart_5743958 baseEnd_5743958 := by
    simpa [prefixWord, tailWord_5743958, baseEnd_5743958] using wordTrace_append hprefix tailTrace_5743958
  have hstable : (prefixWord ++ tailWord_5743958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743958).length < 2 ^ (prefixWord ++ tailWord_5743958).sum := by decide
  have hdescent : baseEnd_5743958 < baseStart_5743958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743979 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_5743979 : Nat := 118140960795 + 5743979 * 2 ^ 59
def prefixEnd_5743979 : Nat := 4983230072969 + 3 ^ 40 * 5743979 * 2
def baseEnd_5743979 : Nat := 2949422096331887389446427

theorem tailTrace_5743979 : CollatzResearch.WordTrace tailWord_5743979 prefixEnd_5743979 2949422096331887389446427 := by
  unfold tailWord_5743979
  simp only [CollatzResearch.WordTrace]
  refine ⟨209500125257552551357426991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139666750171701700904951327 209500125257552551357426991)
  ·
    refine ⟨314250187886328827036140487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209500125257552551357426991 314250187886328827036140487)
    ·
      refine ⟨471375281829493240554210731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314250187886328827036140487 471375281829493240554210731)
      ·
        refine ⟨707062922744239860831316097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471375281829493240554210731 707062922744239860831316097)
        ·
          refine ⟨530297192058179895623487073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707062922744239860831316097 530297192058179895623487073)
          ·
            refine ⟨397722894043634921717615305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530297192058179895623487073 397722894043634921717615305)
            ·
              refine ⟨298292170532726191288211479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397722894043634921717615305 298292170532726191288211479)
              ·
                refine ⟨447438255799089286932317219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298292170532726191288211479 447438255799089286932317219)
                ·
                  refine ⟨671157383698633930398475829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447438255799089286932317219 671157383698633930398475829)
                  ·
                    refine ⟨62921004721746930974857109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671157383698633930398475829 62921004721746930974857109)
                    ·
                      refine ⟨2949422096331887389446427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62921004721746930974857109 2949422096331887389446427)
                      ·
                        rfl

theorem cell23_5743979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_5743979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743979 prefixEnd_5743979 := by exact prefixLift 5743979
  have htrace : WordTrace (prefixWord ++ tailWord_5743979) baseStart_5743979 baseEnd_5743979 := by
    simpa [prefixWord, tailWord_5743979, baseEnd_5743979] using wordTrace_append hprefix tailTrace_5743979
  have hstable : (prefixWord ++ tailWord_5743979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743979).length < 2 ^ (prefixWord ++ tailWord_5743979).sum := by decide
  have hdescent : baseEnd_5743979 < baseStart_5743979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5743996 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_5743996 : Nat := 118140960795 + 5743996 * 2 ^ 59
def prefixEnd_5743996 : Nat := 4983230072969 + 3 ^ 40 * 5743996 * 2
def baseEnd_5743996 : Nat := 2949430825503013822933849

theorem tailTrace_5743996 : CollatzResearch.WordTrace tailWord_5743996 prefixEnd_5743996 2949430825503013822933849 := by
  unfold tailWord_5743996
  simp only [CollatzResearch.WordTrace]
  refine ⟨104750372649245481630397921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139667163532327308840530561 104750372649245481630397921)
  ·
    refine ⟨78562779486934111222798441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104750372649245481630397921 78562779486934111222798441)
    ·
      refine ⟨58922084615200583417098831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78562779486934111222798441 58922084615200583417098831)
      ·
        refine ⟨88383126922800875125648247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58922084615200583417098831 88383126922800875125648247)
        ·
          refine ⟨132574690384201312688472371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88383126922800875125648247 132574690384201312688472371)
          ·
            refine ⟨198862035576301969032708557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132574690384201312688472371 198862035576301969032708557)
            ·
              refine ⟨74573263341113238387265709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198862035576301969032708557 74573263341113238387265709)
              ·
                refine ⟨27964973752917464395224641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74573263341113238387265709 27964973752917464395224641)
                ·
                  refine ⟨20973730314688098296418481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27964973752917464395224641 20973730314688098296418481)
                  ·
                    refine ⟨15730297736016073722313861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20973730314688098296418481 15730297736016073722313861)
                    ·
                      refine ⟨2949430825503013822933849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15730297736016073722313861 2949430825503013822933849)
                      ·
                        rfl

theorem cell23_5743996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_5743996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5743996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5743996 prefixEnd_5743996 := by exact prefixLift 5743996
  have htrace : WordTrace (prefixWord ++ tailWord_5743996) baseStart_5743996 baseEnd_5743996 := by
    simpa [prefixWord, tailWord_5743996, baseEnd_5743996] using wordTrace_append hprefix tailTrace_5743996
  have hstable : (prefixWord ++ tailWord_5743996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5743996).length < 2 ^ (prefixWord ++ tailWord_5743996).sum := by decide
  have hdescent : baseEnd_5743996 < baseStart_5743996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5743996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744000 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 2, 2, 2]
def baseStart_5744000 : Nat := 118140960795 + 5744000 * 2 ^ 59
def prefixEnd_5744000 : Nat := 4983230072969 + 3 ^ 40 * 5744000 * 2
def baseEnd_5744000 : Nat := 2949432879425631807283831

theorem tailTrace_5744000 : CollatzResearch.WordTrace tailWord_5744000 prefixEnd_5744000 2949432879425631807283831 := by
  unfold tailWord_5744000
  simp only [CollatzResearch.WordTrace]
  refine ⟨104750445595238235971970727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139667260793650981295960969 104750445595238235971970727)
  ·
    refine ⟨157125668392857353957956091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104750445595238235971970727 157125668392857353957956091)
    ·
      refine ⟨235688502589286030936934137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157125668392857353957956091 235688502589286030936934137)
      ·
        refine ⟨176766376941964523202700603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235688502589286030936934137 176766376941964523202700603)
        ·
          refine ⟨265149565412946784804050905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176766376941964523202700603 265149565412946784804050905)
          ·
            refine ⟨198862174059710088603038179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265149565412946784804050905 198862174059710088603038179)
            ·
              refine ⟨298293261089565132904557269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198862174059710088603038179 298293261089565132904557269)
              ·
                refine ⟨6991248306786682802450561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 298293261089565132904557269 6991248306786682802450561)
                ·
                  refine ⟨5243436230090012101837921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6991248306786682802450561 5243436230090012101837921)
                  ·
                    refine ⟨3932577172567509076378441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5243436230090012101837921 3932577172567509076378441)
                    ·
                      refine ⟨2949432879425631807283831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932577172567509076378441 2949432879425631807283831)
                      ·
                        rfl

theorem cell23_5744000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_5744000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744000 prefixEnd_5744000 := by exact prefixLift 5744000
  have htrace : WordTrace (prefixWord ++ tailWord_5744000) baseStart_5744000 baseEnd_5744000 := by
    simpa [prefixWord, tailWord_5744000, baseEnd_5744000] using wordTrace_append hprefix tailTrace_5744000
  have hstable : (prefixWord ++ tailWord_5744000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744000).length < 2 ^ (prefixWord ++ tailWord_5744000).sum := by decide
  have hdescent : baseEnd_5744000 < baseStart_5744000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744056 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_5744056 : Nat := 118140960795 + 5744056 * 2 ^ 59
def prefixEnd_5744056 : Nat := 4983230072969 + 3 ^ 40 * 5744056 * 2
def baseEnd_5744056 : Nat := 2949461634342283588183573

theorem tailTrace_5744056 : CollatzResearch.WordTrace tailWord_5744056 prefixEnd_5744056 2949461634342283588183573 := by
  unfold tailWord_5744056
  simp only [CollatzResearch.WordTrace]
  refine ⟨104751466839136796753990011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139668622452182395671986681 104751466839136796753990011)
  ·
    refine ⟨157127200258705195130985017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104751466839136796753990011 157127200258705195130985017)
    ·
      refine ⟨117845400194028896348238763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157127200258705195130985017 117845400194028896348238763)
      ·
        refine ⟨176768100291043344522358145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117845400194028896348238763 176768100291043344522358145)
        ·
          refine ⟨132576075218282508391768609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176768100291043344522358145 132576075218282508391768609)
          ·
            refine ⟨99432056413711881293826457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132576075218282508391768609 99432056413711881293826457)
            ·
              refine ⟨74574042310283910970369843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99432056413711881293826457 74574042310283910970369843)
              ·
                refine ⟨111861063465425866455554765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74574042310283910970369843 111861063465425866455554765)
                ·
                  refine ⟨41947898799534699920833037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111861063465425866455554765 41947898799534699920833037)
                  ·
                    refine ⟨15730462049825512470312389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41947898799534699920833037 15730462049825512470312389)
                    ·
                      refine ⟨2949461634342283588183573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15730462049825512470312389 2949461634342283588183573)
                      ·
                        rfl

theorem cell23_5744056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_5744056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744056 prefixEnd_5744056 := by exact prefixLift 5744056
  have htrace : WordTrace (prefixWord ++ tailWord_5744056) baseStart_5744056 baseEnd_5744056 := by
    simpa [prefixWord, tailWord_5744056, baseEnd_5744056] using wordTrace_append hprefix tailTrace_5744056
  have hstable : (prefixWord ++ tailWord_5744056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744056).length < 2 ^ (prefixWord ++ tailWord_5744056).sum := by decide
  have hdescent : baseEnd_5744056 < baseStart_5744056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744073 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 4, 4, 2]
def baseStart_5744073 : Nat := 118140960795 + 5744073 * 2 ^ 59
def prefixEnd_5744073 : Nat := 4983230072969 + 3 ^ 40 * 5744073 * 2
def baseEnd_5744073 : Nat := 2949470363513410021670995

theorem tailTrace_5744073 : CollatzResearch.WordTrace tailWord_5744073 prefixEnd_5744073 2949470363513410021670995 := by
  unfold tailWord_5744073
  simp only [CollatzResearch.WordTrace]
  refine ⟨209503553719212005411348873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139669035812808003607565915 209503553719212005411348873)
  ·
    refine ⟨157127665289409004058511655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209503553719212005411348873 157127665289409004058511655)
    ·
      refine ⟨235691497934113506087767483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157127665289409004058511655 235691497934113506087767483)
      ·
        refine ⟨353537246901170259131651225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235691497934113506087767483 353537246901170259131651225)
        ·
          refine ⟨265152935175877694348738419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353537246901170259131651225 265152935175877694348738419)
          ·
            refine ⟨397729402763816541523107629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265152935175877694348738419 397729402763816541523107629)
            ·
              refine ⟨149148526036431203071165361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397729402763816541523107629 149148526036431203071165361)
              ·
                refine ⟨111861394527323402303374021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149148526036431203071165361 111861394527323402303374021)
                ·
                  refine ⟨20974011473873137931882629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111861394527323402303374021 20974011473873137931882629)
                  ·
                    refine ⟨3932627151351213362227993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20974011473873137931882629 3932627151351213362227993)
                    ·
                      refine ⟨2949470363513410021670995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932627151351213362227993 2949470363513410021670995)
                      ·
                        rfl

theorem cell23_5744073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 4, 2].length) (baseStart_5744073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744073 prefixEnd_5744073 := by exact prefixLift 5744073
  have htrace : WordTrace (prefixWord ++ tailWord_5744073) baseStart_5744073 baseEnd_5744073 := by
    simpa [prefixWord, tailWord_5744073, baseEnd_5744073] using wordTrace_append hprefix tailTrace_5744073
  have hstable : (prefixWord ++ tailWord_5744073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744073).length < 2 ^ (prefixWord ++ tailWord_5744073).sum := by decide
  have hdescent : baseEnd_5744073 < baseStart_5744073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744113 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 6]
def baseStart_5744113 : Nat := 118140960795 + 5744113 * 2 ^ 59
def prefixEnd_5744113 : Nat := 4983230072969 + 3 ^ 40 * 5744113 * 2
def baseEnd_5744113 : Nat := 327721211415509985018979

theorem tailTrace_5744113 : CollatzResearch.WordTrace tailWord_5744113 prefixEnd_5744113 327721211415509985018979 := by
  unfold tailWord_5744113
  simp only [CollatzResearch.WordTrace]
  refine ⟨209505012639067092242804993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139670008426044728161869995 209505012639067092242804993)
  ·
    refine ⟨157128759479300319182103745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209505012639067092242804993 157128759479300319182103745)
    ·
      refine ⟨117846569609475239386577809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157128759479300319182103745 117846569609475239386577809)
      ·
        refine ⟨88384927207106429539933357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117846569609475239386577809 88384927207106429539933357)
        ·
          refine ⟨33144347702664911077475009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88384927207106429539933357 33144347702664911077475009)
          ·
            refine ⟨24858260776998683308106257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33144347702664911077475009 24858260776998683308106257)
            ·
              refine ⟨18643695582749012481079693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24858260776998683308106257 18643695582749012481079693)
              ·
                refine ⟨6991385843530879680404885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18643695582749012481079693 6991385843530879680404885)
                ·
                  refine ⟨327721211415509985018979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6991385843530879680404885 327721211415509985018979)
                  ·
                    rfl

theorem cell23_5744113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 6].length) (baseStart_5744113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744113 prefixEnd_5744113 := by exact prefixLift 5744113
  have htrace : WordTrace (prefixWord ++ tailWord_5744113) baseStart_5744113 baseEnd_5744113 := by
    simpa [prefixWord, tailWord_5744113, baseEnd_5744113] using wordTrace_append hprefix tailTrace_5744113
  have hstable : (prefixWord ++ tailWord_5744113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744113).length < 2 ^ (prefixWord ++ tailWord_5744113).sum := by decide
  have hdescent : baseEnd_5744113 < baseStart_5744113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744117 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5744117 : Nat := 118140960795 + 5744117 * 2 ^ 59
def prefixEnd_5744117 : Nat := 4983230072969 + 3 ^ 40 * 5744117 * 2
def baseEnd_5744117 : Nat := 983164318887402616506931

theorem tailTrace_5744117 : CollatzResearch.WordTrace tailWord_5744117 prefixEnd_5744117 983164318887402616506931 := by
  unfold tailWord_5744117
  simp only [CollatzResearch.WordTrace]
  refine ⟨209505158531052600925950605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139670105687368400617300403 209505158531052600925950605)
  ·
    refine ⟨78564434449144725347231477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209505158531052600925950605 78564434449144725347231477)
    ·
      refine ⟨7365415729607318001302951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78564434449144725347231477 7365415729607318001302951)
      ·
        refine ⟨11048123594410977001954427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7365415729607318001302951 11048123594410977001954427)
        ·
          refine ⟨16572185391616465502931641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11048123594410977001954427 16572185391616465502931641)
          ·
            refine ⟨12429139043712349127198731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16572185391616465502931641 12429139043712349127198731)
            ·
              refine ⟨18643708565568523690798097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12429139043712349127198731 18643708565568523690798097)
              ·
                refine ⟨13982781424176392768098573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18643708565568523690798097 13982781424176392768098573)
                ·
                  refine ⟨5243543034066147288036965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13982781424176392768098573 5243543034066147288036965)
                  ·
                    refine ⟨983164318887402616506931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243543034066147288036965 983164318887402616506931)
                    ·
                      rfl

theorem cell23_5744117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5744117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744117 prefixEnd_5744117 := by exact prefixLift 5744117
  have htrace : WordTrace (prefixWord ++ tailWord_5744117) baseStart_5744117 baseEnd_5744117 := by
    simpa [prefixWord, tailWord_5744117, baseEnd_5744117] using wordTrace_append hprefix tailTrace_5744117
  have hstable : (prefixWord ++ tailWord_5744117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744117).length < 2 ^ (prefixWord ++ tailWord_5744117).sum := by decide
  have hdescent : baseEnd_5744117 < baseStart_5744117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744157 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_5744157 : Nat := 118140960795 + 5744157 * 2 ^ 59
def prefixEnd_5744157 : Nat := 4983230072969 + 3 ^ 40 * 5744157 * 2
def baseEnd_5744157 : Nat := 2949513495888387693020609

theorem tailTrace_5744157 : CollatzResearch.WordTrace tailWord_5744157 prefixEnd_5744157 2949513495888387693020609 := by
  unfold tailWord_5744157
  simp only [CollatzResearch.WordTrace]
  refine ⟨209506617450907687757406725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139671078300605125171604483 209506617450907687757406725)
  ·
    refine ⟨39282490772045191454513761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209506617450907687757406725 39282490772045191454513761)
    ·
      refine ⟨29461868079033893590885321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39282490772045191454513761 29461868079033893590885321)
      ·
        refine ⟨22096401059275420193163991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29461868079033893590885321 22096401059275420193163991)
        ·
          refine ⟨33144601588913130289745987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22096401059275420193163991 33144601588913130289745987)
          ·
            refine ⟨49716902383369695434618981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33144601588913130289745987 49716902383369695434618981)
            ·
              refine ⟨9321919196881817893991059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49716902383369695434618981 9321919196881817893991059)
              ·
                refine ⟨13982878795322726840986589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321919196881817893991059 13982878795322726840986589)
                ·
                  refine ⟨5243579548246022565369971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13982878795322726840986589 5243579548246022565369971)
                  ·
                    refine ⟨7865369322369033848054957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243579548246022565369971 7865369322369033848054957)
                    ·
                      refine ⟨2949513495888387693020609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7865369322369033848054957 2949513495888387693020609)
                      ·
                        rfl

theorem cell23_5744157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_5744157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744157 prefixEnd_5744157 := by exact prefixLift 5744157
  have htrace : WordTrace (prefixWord ++ tailWord_5744157) baseStart_5744157 baseEnd_5744157 := by
    simpa [prefixWord, tailWord_5744157, baseEnd_5744157] using wordTrace_append hprefix tailTrace_5744157
  have hstable : (prefixWord ++ tailWord_5744157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744157).length < 2 ^ (prefixWord ++ tailWord_5744157).sum := by decide
  have hdescent : baseEnd_5744157 < baseStart_5744157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744220 : List Nat := [2, 2, 4, 1, 2, 2, 2, 8]
def baseStart_5744220 : Nat := 118140960795 + 5744220 * 2 ^ 59
def prefixEnd_5744220 : Nat := 4983230072969 + 3 ^ 40 * 5744220 * 2
def baseEnd_5744220 : Nat := 109242438709985960982697

theorem tailTrace_5744220 : CollatzResearch.WordTrace tailWord_5744220 prefixEnd_5744220 109242438709985960982697 := by
  unfold tailWord_5744220
  simp only [CollatzResearch.WordTrace]
  refine ⟨104754457624839724758475057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139672610166452966344633409 104754457624839724758475057)
  ·
    refine ⟨78565843218629793568856293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104754457624839724758475057 78565843218629793568856293)
    ·
      refine ⟨14731095603493086294160555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78565843218629793568856293 14731095603493086294160555)
      ·
        refine ⟨22096643405239629441240833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14731095603493086294160555 22096643405239629441240833)
        ·
          refine ⟨16572482553929722080930625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22096643405239629441240833 16572482553929722080930625)
          ·
            refine ⟨12429361915447291560697969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16572482553929722080930625 12429361915447291560697969)
            ·
              refine ⟨9322021436585468670523477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12429361915447291560697969 9322021436585468670523477)
              ·
                refine ⟨109242438709985960982697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9322021436585468670523477 109242438709985960982697)
                ·
                  rfl

theorem cell23_5744220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 8].length) (baseStart_5744220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744220 prefixEnd_5744220 := by exact prefixLift 5744220
  have htrace : WordTrace (prefixWord ++ tailWord_5744220) baseStart_5744220 baseEnd_5744220 := by
    simpa [prefixWord, tailWord_5744220, baseEnd_5744220] using wordTrace_append hprefix tailTrace_5744220
  have hstable : (prefixWord ++ tailWord_5744220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744220).length < 2 ^ (prefixWord ++ tailWord_5744220).sum := by decide
  have hdescent : baseEnd_5744220 < baseStart_5744220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744234 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_5744234 : Nat := 118140960795 + 5744234 * 2 ^ 59
def prefixEnd_5744234 : Nat := 4983230072969 + 3 ^ 40 * 5744234 * 2
def baseEnd_5744234 : Nat := 2949553033898783891757755

theorem tailTrace_5744234 : CollatzResearch.WordTrace tailWord_5744234 prefixEnd_5744234 2949553033898783891757755 := by
  unfold tailWord_5744234
  simp only [CollatzResearch.WordTrace]
  refine ⟨52377356467907182476989939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139672950581085819938639837 52377356467907182476989939)
  ·
    refine ⟨78566034701860773715484909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52377356467907182476989939 78566034701860773715484909)
    ·
      refine ⟨29462263013197790143306841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78566034701860773715484909 29462263013197790143306841)
      ·
        refine ⟨22096697259898342607480131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29462263013197790143306841 22096697259898342607480131)
        ·
          refine ⟨33145045889847513911220197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22096697259898342607480131 33145045889847513911220197)
          ·
            refine ⟨6214696104346408858353787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33145045889847513911220197 6214696104346408858353787)
            ·
              refine ⟨9322044156519613287530681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214696104346408858353787 9322044156519613287530681)
              ·
                refine ⟨6991533117389709965648011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9322044156519613287530681 6991533117389709965648011)
                ·
                  refine ⟨10487299676084564948472017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6991533117389709965648011 10487299676084564948472017)
                  ·
                    refine ⟨7865474757063423711354013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10487299676084564948472017 7865474757063423711354013)
                    ·
                      refine ⟨2949553033898783891757755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7865474757063423711354013 2949553033898783891757755)
                      ·
                        rfl

theorem cell23_5744234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_5744234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744234 prefixEnd_5744234 := by exact prefixLift 5744234
  have htrace : WordTrace (prefixWord ++ tailWord_5744234) baseStart_5744234 baseEnd_5744234 := by
    simpa [prefixWord, tailWord_5744234, baseEnd_5744234] using wordTrace_append hprefix tailTrace_5744234
  have hstable : (prefixWord ++ tailWord_5744234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744234).length < 2 ^ (prefixWord ++ tailWord_5744234).sum := by decide
  have hdescent : baseEnd_5744234 < baseStart_5744234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744270 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5744270 : Nat := 118140960795 + 5744270 * 2 ^ 59
def prefixEnd_5744270 : Nat := 4983230072969 + 3 ^ 40 * 5744270 * 2
def baseEnd_5744270 : Nat := 2949571519202345750907589

theorem tailTrace_5744270 : CollatzResearch.WordTrace tailWord_5744270 prefixEnd_5744270 2949571519202345750907589 := by
  unfold tailWord_5744270
  simp only [CollatzResearch.WordTrace]
  refine ⟨26188842362437288507033783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139673825932998872037513509 26188842362437288507033783)
  ·
    refine ⟨39283263543655932760550675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26188842362437288507033783 39283263543655932760550675)
    ·
      refine ⟨58924895315483899140826013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39283263543655932760550675 58924895315483899140826013)
      ·
        refine ⟨22096835743306462177809755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58924895315483899140826013 22096835743306462177809755)
        ·
          refine ⟨33145253614959693266714633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22096835743306462177809755 33145253614959693266714633)
          ·
            refine ⟨24858940211219769950035975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33145253614959693266714633 24858940211219769950035975)
            ·
              refine ⟨37288410316829654925053963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24858940211219769950035975 37288410316829654925053963)
              ·
                refine ⟨55932615475244482387580945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37288410316829654925053963 55932615475244482387580945)
                ·
                  refine ⟨41949461606433361790685709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55932615475244482387580945 41949461606433361790685709)
                  ·
                    refine ⟨15731048102412510671507141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41949461606433361790685709 15731048102412510671507141)
                    ·
                      refine ⟨2949571519202345750907589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15731048102412510671507141 2949571519202345750907589)
                      ·
                        rfl

theorem cell23_5744270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5744270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744270 prefixEnd_5744270 := by exact prefixLift 5744270
  have htrace : WordTrace (prefixWord ++ tailWord_5744270) baseStart_5744270 baseEnd_5744270 := by
    simpa [prefixWord, tailWord_5744270, baseEnd_5744270] using wordTrace_append hprefix tailTrace_5744270
  have hstable : (prefixWord ++ tailWord_5744270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744270).length < 2 ^ (prefixWord ++ tailWord_5744270).sum := by decide
  have hdescent : baseEnd_5744270 < baseStart_5744270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744273 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_5744273 : Nat := 118140960795 + 5744273 * 2 ^ 59
def prefixEnd_5744273 : Nat := 4983230072969 + 3 ^ 40 * 5744273 * 2
def baseEnd_5744273 : Nat := 2949573059644309239170075

theorem tailTrace_5744273 : CollatzResearch.WordTrace tailWord_5744273 prefixEnd_5744273 2949573059644309239170075 := by
  unfold tailWord_5744273
  simp only [CollatzResearch.WordTrace]
  refine ⟨209510848318487439568629473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139673898878991626379086315 209510848318487439568629473)
  ·
    refine ⟨157133136238865579676472105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209510848318487439568629473 157133136238865579676472105)
    ·
      refine ⟨117849852179149184757354079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157133136238865579676472105 117849852179149184757354079)
      ·
        refine ⟨176774778268723777136031119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117849852179149184757354079 176774778268723777136031119)
        ·
          refine ⟨265162167403085665704046679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176774778268723777136031119 265162167403085665704046679)
          ·
            refine ⟨397743251104628498556070019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265162167403085665704046679 397743251104628498556070019)
            ·
              refine ⟨596614876656942747834105029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397743251104628498556070019 596614876656942747834105029)
              ·
                refine ⟨111865289373176765218894693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596614876656942747834105029 111865289373176765218894693)
                ·
                  refine ⟨20974741757470643478542755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111865289373176765218894693 20974741757470643478542755)
                  ·
                    refine ⟨31462112636205965217814133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20974741757470643478542755 31462112636205965217814133)
                    ·
                      refine ⟨2949573059644309239170075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31462112636205965217814133 2949573059644309239170075)
                      ·
                        rfl

theorem cell23_5744273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_5744273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744273 prefixEnd_5744273 := by exact prefixLift 5744273
  have htrace : WordTrace (prefixWord ++ tailWord_5744273) baseStart_5744273 baseEnd_5744273 := by
    simpa [prefixWord, tailWord_5744273, baseEnd_5744273] using wordTrace_append hprefix tailTrace_5744273
  have hstable : (prefixWord ++ tailWord_5744273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744273).length < 2 ^ (prefixWord ++ tailWord_5744273).sum := by decide
  have hdescent : baseEnd_5744273 < baseStart_5744273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744280 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_5744280 : Nat := 118140960795 + 5744280 * 2 ^ 59
def prefixEnd_5744280 : Nat := 4983230072969 + 3 ^ 40 * 5744280 * 2
def baseEnd_5744280 : Nat := 983192218002963570594181

theorem tailTrace_5744280 : CollatzResearch.WordTrace tailWord_5744280 prefixEnd_5744280 983192218002963570594181 := by
  unfold tailWord_5744280
  simp only [CollatzResearch.WordTrace]
  refine ⟨104755551814731039882067147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139674069086308053176089529 104755551814731039882067147)
  ·
    refine ⟨157133327722096559823100721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104755551814731039882067147 157133327722096559823100721)
    ·
      refine ⟨117849995791572419867325541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157133327722096559823100721 117849995791572419867325541)
      ·
        refine ⟨22096874210919828725123539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117849995791572419867325541 22096874210919828725123539)
        ·
          refine ⟨33145311316379743087685309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22096874210919828725123539 33145311316379743087685309)
          ·
            refine ⟨12429491743642403657881991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33145311316379743087685309 12429491743642403657881991)
            ·
              refine ⟨18644237615463605486822987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12429491743642403657881991 18644237615463605486822987)
              ·
                refine ⟨27966356423195408230234481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18644237615463605486822987 27966356423195408230234481)
                ·
                  refine ⟨20974767317396556172675861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27966356423195408230234481 20974767317396556172675861)
                  ·
                    refine ⟨983192218002963570594181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20974767317396556172675861 983192218002963570594181)
                    ·
                      rfl

theorem cell23_5744280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_5744280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744280 prefixEnd_5744280 := by exact prefixLift 5744280
  have htrace : WordTrace (prefixWord ++ tailWord_5744280) baseStart_5744280 baseEnd_5744280 := by
    simpa [prefixWord, tailWord_5744280, baseEnd_5744280] using wordTrace_append hprefix tailTrace_5744280
  have hstable : (prefixWord ++ tailWord_5744280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744280).length < 2 ^ (prefixWord ++ tailWord_5744280).sum := by decide
  have hdescent : baseEnd_5744280 < baseStart_5744280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744293 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 9]
def baseStart_5744293 : Nat := 118140960795 + 5744293 * 2 ^ 59
def prefixEnd_5744293 : Nat := 4983230072969 + 3 ^ 40 * 5744293 * 2
def baseEnd_5744293 : Nat := 327731481028599906768887

theorem tailTrace_5744293 : CollatzResearch.WordTrace tailWord_5744293 prefixEnd_5744293 327731481028599906768887 := by
  unfold tailWord_5744293
  simp only [CollatzResearch.WordTrace]
  refine ⟨209511577778414982984357533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139674385185609988656238355 209511577778414982984357533)
  ·
    refine ⟨78566841666905618619134075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209511577778414982984357533 78566841666905618619134075)
    ·
      refine ⟨117850262500358427928701113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78566841666905618619134075 117850262500358427928701113)
      ·
        refine ⟨88387696875268820946525835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117850262500358427928701113 88387696875268820946525835)
        ·
          refine ⟨132581545312903231419788753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88387696875268820946525835 132581545312903231419788753)
          ·
            refine ⟨99436158984677423564841565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132581545312903231419788753 99436158984677423564841565)
            ·
              refine ⟨37288559619254033836815587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99436158984677423564841565 37288559619254033836815587)
              ·
                refine ⟨55932839428881050755223381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37288559619254033836815587 55932839428881050755223381)
                ·
                  refine ⟨327731481028599906768887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55932839428881050755223381 327731481028599906768887)
                  ·
                    rfl

theorem cell23_5744293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_5744293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744293 prefixEnd_5744293 := by exact prefixLift 5744293
  have htrace : WordTrace (prefixWord ++ tailWord_5744293) baseStart_5744293 baseEnd_5744293 := by
    simpa [prefixWord, tailWord_5744293, baseEnd_5744293] using wordTrace_append hprefix tailTrace_5744293
  have hstable : (prefixWord ++ tailWord_5744293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744293).length < 2 ^ (prefixWord ++ tailWord_5744293).sum := by decide
  have hdescent : baseEnd_5744293 < baseStart_5744293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744320 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_5744320 : Nat := 118140960795 + 5744320 * 2 ^ 59
def prefixEnd_5744320 : Nat := 4983230072969 + 3 ^ 40 * 5744320 * 2
def baseEnd_5744320 : Nat := 2949597193235070555282359

theorem tailTrace_5744320 : CollatzResearch.WordTrace tailWord_5744320 prefixEnd_5744320 2949597193235070555282359 := by
  unfold tailWord_5744320
  simp only [CollatzResearch.WordTrace]
  refine ⟨104756281274658583297795207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139675041699544777730393609 104756281274658583297795207)
  ·
    refine ⟨157134421911987874946692811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104756281274658583297795207 157134421911987874946692811)
    ·
      refine ⟨235701632867981812420039217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157134421911987874946692811 235701632867981812420039217)
      ·
        refine ⟨176776224650986359315029413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235701632867981812420039217 176776224650986359315029413)
        ·
          refine ⟨33145542122059942371568015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176776224650986359315029413 33145542122059942371568015)
          ·
            refine ⟨49718313183089913557352023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33145542122059942371568015 49718313183089913557352023)
            ·
              refine ⟨74577469774634870336028035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49718313183089913557352023 74577469774634870336028035)
              ·
                refine ⟨111866204661952305504042053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74577469774634870336028035 111866204661952305504042053)
                ·
                  refine ⟨20974913374116057282007885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111866204661952305504042053 20974913374116057282007885)
                  ·
                    refine ⟨7865592515293521480752957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20974913374116057282007885 7865592515293521480752957)
                    ·
                      refine ⟨2949597193235070555282359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7865592515293521480752957 2949597193235070555282359)
                      ·
                        rfl

theorem cell23_5744320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_5744320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744320 prefixEnd_5744320 := by exact prefixLift 5744320
  have htrace : WordTrace (prefixWord ++ tailWord_5744320) baseStart_5744320 baseEnd_5744320 := by
    simpa [prefixWord, tailWord_5744320, baseEnd_5744320] using wordTrace_append hprefix tailTrace_5744320
  have hstable : (prefixWord ++ tailWord_5744320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744320).length < 2 ^ (prefixWord ++ tailWord_5744320).sum := by decide
  have hdescent : baseEnd_5744320 < baseStart_5744320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744338 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_5744338 : Nat := 118140960795 + 5744338 * 2 ^ 59
def prefixEnd_5744338 : Nat := 4983230072969 + 3 ^ 40 * 5744338 * 2
def baseEnd_5744338 : Nat := 2949606435886851484857277

theorem tailTrace_5744338 : CollatzResearch.WordTrace tailWord_5744338 prefixEnd_5744338 2949606435886851484857277 := by
  unfold tailWord_5744338
  simp only [CollatzResearch.WordTrace]
  refine ⟨52378304765812988917436417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139675479375501303779830445 52378304765812988917436417)
  ·
    refine ⟨39283728574359741688077313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52378304765812988917436417 39283728574359741688077313)
    ·
      refine ⟨29462796430769806266057985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39283728574359741688077313 29462796430769806266057985)
      ·
        refine ⟨22097097323077354699543489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29462796430769806266057985 22097097323077354699543489)
        ·
          refine ⟨16572822992308016024657617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22097097323077354699543489 16572822992308016024657617)
          ·
            refine ⟨12429617244231012018493213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16572822992308016024657617 12429617244231012018493213)
            ·
              refine ⟨4661106466586629506934955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12429617244231012018493213 4661106466586629506934955)
              ·
                refine ⟨6991659699879944260402433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661106466586629506934955 6991659699879944260402433)
                ·
                  refine ⟨5243744774909958195301825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6991659699879944260402433 5243744774909958195301825)
                  ·
                    refine ⟨3932808581182468646476369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5243744774909958195301825 3932808581182468646476369)
                    ·
                      refine ⟨2949606435886851484857277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932808581182468646476369 2949606435886851484857277)
                      ·
                        rfl

theorem cell23_5744338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_5744338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744338 prefixEnd_5744338 := by exact prefixLift 5744338
  have htrace : WordTrace (prefixWord ++ tailWord_5744338) baseStart_5744338 baseEnd_5744338 := by
    simpa [prefixWord, tailWord_5744338, baseEnd_5744338] using wordTrace_append hprefix tailTrace_5744338
  have hstable : (prefixWord ++ tailWord_5744338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744338).length < 2 ^ (prefixWord ++ tailWord_5744338).sum := by decide
  have hdescent : baseEnd_5744338 < baseStart_5744338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744387 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 3, 4]
def baseStart_5744387 : Nat := 118140960795 + 5744387 * 2 ^ 59
def prefixEnd_5744387 : Nat := 4983230072969 + 3 ^ 40 * 5744387 * 2
def baseEnd_5744387 : Nat := 983210532146307264381517

theorem tailTrace_5744387 : CollatzResearch.WordTrace tailWord_5744387 prefixEnd_5744387 983210532146307264381517 := by
  unfold tailWord_5744387
  simp only [CollatzResearch.WordTrace]
  refine ⟨209515006240074437038279415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139676670826716291358852943 209515006240074437038279415)
  ·
    refine ⟨314272509360111655557419123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209515006240074437038279415 314272509360111655557419123)
    ·
      refine ⟨471408764040167483336128685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314272509360111655557419123 471408764040167483336128685)
      ·
        refine ⟨176778286515062806251048257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471408764040167483336128685 176778286515062806251048257)
        ·
          refine ⟨132583714886297104688286193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176778286515062806251048257 132583714886297104688286193)
          ·
            refine ⟨99437786164722828516214645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132583714886297104688286193 99437786164722828516214645)
            ·
              refine ⟨9322292452942765173395123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99437786164722828516214645 9322292452942765173395123)
              ·
                refine ⟨13983438679414147760092685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9322292452942765173395123 13983438679414147760092685)
                ·
                  refine ⟨5243789504780305410034757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13983438679414147760092685 5243789504780305410034757)
                  ·
                    refine ⟨983210532146307264381517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243789504780305410034757 983210532146307264381517)
                    ·
                      rfl

theorem cell23_5744387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 4].length) (baseStart_5744387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744387 prefixEnd_5744387 := by exact prefixLift 5744387
  have htrace : WordTrace (prefixWord ++ tailWord_5744387) baseStart_5744387 baseEnd_5744387 := by
    simpa [prefixWord, tailWord_5744387, baseEnd_5744387] using wordTrace_append hprefix tailTrace_5744387
  have hstable : (prefixWord ++ tailWord_5744387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744387).length < 2 ^ (prefixWord ++ tailWord_5744387).sum := by decide
  have hdescent : baseEnd_5744387 < baseStart_5744387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744438 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5744438 : Nat := 118140960795 + 5744438 * 2 ^ 59
def prefixEnd_5744438 : Nat := 4983230072969 + 3 ^ 40 * 5744438 * 2
def baseEnd_5744438 : Nat := 983219261317433697868939

theorem tailTrace_5744438 : CollatzResearch.WordTrace tailWord_5744438 prefixEnd_5744438 983219261317433697868939 := by
  unfold tailWord_5744438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094804147680604546774123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139677910908593115165590645 13094804147680604546774123)
  ·
    refine ⟨19642206221520906820161185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13094804147680604546774123 19642206221520906820161185)
    ·
      refine ⟨14731654666140680115120889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19642206221520906820161185 14731654666140680115120889)
      ·
        refine ⟨11048740999605510086340667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14731654666140680115120889 11048740999605510086340667)
        ·
          refine ⟨16573111499408265129511001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11048740999605510086340667 16573111499408265129511001)
          ·
            refine ⟨12429833624556198847133251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16573111499408265129511001 12429833624556198847133251)
            ·
              refine ⟨18644750436834298270699877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12429833624556198847133251 18644750436834298270699877)
              ·
                refine ⟨3495890706906430925756227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18644750436834298270699877 3495890706906430925756227)
                ·
                  refine ⟨5243836060359646388634341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3495890706906430925756227 5243836060359646388634341)
                  ·
                    refine ⟨983219261317433697868939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243836060359646388634341 983219261317433697868939)
                    ·
                      rfl

theorem cell23_5744438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5744438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744438 prefixEnd_5744438 := by exact prefixLift 5744438
  have htrace : WordTrace (prefixWord ++ tailWord_5744438) baseStart_5744438 baseEnd_5744438 := by
    simpa [prefixWord, tailWord_5744438, baseEnd_5744438] using wordTrace_append hprefix tailTrace_5744438
  have hstable : (prefixWord ++ tailWord_5744438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744438).length < 2 ^ (prefixWord ++ tailWord_5744438).sum := by decide
  have hdescent : baseEnd_5744438 < baseStart_5744438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744461 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_5744461 : Nat := 118140960795 + 5744461 * 2 ^ 59
def prefixEnd_5744461 : Nat := 4983230072969 + 3 ^ 40 * 5744461 * 2
def baseEnd_5744461 : Nat := 2949669594007354503619211

theorem tailTrace_5744461 : CollatzResearch.WordTrace tailWord_5744461 prefixEnd_5744461 2949669594007354503619211 := by
  unfold tailWord_5744461
  simp only [CollatzResearch.WordTrace]
  refine ⟨209517705241806347676473237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139678470161204231784315491 209517705241806347676473237)
  ·
    refine ⟨9821142433209672547334683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209517705241806347676473237 9821142433209672547334683)
    ·
      refine ⟨14731713649814508821002025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9821142433209672547334683 14731713649814508821002025)
      ·
        refine ⟨11048785237360881615751519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14731713649814508821002025 11048785237360881615751519)
        ·
          refine ⟨16573177856041322423627279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11048785237360881615751519 16573177856041322423627279)
          ·
            refine ⟨24859766784061983635440919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16573177856041322423627279 24859766784061983635440919)
            ·
              refine ⟨37289650176092975453161379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24859766784061983635440919 37289650176092975453161379)
              ·
                refine ⟨55934475264139463179742069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37289650176092975453161379 55934475264139463179742069)
                ·
                  refine ⟨5243857056013074673100819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55934475264139463179742069 5243857056013074673100819)
                  ·
                    refine ⟨7865785584019612009651229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243857056013074673100819 7865785584019612009651229)
                    ·
                      refine ⟨2949669594007354503619211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7865785584019612009651229 2949669594007354503619211)
                      ·
                        rfl

theorem cell23_5744461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_5744461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744461 prefixEnd_5744461 := by exact prefixLift 5744461
  have htrace : WordTrace (prefixWord ++ tailWord_5744461) baseStart_5744461 baseEnd_5744461 := by
    simpa [prefixWord, tailWord_5744461, baseEnd_5744461] using wordTrace_append hprefix tailTrace_5744461
  have hstable : (prefixWord ++ tailWord_5744461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744461).length < 2 ^ (prefixWord ++ tailWord_5744461).sum := by decide
  have hdescent : baseEnd_5744461 < baseStart_5744461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744487 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_5744487 : Nat := 118140960795 + 5744487 * 2 ^ 59
def prefixEnd_5744487 : Nat := 4983230072969 + 3 ^ 40 * 5744487 * 2
def baseEnd_5744487 : Nat := 2949682944504371401894091

theorem tailTrace_5744487 : CollatzResearch.WordTrace tailWord_5744487 prefixEnd_5744487 2949682944504371401894091 := by
  unfold tailWord_5744487
  simp only [CollatzResearch.WordTrace]
  refine ⟨209518653539712154116919715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139679102359808102744613143 209518653539712154116919715)
  ·
    refine ⟨314277980309568231175379573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209518653539712154116919715 314277980309568231175379573)
    ·
      refine ⟨29463560654022021672691835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314277980309568231175379573 29463560654022021672691835)
      ·
        refine ⟨44195340981033032509037753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29463560654022021672691835 44195340981033032509037753)
        ·
          refine ⟨33146505735774774381778315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44195340981033032509037753 33146505735774774381778315)
          ·
            refine ⟨49719758603662161572667473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33146505735774774381778315 49719758603662161572667473)
            ·
              refine ⟨37289818952746621179500605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49719758603662161572667473 37289818952746621179500605)
              ·
                refine ⟨13983682107279982942312727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37289818952746621179500605 13983682107279982942312727)
                ·
                  refine ⟨20975523160919974413469091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13983682107279982942312727 20975523160919974413469091)
                  ·
                    refine ⟨31463284741379961620203637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20975523160919974413469091 31463284741379961620203637)
                    ·
                      refine ⟨2949682944504371401894091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31463284741379961620203637 2949682944504371401894091)
                      ·
                        rfl

theorem cell23_5744487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_5744487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744487 prefixEnd_5744487 := by exact prefixLift 5744487
  have htrace : WordTrace (prefixWord ++ tailWord_5744487) baseStart_5744487 baseEnd_5744487 := by
    simpa [prefixWord, tailWord_5744487, baseEnd_5744487] using wordTrace_append hprefix tailTrace_5744487
  have hstable : (prefixWord ++ tailWord_5744487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744487).length < 2 ^ (prefixWord ++ tailWord_5744487).sum := by decide
  have hdescent : baseEnd_5744487 < baseStart_5744487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744535 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 1, 2, 2]
def baseStart_5744535 : Nat := 118140960795 + 5744535 * 2 ^ 59
def prefixEnd_5744535 : Nat := 4983230072969 + 3 ^ 40 * 5744535 * 2
def baseEnd_5744535 : Nat := 2949707591575787214093871

theorem tailTrace_5744535 : CollatzResearch.WordTrace tailWord_5744535 prefixEnd_5744535 2949707591575787214093871 := by
  unfold tailWord_5744535
  simp only [CollatzResearch.WordTrace]
  refine ⟨209520404243538258314667059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139680269495692172209778039 209520404243538258314667059)
  ·
    refine ⟨314280606365307387472000589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209520404243538258314667059 314280606365307387472000589)
    ·
      refine ⟨117855227386990270302000221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314280606365307387472000589 117855227386990270302000221)
      ·
        refine ⟨44195710270121351363250083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117855227386990270302000221 44195710270121351363250083)
        ·
          refine ⟨66293565405182027044875125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44195710270121351363250083 66293565405182027044875125)
          ·
            refine ⟨6215021756735815035457043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66293565405182027044875125 6215021756735815035457043)
            ·
              refine ⟨9322532635103722553185565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215021756735815035457043 9322532635103722553185565)
              ·
                refine ⟨3495949738163895957444587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9322532635103722553185565 3495949738163895957444587)
                ·
                  refine ⟨5243924607245843936166881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3495949738163895957444587 5243924607245843936166881)
                  ·
                    refine ⟨3932943455434382952125161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5243924607245843936166881 3932943455434382952125161)
                    ·
                      refine ⟨2949707591575787214093871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932943455434382952125161 2949707591575787214093871)
                      ·
                        rfl

theorem cell23_5744535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_5744535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744535 prefixEnd_5744535 := by exact prefixLift 5744535
  have htrace : WordTrace (prefixWord ++ tailWord_5744535) baseStart_5744535 baseEnd_5744535 := by
    simpa [prefixWord, tailWord_5744535, baseEnd_5744535] using wordTrace_append hprefix tailTrace_5744535
  have hstable : (prefixWord ++ tailWord_5744535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744535).length < 2 ^ (prefixWord ++ tailWord_5744535).sum := by decide
  have hdescent : baseEnd_5744535 < baseStart_5744535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744544 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 5, 3, 2]
def baseStart_5744544 : Nat := 118140960795 + 5744544 * 2 ^ 59
def prefixEnd_5744544 : Nat := 4983230072969 + 3 ^ 40 * 5744544 * 2
def baseEnd_5744544 : Nat := 2949712212901677678881329

theorem tailTrace_5744544 : CollatzResearch.WordTrace tailWord_5744544 prefixEnd_5744544 2949712212901677678881329 := by
  unfold tailWord_5744544
  simp only [CollatzResearch.WordTrace]
  refine ⟨104760366250252826425872343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139680488333670435234496457 104760366250252826425872343)
  ·
    refine ⟨157140549375379239638808515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104760366250252826425872343 157140549375379239638808515)
    ·
      refine ⟨235710824063068859458212773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157140549375379239638808515 235710824063068859458212773)
      ·
        refine ⟨44195779511825411148414895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235710824063068859458212773 44195779511825411148414895)
        ·
          refine ⟨66293669267738116722622343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44195779511825411148414895 66293669267738116722622343)
          ·
            refine ⟨99440503901607175083933515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66293669267738116722622343 99440503901607175083933515)
            ·
              refine ⟨149160755852410762625900273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99440503901607175083933515 149160755852410762625900273)
              ·
                refine ⟨111870566889308071969425205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149160755852410762625900273 111870566889308071969425205)
                ·
                  refine ⟨10487865645872631747133613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111870566889308071969425205 10487865645872631747133613)
                  ·
                    refine ⟨3932949617202236905175105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10487865645872631747133613 3932949617202236905175105)
                    ·
                      refine ⟨2949712212901677678881329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932949617202236905175105 2949712212901677678881329)
                      ·
                        rfl

theorem cell23_5744544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_5744544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744544 prefixEnd_5744544 := by exact prefixLift 5744544
  have htrace : WordTrace (prefixWord ++ tailWord_5744544) baseStart_5744544 baseEnd_5744544 := by
    simpa [prefixWord, tailWord_5744544, baseEnd_5744544] using wordTrace_append hprefix tailTrace_5744544
  have hstable : (prefixWord ++ tailWord_5744544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744544).length < 2 ^ (prefixWord ++ tailWord_5744544).sum := by decide
  have hdescent : baseEnd_5744544 < baseStart_5744544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744551 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_5744551 : Nat := 118140960795 + 5744551 * 2 ^ 59
def prefixEnd_5744551 : Nat := 4983230072969 + 3 ^ 40 * 5744551 * 2
def baseEnd_5744551 : Nat := 2949715807266259151493797

theorem tailTrace_5744551 : CollatzResearch.WordTrace tailWord_5744551 prefixEnd_5744551 2949715807266259151493797 := by
  unfold tailWord_5744551
  simp only [CollatzResearch.WordTrace]
  refine ⟨209520987811480293047249507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139680658540986862031499671 209520987811480293047249507)
  ·
    refine ⟨314281481717220439570874261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209520987811480293047249507 314281481717220439570874261)
    ·
      refine ⟨14731944455494708104884731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 314281481717220439570874261 14731944455494708104884731)
      ·
        refine ⟨22097916683242062157327097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14731944455494708104884731 22097916683242062157327097)
        ·
          refine ⟨16573437512431546617995323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22097916683242062157327097 16573437512431546617995323)
          ·
            refine ⟨24860156268647319926992985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16573437512431546617995323 24860156268647319926992985)
            ·
              refine ⟨18645117201485489945244739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24860156268647319926992985 18645117201485489945244739)
              ·
                refine ⟨27967675802228234917867109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18645117201485489945244739 27967675802228234917867109)
                ·
                  refine ⟨5243939212917794047100083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27967675802228234917867109 5243939212917794047100083)
                  ·
                    refine ⟨7865908819376691070650125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5243939212917794047100083 7865908819376691070650125)
                    ·
                      refine ⟨2949715807266259151493797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7865908819376691070650125 2949715807266259151493797)
                      ·
                        rfl

theorem cell23_5744551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_5744551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744551 prefixEnd_5744551 := by exact prefixLift 5744551
  have htrace : WordTrace (prefixWord ++ tailWord_5744551) baseStart_5744551 baseEnd_5744551 := by
    simpa [prefixWord, tailWord_5744551, baseEnd_5744551] using wordTrace_append hprefix tailTrace_5744551
  have hstable : (prefixWord ++ tailWord_5744551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744551).length < 2 ^ (prefixWord ++ tailWord_5744551).sum := by decide
  have hdescent : baseEnd_5744551 < baseStart_5744551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744552 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5744552 : Nat := 118140960795 + 5744552 * 2 ^ 59
def prefixEnd_5744552 : Nat := 4983230072969 + 3 ^ 40 * 5744552 * 2
def baseEnd_5744552 : Nat := 2949716320746913647581293

theorem tailTrace_5744552 : CollatzResearch.WordTrace tailWord_5744552 prefixEnd_5744552 2949716320746913647581293 := by
  unfold tailWord_5744552
  simp only [CollatzResearch.WordTrace]
  refine ⟨104760512142238335109017955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139680682856317780145357273 104760512142238335109017955)
  ·
    refine ⟨157140768213357502663526933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104760512142238335109017955 157140768213357502663526933)
    ·
      refine ⟨7365973510001132937352825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157140768213357502663526933 7365973510001132937352825)
      ·
        refine ⟨5524480132500849703014619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7365973510001132937352825 5524480132500849703014619)
        ·
          refine ⟨8286720198751274554521929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524480132500849703014619 8286720198751274554521929)
          ·
            refine ⟨6215040149063455915891447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8286720198751274554521929 6215040149063455915891447)
            ·
              refine ⟨9322560223595183873837171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215040149063455915891447 9322560223595183873837171)
              ·
                refine ⟨13983840335392775810755757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9322560223595183873837171 13983840335392775810755757)
                ·
                  refine ⟨5243940125772290929033409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13983840335392775810755757 5243940125772290929033409)
                  ·
                    refine ⟨3932955094329218196775057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5243940125772290929033409 3932955094329218196775057)
                    ·
                      refine ⟨2949716320746913647581293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3932955094329218196775057 2949716320746913647581293)
                      ·
                        rfl

theorem cell23_5744552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5744552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744552 prefixEnd_5744552 := by exact prefixLift 5744552
  have htrace : WordTrace (prefixWord ++ tailWord_5744552) baseStart_5744552 baseEnd_5744552 := by
    simpa [prefixWord, tailWord_5744552, baseEnd_5744552] using wordTrace_append hprefix tailTrace_5744552
  have hstable : (prefixWord ++ tailWord_5744552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744552).length < 2 ^ (prefixWord ++ tailWord_5744552).sum := by decide
  have hdescent : baseEnd_5744552 < baseStart_5744552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744558 : List Nat := [4, 1, 5, 1, 1, 1, 2, 8]
def baseStart_5744558 : Nat := 118140960795 + 5744558 * 2 ^ 59
def prefixEnd_5744558 : Nat := 4983230072969 + 3 ^ 40 * 5744558 * 2
def baseEnd_5744558 : Nat := 109248866727068171263195

theorem tailTrace_5744558 : CollatzResearch.WordTrace tailWord_5744558 prefixEnd_5744558 109248866727068171263195 := by
  unfold tailWord_5744558
  simp only [CollatzResearch.WordTrace]
  refine ⟨26190155390306866655344291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139680828748303288828502885 26190155390306866655344291)
  ·
    refine ⟨39285233085460299983016437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26190155390306866655344291 39285233085460299983016437)
    ·
      refine ⟨3682990601761903123407791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39285233085460299983016437 3682990601761903123407791)
      ·
        refine ⟨5524485902642854685111687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682990601761903123407791 5524485902642854685111687)
        ·
          refine ⟨8286728853964282027667531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524485902642854685111687 8286728853964282027667531)
          ·
            refine ⟨12430093280946423041501297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8286728853964282027667531 12430093280946423041501297)
            ·
              refine ⟨9322569960709817281125973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12430093280946423041501297 9322569960709817281125973)
              ·
                refine ⟨109248866727068171263195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9322569960709817281125973 109248866727068171263195)
                ·
                  rfl

theorem cell23_5744558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_5744558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744558 prefixEnd_5744558 := by exact prefixLift 5744558
  have htrace : WordTrace (prefixWord ++ tailWord_5744558) baseStart_5744558 baseEnd_5744558 := by
    simpa [prefixWord, tailWord_5744558, baseEnd_5744558] using wordTrace_append hprefix tailTrace_5744558
  have hstable : (prefixWord ++ tailWord_5744558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744558).length < 2 ^ (prefixWord ++ tailWord_5744558).sum := by decide
  have hdescent : baseEnd_5744558 < baseStart_5744558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744627 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 4, 5]
def baseStart_5744627 : Nat := 118140960795 + 5744627 * 2 ^ 59
def prefixEnd_5744627 : Nat := 4983230072969 + 3 ^ 40 * 5744627 * 2
def baseEnd_5744627 : Nat := 983251610598666951381149

theorem tailTrace_5744627 : CollatzResearch.WordTrace tailWord_5744627 prefixEnd_5744627 983251610598666951381149 := by
  unfold tailWord_5744627
  simp only [CollatzResearch.WordTrace]
  refine ⟨209523759759204958027016135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139682506506136638684677423 209523759759204958027016135)
  ·
    refine ⟨314285639638807437040524203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209523759759204958027016135 314285639638807437040524203)
    ·
      refine ⟨471428459458211155560786305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314285639638807437040524203 471428459458211155560786305)
      ·
        refine ⟨353571344593658366670589729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471428459458211155560786305 353571344593658366670589729)
        ·
          refine ⟨265178508445243775002942297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353571344593658366670589729 265178508445243775002942297)
          ·
            refine ⟨198883881333932831252206723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265178508445243775002942297 198883881333932831252206723)
            ·
              refine ⟨298325822000899246878310085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198883881333932831252206723 298325822000899246878310085)
              ·
                refine ⟨55936091625168608789683141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298325822000899246878310085 55936091625168608789683141)
                ·
                  refine ⟨10488017179719114148065589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55936091625168608789683141 10488017179719114148065589)
                  ·
                    refine ⟨983251610598666951381149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10488017179719114148065589 983251610598666951381149)
                    ·
                      rfl

theorem cell23_5744627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 5].length) (baseStart_5744627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744627 prefixEnd_5744627 := by exact prefixLift 5744627
  have htrace : WordTrace (prefixWord ++ tailWord_5744627) baseStart_5744627 baseEnd_5744627 := by
    simpa [prefixWord, tailWord_5744627, baseEnd_5744627] using wordTrace_append hprefix tailTrace_5744627
  have hstable : (prefixWord ++ tailWord_5744627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744627).length < 2 ^ (prefixWord ++ tailWord_5744627).sum := by decide
  have hdescent : baseEnd_5744627 < baseStart_5744627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744637 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_5744637 : Nat := 118140960795 + 5744637 * 2 ^ 59
def prefixEnd_5744637 : Nat := 4983230072969 + 3 ^ 40 * 5744637 * 2
def baseEnd_5744637 : Nat := 2949759966602545815018401

theorem tailTrace_5744637 : CollatzResearch.WordTrace tailWord_5744637 prefixEnd_5744637 2949759966602545815018401 := by
  unfold tailWord_5744637
  simp only [CollatzResearch.WordTrace]
  refine ⟨209524124489168729734880165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139682749659445819823253443 209524124489168729734880165)
  ·
    refine ⟨39285773341719136825290031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209524124489168729734880165 39285773341719136825290031)
    ·
      refine ⟨58928660012578705237935047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39285773341719136825290031 58928660012578705237935047)
      ·
        refine ⟨88392990018868057856902571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58928660012578705237935047 88392990018868057856902571)
        ·
          refine ⟨132589485028302086785353857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88392990018868057856902571 132589485028302086785353857)
          ·
            refine ⟨99442113771226565089015393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132589485028302086785353857 99442113771226565089015393)
            ·
              refine ⟨74581585328419923816761545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99442113771226565089015393 74581585328419923816761545)
              ·
                refine ⟨55936188996314942862571159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74581585328419923816761545 55936188996314942862571159)
                ·
                  refine ⟨83904283494472414293856739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55936188996314942862571159 83904283494472414293856739)
                  ·
                    refine ⟨125856425241708621440785109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83904283494472414293856739 125856425241708621440785109)
                    ·
                      refine ⟨2949759966602545815018401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125856425241708621440785109 2949759966602545815018401)
                      ·
                        rfl

theorem cell23_5744637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_5744637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744637 prefixEnd_5744637 := by exact prefixLift 5744637
  have htrace : WordTrace (prefixWord ++ tailWord_5744637) baseStart_5744637 baseEnd_5744637 := by
    simpa [prefixWord, tailWord_5744637, baseEnd_5744637] using wordTrace_append hprefix tailTrace_5744637
  have hstable : (prefixWord ++ tailWord_5744637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744637).length < 2 ^ (prefixWord ++ tailWord_5744637).sum := by decide
  have hdescent : baseEnd_5744637 < baseStart_5744637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744664 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5744664 : Nat := 118140960795 + 5744664 * 2 ^ 59
def prefixEnd_5744664 : Nat := 4983230072969 + 3 ^ 40 * 5744664 * 2
def baseEnd_5744664 : Nat := 2949773830580217209380777

theorem tailTrace_5744664 : CollatzResearch.WordTrace tailWord_5744664 prefixEnd_5744664 2949773830580217209380777 := by
  unfold tailWord_5744664
  simp only [CollatzResearch.WordTrace]
  refine ⟨104762554630035456673056523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139683406173380608897408697 104762554630035456673056523)
  ·
    refine ⟨157143831945053185009584785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104762554630035456673056523 157143831945053185009584785)
    ·
      refine ⟨117857873958789888757188589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157143831945053185009584785 117857873958789888757188589)
      ·
        refine ⟨44196702734546208283945721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117857873958789888757188589 44196702734546208283945721)
        ·
          refine ⟨33147527050909656212959291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44196702734546208283945721 33147527050909656212959291)
          ·
            refine ⟨49721290576364484319438937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33147527050909656212959291 49721290576364484319438937)
            ·
              refine ⟨37290967932273363239579203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49721290576364484319438937 37290967932273363239579203)
              ·
                refine ⟨55936451898410044859368805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37290967932273363239579203 55936451898410044859368805)
                ·
                  refine ⟨10488084730951883411131651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55936451898410044859368805 10488084730951883411131651)
                  ·
                    refine ⟨15732127096427825116697477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10488084730951883411131651 15732127096427825116697477)
                    ·
                      refine ⟨2949773830580217209380777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15732127096427825116697477 2949773830580217209380777)
                      ·
                        rfl

theorem cell23_5744664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5744664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744664 prefixEnd_5744664 := by exact prefixLift 5744664
  have htrace : WordTrace (prefixWord ++ tailWord_5744664) baseStart_5744664 baseEnd_5744664 := by
    simpa [prefixWord, tailWord_5744664, baseEnd_5744664] using wordTrace_append hprefix tailTrace_5744664
  have hstable : (prefixWord ++ tailWord_5744664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744664).length < 2 ^ (prefixWord ++ tailWord_5744664).sum := by decide
  have hdescent : baseEnd_5744664 < baseStart_5744664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744684 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_5744684 : Nat := 118140960795 + 5744684 * 2 ^ 59
def prefixEnd_5744684 : Nat := 4983230072969 + 3 ^ 40 * 5744684 * 2
def baseEnd_5744684 : Nat := 2949784100193307131130685

theorem tailTrace_5744684 : CollatzResearch.WordTrace tailWord_5744684 prefixEnd_5744684 2949784100193307131130685 := by
  unfold tailWord_5744684
  simp only [CollatzResearch.WordTrace]
  refine ⟨104762919359999228380920553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139683892479998971174560737 104762919359999228380920553)
  ·
    refine ⟨78572189519999421285690415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104762919359999228380920553 78572189519999421285690415)
    ·
      refine ⟨117858284279999131928535623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78572189519999421285690415 117858284279999131928535623)
      ·
        refine ⟨176787426419998697892803435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117858284279999131928535623 176787426419998697892803435)
        ·
          refine ⟨265181139629998046839205153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176787426419998697892803435 265181139629998046839205153)
          ·
            refine ⟨198885854722498535129403865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265181139629998046839205153 198885854722498535129403865)
            ·
              refine ⟨149164391041873901347052899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198885854722498535129403865 149164391041873901347052899)
              ·
                refine ⟨223746586562810852020579349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149164391041873901347052899 223746586562810852020579349)
                ·
                  refine ⟨10488121245131758688464657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223746586562810852020579349 10488121245131758688464657)
                  ·
                    refine ⟨7866090933848819016348493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10488121245131758688464657 7866090933848819016348493)
                    ·
                      refine ⟨2949784100193307131130685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866090933848819016348493 2949784100193307131130685)
                      ·
                        rfl

theorem cell23_5744684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_5744684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744684 prefixEnd_5744684 := by exact prefixLift 5744684
  have htrace : WordTrace (prefixWord ++ tailWord_5744684) baseStart_5744684 baseEnd_5744684 := by
    simpa [prefixWord, tailWord_5744684, baseEnd_5744684] using wordTrace_append hprefix tailTrace_5744684
  have hstable : (prefixWord ++ tailWord_5744684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744684).length < 2 ^ (prefixWord ++ tailWord_5744684).sum := by decide
  have hdescent : baseEnd_5744684 < baseStart_5744684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744701 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5744701 : Nat := 118140960795 + 5744701 * 2 ^ 59
def prefixEnd_5744701 : Nat := 4983230072969 + 3 ^ 40 * 5744701 * 2
def baseEnd_5744701 : Nat := 2949792829364433564618107

theorem tailTrace_5744701 : CollatzResearch.WordTrace tailWord_5744701 prefixEnd_5744701 2949792829364433564618107 := by
  unfold tailWord_5744701
  simp only [CollatzResearch.WordTrace]
  refine ⟨209526458760936868665209957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139684305840624579110139971 209526458760936868665209957)
  ·
    refine ⟨39286211017675662874726867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209526458760936868665209957 39286211017675662874726867)
    ·
      refine ⟨58929316526513494312090301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39286211017675662874726867 58929316526513494312090301)
      ·
        refine ⟨22098493697442560367033863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58929316526513494312090301 22098493697442560367033863)
        ·
          refine ⟨33147740546163840550550795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22098493697442560367033863 33147740546163840550550795)
          ·
            refine ⟨49721610819245760825826193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33147740546163840550550795 49721610819245760825826193)
            ·
              refine ⟨37291208114434320619369645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49721610819245760825826193 37291208114434320619369645)
              ·
                refine ⟨13984203042912870232263617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37291208114434320619369645 13984203042912870232263617)
                ·
                  refine ⟨10488152282184652674197713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13984203042912870232263617 10488152282184652674197713)
                  ·
                    refine ⟨7866114211638489505648285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10488152282184652674197713 7866114211638489505648285)
                    ·
                      refine ⟨2949792829364433564618107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866114211638489505648285 2949792829364433564618107)
                      ·
                        rfl

theorem cell23_5744701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5744701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744701 prefixEnd_5744701 := by exact prefixLift 5744701
  have htrace : WordTrace (prefixWord ++ tailWord_5744701) baseStart_5744701 baseEnd_5744701 := by
    simpa [prefixWord, tailWord_5744701, baseEnd_5744701] using wordTrace_append hprefix tailTrace_5744701
  have hstable : (prefixWord ++ tailWord_5744701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744701).length < 2 ^ (prefixWord ++ tailWord_5744701).sum := by decide
  have hdescent : baseEnd_5744701 < baseStart_5744701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744707 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_5744707 : Nat := 118140960795 + 5744707 * 2 ^ 59
def prefixEnd_5744707 : Nat := 4983230072969 + 3 ^ 40 * 5744707 * 2
def baseEnd_5744707 : Nat := 2949795910248360541143079

theorem tailTrace_5744707 : CollatzResearch.WordTrace tailWord_5744707 prefixEnd_5744707 2949795910248360541143079 := by
  unfold tailWord_5744707
  simp only [CollatzResearch.WordTrace]
  refine ⟨209526677598915131689928375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139684451732610087793285583 209526677598915131689928375)
  ·
    refine ⟨314290016398372697534892563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209526677598915131689928375 314290016398372697534892563)
    ·
      refine ⟨471435024597559046302338845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314290016398372697534892563 471435024597559046302338845)
      ·
        refine ⟨176788134224084642363377067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471435024597559046302338845 176788134224084642363377067)
        ·
          refine ⟨265182201336126963545065601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176788134224084642363377067 265182201336126963545065601)
          ·
            refine ⟨198886651002095222658799201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265182201336126963545065601 198886651002095222658799201)
            ·
              refine ⟨149164988251571416994099401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198886651002095222658799201 149164988251571416994099401)
              ·
                refine ⟨111873741188678562745574551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149164988251571416994099401 111873741188678562745574551)
                ·
                  refine ⟨167810611783017844118361827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111873741188678562745574551 167810611783017844118361827)
                  ·
                    refine ⟨251715917674526766177542741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167810611783017844118361827 251715917674526766177542741)
                    ·
                      refine ⟨2949795910248360541143079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 251715917674526766177542741 2949795910248360541143079)
                      ·
                        rfl

theorem cell23_5744707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_5744707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744707 prefixEnd_5744707 := by exact prefixLift 5744707
  have htrace : WordTrace (prefixWord ++ tailWord_5744707) baseStart_5744707 baseEnd_5744707 := by
    simpa [prefixWord, tailWord_5744707, baseEnd_5744707] using wordTrace_append hprefix tailTrace_5744707
  have hstable : (prefixWord ++ tailWord_5744707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744707).length < 2 ^ (prefixWord ++ tailWord_5744707).sum := by decide
  have hdescent : baseEnd_5744707 < baseStart_5744707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744725 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_5744725 : Nat := 118140960795 + 5744725 * 2 ^ 59
def prefixEnd_5744725 : Nat := 4983230072969 + 3 ^ 40 * 5744725 * 2
def baseEnd_5744725 : Nat := 983268384300047156905999

theorem tailTrace_5744725 : CollatzResearch.WordTrace tailWord_5744725 prefixEnd_5744725 983268384300047156905999 := by
  unfold tailWord_5744725
  simp only [CollatzResearch.WordTrace]
  refine ⟨209527334112849920764083629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139684889408566613842722419 209527334112849920764083629)
  ·
    refine ⟨78572750292318720286531361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209527334112849920764083629 78572750292318720286531361)
    ·
      refine ⟨58929562719239040214898521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78572750292318720286531361 58929562719239040214898521)
      ·
        refine ⟨44197172039429280161173891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58929562719239040214898521 44197172039429280161173891)
        ·
          refine ⟨66295758059143920241760837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44197172039429280161173891 66295758059143920241760837)
          ·
            refine ⟨12430454636089485045330157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66295758059143920241760837 12430454636089485045330157)
            ·
              refine ⟨4661420488533556891998809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12430454636089485045330157 4661420488533556891998809)
              ·
                refine ⟨3496065366400167668999107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4661420488533556891998809 3496065366400167668999107)
                ·
                  refine ⟨5244098049600251503498661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496065366400167668999107 5244098049600251503498661)
                  ·
                    refine ⟨983268384300047156905999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244098049600251503498661 983268384300047156905999)
                    ·
                      rfl

theorem cell23_5744725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_5744725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744725 prefixEnd_5744725 := by exact prefixLift 5744725
  have htrace : WordTrace (prefixWord ++ tailWord_5744725) baseStart_5744725 baseEnd_5744725 := by
    simpa [prefixWord, tailWord_5744725, baseEnd_5744725] using wordTrace_append hprefix tailTrace_5744725
  have hstable : (prefixWord ++ tailWord_5744725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744725).length < 2 ^ (prefixWord ++ tailWord_5744725).sum := by decide
  have hdescent : baseEnd_5744725 < baseStart_5744725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744738 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_5744738 : Nat := 118140960795 + 5744738 * 2 ^ 59
def prefixEnd_5744738 : Nat := 4983230072969 + 3 ^ 40 * 5744738 * 2
def baseEnd_5744738 : Nat := 327756869794294435539493

theorem tailTrace_5744738 : CollatzResearch.WordTrace tailWord_5744738 prefixEnd_5744738 327756869794294435539493 := by
  unfold tailWord_5744738
  simp only [CollatzResearch.WordTrace]
  refine ⟨52381952065450705996076717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139685205507868549322871245 52381952065450705996076717)
  ·
    refine ⟨19643232024544014748528769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52381952065450705996076717 19643232024544014748528769)
    ·
      refine ⟨14732424018408011061396577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19643232024544014748528769 14732424018408011061396577)
      ·
        refine ⟨11049318013806008296047433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14732424018408011061396577 11049318013806008296047433)
        ·
          refine ⟨8286988510354506222035575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11049318013806008296047433 8286988510354506222035575)
          ·
            refine ⟨12430482765531759333053363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8286988510354506222035575 12430482765531759333053363)
            ·
              refine ⟨18645724148297638999580045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12430482765531759333053363 18645724148297638999580045)
              ·
                refine ⟨6992146555611614624842517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18645724148297638999580045 6992146555611614624842517)
                ·
                  refine ⟨327756869794294435539493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6992146555611614624842517 327756869794294435539493)
                  ·
                    rfl

theorem cell23_5744738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_5744738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744738 prefixEnd_5744738 := by exact prefixLift 5744738
  have htrace : WordTrace (prefixWord ++ tailWord_5744738) baseStart_5744738 baseEnd_5744738 := by
    simpa [prefixWord, tailWord_5744738, baseEnd_5744738] using wordTrace_append hprefix tailTrace_5744738
  have hstable : (prefixWord ++ tailWord_5744738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744738).length < 2 ^ (prefixWord ++ tailWord_5744738).sum := by decide
  have hdescent : baseEnd_5744738 < baseStart_5744738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744751 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 1, 5]
def baseStart_5744751 : Nat := 118140960795 + 5744751 * 2 ^ 59
def prefixEnd_5744751 : Nat := 4983230072969 + 3 ^ 40 * 5744751 * 2
def baseEnd_5744751 : Nat := 983272834465719456330959

theorem tailTrace_5744751 : CollatzResearch.WordTrace tailWord_5744751 prefixEnd_5744751 983272834465719456330959 := by
  unfold tailWord_5744751
  simp only [CollatzResearch.WordTrace]
  refine ⟨209528282410755727204530107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139685521607170484803020071 209528282410755727204530107)
  ·
    refine ⟨314292423616133590806795161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209528282410755727204530107 314292423616133590806795161)
    ·
      refine ⟨235719317712100193105096371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314292423616133590806795161 235719317712100193105096371)
      ·
        refine ⟨353578976568150289657644557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235719317712100193105096371 353578976568150289657644557)
        ·
          refine ⟨132592116213056358621616709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353578976568150289657644557 132592116213056358621616709)
          ·
            refine ⟨24861021789948067241553133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132592116213056358621616709 24861021789948067241553133)
            ·
              refine ⟨9322883171230525215582425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24861021789948067241553133 9322883171230525215582425)
              ·
                refine ⟨6992162378422893911686819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9322883171230525215582425 6992162378422893911686819)
                ·
                  refine ⟨10488243567634340867530229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6992162378422893911686819 10488243567634340867530229)
                  ·
                    refine ⟨983272834465719456330959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10488243567634340867530229 983272834465719456330959)
                    ·
                      rfl

theorem cell23_5744751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_5744751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744751 prefixEnd_5744751 := by exact prefixLift 5744751
  have htrace : WordTrace (prefixWord ++ tailWord_5744751) baseStart_5744751 baseEnd_5744751 := by
    simpa [prefixWord, tailWord_5744751, baseEnd_5744751] using wordTrace_append hprefix tailTrace_5744751
  have hstable : (prefixWord ++ tailWord_5744751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744751).length < 2 ^ (prefixWord ++ tailWord_5744751).sum := by decide
  have hdescent : baseEnd_5744751 < baseStart_5744751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744764 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_5744764 : Nat := 118140960795 + 5744764 * 2 ^ 59
def prefixEnd_5744764 : Nat := 4983230072969 + 3 ^ 40 * 5744764 * 2
def baseEnd_5744764 : Nat := 983275059548555606043439

theorem tailTrace_5744764 : CollatzResearch.WordTrace tailWord_5744764 prefixEnd_5744764 983275059548555606043439 := by
  unfold tailWord_5744764
  simp only [CollatzResearch.WordTrace]
  refine ⟨104764378279854315212376673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139685837706472420283168897 104764378279854315212376673)
  ·
    refine ⟨78573283709890736409282505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104764378279854315212376673 78573283709890736409282505)
    ·
      refine ⟨58929962782418052306961879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78573283709890736409282505 58929962782418052306961879)
      ·
        refine ⟨88394944173627078460442819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58929962782418052306961879 88394944173627078460442819)
        ·
          refine ⟨132592416260440617690664229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88394944173627078460442819 132592416260440617690664229)
          ·
            refine ⟨24861078048832615816999543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132592416260440617690664229 24861078048832615816999543)
            ·
              refine ⟨37291617073248923725499315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24861078048832615816999543 37291617073248923725499315)
              ·
                refine ⟨55937425609873385588248973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37291617073248923725499315 55937425609873385588248973)
                ·
                  refine ⟨20976534603702519595593365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55937425609873385588248973 20976534603702519595593365)
                  ·
                    refine ⟨983275059548555606043439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20976534603702519595593365 983275059548555606043439)
                    ·
                      rfl

theorem cell23_5744764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_5744764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744764 prefixEnd_5744764 := by exact prefixLift 5744764
  have htrace : WordTrace (prefixWord ++ tailWord_5744764) baseStart_5744764 baseEnd_5744764 := by
    simpa [prefixWord, tailWord_5744764, baseEnd_5744764] using wordTrace_append hprefix tailTrace_5744764
  have hstable : (prefixWord ++ tailWord_5744764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744764).length < 2 ^ (prefixWord ++ tailWord_5744764).sum := by decide
  have hdescent : baseEnd_5744764 < baseStart_5744764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744782 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5744782 : Nat := 118140960795 + 5744782 * 2 ^ 59
def prefixEnd_5744782 : Nat := 4983230072969 + 3 ^ 40 * 5744782 * 2
def baseEnd_5744782 : Nat := 2949834421297447747705235

theorem tailTrace_5744782 : CollatzResearch.WordTrace tailWord_5744782 prefixEnd_5744782 2949834421297447747705235 := by
  unfold tailWord_5744782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26191176634205427437363575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139686275382428946332605733 26191176634205427437363575)
  ·
    refine ⟨39286764951308141156045363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26191176634205427437363575 39286764951308141156045363)
    ·
      refine ⟨58930147426962211734068045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39286764951308141156045363 58930147426962211734068045)
      ·
        refine ⟨22098805285110829400275517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58930147426962211734068045 22098805285110829400275517)
        ·
          refine ⟨8287051981916561025103319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22098805285110829400275517 8287051981916561025103319)
          ·
            refine ⟨12430577972874841537654979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287051981916561025103319 12430577972874841537654979)
            ·
              refine ⟨18645866959312262306482469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12430577972874841537654979 18645866959312262306482469)
              ·
                refine ⟨3496100054871049182465463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18645866959312262306482469 3496100054871049182465463)
                ·
                  refine ⟨5244150082306573773698195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496100054871049182465463 5244150082306573773698195)
                  ·
                    refine ⟨7866225123459860660547293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5244150082306573773698195 7866225123459860660547293)
                    ·
                      refine ⟨2949834421297447747705235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866225123459860660547293 2949834421297447747705235)
                      ·
                        rfl

theorem cell23_5744782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5744782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744782 prefixEnd_5744782 := by exact prefixLift 5744782
  have htrace : WordTrace (prefixWord ++ tailWord_5744782) baseStart_5744782 baseEnd_5744782 := by
    simpa [prefixWord, tailWord_5744782, baseEnd_5744782] using wordTrace_append hprefix tailTrace_5744782
  have hstable : (prefixWord ++ tailWord_5744782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744782).length < 2 ^ (prefixWord ++ tailWord_5744782).sum := by decide
  have hdescent : baseEnd_5744782 < baseStart_5744782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744784 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_5744784 : Nat := 118140960795 + 5744784 * 2 ^ 59
def prefixEnd_5744784 : Nat := 4983230072969 + 3 ^ 40 * 5744784 * 2
def baseEnd_5744784 : Nat := 2949835448258756739880225

theorem tailTrace_5744784 : CollatzResearch.WordTrace tailWord_5744784 prefixEnd_5744784 2949835448258756739880225 := by
  unfold tailWord_5744784
  simp only [CollatzResearch.WordTrace]
  refine ⟨104764743009818086920240703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139686324013090782560320937 104764743009818086920240703)
  ·
    refine ⟨157147114514727130380361055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104764743009818086920240703 157147114514727130380361055)
    ·
      refine ⟨235720671772090695570541583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157147114514727130380361055 235720671772090695570541583)
      ·
        refine ⟨353581007658136043355812375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235720671772090695570541583 353581007658136043355812375)
        ·
          refine ⟨530371511487204065033718563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353581007658136043355812375 530371511487204065033718563)
          ·
            refine ⟨795557267230806097550577845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530371511487204065033718563 795557267230806097550577845)
            ·
              refine ⟨74583493802888071645366673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 795557267230806097550577845 74583493802888071645366673)
              ·
                refine ⟨55937620352166053734025005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74583493802888071645366673 55937620352166053734025005)
                ·
                  refine ⟨20976607632062270150259377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55937620352166053734025005 20976607632062270150259377)
                  ·
                    refine ⟨15732455724046702612694533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20976607632062270150259377 15732455724046702612694533)
                    ·
                      refine ⟨2949835448258756739880225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15732455724046702612694533 2949835448258756739880225)
                      ·
                        rfl

theorem cell23_5744784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_5744784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744784 prefixEnd_5744784 := by exact prefixLift 5744784
  have htrace : WordTrace (prefixWord ++ tailWord_5744784) baseStart_5744784 baseEnd_5744784 := by
    simpa [prefixWord, tailWord_5744784, baseEnd_5744784] using wordTrace_append hprefix tailTrace_5744784
  have hstable : (prefixWord ++ tailWord_5744784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744784).length < 2 ^ (prefixWord ++ tailWord_5744784).sum := by decide
  have hdescent : baseEnd_5744784 < baseStart_5744784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744801 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5744801 : Nat := 118140960795 + 5744801 * 2 ^ 59
def prefixEnd_5744801 : Nat := 4983230072969 + 3 ^ 40 * 5744801 * 2
def baseEnd_5744801 : Nat := 2949844177429883173367647

theorem tailTrace_5744801 : CollatzResearch.WordTrace tailWord_5744801 prefixEnd_5744801 2949844177429883173367647 := by
  unfold tailWord_5744801
  simp only [CollatzResearch.WordTrace]
  refine ⟨209530106060574585743850257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139686737373716390495900171 209530106060574585743850257)
  ·
    refine ⟨157147579545430939307887693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209530106060574585743850257 157147579545430939307887693)
    ·
      refine ⟨58930342329536602240457885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157147579545430939307887693 58930342329536602240457885)
      ·
        refine ⟨22098878373576225840171707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58930342329536602240457885 22098878373576225840171707)
        ·
          refine ⟨33148317560364338760257561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22098878373576225840171707 33148317560364338760257561)
          ·
            refine ⟨24861238170273254070193171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33148317560364338760257561 24861238170273254070193171)
            ·
              refine ⟨37291857255409881105289757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24861238170273254070193171 37291857255409881105289757)
              ·
                refine ⟨13984446470778705414483659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37291857255409881105289757 13984446470778705414483659)
                ·
                  refine ⟨20976669706168058121725489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13984446470778705414483659 20976669706168058121725489)
                  ·
                    refine ⟨15732502279626043591294117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20976669706168058121725489 15732502279626043591294117)
                    ·
                      refine ⟨2949844177429883173367647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15732502279626043591294117 2949844177429883173367647)
                      ·
                        rfl

theorem cell23_5744801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5744801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744801 prefixEnd_5744801 := by exact prefixLift 5744801
  have htrace : WordTrace (prefixWord ++ tailWord_5744801) baseStart_5744801 baseEnd_5744801 := by
    simpa [prefixWord, tailWord_5744801, baseEnd_5744801] using wordTrace_append hprefix tailTrace_5744801
  have hstable : (prefixWord ++ tailWord_5744801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744801).length < 2 ^ (prefixWord ++ tailWord_5744801).sum := by decide
  have hdescent : baseEnd_5744801 < baseStart_5744801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744865 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_5744865 : Nat := 118140960795 + 5744865 * 2 ^ 59
def prefixEnd_5744865 : Nat := 4983230072969 + 3 ^ 40 * 5744865 * 2
def baseEnd_5744865 : Nat := 2949877040191770922967353

theorem tailTrace_5744865 : CollatzResearch.WordTrace tailWord_5744865 prefixEnd_5744865 2949877040191770922967353 := by
  unfold tailWord_5744865
  simp only [CollatzResearch.WordTrace]
  refine ⟨209532440332342724674180049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139688293554895149782786699 209532440332342724674180049)
  ·
    refine ⟨157149330249257043505635037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209532440332342724674180049 157149330249257043505635037)
    ·
      refine ⟨58930998843471391314613139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157149330249257043505635037 58930998843471391314613139)
      ·
        refine ⟨88396498265207086971919709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58930998843471391314613139 88396498265207086971919709)
        ·
          refine ⟨33148686849452657614469891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88396498265207086971919709 33148686849452657614469891)
          ·
            refine ⟨49723030274178986421704837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33148686849452657614469891 49723030274178986421704837)
            ·
              refine ⟨9323068176408559954069657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49723030274178986421704837 9323068176408559954069657)
              ·
                refine ⟨6992301132306419965552243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9323068176408559954069657 6992301132306419965552243)
                ·
                  refine ⟨10488451698459629948328365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6992301132306419965552243 10488451698459629948328365)
                  ·
                    refine ⟨3933169386922361230623137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10488451698459629948328365 3933169386922361230623137)
                    ·
                      refine ⟨2949877040191770922967353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933169386922361230623137 2949877040191770922967353)
                      ·
                        rfl

theorem cell23_5744865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_5744865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744865 prefixEnd_5744865 := by exact prefixLift 5744865
  have htrace : WordTrace (prefixWord ++ tailWord_5744865) baseStart_5744865 baseEnd_5744865 := by
    simpa [prefixWord, tailWord_5744865, baseEnd_5744865] using wordTrace_append hprefix tailTrace_5744865
  have hstable : (prefixWord ++ tailWord_5744865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744865).length < 2 ^ (prefixWord ++ tailWord_5744865).sum := by decide
  have hdescent : baseEnd_5744865 < baseStart_5744865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744878 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_5744878 : Nat := 118140960795 + 5744878 * 2 ^ 59
def prefixEnd_5744878 : Nat := 4983230072969 + 3 ^ 40 * 5744878 * 2
def baseEnd_5744878 : Nat := 2949883715440279372104793

theorem tailTrace_5744878 : CollatzResearch.WordTrace tailWord_5744878 prefixEnd_5744878 2949883715440279372104793 := by
  unfold tailWord_5744878
  simp only [CollatzResearch.WordTrace]
  refine ⟨26191614310161953486800411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139688609654197085262935525 26191614310161953486800411)
  ·
    refine ⟨39287421465242930230200617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26191614310161953486800411 39287421465242930230200617)
    ·
      refine ⟨29465566098932197672650463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39287421465242930230200617 29465566098932197672650463)
      ·
        refine ⟨44198349148398296508975695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29465566098932197672650463 44198349148398296508975695)
        ·
          refine ⟨66297523722597444763463543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44198349148398296508975695 66297523722597444763463543)
          ·
            refine ⟨99446285583896167145195315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66297523722597444763463543 99446285583896167145195315)
            ·
              refine ⟨149169428375844250717792973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99446285583896167145195315 149169428375844250717792973)
              ·
                refine ⟨55938535640941594019172365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149169428375844250717792973 55938535640941594019172365)
                ·
                  refine ⟨20976950865353097757189637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55938535640941594019172365 20976950865353097757189637)
                  ·
                    refine ⟨3933178287253705829473057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20976950865353097757189637 3933178287253705829473057)
                    ·
                      refine ⟨2949883715440279372104793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933178287253705829473057 2949883715440279372104793)
                      ·
                        rfl

theorem cell23_5744878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_5744878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744878 prefixEnd_5744878 := by exact prefixLift 5744878
  have htrace : WordTrace (prefixWord ++ tailWord_5744878) baseStart_5744878 baseEnd_5744878 := by
    simpa [prefixWord, tailWord_5744878, baseEnd_5744878] using wordTrace_append hprefix tailTrace_5744878
  have hstable : (prefixWord ++ tailWord_5744878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744878).length < 2 ^ (prefixWord ++ tailWord_5744878).sum := by decide
  have hdescent : baseEnd_5744878 < baseStart_5744878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744895 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 2, 2, 2]
def baseStart_5744895 : Nat := 118140960795 + 5744895 * 2 ^ 59
def prefixEnd_5744895 : Nat := 4983230072969 + 3 ^ 40 * 5744895 * 2
def baseEnd_5744895 : Nat := 2949892444611405805592215

theorem tailTrace_5744895 : CollatzResearch.WordTrace tailWord_5744895 prefixEnd_5744895 2949892444611405805592215 := by
  unfold tailWord_5744895
  simp only [CollatzResearch.WordTrace]
  refine ⟨209533534522234039797772139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139689023014822693198514759 209533534522234039797772139)
  ·
    refine ⟨314300301783351059696658209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209533534522234039797772139 314300301783351059696658209)
    ·
      refine ⟨235725226337513294772493657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314300301783351059696658209 235725226337513294772493657)
      ·
        refine ⟨176793919753134971079370243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235725226337513294772493657 176793919753134971079370243)
        ·
          refine ⟨265190879629702456619055365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176793919753134971079370243 265190879629702456619055365)
          ·
            refine ⟨49723289930569210616072881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265190879629702456619055365 49723289930569210616072881)
            ·
              refine ⟨37292467447926907962054661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49723289930569210616072881 37292467447926907962054661)
              ·
                refine ⟨6992337646486295242885249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37292467447926907962054661 6992337646486295242885249)
                ·
                  refine ⟨5244253234864721432163937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6992337646486295242885249 5244253234864721432163937)
                  ·
                    refine ⟨3933189926148541074122953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5244253234864721432163937 3933189926148541074122953)
                    ·
                      refine ⟨2949892444611405805592215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933189926148541074122953 2949892444611405805592215)
                      ·
                        rfl

theorem cell23_5744895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_5744895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744895 prefixEnd_5744895 := by exact prefixLift 5744895
  have htrace : WordTrace (prefixWord ++ tailWord_5744895) baseStart_5744895 baseEnd_5744895 := by
    simpa [prefixWord, tailWord_5744895, baseEnd_5744895] using wordTrace_append hprefix tailTrace_5744895
  have hstable : (prefixWord ++ tailWord_5744895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744895).length < 2 ^ (prefixWord ++ tailWord_5744895).sum := by decide
  have hdescent : baseEnd_5744895 < baseStart_5744895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744911 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_5744911 : Nat := 118140960795 + 5744911 * 2 ^ 59
def prefixEnd_5744911 : Nat := 4983230072969 + 3 ^ 40 * 5744911 * 2
def baseEnd_5744911 : Nat := 2949900660301877742992141

theorem tailTrace_5744911 : CollatzResearch.WordTrace tailWord_5744911 prefixEnd_5744911 2949900660301877742992141 := by
  unfold tailWord_5744911
  simp only [CollatzResearch.WordTrace]
  refine ⟨209534118090176074530354587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139689412060117383020236391 209534118090176074530354587)
  ·
    refine ⟨314301177135264111795531881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209534118090176074530354587 314301177135264111795531881)
    ·
      refine ⟨235725882851448083846648911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314301177135264111795531881 235725882851448083846648911)
      ·
        refine ⟨353588824277172125769973367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235725882851448083846648911 353588824277172125769973367)
        ·
          refine ⟨530383236415758188654960051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353588824277172125769973367 530383236415758188654960051)
          ·
            refine ⟨795574854623637282982440077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530383236415758188654960051 795574854623637282982440077)
            ·
              refine ⟨298340570483863981118415029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795574854623637282982440077 298340570483863981118415029)
              ·
                refine ⟨27969428482862248229851409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298340570483863981118415029 27969428482862248229851409)
                ·
                  refine ⟨20977071362146686172388557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27969428482862248229851409 20977071362146686172388557)
                  ·
                    refine ⟨7866401760805007314645709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20977071362146686172388557 7866401760805007314645709)
                    ·
                      refine ⟨2949900660301877742992141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866401760805007314645709 2949900660301877742992141)
                      ·
                        rfl

theorem cell23_5744911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_5744911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744911 prefixEnd_5744911 := by exact prefixLift 5744911
  have htrace : WordTrace (prefixWord ++ tailWord_5744911) baseStart_5744911 baseEnd_5744911 := by
    simpa [prefixWord, tailWord_5744911, baseEnd_5744911] using wordTrace_append hprefix tailTrace_5744911
  have hstable : (prefixWord ++ tailWord_5744911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744911).length < 2 ^ (prefixWord ++ tailWord_5744911).sum := by decide
  have hdescent : baseEnd_5744911 < baseStart_5744911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744958 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_5744958 : Nat := 118140960795 + 5744958 * 2 ^ 59
def prefixEnd_5744958 : Nat := 4983230072969 + 3 ^ 40 * 5744958 * 2
def baseEnd_5744958 : Nat := 2949924793892639059104425

theorem tailTrace_5744958 : CollatzResearch.WordTrace tailWord_5744958 prefixEnd_5744958 2949924793892639059104425 := by
  unfold tailWord_5744958
  simp only [CollatzResearch.WordTrace]
  refine ⟨26191979040125725194664441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139690554880670534371543685 26191979040125725194664441)
  ·
    refine ⟨19643984280094293895998331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26191979040125725194664441 19643984280094293895998331)
    ·
      refine ⟨29465976420141440843997497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19643984280094293895998331 29465976420141440843997497)
      ·
        refine ⟨22099482315106080632998123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29465976420141440843997497 22099482315106080632998123)
        ·
          refine ⟨33149223472659120949497185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22099482315106080632998123 33149223472659120949497185)
          ·
            refine ⟨24861917604494340712122889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33149223472659120949497185 24861917604494340712122889)
            ·
              refine ⟨18646438203370755534092167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24861917604494340712122889 18646438203370755534092167)
              ·
                refine ⟨27969657305056133301138251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18646438203370755534092167 27969657305056133301138251)
                ·
                  refine ⟨41954485957584199951707377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27969657305056133301138251 41954485957584199951707377)
                  ·
                    refine ⟨31465864468188149963780533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41954485957584199951707377 31465864468188149963780533)
                    ·
                      refine ⟨2949924793892639059104425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31465864468188149963780533 2949924793892639059104425)
                      ·
                        rfl

theorem cell23_5744958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_5744958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744958 prefixEnd_5744958 := by exact prefixLift 5744958
  have htrace : WordTrace (prefixWord ++ tailWord_5744958) baseStart_5744958 baseEnd_5744958 := by
    simpa [prefixWord, tailWord_5744958, baseEnd_5744958] using wordTrace_append hprefix tailTrace_5744958
  have hstable : (prefixWord ++ tailWord_5744958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744958).length < 2 ^ (prefixWord ++ tailWord_5744958).sum := by decide
  have hdescent : baseEnd_5744958 < baseStart_5744958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744968 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_5744968 : Nat := 118140960795 + 5744968 * 2 ^ 59
def prefixEnd_5744968 : Nat := 4983230072969 + 3 ^ 40 * 5744968 * 2
def baseEnd_5744968 : Nat := 2949929928699184019979379

theorem tailTrace_5744968 : CollatzResearch.WordTrace tailWord_5744968 prefixEnd_5744968 2949929928699184019979379 := by
  unfold tailWord_5744968
  simp only [CollatzResearch.WordTrace]
  refine ⟨104768098525484786632589779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139690798033979715510119705 104768098525484786632589779)
  ·
    refine ⟨157152147788227179948884669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104768098525484786632589779 157152147788227179948884669)
    ·
      refine ⟨58932055420585192480831751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157152147788227179948884669 58932055420585192480831751)
      ·
        refine ⟨88398083130877788721247627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58932055420585192480831751 88398083130877788721247627)
        ·
          refine ⟨132597124696316683081871441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88398083130877788721247627 132597124696316683081871441)
          ·
            refine ⟨99447843522237512311403581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132597124696316683081871441 99447843522237512311403581)
            ·
              refine ⟨37292941320839067116776343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99447843522237512311403581 37292941320839067116776343)
              ·
                refine ⟨55939411981258600675164515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37292941320839067116776343 55939411981258600675164515)
                ·
                  refine ⟨83909117971887901012746773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55939411981258600675164515 83909117971887901012746773)
                  ·
                    refine ⟨3933239904932245359972505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83909117971887901012746773 3933239904932245359972505)
                    ·
                      refine ⟨2949929928699184019979379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933239904932245359972505 2949929928699184019979379)
                      ·
                        rfl

theorem cell23_5744968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_5744968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744968 prefixEnd_5744968 := by exact prefixLift 5744968
  have htrace : WordTrace (prefixWord ++ tailWord_5744968) baseStart_5744968 baseEnd_5744968 := by
    simpa [prefixWord, tailWord_5744968, baseEnd_5744968] using wordTrace_append hprefix tailTrace_5744968
  have hstable : (prefixWord ++ tailWord_5744968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744968).length < 2 ^ (prefixWord ++ tailWord_5744968).sum := by decide
  have hdescent : baseEnd_5744968 < baseStart_5744968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5744978 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_5744978 : Nat := 118140960795 + 5744978 * 2 ^ 59
def prefixEnd_5744978 : Nat := 4983230072969 + 3 ^ 40 * 5744978 * 2
def baseEnd_5744978 : Nat := 983311687835242993618111

theorem tailTrace_5744978 : CollatzResearch.WordTrace tailWord_5744978 prefixEnd_5744978 983311687835242993618111 := by
  unfold tailWord_5744978
  simp only [CollatzResearch.WordTrace]
  refine ⟨52384140445233336243260897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139691041187288896648695725 52384140445233336243260897)
  ·
    refine ⟨39288105333925002182445673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52384140445233336243260897 39288105333925002182445673)
    ·
      refine ⟨29466079000443751636834255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39288105333925002182445673 29466079000443751636834255)
      ·
        refine ⟨44199118500665627455251383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29466079000443751636834255 44199118500665627455251383)
        ·
          refine ⟨66298677750998441182877075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44199118500665627455251383 66298677750998441182877075)
          ·
            refine ⟨99448016626497661774315613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66298677750998441182877075 99448016626497661774315613)
            ·
              refine ⟨37293006234936623165368355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99448016626497661774315613 37293006234936623165368355)
              ·
                refine ⟨55939509352404934748052533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37293006234936623165368355 55939509352404934748052533)
                ·
                  refine ⟨5244329001787962632629925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55939509352404934748052533 5244329001787962632629925)
                  ·
                    refine ⟨983311687835242993618111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244329001787962632629925 983311687835242993618111)
                    ·
                      rfl

theorem cell23_5744978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_5744978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5744978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5744978 prefixEnd_5744978 := by exact prefixLift 5744978
  have htrace : WordTrace (prefixWord ++ tailWord_5744978) baseStart_5744978 baseEnd_5744978 := by
    simpa [prefixWord, tailWord_5744978, baseEnd_5744978] using wordTrace_append hprefix tailTrace_5744978
  have hstable : (prefixWord ++ tailWord_5744978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5744978).length < 2 ^ (prefixWord ++ tailWord_5744978).sum := by decide
  have hdescent : baseEnd_5744978 < baseStart_5744978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5744978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745008 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 6]
def baseStart_5745008 : Nat := 118140960795 + 5745008 * 2 ^ 59
def prefixEnd_5745008 : Nat := 4983230072969 + 3 ^ 40 * 5745008 * 2
def baseEnd_5745008 : Nat := 327772274213929318164355

theorem tailTrace_5745008 : CollatzResearch.WordTrace tailWord_5745008 prefixEnd_5745008 327772274213929318164355 := by
  unfold tailWord_5745008
  simp only [CollatzResearch.WordTrace]
  refine ⟨104768827985412330048317839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139691770647216440064423785 104768827985412330048317839)
  ·
    refine ⟨157153241978118495072476759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104768827985412330048317839 157153241978118495072476759)
    ·
      refine ⟨235729862967177742608715139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157153241978118495072476759 235729862967177742608715139)
      ·
        refine ⟨353594794450766613913072709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235729862967177742608715139 353594794450766613913072709)
        ·
          refine ⟨66299023959518740108701133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353594794450766613913072709 66299023959518740108701133)
          ·
            refine ⟨24862133984819527540762925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66299023959518740108701133 24862133984819527540762925)
            ·
              refine ⟨9323300244307322827786097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24862133984819527540762925 9323300244307322827786097)
              ·
                refine ⟨6992475183230492120839573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9323300244307322827786097 6992475183230492120839573)
                ·
                  refine ⟨327772274213929318164355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6992475183230492120839573 327772274213929318164355)
                  ·
                    rfl

theorem cell23_5745008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_5745008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745008 prefixEnd_5745008 := by exact prefixLift 5745008
  have htrace : WordTrace (prefixWord ++ tailWord_5745008) baseStart_5745008 baseEnd_5745008 := by
    simpa [prefixWord, tailWord_5745008, baseEnd_5745008] using wordTrace_append hprefix tailTrace_5745008
  have hstable : (prefixWord ++ tailWord_5745008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745008).length < 2 ^ (prefixWord ++ tailWord_5745008).sum := by decide
  have hdescent : baseEnd_5745008 < baseStart_5745008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745035 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 3]
def baseStart_5745035 : Nat := 118140960795 + 5745035 * 2 ^ 59
def prefixEnd_5745035 : Nat := 4983230072969 + 3 ^ 40 * 5745035 * 2
def baseEnd_5745035 : Nat := 2949964331903035257841571

theorem tailTrace_5745035 : CollatzResearch.WordTrace tailWord_5745035 prefixEnd_5745035 2949964331903035257841571 := by
  unfold tailWord_5745035
  simp only [CollatzResearch.WordTrace]
  refine ⟨209538640741726843707868559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139692427161151229138579039 209538640741726843707868559)
  ·
    refine ⟨314307961112590265561802839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209538640741726843707868559 314307961112590265561802839)
    ·
      refine ⟨471461941668885398342704259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314307961112590265561802839 471461941668885398342704259)
      ·
        refine ⟨707192912503328097514056389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471461941668885398342704259 707192912503328097514056389)
        ·
          refine ⟨132598671094374018283885573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 707192912503328097514056389 132598671094374018283885573)
          ·
            refine ⟨24862250830195128428228545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132598671094374018283885573 24862250830195128428228545)
            ·
              refine ⟨18646688122646346321171409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24862250830195128428228545 18646688122646346321171409)
              ·
                refine ⟨13985016091984759740878557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18646688122646346321171409 13985016091984759740878557)
                ·
                  refine ⟨5244381034494284902829459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13985016091984759740878557 5244381034494284902829459)
                  ·
                    refine ⟨7866571551741427354244189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5244381034494284902829459 7866571551741427354244189)
                    ·
                      refine ⟨2949964331903035257841571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866571551741427354244189 2949964331903035257841571)
                      ·
                        rfl

theorem cell23_5745035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 3].length) (baseStart_5745035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745035 prefixEnd_5745035 := by exact prefixLift 5745035
  have htrace : WordTrace (prefixWord ++ tailWord_5745035) baseStart_5745035 baseEnd_5745035 := by
    simpa [prefixWord, tailWord_5745035, baseEnd_5745035] using wordTrace_append hprefix tailTrace_5745035
  have hstable : (prefixWord ++ tailWord_5745035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745035).length < 2 ^ (prefixWord ++ tailWord_5745035).sum := by decide
  have hdescent : baseEnd_5745035 < baseStart_5745035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745045 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_5745045 : Nat := 118140960795 + 5745045 * 2 ^ 59
def prefixEnd_5745045 : Nat := 4983230072969 + 3 ^ 40 * 5745045 * 2
def baseEnd_5745045 : Nat := 2949969466709580218716525

theorem tailTrace_5745045 : CollatzResearch.WordTrace tailWord_5745045 prefixEnd_5745045 2949969466709580218716525 := by
  unfold tailWord_5745045
  simp only [CollatzResearch.WordTrace]
  refine ⟨209539005471690615415732589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139692670314460410277155059 209539005471690615415732589)
  ·
    refine ⟨78577127051883980780899721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209539005471690615415732589 78577127051883980780899721)
    ·
      refine ⟨58932845288912985585674791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78577127051883980780899721 58932845288912985585674791)
      ·
        refine ⟨88399267933369478378512187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58932845288912985585674791 88399267933369478378512187)
        ·
          refine ⟨132598901900054217567768281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88399267933369478378512187 132598901900054217567768281)
          ·
            refine ⟨99449176425040663175826211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132598901900054217567768281 99449176425040663175826211)
            ·
              refine ⟨149173764637560994763739317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99449176425040663175826211 149173764637560994763739317)
              ·
                refine ⟨13985040434771343259100561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149173764637560994763739317 13985040434771343259100561)
                ·
                  refine ⟨10488780326078507444325421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13985040434771343259100561 10488780326078507444325421)
                  ·
                    refine ⟨3933292622279440291622033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10488780326078507444325421 3933292622279440291622033)
                    ·
                      refine ⟨2949969466709580218716525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933292622279440291622033 2949969466709580218716525)
                      ·
                        rfl

theorem cell23_5745045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_5745045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745045 prefixEnd_5745045 := by exact prefixLift 5745045
  have htrace : WordTrace (prefixWord ++ tailWord_5745045) baseStart_5745045 baseEnd_5745045 := by
    simpa [prefixWord, tailWord_5745045, baseEnd_5745045] using wordTrace_append hprefix tailTrace_5745045
  have hstable : (prefixWord ++ tailWord_5745045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745045).length < 2 ^ (prefixWord ++ tailWord_5745045).sum := by decide
  have hdescent : baseEnd_5745045 < baseStart_5745045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745076 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 6]
def baseStart_5745076 : Nat := 118140960795 + 5745076 * 2 ^ 59
def prefixEnd_5745076 : Nat := 4983230072969 + 3 ^ 40 * 5745076 * 2
def baseEnd_5745076 : Nat := 327776153845541066380987

theorem tailTrace_5745076 : CollatzResearch.WordTrace tailWord_5745076 prefixEnd_5745076 327776153845541066380987 := by
  unfold tailWord_5745076
  simp only [CollatzResearch.WordTrace]
  refine ⟨104770068067289153855055541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139693424089718871806740721 104770068067289153855055541)
  ·
    refine ⟨9822193881308358173911457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104770068067289153855055541 9822193881308358173911457)
    ·
      refine ⟨7366645410981268630433593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9822193881308358173911457 7366645410981268630433593)
      ·
        refine ⟨5524984058235951472825195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7366645410981268630433593 5524984058235951472825195)
        ·
          refine ⟨8287476087353927209237793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524984058235951472825195 8287476087353927209237793)
          ·
            refine ⟨6215607065515445406928345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8287476087353927209237793 6215607065515445406928345)
            ·
              refine ⟨4661705299136584055196259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6215607065515445406928345 4661705299136584055196259)
              ·
                refine ⟨6992557948704876082794389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661705299136584055196259 6992557948704876082794389)
                ·
                  refine ⟨327776153845541066380987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6992557948704876082794389 327776153845541066380987)
                  ·
                    rfl

theorem cell23_5745076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_5745076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745076 prefixEnd_5745076 := by exact prefixLift 5745076
  have htrace : WordTrace (prefixWord ++ tailWord_5745076) baseStart_5745076 baseEnd_5745076 := by
    simpa [prefixWord, tailWord_5745076, baseEnd_5745076] using wordTrace_append hprefix tailTrace_5745076
  have hstable : (prefixWord ++ tailWord_5745076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745076).length < 2 ^ (prefixWord ++ tailWord_5745076).sum := by decide
  have hdescent : baseEnd_5745076 < baseStart_5745076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745088 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_5745088 : Nat := 118140960795 + 5745088 * 2 ^ 59
def prefixEnd_5745088 : Nat := 4983230072969 + 3 ^ 40 * 5745088 * 2
def baseEnd_5745088 : Nat := 2949991546377723550478827

theorem tailTrace_5745088 : CollatzResearch.WordTrace tailWord_5745088 prefixEnd_5745088 2949991546377723550478827 := by
  unfold tailWord_5745088
  simp only [CollatzResearch.WordTrace]
  refine ⟨104770286905267416879773959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139693715873689889173031945 104770286905267416879773959)
  ·
    refine ⟨157155430357901125319660939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104770286905267416879773959 157155430357901125319660939)
    ·
      refine ⟨235733145536851687979491409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157155430357901125319660939 235733145536851687979491409)
      ·
        refine ⟨176799859152638765984618557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235733145536851687979491409 176799859152638765984618557)
        ·
          refine ⟨66299947182239537244231959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176799859152638765984618557 66299947182239537244231959)
          ·
            refine ⟨99449920773359305866347939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66299947182239537244231959 99449920773359305866347939)
            ·
              refine ⟨149174881160038958799521909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99449920773359305866347939 149174881160038958799521909)
              ·
                refine ⟨13985145108753652387455179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149174881160038958799521909 13985145108753652387455179)
                ·
                  refine ⟨20977717663130478581182769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13985145108753652387455179 20977717663130478581182769)
                  ·
                    refine ⟨15733288247347858935887077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20977717663130478581182769 15733288247347858935887077)
                    ·
                      refine ⟨2949991546377723550478827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15733288247347858935887077 2949991546377723550478827)
                      ·
                        rfl

theorem cell23_5745088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_5745088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745088 prefixEnd_5745088 := by exact prefixLift 5745088
  have htrace : WordTrace (prefixWord ++ tailWord_5745088) baseStart_5745088 baseEnd_5745088 := by
    simpa [prefixWord, tailWord_5745088, baseEnd_5745088] using wordTrace_append hprefix tailTrace_5745088
  have hstable : (prefixWord ++ tailWord_5745088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745088).length < 2 ^ (prefixWord ++ tailWord_5745088).sum := by decide
  have hdescent : baseEnd_5745088 < baseStart_5745088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745089 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5745089 : Nat := 118140960795 + 5745089 * 2 ^ 59
def prefixEnd_5745089 : Nat := 4983230072969 + 3 ^ 40 * 5745089 * 2
def baseEnd_5745089 : Nat := 983330686619459348855441

theorem tailTrace_5745089 : CollatzResearch.WordTrace tailWord_5745089 prefixEnd_5745089 983330686619459348855441 := by
  unfold tailWord_5745089
  simp only [CollatzResearch.WordTrace]
  refine ⟨209540610283531210930334321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139693740189020807286889547 209540610283531210930334321)
  ·
    refine ⟨157155457712648408197750741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209540610283531210930334321 157155457712648408197750741)
    ·
      refine ⟨3683331040140197067134783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 157155457712648408197750741 3683331040140197067134783)
      ·
        refine ⟨5524996560210295600702175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3683331040140197067134783 5524996560210295600702175)
        ·
          refine ⟨8287494840315443401053263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524996560210295600702175 8287494840315443401053263)
          ·
            refine ⟨12431242260473165101579895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287494840315443401053263 12431242260473165101579895)
            ·
              refine ⟨18646863390709747652369843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431242260473165101579895 18646863390709747652369843)
              ·
                refine ⟨27970295086064621478554765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18646863390709747652369843 27970295086064621478554765)
                ·
                  refine ⟨10488860657274233054458037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27970295086064621478554765 10488860657274233054458037)
                  ·
                    refine ⟨983330686619459348855441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10488860657274233054458037 983330686619459348855441)
                    ·
                      rfl

theorem cell23_5745089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5745089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745089 prefixEnd_5745089 := by exact prefixLift 5745089
  have htrace : WordTrace (prefixWord ++ tailWord_5745089) baseStart_5745089 baseEnd_5745089 := by
    simpa [prefixWord, tailWord_5745089, baseEnd_5745089] using wordTrace_append hprefix tailTrace_5745089
  have hstable : (prefixWord ++ tailWord_5745089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745089).length < 2 ^ (prefixWord ++ tailWord_5745089).sum := by decide
  have hdescent : baseEnd_5745089 < baseStart_5745089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745092 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5745092 : Nat := 118140960795 + 5745092 * 2 ^ 59
def prefixEnd_5745092 : Nat := 4983230072969 + 3 ^ 40 * 5745092 * 2
def baseEnd_5745092 : Nat := 2949993600300341534828809

theorem tailTrace_5745092 : CollatzResearch.WordTrace tailWord_5745092 prefixEnd_5745092 2949993600300341534828809 := by
  unfold tailWord_5745092
  simp only [CollatzResearch.WordTrace]
  refine ⟨104770359851260171221346765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139693813135013561628462353 104770359851260171221346765)
  ·
    refine ⟨39288884944222564208005037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104770359851260171221346765 39288884944222564208005037)
    ·
      refine ⟨14733331854083461578001889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39288884944222564208005037 14733331854083461578001889)
      ·
        refine ⟨11049998890562596183501417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14733331854083461578001889 11049998890562596183501417)
        ·
          refine ⟨8287499167921947137626063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11049998890562596183501417 8287499167921947137626063)
          ·
            refine ⟨12431248751882920706439095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287499167921947137626063 12431248751882920706439095)
            ·
              refine ⟨18646873127824381059658643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431248751882920706439095 18646873127824381059658643)
              ·
                refine ⟨27970309691736571589487965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18646873127824381059658643 27970309691736571589487965)
                ·
                  refine ⟨10488866134401214346057987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27970309691736571589487965 10488866134401214346057987)
                  ·
                    refine ⟨15733299201601821519086981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10488866134401214346057987 15733299201601821519086981)
                    ·
                      refine ⟨2949993600300341534828809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15733299201601821519086981 2949993600300341534828809)
                      ·
                        rfl

theorem cell23_5745092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5745092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745092 prefixEnd_5745092 := by exact prefixLift 5745092
  have htrace : WordTrace (prefixWord ++ tailWord_5745092) baseStart_5745092 baseEnd_5745092 := by
    simpa [prefixWord, tailWord_5745092, baseEnd_5745092] using wordTrace_append hprefix tailTrace_5745092
  have hstable : (prefixWord ++ tailWord_5745092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745092).length < 2 ^ (prefixWord ++ tailWord_5745092).sum := by decide
  have hdescent : baseEnd_5745092 < baseStart_5745092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745095 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_5745095 : Nat := 118140960795 + 5745095 * 2 ^ 59
def prefixEnd_5745095 : Nat := 4983230072969 + 3 ^ 40 * 5745095 * 2
def baseEnd_5745095 : Nat := 2949995140742305023091295

theorem tailTrace_5745095 : CollatzResearch.WordTrace tailWord_5745095 prefixEnd_5745095 2949995140742305023091295 := by
  unfold tailWord_5745095
  simp only [CollatzResearch.WordTrace]
  refine ⟨209540829121509473955052739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139693886081006315970035159 209540829121509473955052739)
  ·
    refine ⟨314311243682264210932579109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209540829121509473955052739 314311243682264210932579109)
    ·
      refine ⟨58933358190424539549858583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314311243682264210932579109 58933358190424539549858583)
      ·
        refine ⟨88400037285636809324787875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58933358190424539549858583 88400037285636809324787875)
        ·
          refine ⟨132600055928455213987181813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88400037285636809324787875 132600055928455213987181813)
          ·
            refine ⟨12431255243292676311298295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132600055928455213987181813 12431255243292676311298295)
            ·
              refine ⟨18646882864939014466947443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431255243292676311298295 18646882864939014466947443)
              ·
                refine ⟨27970324297408521700421165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18646882864939014466947443 27970324297408521700421165)
                ·
                  refine ⟨10488871611528195637657937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27970324297408521700421165 10488871611528195637657937)
                  ·
                    refine ⟨7866653708646146728243453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10488871611528195637657937 7866653708646146728243453)
                    ·
                      refine ⟨2949995140742305023091295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866653708646146728243453 2949995140742305023091295)
                      ·
                        rfl

theorem cell23_5745095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_5745095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745095 prefixEnd_5745095 := by exact prefixLift 5745095
  have htrace : WordTrace (prefixWord ++ tailWord_5745095) baseStart_5745095 baseEnd_5745095 := by
    simpa [prefixWord, tailWord_5745095, baseEnd_5745095] using wordTrace_append hprefix tailTrace_5745095
  have hstable : (prefixWord ++ tailWord_5745095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745095).length < 2 ^ (prefixWord ++ tailWord_5745095).sum := by decide
  have hdescent : baseEnd_5745095 < baseStart_5745095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745128 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5745128 : Nat := 118140960795 + 5745128 * 2 ^ 59
def prefixEnd_5745128 : Nat := 4983230072969 + 3 ^ 40 * 5745128 * 2
def baseEnd_5745128 : Nat := 983337361867967797992881

theorem tailTrace_5745128 : CollatzResearch.WordTrace tailWord_5745128 prefixEnd_5745128 983337361867967797992881 := by
  unfold tailWord_5745128
  simp only [CollatzResearch.WordTrace]
  refine ⟨104771016365194960295502019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139694688486926613727336025 104771016365194960295502019)
  ·
    refine ⟨157156524547792440443253029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104771016365194960295502019 157156524547792440443253029)
    ·
      refine ⟨29466848352711082583109943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157156524547792440443253029 29466848352711082583109943)
      ·
        refine ⟨44200272529066623874664915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29466848352711082583109943 44200272529066623874664915)
        ·
          refine ⟨66300408793599935811997373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44200272529066623874664915 66300408793599935811997373)
          ·
            refine ⟨24862653297599975929499015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66300408793599935811997373 24862653297599975929499015)
            ·
              refine ⟨37293979946399963894248523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24862653297599975929499015 37293979946399963894248523)
              ·
                refine ⟨55940969919599945841372785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37293979946399963894248523 55940969919599945841372785)
                ·
                  refine ⟨41955727439699959381029589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55940969919599945841372785 41955727439699959381029589)
                  ·
                    refine ⟨983337361867967797992881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41955727439699959381029589 983337361867967797992881)
                    ·
                      rfl

theorem cell23_5745128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5745128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745128 prefixEnd_5745128 := by exact prefixLift 5745128
  have htrace : WordTrace (prefixWord ++ tailWord_5745128) baseStart_5745128 baseEnd_5745128 := by
    simpa [prefixWord, tailWord_5745128, baseEnd_5745128] using wordTrace_append hprefix tailTrace_5745128
  have hstable : (prefixWord ++ tailWord_5745128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745128).length < 2 ^ (prefixWord ++ tailWord_5745128).sum := by decide
  have hdescent : baseEnd_5745128 < baseStart_5745128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745142 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_5745142 : Nat := 118140960795 + 5745142 * 2 ^ 59
def prefixEnd_5745142 : Nat := 4983230072969 + 3 ^ 40 * 5745142 * 2
def baseEnd_5745142 : Nat := 2950019274333066339203579

theorem tailTrace_5745142 : CollatzResearch.WordTrace tailWord_5745142 prefixEnd_5745142 2950019274333066339203579 := by
  unfold tailWord_5745142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096408959521200061375855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139695028901559467321342453 13096408959521200061375855)
  ·
    refine ⟨19644613439281800092063783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13096408959521200061375855 19644613439281800092063783)
    ·
      refine ⟨29466920158922700138095675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19644613439281800092063783 29466920158922700138095675)
      ·
        refine ⟨44200380238384050207143513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29466920158922700138095675 44200380238384050207143513)
        ·
          refine ⟨33150285178788037655357635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44200380238384050207143513 33150285178788037655357635)
          ·
            refine ⟨49725427768182056483036453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33150285178788037655357635 49725427768182056483036453)
            ·
              refine ⟨9323517706534135590569335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49725427768182056483036453 9323517706534135590569335)
              ·
                refine ⟨13985276559801203385854003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9323517706534135590569335 13985276559801203385854003)
                ·
                  refine ⟨20977914839701805078781005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13985276559801203385854003 20977914839701805078781005)
                  ·
                    refine ⟨7866718064888176904542877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20977914839701805078781005 7866718064888176904542877)
                    ·
                      refine ⟨2950019274333066339203579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866718064888176904542877 2950019274333066339203579)
                      ·
                        rfl

theorem cell23_5745142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_5745142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745142 prefixEnd_5745142 := by exact prefixLift 5745142
  have htrace : WordTrace (prefixWord ++ tailWord_5745142) baseStart_5745142 baseEnd_5745142 := by
    simpa [prefixWord, tailWord_5745142, baseEnd_5745142] using wordTrace_append hprefix tailTrace_5745142
  have hstable : (prefixWord ++ tailWord_5745142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745142).length < 2 ^ (prefixWord ++ tailWord_5745142).sum := by decide
  have hdescent : baseEnd_5745142 < baseStart_5745142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745148 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_5745148 : Nat := 118140960795 + 5745148 * 2 ^ 59
def prefixEnd_5745148 : Nat := 4983230072969 + 3 ^ 40 * 5745148 * 2
def baseEnd_5745148 : Nat := 2950022355216993315728551

theorem tailTrace_5745148 : CollatzResearch.WordTrace tailWord_5745148 prefixEnd_5745148 2950022355216993315728551 := by
  unfold tailWord_5745148
  simp only [CollatzResearch.WordTrace]
  refine ⟨104771381095158732003366049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139695174793544976004488065 104771381095158732003366049)
  ·
    refine ⟨78578535821369049002524537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104771381095158732003366049 78578535821369049002524537)
    ·
      refine ⟨58933901866026786751893403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78578535821369049002524537 58933901866026786751893403)
      ·
        refine ⟨88400852799040180127840105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58933901866026786751893403 88400852799040180127840105)
        ·
          refine ⟨66300639599280135095880079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88400852799040180127840105 66300639599280135095880079)
          ·
            refine ⟨99450959398920202643820119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66300639599280135095880079 99450959398920202643820119)
            ·
              refine ⟨149176439098380303965730179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99450959398920202643820119 149176439098380303965730179)
              ·
                refine ⟨223764658647570455948595269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149176439098380303965730179 223764658647570455948595269)
                ·
                  refine ⟨41955873496419460490361613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223764658647570455948595269 41955873496419460490361613)
                  ·
                    refine ⟨15733452561157297683885605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41955873496419460490361613 15733452561157297683885605)
                    ·
                      refine ⟨2950022355216993315728551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15733452561157297683885605 2950022355216993315728551)
                      ·
                        rfl

theorem cell23_5745148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_5745148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745148 prefixEnd_5745148 := by exact prefixLift 5745148
  have htrace : WordTrace (prefixWord ++ tailWord_5745148) baseStart_5745148 baseEnd_5745148 := by
    simpa [prefixWord, tailWord_5745148, baseEnd_5745148] using wordTrace_append hprefix tailTrace_5745148
  have hstable : (prefixWord ++ tailWord_5745148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745148).length < 2 ^ (prefixWord ++ tailWord_5745148).sum := by decide
  have hdescent : baseEnd_5745148 < baseStart_5745148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745225 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 7, 2]
def baseStart_5745225 : Nat := 118140960795 + 5745225 * 2 ^ 59
def prefixEnd_5745225 : Nat := 4983230072969 + 3 ^ 40 * 5745225 * 2
def baseEnd_5745225 : Nat := 2950061893227389514465697

theorem tailTrace_5745225 : CollatzResearch.WordTrace tailWord_5745225 prefixEnd_5745225 2950061893227389514465697 := by
  unfold tailWord_5745225
  simp only [CollatzResearch.WordTrace]
  refine ⟨209545570611038506157285129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139697047074025670771523419 209545570611038506157285129)
  ·
    refine ⟨157159177958278879617963847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209545570611038506157285129 157159177958278879617963847)
    ·
      refine ⟨235738766937418319426945771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157159177958278879617963847 235738766937418319426945771)
      ·
        refine ⟨353608150406127479140418657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235738766937418319426945771 353608150406127479140418657)
        ·
          refine ⟨265206112804595609355313993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353608150406127479140418657 265206112804595609355313993)
          ·
            refine ⟨198904584603446707016485495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265206112804595609355313993 198904584603446707016485495)
            ·
              refine ⟨298356876905170060524728243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198904584603446707016485495 298356876905170060524728243)
              ·
                refine ⟨447535315357755090787092365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298356876905170060524728243 447535315357755090787092365)
                ·
                  refine ⟨167825743259158159045159637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447535315357755090787092365 167825743259158159045159637)
                  ·
                    refine ⟨3933415857636519352620929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167825743259158159045159637 3933415857636519352620929)
                    ·
                      refine ⟨2950061893227389514465697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933415857636519352620929 2950061893227389514465697)
                      ·
                        rfl

theorem cell23_5745225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 7, 2].length) (baseStart_5745225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745225 prefixEnd_5745225 := by exact prefixLift 5745225
  have htrace : WordTrace (prefixWord ++ tailWord_5745225) baseStart_5745225 baseEnd_5745225 := by
    simpa [prefixWord, tailWord_5745225, baseEnd_5745225] using wordTrace_append hprefix tailTrace_5745225
  have hstable : (prefixWord ++ tailWord_5745225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745225).length < 2 ^ (prefixWord ++ tailWord_5745225).sum := by decide
  have hdescent : baseEnd_5745225 < baseStart_5745225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745255 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_5745255 : Nat := 118140960795 + 5745255 * 2 ^ 59
def prefixEnd_5745255 : Nat := 4983230072969 + 3 ^ 40 * 5745255 * 2
def baseEnd_5745255 : Nat := 2950077297647024397090559

theorem tailTrace_5745255 : CollatzResearch.WordTrace tailWord_5745255 prefixEnd_5745255 2950077297647024397090559 := by
  unfold tailWord_5745255
  simp only [CollatzResearch.WordTrace]
  refine ⟨209546664800929821280877219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139697776533953214187251479 209546664800929821280877219)
  ·
    refine ⟨314319997201394731921315829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209546664800929821280877219 314319997201394731921315829)
    ·
      refine ⟨29467499737630756117623359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314319997201394731921315829 29467499737630756117623359)
      ·
        refine ⟨44201249606446134176435039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29467499737630756117623359 44201249606446134176435039)
        ·
          refine ⟨66301874409669201264652559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44201249606446134176435039 66301874409669201264652559)
          ·
            refine ⟨99452811614503801896978839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66301874409669201264652559 99452811614503801896978839)
            ·
              refine ⟨149179217421755702845468259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99452811614503801896978839 149179217421755702845468259)
              ·
                refine ⟨223768826132633554268202389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149179217421755702845468259 223768826132633554268202389)
                ·
                  refine ⟨10489163724967197856321987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223768826132633554268202389 10489163724967197856321987)
                  ·
                    refine ⟨15733745587450796784482981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10489163724967197856321987 15733745587450796784482981)
                    ·
                      refine ⟨2950077297647024397090559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15733745587450796784482981 2950077297647024397090559)
                      ·
                        rfl

theorem cell23_5745255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_5745255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745255 prefixEnd_5745255 := by exact prefixLift 5745255
  have htrace : WordTrace (prefixWord ++ tailWord_5745255) baseStart_5745255 baseEnd_5745255 := by
    simpa [prefixWord, tailWord_5745255, baseEnd_5745255] using wordTrace_append hprefix tailTrace_5745255
  have hstable : (prefixWord ++ tailWord_5745255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745255).length < 2 ^ (prefixWord ++ tailWord_5745255).sum := by decide
  have hdescent : baseEnd_5745255 < baseStart_5745255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745269 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_5745269 : Nat := 118140960795 + 5745269 * 2 ^ 59
def prefixEnd_5745269 : Nat := 4983230072969 + 3 ^ 40 * 5745269 * 2
def baseEnd_5745269 : Nat := 983361495458729114105165

theorem tailTrace_5745269 : CollatzResearch.WordTrace tailWord_5745269 prefixEnd_5745269 983361495458729114105165 := by
  unfold tailWord_5745269
  simp only [CollatzResearch.WordTrace]
  refine ⟨209547175422879101671886861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139698116948586067781257907 209547175422879101671886861)
  ·
    refine ⟨78580190783579663126957573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209547175422879101671886861 78580190783579663126957573)
    ·
      refine ⟨14733785771921186836304545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78580190783579663126957573 14733785771921186836304545)
      ·
        refine ⟨11050339328940890127228409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14733785771921186836304545 11050339328940890127228409)
        ·
          refine ⟨8287754496705667595421307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11050339328940890127228409 8287754496705667595421307)
          ·
            refine ⟨12431631745058501393131961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287754496705667595421307 12431631745058501393131961)
            ·
              refine ⟨9323723808793876044848971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12431631745058501393131961 9323723808793876044848971)
              ·
                refine ⟨13985585713190814067273457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9323723808793876044848971 13985585713190814067273457)
                ·
                  refine ⟨10489189284893110550455093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13985585713190814067273457 10489189284893110550455093)
                  ·
                    refine ⟨983361495458729114105165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10489189284893110550455093 983361495458729114105165)
                    ·
                      rfl

theorem cell23_5745269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_5745269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745269 prefixEnd_5745269 := by exact prefixLift 5745269
  have htrace : WordTrace (prefixWord ++ tailWord_5745269) baseStart_5745269 baseEnd_5745269 := by
    simpa [prefixWord, tailWord_5745269, baseEnd_5745269] using wordTrace_append hprefix tailTrace_5745269
  have hstable : (prefixWord ++ tailWord_5745269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745269).length < 2 ^ (prefixWord ++ tailWord_5745269).sum := by decide
  have hdescent : baseEnd_5745269 < baseStart_5745269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745306 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5745306 : Nat := 118140960795 + 5745306 * 2 ^ 59
def prefixEnd_5745306 : Nat := 4983230072969 + 3 ^ 40 * 5745306 * 2
def baseEnd_5745306 : Nat := 2950103485160403697552825

theorem tailTrace_5745306 : CollatzResearch.WordTrace tailWord_5745306 prefixEnd_5745306 2950103485160403697552825 := by
  unfold tailWord_5745306
  simp only [CollatzResearch.WordTrace]
  refine ⟨52387131230936264247745943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139699016615830037993989181 52387131230936264247745943)
  ·
    refine ⟨78580696846404396371618915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52387131230936264247745943 78580696846404396371618915)
    ·
      refine ⟨117871045269606594557428373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78580696846404396371618915 117871045269606594557428373)
      ·
        refine ⟨5525205247012809119879455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117871045269606594557428373 5525205247012809119879455)
        ·
          refine ⟨8287807870519213679819183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525205247012809119879455 8287807870519213679819183)
          ·
            refine ⟨12431711805778820519728775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287807870519213679819183 12431711805778820519728775)
            ·
              refine ⟨18647567708668230779593163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431711805778820519728775 18647567708668230779593163)
              ·
                refine ⟨27971351563002346169389745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18647567708668230779593163 27971351563002346169389745)
                ·
                  refine ⟨20978513672251759627042309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27971351563002346169389745 20978513672251759627042309)
                  ·
                    refine ⟨3933471313547204930070433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20978513672251759627042309 3933471313547204930070433)
                    ·
                      refine ⟨2950103485160403697552825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933471313547204930070433 2950103485160403697552825)
                      ·
                        rfl

theorem cell23_5745306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5745306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745306 prefixEnd_5745306 := by exact prefixLift 5745306
  have htrace : WordTrace (prefixWord ++ tailWord_5745306) baseStart_5745306 baseEnd_5745306 := by
    simpa [prefixWord, tailWord_5745306, baseEnd_5745306] using wordTrace_append hprefix tailTrace_5745306
  have hstable : (prefixWord ++ tailWord_5745306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745306).length < 2 ^ (prefixWord ++ tailWord_5745306).sum := by decide
  have hdescent : baseEnd_5745306 < baseStart_5745306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745326 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5745326 : Nat := 118140960795 + 5745326 * 2 ^ 59
def prefixEnd_5745326 : Nat := 4983230072969 + 3 ^ 40 * 5745326 * 2
def baseEnd_5745326 : Nat := 2950113754773493619302733

theorem tailTrace_5745326 : CollatzResearch.WordTrace tailWord_5745326 prefixEnd_5745326 2950113754773493619302733 := by
  unfold tailWord_5745326
  simp only [CollatzResearch.WordTrace]
  refine ⟨26193656797959075050838979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139699502922448400271141221 26193656797959075050838979)
  ·
    refine ⟨39290485196938612576258469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26193656797959075050838979 39290485196938612576258469)
    ·
      refine ⟨7366965974425989858048463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39290485196938612576258469 7366965974425989858048463)
      ·
        refine ⟨11050448961638984787072695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7366965974425989858048463 11050448961638984787072695)
        ·
          refine ⟨16575673442458477180609043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050448961638984787072695 16575673442458477180609043)
          ·
            refine ⟨24863510163687715770913565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16575673442458477180609043 24863510163687715770913565)
            ·
              refine ⟨9323816311382893414092587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24863510163687715770913565 9323816311382893414092587)
              ·
                refine ⟨13985724467074340121138881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9323816311382893414092587 13985724467074340121138881)
                ·
                  refine ⟨10489293350305755090854161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13985724467074340121138881 10489293350305755090854161)
                  ·
                    refine ⟨7866970012729316318140621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10489293350305755090854161 7866970012729316318140621)
                    ·
                      refine ⟨2950113754773493619302733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7866970012729316318140621 2950113754773493619302733)
                      ·
                        rfl

theorem cell23_5745326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5745326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745326 prefixEnd_5745326 := by exact prefixLift 5745326
  have htrace : WordTrace (prefixWord ++ tailWord_5745326) baseStart_5745326 baseEnd_5745326 := by
    simpa [prefixWord, tailWord_5745326, baseEnd_5745326] using wordTrace_append hprefix tailTrace_5745326
  have hstable : (prefixWord ++ tailWord_5745326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745326).length < 2 ^ (prefixWord ++ tailWord_5745326).sum := by decide
  have hdescent : baseEnd_5745326 < baseStart_5745326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745356 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5745356 : Nat := 118140960795 + 5745356 * 2 ^ 59
def prefixEnd_5745356 : Nat := 4983230072969 + 3 ^ 40 * 5745356 * 2
def baseEnd_5745356 : Nat := 2950129159193128501927595

theorem tailTrace_5745356 : CollatzResearch.WordTrace tailWord_5745356 prefixEnd_5745356 2950129159193128501927595 := by
  unfold tailWord_5745356
  simp only [CollatzResearch.WordTrace]
  refine ⟨104775174286781957765151961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139700232382375943686869281 104775174286781957765151961)
  ·
    refine ⟨78581380715086468323863971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104775174286781957765151961 78581380715086468323863971)
    ·
      refine ⟨117872071072629702485795957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78581380715086468323863971 117872071072629702485795957)
      ·
        refine ⟨11050506663059034608043371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117872071072629702485795957 11050506663059034608043371)
        ·
          refine ⟨16575759994588551912065057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050506663059034608043371 16575759994588551912065057)
          ·
            refine ⟨12431819995941413934048793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16575759994588551912065057 12431819995941413934048793)
            ·
              refine ⟨9323864996956060450536595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12431819995941413934048793 9323864996956060450536595)
              ·
                refine ⟨13985797495434090675804893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9323864996956060450536595 13985797495434090675804893)
                ·
                  refine ⟨5244674060787784003426835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13985797495434090675804893 5244674060787784003426835)
                  ·
                    refine ⟨7867011091181676005140253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5244674060787784003426835 7867011091181676005140253)
                    ·
                      refine ⟨2950129159193128501927595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7867011091181676005140253 2950129159193128501927595)
                      ·
                        rfl

theorem cell23_5745356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5745356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745356 prefixEnd_5745356 := by exact prefixLift 5745356
  have htrace : WordTrace (prefixWord ++ tailWord_5745356) baseStart_5745356 baseEnd_5745356 := by
    simpa [prefixWord, tailWord_5745356, baseEnd_5745356] using wordTrace_append hprefix tailTrace_5745356
  have hstable : (prefixWord ++ tailWord_5745356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745356).length < 2 ^ (prefixWord ++ tailWord_5745356).sum := by decide
  have hdescent : baseEnd_5745356 < baseStart_5745356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745379 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5745379 : Nat := 118140960795 + 5745379 * 2 ^ 59
def prefixEnd_5745379 : Nat := 4983230072969 + 3 ^ 40 * 5745379 * 2
def baseEnd_5745379 : Nat := 2950140969248181911939989

theorem tailTrace_5745379 : CollatzResearch.WordTrace tailWord_5745379 prefixEnd_5745379 2950140969248181911939989 := by
  unfold tailWord_5745379
  simp only [CollatzResearch.WordTrace]
  refine ⟨209551187452480590458391191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139700791634987060305594127 209551187452480590458391191)
  ·
    refine ⟨314326781178720885687586787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209551187452480590458391191 314326781178720885687586787)
    ·
      refine ⟨471490171768081328531380181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314326781178720885687586787 471490171768081328531380181)
      ·
        refine ⟨11050550900814406137454223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 471490171768081328531380181 11050550900814406137454223)
        ·
          refine ⟨16575826351221609206181335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050550900814406137454223 16575826351221609206181335)
          ·
            refine ⟨24863739526832413809272003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16575826351221609206181335 24863739526832413809272003)
            ·
              refine ⟨37295609290248620713908005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24863739526832413809272003 37295609290248620713908005)
              ·
                refine ⟨6992926741921616383857751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37295609290248620713908005 6992926741921616383857751)
                ·
                  refine ⟨10489390112882424575786627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6992926741921616383857751 10489390112882424575786627)
                  ·
                    refine ⟨15734085169323636863679941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10489390112882424575786627 15734085169323636863679941)
                    ·
                      refine ⟨2950140969248181911939989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15734085169323636863679941 2950140969248181911939989)
                      ·
                        rfl

theorem cell23_5745379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5745379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745379 prefixEnd_5745379 := by exact prefixLift 5745379
  have htrace : WordTrace (prefixWord ++ tailWord_5745379) baseStart_5745379 baseEnd_5745379 := by
    simpa [prefixWord, tailWord_5745379, baseEnd_5745379] using wordTrace_append hprefix tailTrace_5745379
  have hstable : (prefixWord ++ tailWord_5745379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745379).length < 2 ^ (prefixWord ++ tailWord_5745379).sum := by decide
  have hdescent : baseEnd_5745379 < baseStart_5745379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745450 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5745450 : Nat := 118140960795 + 5745450 * 2 ^ 59
def prefixEnd_5745450 : Nat := 4983230072969 + 3 ^ 40 * 5745450 * 2
def baseEnd_5745450 : Nat := 2950177426374651134152163

theorem tailTrace_5745450 : CollatzResearch.WordTrace tailWord_5745450 prefixEnd_5745450 2950177426374651134152163 := by
  unfold tailWord_5745450
  simp only [CollatzResearch.WordTrace]
  refine ⟨52388444258805842396056451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139702518023482246389483869 52388444258805842396056451)
  ·
    refine ⟨78582666388208763594084677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52388444258805842396056451 78582666388208763594084677)
    ·
      refine ⟨14734249947789143173890877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78582666388208763594084677 14734249947789143173890877)
      ·
        refine ⟨5525343730420928690209079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14734249947789143173890877 5525343730420928690209079)
        ·
          refine ⟨8288015595631393035313619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525343730420928690209079 8288015595631393035313619)
          ·
            refine ⟨12432023393447089552970429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8288015595631393035313619 12432023393447089552970429)
            ·
              refine ⟨4662008772542658582363911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12432023393447089552970429 4662008772542658582363911)
              ·
                refine ⟨6993013158813987873545867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662008772542658582363911 6993013158813987873545867)
                ·
                  refine ⟨10489519738220981810318801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6993013158813987873545867 10489519738220981810318801)
                  ·
                    refine ⟨7867139803665736357739101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10489519738220981810318801 7867139803665736357739101)
                    ·
                      refine ⟨2950177426374651134152163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7867139803665736357739101 2950177426374651134152163)
                      ·
                        rfl

theorem cell23_5745450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5745450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745450 prefixEnd_5745450 := by exact prefixLift 5745450
  have htrace : WordTrace (prefixWord ++ tailWord_5745450) baseStart_5745450 baseEnd_5745450 := by
    simpa [prefixWord, tailWord_5745450, baseEnd_5745450] using wordTrace_append hprefix tailTrace_5745450
  have hstable : (prefixWord ++ tailWord_5745450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745450).length < 2 ^ (prefixWord ++ tailWord_5745450).sum := by decide
  have hdescent : baseEnd_5745450 < baseStart_5745450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745509 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 5]
def baseStart_5745509 : Nat := 118140960795 + 5745509 * 2 ^ 59
def prefixEnd_5745509 : Nat := 4983230072969 + 3 ^ 40 * 5745509 * 2
def baseEnd_5745509 : Nat := 327800857970362933701599

theorem tailTrace_5745509 : CollatzResearch.WordTrace tailWord_5745509 prefixEnd_5745509 327800857970362933701599 := by
  unfold tailWord_5745509
  simp only [CollatzResearch.WordTrace]
  refine ⟨209555928942009622660623581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139703952628006415107082387 209555928942009622660623581)
  ·
    refine ⟨78583473353253608497733843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209555928942009622660623581 78583473353253608497733843)
    ·
      refine ⟨117875210029880412746600765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78583473353253608497733843 117875210029880412746600765)
      ·
        refine ⟨44203203761205154779975287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117875210029880412746600765 44203203761205154779975287)
        ·
          refine ⟨66304805641807732169962931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44203203761205154779975287 66304805641807732169962931)
          ·
            refine ⟨99457208462711598254944397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66304805641807732169962931 99457208462711598254944397)
            ·
              refine ⟨37296453173516849345604149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99457208462711598254944397 37296453173516849345604149)
              ·
                refine ⟨3496542485017204626150389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37296453173516849345604149 3496542485017204626150389)
                ·
                  refine ⟨327800857970362933701599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3496542485017204626150389 327800857970362933701599)
                  ·
                    rfl

theorem cell23_5745509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_5745509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745509 prefixEnd_5745509 := by exact prefixLift 5745509
  have htrace : WordTrace (prefixWord ++ tailWord_5745509) baseStart_5745509 baseEnd_5745509 := by
    simpa [prefixWord, tailWord_5745509, baseEnd_5745509] using wordTrace_append hprefix tailTrace_5745509
  have hstable : (prefixWord ++ tailWord_5745509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745509).length < 2 ^ (prefixWord ++ tailWord_5745509).sum := by decide
  have hdescent : baseEnd_5745509 < baseStart_5745509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745526 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_5745526 : Nat := 118140960795 + 5745526 * 2 ^ 59
def prefixEnd_5745526 : Nat := 4983230072969 + 3 ^ 40 * 5745526 * 2
def baseEnd_5745526 : Nat := 327801827878265870755757

theorem tailTrace_5745526 : CollatzResearch.WordTrace tailWord_5745526 prefixEnd_5745526 327801827878265870755757 := by
  unfold tailWord_5745526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097284311434252160249527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139704365988632023042661621 13097284311434252160249527)
  ·
    refine ⟨19645926467151378240374291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13097284311434252160249527 19645926467151378240374291)
    ·
      refine ⟨29468889700727067360561437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19645926467151378240374291 29468889700727067360561437)
      ·
        refine ⟨11050833637772650260210539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29468889700727067360561437 11050833637772650260210539)
        ·
          refine ⟨16576250456658975390315809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050833637772650260210539 16576250456658975390315809)
          ·
            refine ⟨12432187842494231542736857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16576250456658975390315809 12432187842494231542736857)
            ·
              refine ⟨9324140881870673657052643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12432187842494231542736857 9324140881870673657052643)
              ·
                refine ⟨13986211322806010485578965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9324140881870673657052643 13986211322806010485578965)
                ·
                  refine ⟨327801827878265870755757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13986211322806010485578965 327801827878265870755757)
                  ·
                    rfl

theorem cell23_5745526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_5745526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745526 prefixEnd_5745526 := by exact prefixLift 5745526
  have htrace : WordTrace (prefixWord ++ tailWord_5745526) baseStart_5745526 baseEnd_5745526 := by
    simpa [prefixWord, tailWord_5745526, baseEnd_5745526] using wordTrace_append hprefix tailTrace_5745526
  have hstable : (prefixWord ++ tailWord_5745526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745526).length < 2 ^ (prefixWord ++ tailWord_5745526).sum := by decide
  have hdescent : baseEnd_5745526 < baseStart_5745526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745532 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_5745532 : Nat := 118140960795 + 5745532 * 2 ^ 59
def prefixEnd_5745532 : Nat := 4983230072969 + 3 ^ 40 * 5745532 * 2
def baseEnd_5745532 : Nat := 2950219531788319813326785

theorem tailTrace_5745532 : CollatzResearch.WordTrace tailWord_5745532 prefixEnd_5745532 2950219531788319813326785 := by
  unfold tailWord_5745532
  simp only [CollatzResearch.WordTrace]
  refine ⟨104778383910463148794355425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139704511880617531725807233 104778383910463148794355425)
  ·
    refine ⟨78583787932847361595766569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104778383910463148794355425 78583787932847361595766569)
    ·
      refine ⟨58937840949635521196824927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78583787932847361595766569 58937840949635521196824927)
      ·
        refine ⟨88406761424453281795237391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58937840949635521196824927 88406761424453281795237391)
        ·
          refine ⟨132610142136679922692856087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88406761424453281795237391 132610142136679922692856087)
          ·
            refine ⟨198915213205019884039284131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132610142136679922692856087 198915213205019884039284131)
            ·
              refine ⟨298372819807529826058926197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198915213205019884039284131 298372819807529826058926197)
              ·
                refine ⟨27972451856955921193024331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298372819807529826058926197 27972451856955921193024331)
                ·
                  refine ⟨41958677785433881789536497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27972451856955921193024331 41958677785433881789536497)
                  ·
                    refine ⟨31469008339075411342152373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41958677785433881789536497 31469008339075411342152373)
                    ·
                      refine ⟨2950219531788319813326785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31469008339075411342152373 2950219531788319813326785)
                      ·
                        rfl

theorem cell23_5745532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_5745532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745532 prefixEnd_5745532 := by exact prefixLift 5745532
  have htrace : WordTrace (prefixWord ++ tailWord_5745532) baseStart_5745532 baseEnd_5745532 := by
    simpa [prefixWord, tailWord_5745532, baseEnd_5745532] using wordTrace_append hprefix tailTrace_5745532
  have hstable : (prefixWord ++ tailWord_5745532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745532).length < 2 ^ (prefixWord ++ tailWord_5745532).sum := by decide
  have hdescent : baseEnd_5745532 < baseStart_5745532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745559 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_5745559 : Nat := 118140960795 + 5745559 * 2 ^ 59
def prefixEnd_5745559 : Nat := 4983230072969 + 3 ^ 40 * 5745559 * 2
def baseEnd_5745559 : Nat := 2950233395765991207689161

theorem tailTrace_5745559 : CollatzResearch.WordTrace tailWord_5745559 prefixEnd_5745559 2950233395765991207689161 := by
  unfold tailWord_5745559
  simp only [CollatzResearch.WordTrace]
  refine ⟨209557752591828481199943731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139705168394552320799962487 209557752591828481199943731)
  ·
    refine ⟨314336628887742721799915597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209557752591828481199943731 314336628887742721799915597)
    ·
      refine ⟨117876235832903520674968349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314336628887742721799915597 117876235832903520674968349)
      ·
        refine ⟨44203588437338820253113131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117876235832903520674968349 44203588437338820253113131)
        ·
          refine ⟨66305382656008230379669697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44203588437338820253113131 66305382656008230379669697)
          ·
            refine ⟨49729036992006172784752273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66305382656008230379669697 49729036992006172784752273)
            ·
              refine ⟨37296777744004629588564205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49729036992006172784752273 37296777744004629588564205)
              ·
                refine ⟨13986291654001736095711577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37296777744004629588564205 13986291654001736095711577)
                ·
                  refine ⟨10489718740501302071783683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13986291654001736095711577 10489718740501302071783683)
                  ·
                    refine ⟨15734578110751953107675525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10489718740501302071783683 15734578110751953107675525)
                    ·
                      refine ⟨2950233395765991207689161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15734578110751953107675525 2950233395765991207689161)
                      ·
                        rfl

theorem cell23_5745559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_5745559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745559 prefixEnd_5745559 := by exact prefixLift 5745559
  have htrace : WordTrace (prefixWord ++ tailWord_5745559) baseStart_5745559 baseEnd_5745559 := by
    simpa [prefixWord, tailWord_5745559, baseEnd_5745559] using wordTrace_append hprefix tailTrace_5745559
  have hstable : (prefixWord ++ tailWord_5745559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745559).length < 2 ^ (prefixWord ++ tailWord_5745559).sum := by decide
  have hdescent : baseEnd_5745559 < baseStart_5745559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745579 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 3]
def baseStart_5745579 : Nat := 118140960795 + 5745579 * 2 ^ 59
def prefixEnd_5745579 : Nat := 4983230072969 + 3 ^ 40 * 5745579 * 2
def baseEnd_5745579 : Nat := 2950243665379081129439069

theorem tailTrace_5745579 : CollatzResearch.WordTrace tailWord_5745579 prefixEnd_5745579 2950243665379081129439069 := by
  unfold tailWord_5745579
  simp only [CollatzResearch.WordTrace]
  refine ⟨209558482051756024615671791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139705654701170683077114527 209558482051756024615671791)
  ·
    refine ⟨314337723077634036923507687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209558482051756024615671791 314337723077634036923507687)
    ·
      refine ⟨471506584616451055385261531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314337723077634036923507687 471506584616451055385261531)
      ·
        refine ⟨707259876924676583077892297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471506584616451055385261531 707259876924676583077892297)
        ·
          refine ⟨530444907693507437308419223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707259876924676583077892297 530444907693507437308419223)
          ·
            refine ⟨795667361540261155962628835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530444907693507437308419223 795667361540261155962628835)
            ·
              refine ⟨1193501042310391733943943253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795667361540261155962628835 1193501042310391733943943253)
              ·
                refine ⟨13986340339574903132155585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1193501042310391733943943253 13986340339574903132155585)
                ·
                  refine ⟨10489755254681177349116689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13986340339574903132155585 10489755254681177349116689)
                  ·
                    refine ⟨7867316441010883011837517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10489755254681177349116689 7867316441010883011837517)
                    ·
                      refine ⟨2950243665379081129439069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7867316441010883011837517 2950243665379081129439069)
                      ·
                        rfl

theorem cell23_5745579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 3].length) (baseStart_5745579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745579 prefixEnd_5745579 := by exact prefixLift 5745579
  have htrace : WordTrace (prefixWord ++ tailWord_5745579) baseStart_5745579 baseEnd_5745579 := by
    simpa [prefixWord, tailWord_5745579, baseEnd_5745579] using wordTrace_append hprefix tailTrace_5745579
  have hstable : (prefixWord ++ tailWord_5745579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745579).length < 2 ^ (prefixWord ++ tailWord_5745579).sum := by decide
  have hdescent : baseEnd_5745579 < baseStart_5745579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745636 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_5745636 : Nat := 118140960795 + 5745636 * 2 ^ 59
def prefixEnd_5745636 : Nat := 4983230072969 + 3 ^ 40 * 5745636 * 2
def baseEnd_5745636 : Nat := 2950272933776387406426307

theorem tailTrace_5745636 : CollatzResearch.WordTrace tailWord_5745636 prefixEnd_5745636 2950272933776387406426307 := by
  unfold tailWord_5745636
  simp only [CollatzResearch.WordTrace]
  refine ⟨104780280506274761675248381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139707040675033015566997841 104780280506274761675248381)
  ·
    refine ⟨39292605189853035628218143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104780280506274761675248381 39292605189853035628218143)
    ·
      refine ⟨58938907784779553442327215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39292605189853035628218143 58938907784779553442327215)
      ·
        refine ⟨88408361677169330163490823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58938907784779553442327215 88408361677169330163490823)
        ·
          refine ⟨132612542515753995245236235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88408361677169330163490823 132612542515753995245236235)
          ·
            refine ⟨198918813773630992867854353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132612542515753995245236235 198918813773630992867854353)
            ·
              refine ⟨149189110330223244650890765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198918813773630992867854353 149189110330223244650890765)
              ·
                refine ⟨55945916373833716744084037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149189110330223244650890765 55945916373833716744084037)
                ·
                  refine ⟨10489859320093821889515757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55945916373833716744084037 10489859320093821889515757)
                  ·
                    refine ⟨3933697245035183208568409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10489859320093821889515757 3933697245035183208568409)
                    ·
                      refine ⟨2950272933776387406426307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933697245035183208568409 2950272933776387406426307)
                      ·
                        rfl

theorem cell23_5745636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_5745636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745636 prefixEnd_5745636 := by exact prefixLift 5745636
  have htrace : WordTrace (prefixWord ++ tailWord_5745636) baseStart_5745636 baseEnd_5745636 := by
    simpa [prefixWord, tailWord_5745636, baseEnd_5745636] using wordTrace_append hprefix tailTrace_5745636
  have hstable : (prefixWord ++ tailWord_5745636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745636).length < 2 ^ (prefixWord ++ tailWord_5745636).sum := by decide
  have hdescent : baseEnd_5745636 < baseStart_5745636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745659 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 6, 4]
def baseStart_5745659 : Nat := 118140960795 + 5745659 * 2 ^ 59
def prefixEnd_5745659 : Nat := 4983230072969 + 3 ^ 40 * 5745659 * 2
def baseEnd_5745659 : Nat := 983428247943813605479567

theorem tailTrace_5745659 : CollatzResearch.WordTrace tailWord_5745659 prefixEnd_5745659 983428247943813605479567 := by
  unfold tailWord_5745659
  simp only [CollatzResearch.WordTrace]
  refine ⟨209561399891466198278584031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139707599927644132185722687 209561399891466198278584031)
  ·
    refine ⟨314342099837199297417876047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209561399891466198278584031 314342099837199297417876047)
    ·
      refine ⟨471513149755798946126814071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314342099837199297417876047 471513149755798946126814071)
      ·
        refine ⟨707269724633698419190221107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471513149755798946126814071 707269724633698419190221107)
        ·
          refine ⟨1060904586950547628785331661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707269724633698419190221107 1060904586950547628785331661)
          ·
            refine ⟨397839220106455360794499373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060904586950547628785331661 397839220106455360794499373)
            ·
              refine ⟨149189707539920760297937265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397839220106455360794499373 149189707539920760297937265)
              ·
                refine ⟨111892280654940570223452949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149189707539920760297937265 111892280654940570223452949)
                ·
                  refine ⟨5244950655700339229224357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111892280654940570223452949 5244950655700339229224357)
                  ·
                    refine ⟨983428247943813605479567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244950655700339229224357 983428247943813605479567)
                    ·
                      rfl

theorem cell23_5745659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 4].length) (baseStart_5745659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745659 prefixEnd_5745659 := by exact prefixLift 5745659
  have htrace : WordTrace (prefixWord ++ tailWord_5745659) baseStart_5745659 baseEnd_5745659 := by
    simpa [prefixWord, tailWord_5745659, baseEnd_5745659] using wordTrace_append hprefix tailTrace_5745659
  have hstable : (prefixWord ++ tailWord_5745659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745659).length < 2 ^ (prefixWord ++ tailWord_5745659).sum := by decide
  have hdescent : baseEnd_5745659 < baseStart_5745659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745693 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_5745693 : Nat := 118140960795 + 5745693 * 2 ^ 59
def prefixEnd_5745693 : Nat := 4983230072969 + 3 ^ 40 * 5745693 * 2
def baseEnd_5745693 : Nat := 983434067391231227804515

theorem tailTrace_5745693 : CollatzResearch.WordTrace tailWord_5745693 prefixEnd_5745693 983434067391231227804515 := by
  unfold tailWord_5745693
  simp only [CollatzResearch.WordTrace]
  refine ⟨209562639973343022085321733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139708426648895348056881155 209562639973343022085321733)
  ·
    refine ⟨39292994995001816640997825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209562639973343022085321733 39292994995001816640997825)
    ·
      refine ⟨29469746246251362480748369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39292994995001816640997825 29469746246251362480748369)
      ·
        refine ⟨22102309684688521860561277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29469746246251362480748369 22102309684688521860561277)
        ·
          refine ⟨8288366131758195697710479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22102309684688521860561277 8288366131758195697710479)
          ·
            refine ⟨12432549197637293546565719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8288366131758195697710479 12432549197637293546565719)
            ·
              refine ⟨18648823796455940319848579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12432549197637293546565719 18648823796455940319848579)
              ·
                refine ⟨27973235694683910479772869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18648823796455940319848579 27973235694683910479772869)
                ·
                  refine ⟨5244981692753233214957413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27973235694683910479772869 5244981692753233214957413)
                  ·
                    refine ⟨983434067391231227804515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244981692753233214957413 983434067391231227804515)
                    ·
                      rfl

theorem cell23_5745693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_5745693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745693 prefixEnd_5745693 := by exact prefixLift 5745693
  have htrace : WordTrace (prefixWord ++ tailWord_5745693) baseStart_5745693 baseEnd_5745693 := by
    simpa [prefixWord, tailWord_5745693, baseEnd_5745693] using wordTrace_append hprefix tailTrace_5745693
  have hstable : (prefixWord ++ tailWord_5745693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745693).length < 2 ^ (prefixWord ++ tailWord_5745693).sum := by decide
  have hdescent : baseEnd_5745693 < baseStart_5745693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745700 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5745700 : Nat := 118140960795 + 5745700 * 2 ^ 59
def prefixEnd_5745700 : Nat := 4983230072969 + 3 ^ 40 * 5745700 * 2
def baseEnd_5745700 : Nat := 2950305796538275156026013

theorem tailTrace_5745700 : CollatzResearch.WordTrace tailWord_5745700 prefixEnd_5745700 2950305796538275156026013 := by
  unfold tailWord_5745700
  simp only [CollatzResearch.WordTrace]
  refine ⟨104781447642158831140413277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139708596856211774853884369 104781447642158831140413277)
  ·
    refine ⟨39293042865809561677654979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104781447642158831140413277 39293042865809561677654979)
    ·
      refine ⟨58939564298714342516482469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39293042865809561677654979 58939564298714342516482469)
      ·
        refine ⟨11051168306008939221840463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58939564298714342516482469 11051168306008939221840463)
        ·
          refine ⟨16576752459013408832760695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051168306008939221840463 16576752459013408832760695)
          ·
            refine ⟨24865128688520113249141043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16576752459013408832760695 24865128688520113249141043)
            ·
              refine ⟨37297693032780169873711565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24865128688520113249141043 37297693032780169873711565)
              ·
                refine ⟨13986634887292563702641837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37297693032780169873711565 13986634887292563702641837)
                ·
                  refine ⟨5244988082734711388490689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13986634887292563702641837 5244988082734711388490689)
                  ·
                    refine ⟨3933741062051033541368017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5244988082734711388490689 3933741062051033541368017)
                    ·
                      refine ⟨2950305796538275156026013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933741062051033541368017 2950305796538275156026013)
                      ·
                        rfl

theorem cell23_5745700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5745700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745700 prefixEnd_5745700 := by exact prefixLift 5745700
  have htrace : WordTrace (prefixWord ++ tailWord_5745700) baseStart_5745700 baseEnd_5745700 := by
    simpa [prefixWord, tailWord_5745700, baseEnd_5745700] using wordTrace_append hprefix tailTrace_5745700
  have hstable : (prefixWord ++ tailWord_5745700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745700).length < 2 ^ (prefixWord ++ tailWord_5745700).sum := by decide
  have hdescent : baseEnd_5745700 < baseStart_5745700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745703 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5745703 : Nat := 118140960795 + 5745703 * 2 ^ 59
def prefixEnd_5745703 : Nat := 4983230072969 + 3 ^ 40 * 5745703 * 2
def baseEnd_5745703 : Nat := 2950307336980238644288499

theorem tailTrace_5745703 : CollatzResearch.WordTrace tailWord_5745703 prefixEnd_5745703 2950307336980238644288499 := by
  unfold tailWord_5745703
  simp only [CollatzResearch.WordTrace]
  refine ⟨209563004703306793793185763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139708669802204529195457175 209563004703306793793185763)
  ·
    refine ⟨314344507054960190689778645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209563004703306793793185763 314344507054960190689778645)
    ·
      refine ⟨7367449384100629469291687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 314344507054960190689778645 7367449384100629469291687)
      ·
        refine ⟨11051174076150944203937531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367449384100629469291687 11051174076150944203937531)
        ·
          refine ⟨16576761114226416305906297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11051174076150944203937531 16576761114226416305906297)
          ·
            refine ⟨12432570835669812229429723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16576761114226416305906297 12432570835669812229429723)
            ·
              refine ⟨18648856253504718344144585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12432570835669812229429723 18648856253504718344144585)
              ·
                refine ⟨13986642190128538758108439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18648856253504718344144585 13986642190128538758108439)
                ·
                  refine ⟨20979963285192808137162659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13986642190128538758108439 20979963285192808137162659)
                  ·
                    refine ⟨31469944927789212205743989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20979963285192808137162659 31469944927789212205743989)
                    ·
                      refine ⟨2950307336980238644288499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31469944927789212205743989 2950307336980238644288499)
                      ·
                        rfl

theorem cell23_5745703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5745703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745703 prefixEnd_5745703 := by exact prefixLift 5745703
  have htrace : WordTrace (prefixWord ++ tailWord_5745703) baseStart_5745703 baseEnd_5745703 := by
    simpa [prefixWord, tailWord_5745703, baseEnd_5745703] using wordTrace_append hprefix tailTrace_5745703
  have hstable : (prefixWord ++ tailWord_5745703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745703).length < 2 ^ (prefixWord ++ tailWord_5745703).sum := by decide
  have hdescent : baseEnd_5745703 < baseStart_5745703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745710 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_5745710 : Nat := 118140960795 + 5745710 * 2 ^ 59
def prefixEnd_5745710 : Nat := 4983230072969 + 3 ^ 40 * 5745710 * 2
def baseEnd_5745710 : Nat := 983436977114940038966989

theorem tailTrace_5745710 : CollatzResearch.WordTrace tailWord_5745710 prefixEnd_5745710 983436977114940038966989 := by
  unfold tailWord_5745710
  simp only [CollatzResearch.WordTrace]
  refine ⟨26195407501785179248586323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139708840009520955992460389 26195407501785179248586323)
  ·
    refine ⟨39293111252677768872879485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26195407501785179248586323 39293111252677768872879485)
    ·
      refine ⟨14734916719754163327329807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39293111252677768872879485 14734916719754163327329807)
      ·
        refine ⟨22102375079631244990994711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14734916719754163327329807 22102375079631244990994711)
        ·
          refine ⟨33153562619446867486492067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22102375079631244990994711 33153562619446867486492067)
          ·
            refine ⟨49730343929170301229738101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33153562619446867486492067 49730343929170301229738101)
            ·
              refine ⟨4662219743359715740287947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49730343929170301229738101 4662219743359715740287947)
              ·
                refine ⟨6993329615039573610431921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662219743359715740287947 6993329615039573610431921)
                ·
                  refine ⟨5244997211279680207823941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6993329615039573610431921 5244997211279680207823941)
                  ·
                    refine ⟨983436977114940038966989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244997211279680207823941 983436977114940038966989)
                    ·
                      rfl

theorem cell23_5745710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_5745710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745710 prefixEnd_5745710 := by exact prefixLift 5745710
  have htrace : WordTrace (prefixWord ++ tailWord_5745710) baseStart_5745710 baseEnd_5745710 := by
    simpa [prefixWord, tailWord_5745710, baseEnd_5745710] using wordTrace_append hprefix tailTrace_5745710
  have hstable : (prefixWord ++ tailWord_5745710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745710).length < 2 ^ (prefixWord ++ tailWord_5745710).sum := by decide
  have hdescent : baseEnd_5745710 < baseStart_5745710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745756 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5745756 : Nat := 118140960795 + 5745756 * 2 ^ 59
def prefixEnd_5745756 : Nat := 4983230072969 + 3 ^ 40 * 5745756 * 2
def baseEnd_5745756 : Nat := 2950334551454926936925755

theorem tailTrace_5745756 : CollatzResearch.WordTrace tailWord_5745756 prefixEnd_5745756 2950334551454926936925755 := by
  unfold tailWord_5745756
  simp only [CollatzResearch.WordTrace]
  refine ⟨104782468886057391922432561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139709958514743189229910081 104782468886057391922432561)
  ·
    refine ⟨78586851664543043941824421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104782468886057391922432561 78586851664543043941824421)
    ·
      refine ⟨14735034687101820739092079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78586851664543043941824421 14735034687101820739092079)
      ·
        refine ⟨22102552030652731108638119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14735034687101820739092079 22102552030652731108638119)
        ·
          refine ⟨33153828045979096662957179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22102552030652731108638119 33153828045979096662957179)
          ·
            refine ⟨49730742068968644994435769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33153828045979096662957179 49730742068968644994435769)
            ·
              refine ⟨37298056551726483745826827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49730742068968644994435769 37298056551726483745826827)
              ·
                refine ⟨55947084827589725618740241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37298056551726483745826827 55947084827589725618740241)
                ·
                  refine ⟨41960313620692294214055181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55947084827589725618740241 41960313620692294214055181)
                  ·
                    refine ⟨15735117607759610330270693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41960313620692294214055181 15735117607759610330270693)
                    ·
                      refine ⟨2950334551454926936925755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15735117607759610330270693 2950334551454926936925755)
                      ·
                        rfl

theorem cell23_5745756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5745756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745756 prefixEnd_5745756 := by exact prefixLift 5745756
  have htrace : WordTrace (prefixWord ++ tailWord_5745756) baseStart_5745756 baseEnd_5745756 := by
    simpa [prefixWord, tailWord_5745756, baseEnd_5745756] using wordTrace_append hprefix tailTrace_5745756
  have hstable : (prefixWord ++ tailWord_5745756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745756).length < 2 ^ (prefixWord ++ tailWord_5745756).sum := by decide
  have hdescent : baseEnd_5745756 < baseStart_5745756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745759 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_5745759 : Nat := 118140960795 + 5745759 * 2 ^ 59
def prefixEnd_5745759 : Nat := 4983230072969 + 3 ^ 40 * 5745759 * 2
def baseEnd_5745759 : Nat := 2950336091896890425188241

theorem tailTrace_5745759 : CollatzResearch.WordTrace tailWord_5745759 prefixEnd_5745759 2950336091896890425188241 := by
  unfold tailWord_5745759
  simp only [CollatzResearch.WordTrace]
  refine ⟨209565047191103915357224331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139710031460735943571482887 209565047191103915357224331)
  ·
    refine ⟨314347570786655873035836497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209565047191103915357224331 314347570786655873035836497)
    ·
      refine ⟨235760678089991904776877373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314347570786655873035836497 235760678089991904776877373)
      ·
        refine ⟨88410254283746964291329015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235760678089991904776877373 88410254283746964291329015)
        ·
          refine ⟨132615381425620446436993523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88410254283746964291329015 132615381425620446436993523)
          ·
            refine ⟨198923072138430669655490285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132615381425620446436993523 198923072138430669655490285)
            ·
              refine ⟨74596152051911501120808857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198923072138430669655490285 74596152051911501120808857)
              ·
                refine ⟨55947114038933625840606643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74596152051911501120808857 55947114038933625840606643)
                ·
                  refine ⟨83920671058400438760909965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55947114038933625840606643 83920671058400438760909965)
                  ·
                    refine ⟨31470251646900164535341237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83920671058400438760909965 31470251646900164535341237)
                    ·
                      refine ⟨2950336091896890425188241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31470251646900164535341237 2950336091896890425188241)
                      ·
                        rfl

theorem cell23_5745759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_5745759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745759 prefixEnd_5745759 := by exact prefixLift 5745759
  have htrace : WordTrace (prefixWord ++ tailWord_5745759) baseStart_5745759 baseEnd_5745759 := by
    simpa [prefixWord, tailWord_5745759, baseEnd_5745759] using wordTrace_append hprefix tailTrace_5745759
  have hstable : (prefixWord ++ tailWord_5745759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745759).length < 2 ^ (prefixWord ++ tailWord_5745759).sum := by decide
  have hdescent : baseEnd_5745759 < baseStart_5745759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745767 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_5745767 : Nat := 118140960795 + 5745767 * 2 ^ 59
def prefixEnd_5745767 : Nat := 4983230072969 + 3 ^ 40 * 5745767 * 2
def baseEnd_5745767 : Nat := 2950340199742126393888205

theorem tailTrace_5745767 : CollatzResearch.WordTrace tailWord_5745767 prefixEnd_5745767 2950340199742126393888205 := by
  unfold tailWord_5745767
  simp only [CollatzResearch.WordTrace]
  refine ⟨209565338975074932723515555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139710225983383288482343703 209565338975074932723515555)
  ·
    refine ⟨314348008462612399085273333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209565338975074932723515555 314348008462612399085273333)
    ·
      refine ⟨29470125793369912414244375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314348008462612399085273333 29470125793369912414244375)
      ·
        refine ⟨44205188690054868621366563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29470125793369912414244375 44205188690054868621366563)
        ·
          refine ⟨66307783035082302932049845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44205188690054868621366563 66307783035082302932049845)
          ·
            refine ⟨6216354659538965899879673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66307783035082302932049845 6216354659538965899879673)
            ·
              refine ⟨4662265994654224424909755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6216354659538965899879673 4662265994654224424909755)
              ·
                refine ⟨6993398991981336637364633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662265994654224424909755 6993398991981336637364633)
                ·
                  refine ⟨5245049243986002478023475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6993398991981336637364633 5245049243986002478023475)
                  ·
                    refine ⟨7867573865979003717035213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245049243986002478023475 7867573865979003717035213)
                    ·
                      refine ⟨2950340199742126393888205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7867573865979003717035213 2950340199742126393888205)
                      ·
                        rfl

theorem cell23_5745767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_5745767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745767 prefixEnd_5745767 := by exact prefixLift 5745767
  have htrace : WordTrace (prefixWord ++ tailWord_5745767) baseStart_5745767 baseEnd_5745767 := by
    simpa [prefixWord, tailWord_5745767, baseEnd_5745767] using wordTrace_append hprefix tailTrace_5745767
  have hstable : (prefixWord ++ tailWord_5745767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745767).length < 2 ^ (prefixWord ++ tailWord_5745767).sum := by decide
  have hdescent : baseEnd_5745767 < baseStart_5745767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745858 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_5745858 : Nat := 118140960795 + 5745858 * 2 ^ 59
def prefixEnd_5745858 : Nat := 4983230072969 + 3 ^ 40 * 5745858 * 2
def baseEnd_5745858 : Nat := 2950386926481685537850287

theorem tailTrace_5745858 : CollatzResearch.WordTrace tailWord_5745858 prefixEnd_5745858 2950386926481685537850287 := by
  unfold tailWord_5745858
  simp only [CollatzResearch.WordTrace]
  refine ⟨52392164504436313816269557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139712438678496836843385485 52392164504436313816269557)
  ·
    refine ⟨4911765422290904420275271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52392164504436313816269557 4911765422290904420275271)
    ·
      refine ⟨7367648133436356630412907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4911765422290904420275271 7367648133436356630412907)
      ·
        refine ⟨11051472200154534945619361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7367648133436356630412907 11051472200154534945619361)
        ·
          refine ⟨8288604150115901209214521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11051472200154534945619361 8288604150115901209214521)
          ·
            refine ⟨6216453112586925906910891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8288604150115901209214521 6216453112586925906910891)
            ·
              refine ⟨9324679668880388860366337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216453112586925906910891 9324679668880388860366337)
              ·
                refine ⟨6993509751660291645274753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9324679668880388860366337 6993509751660291645274753)
                ·
                  refine ⟨5245132313745218733956065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6993509751660291645274753 5245132313745218733956065)
                  ·
                    refine ⟨3933849235308914050467049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5245132313745218733956065 3933849235308914050467049)
                    ·
                      refine ⟨2950386926481685537850287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933849235308914050467049 2950386926481685537850287)
                      ·
                        rfl

theorem cell23_5745858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_5745858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745858 prefixEnd_5745858 := by exact prefixLift 5745858
  have htrace : WordTrace (prefixWord ++ tailWord_5745858) baseStart_5745858 baseEnd_5745858 := by
    simpa [prefixWord, tailWord_5745858, baseEnd_5745858] using wordTrace_append hprefix tailTrace_5745858
  have hstable : (prefixWord ++ tailWord_5745858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745858).length < 2 ^ (prefixWord ++ tailWord_5745858).sum := by decide
  have hdescent : baseEnd_5745858 < baseStart_5745858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745907 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 1, 4]
def baseStart_5745907 : Nat := 118140960795 + 5745907 * 2 ^ 59
def prefixEnd_5745907 : Nat := 4983230072969 + 3 ^ 40 * 5745907 * 2
def baseEnd_5745907 : Nat := 983470695677918615379187

theorem tailTrace_5745907 : CollatzResearch.WordTrace tailWord_5745907 prefixEnd_5745907 983470695677918615379187 := by
  unfold tailWord_5745907
  simp only [CollatzResearch.WordTrace]
  refine ⟨209570445194567736633611975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139713630129711824422407983 209570445194567736633611975)
  ·
    refine ⟨314355667791851604950417963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209570445194567736633611975 314355667791851604950417963)
    ·
      refine ⟨471533501687777407425626945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314355667791851604950417963 471533501687777407425626945)
      ·
        refine ⟨353650126265833055569220209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471533501687777407425626945 353650126265833055569220209)
        ·
          refine ⟨265237594699374791676915157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353650126265833055569220209 265237594699374791676915157)
          ·
            refine ⟨6216506125766596679927699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265237594699374791676915157 6216506125766596679927699)
            ·
              refine ⟨9324759188649895019891549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216506125766596679927699 9324759188649895019891549)
              ·
                refine ⟨3496784695743710632459331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9324759188649895019891549 3496784695743710632459331)
                ·
                  refine ⟨5245177043615565948688997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496784695743710632459331 5245177043615565948688997)
                  ·
                    refine ⟨983470695677918615379187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245177043615565948688997 983470695677918615379187)
                    ·
                      rfl

theorem cell23_5745907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 4].length) (baseStart_5745907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745907 prefixEnd_5745907 := by exact prefixLift 5745907
  have htrace : WordTrace (prefixWord ++ tailWord_5745907) baseStart_5745907 baseEnd_5745907 := by
    simpa [prefixWord, tailWord_5745907, baseEnd_5745907] using wordTrace_append hprefix tailTrace_5745907
  have hstable : (prefixWord ++ tailWord_5745907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745907).length < 2 ^ (prefixWord ++ tailWord_5745907).sum := by decide
  have hdescent : baseEnd_5745907 < baseStart_5745907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745924 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_5745924 : Nat := 118140960795 + 5745924 * 2 ^ 59
def prefixEnd_5745924 : Nat := 4983230072969 + 3 ^ 40 * 5745924 * 2
def baseEnd_5745924 : Nat := 983473605401627426541661

theorem tailTrace_5745924 : CollatzResearch.WordTrace tailWord_5745924 prefixEnd_5745924 983473605401627426541661 := by
  unfold tailWord_5745924
  simp only [CollatzResearch.WordTrace]
  refine ⟨104785532617753074268490413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139714043490337432357987217 104785532617753074268490413)
  ·
    refine ⟨39294574731657402850683905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104785532617753074268490413 39294574731657402850683905)
    ·
      refine ⟨29470931048743052138012929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39294574731657402850683905 29470931048743052138012929)
      ·
        refine ⟨22103198286557289103509697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29470931048743052138012929 22103198286557289103509697)
        ·
          refine ⟨16577398714917966827632273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22103198286557289103509697 16577398714917966827632273)
          ·
            refine ⟨12433049036188475120724205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16577398714917966827632273 12433049036188475120724205)
            ·
              refine ⟨4662393388570678170271577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12433049036188475120724205 4662393388570678170271577)
              ·
                refine ⟨3496795041428008627703683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662393388570678170271577 3496795041428008627703683)
                ·
                  refine ⟨5245192562142012941555525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496795041428008627703683 5245192562142012941555525)
                  ·
                    refine ⟨983473605401627426541661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245192562142012941555525 983473605401627426541661)
                    ·
                      rfl

theorem cell23_5745924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_5745924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745924 prefixEnd_5745924 := by exact prefixLift 5745924
  have htrace : WordTrace (prefixWord ++ tailWord_5745924) baseStart_5745924 baseEnd_5745924 := by
    simpa [prefixWord, tailWord_5745924, baseEnd_5745924] using wordTrace_append hprefix tailTrace_5745924
  have hstable : (prefixWord ++ tailWord_5745924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745924).length < 2 ^ (prefixWord ++ tailWord_5745924).sum := by decide
  have hdescent : baseEnd_5745924 < baseStart_5745924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745957 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 2, 3, 2]
def baseStart_5745957 : Nat := 118140960795 + 5745957 * 2 ^ 59
def prefixEnd_5745957 : Nat := 4983230072969 + 3 ^ 40 * 5745957 * 2
def baseEnd_5745957 : Nat := 2950437761066480650512331

theorem tailTrace_5745957 : CollatzResearch.WordTrace tailWord_5745957 prefixEnd_5745957 2950437761066480650512331 := by
  unfold tailWord_5745957
  simp only [CollatzResearch.WordTrace]
  refine ⟨209572268844386595172932125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139714845896257730115288083 209572268844386595172932125)
  ·
    refine ⟨78589600816644973189849547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209572268844386595172932125 78589600816644973189849547)
    ·
      refine ⟨117884401224967459784774321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78589600816644973189849547 117884401224967459784774321)
      ·
        refine ⟨88413300918725594838580741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117884401224967459784774321 88413300918725594838580741)
        ·
          refine ⟨16577493922261049032233889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88413300918725594838580741 16577493922261049032233889)
          ·
            refine ⟨12433120441695786774175417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16577493922261049032233889 12433120441695786774175417)
            ·
              refine ⟨9324840331271840080631563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12433120441695786774175417 9324840331271840080631563)
              ·
                refine ⟨13987260496907760120947345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9324840331271840080631563 13987260496907760120947345)
                ·
                  refine ⟨10490445372680820090710509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13987260496907760120947345 10490445372680820090710509)
                  ·
                    refine ⟨3933917014755307534016441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10490445372680820090710509 3933917014755307534016441)
                    ·
                      refine ⟨2950437761066480650512331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3933917014755307534016441 2950437761066480650512331)
                      ·
                        rfl

theorem cell23_5745957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_5745957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745957 prefixEnd_5745957 := by exact prefixLift 5745957
  have htrace : WordTrace (prefixWord ++ tailWord_5745957) baseStart_5745957 baseEnd_5745957 := by
    simpa [prefixWord, tailWord_5745957, baseEnd_5745957] using wordTrace_append hprefix tailTrace_5745957
  have hstable : (prefixWord ++ tailWord_5745957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745957).length < 2 ^ (prefixWord ++ tailWord_5745957).sum := by decide
  have hdescent : baseEnd_5745957 < baseStart_5745957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745980 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_5745980 : Nat := 118140960795 + 5745980 * 2 ^ 59
def prefixEnd_5745980 : Nat := 4983230072969 + 3 ^ 40 * 5745980 * 2
def baseEnd_5745980 : Nat := 983483190373844686841575

theorem tailTrace_5745980 : CollatzResearch.WordTrace tailWord_5745980 prefixEnd_5745980 983483190373844686841575 := by
  unfold tailWord_5745980
  simp only [CollatzResearch.WordTrace]
  refine ⟨104786553861651635050509697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139715405148868846734012929 104786553861651635050509697)
  ·
    refine ⟨78589915396238726287882273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104786553861651635050509697 78589915396238726287882273)
    ·
      refine ⟨58942436547179044715911705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78589915396238726287882273 58942436547179044715911705)
      ·
        refine ⟨44206827410384283536933779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58942436547179044715911705 44206827410384283536933779)
        ·
          refine ⟨66310241115576425305400669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44206827410384283536933779 66310241115576425305400669)
          ·
            refine ⟨24866340418341159489525251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66310241115576425305400669 24866340418341159489525251)
            ·
              refine ⟨37299510627511739234287877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24866340418341159489525251 37299510627511739234287877)
              ·
                refine ⟨6993658242658451106428977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37299510627511739234287877 6993658242658451106428977)
                ·
                  refine ⟨5245243681993838329821733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6993658242658451106428977 5245243681993838329821733)
                  ·
                    refine ⟨983483190373844686841575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245243681993838329821733 983483190373844686841575)
                    ·
                      rfl

theorem cell23_5745980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_5745980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745980 prefixEnd_5745980 := by exact prefixLift 5745980
  have htrace : WordTrace (prefixWord ++ tailWord_5745980) baseStart_5745980 baseEnd_5745980 := by
    simpa [prefixWord, tailWord_5745980, baseEnd_5745980] using wordTrace_append hprefix tailTrace_5745980
  have hstable : (prefixWord ++ tailWord_5745980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745980).length < 2 ^ (prefixWord ++ tailWord_5745980).sum := by decide
  have hdescent : baseEnd_5745980 < baseStart_5745980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5745981 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5745981 : Nat := 118140960795 + 5745981 * 2 ^ 59
def prefixEnd_5745981 : Nat := 4983230072969 + 3 ^ 40 * 5745981 * 2
def baseEnd_5745981 : Nat := 2950450084602188556612221

theorem tailTrace_5745981 : CollatzResearch.WordTrace tailWord_5745981 prefixEnd_5745981 2950450084602188556612221 := by
  unfold tailWord_5745981
  simp only [CollatzResearch.WordTrace]
  refine ⟨209573144196299647271805797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139715429464199764847870531 209573144196299647271805797)
  ·
    refine ⟨39294964536806183863463587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209573144196299647271805797 39294964536806183863463587)
    ·
      refine ⟨58942446805209275795195381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39294964536806183863463587 58942446805209275795195381)
      ·
        refine ⟨5525854387988369605799567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58942446805209275795195381 5525854387988369605799567)
        ·
          refine ⟨8288781581982554408699351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525854387988369605799567 8288781581982554408699351)
          ·
            refine ⟨12433172372973831613049027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8288781581982554408699351 12433172372973831613049027)
            ·
              refine ⟨18649758559460747419573541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12433172372973831613049027 18649758559460747419573541)
              ·
                refine ⟨3496829729898890141170039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18649758559460747419573541 3496829729898890141170039)
                ·
                  refine ⟨5245244594848335211755059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496829729898890141170039 5245244594848335211755059)
                  ·
                    refine ⟨7867866892272502817632589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245244594848335211755059 7867866892272502817632589)
                    ·
                      refine ⟨2950450084602188556612221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7867866892272502817632589 2950450084602188556612221)
                      ·
                        rfl

theorem cell23_5745981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5745981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5745981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5745981 prefixEnd_5745981 := by exact prefixLift 5745981
  have htrace : WordTrace (prefixWord ++ tailWord_5745981) baseStart_5745981 baseEnd_5745981 := by
    simpa [prefixWord, tailWord_5745981, baseEnd_5745981] using wordTrace_append hprefix tailTrace_5745981
  have hstable : (prefixWord ++ tailWord_5745981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5745981).length < 2 ^ (prefixWord ++ tailWord_5745981).sum := by decide
  have hdescent : baseEnd_5745981 < baseStart_5745981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5745981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746020 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_5746020 : Nat := 118140960795 + 5746020 * 2 ^ 59
def prefixEnd_5746020 : Nat := 4983230072969 + 3 ^ 40 * 5746020 * 2
def baseEnd_5746020 : Nat := 2950470110347713904024541

theorem tailTrace_5746020 : CollatzResearch.WordTrace tailWord_5746020 prefixEnd_5746020 2950470110347713904024541 := by
  unfold tailWord_5746020
  simp only [CollatzResearch.WordTrace]
  refine ⟨104787283321579178466237757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139716377762105571288317009 104787283321579178466237757)
  ·
    refine ⟨39295231245592191924839159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104787283321579178466237757 39295231245592191924839159)
    ·
      refine ⟨58942846868388287887258739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39295231245592191924839159 58942846868388287887258739)
      ·
        refine ⟨88414270302582431830888109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58942846868388287887258739 88414270302582431830888109)
        ·
          refine ⟨33155351363468411936583041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88414270302582431830888109 33155351363468411936583041)
          ·
            refine ⟨24866513522601308952437281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33155351363468411936583041 24866513522601308952437281)
            ·
              refine ⟨18649885141950981714327961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24866513522601308952437281 18649885141950981714327961)
              ·
                refine ⟨13987413856463236285745971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18649885141950981714327961 13987413856463236285745971)
                ·
                  refine ⟨20981120784694854428618957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13987413856463236285745971 20981120784694854428618957)
                  ·
                    refine ⟨7867920294260570410732109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20981120784694854428618957 7867920294260570410732109)
                    ·
                      refine ⟨2950470110347713904024541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7867920294260570410732109 2950470110347713904024541)
                      ·
                        rfl

theorem cell23_5746020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_5746020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746020 prefixEnd_5746020 := by exact prefixLift 5746020
  have htrace : WordTrace (prefixWord ++ tailWord_5746020) baseStart_5746020 baseEnd_5746020 := by
    simpa [prefixWord, tailWord_5746020, baseEnd_5746020] using wordTrace_append hprefix tailTrace_5746020
  have hstable : (prefixWord ++ tailWord_5746020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746020).length < 2 ^ (prefixWord ++ tailWord_5746020).sum := by decide
  have hdescent : baseEnd_5746020 < baseStart_5746020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746053 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_5746053 : Nat := 118140960795 + 5746053 * 2 ^ 59
def prefixEnd_5746053 : Nat := 4983230072969 + 3 ^ 40 * 5746053 * 2
def baseEnd_5746053 : Nat := 983495685069770758303963

theorem tailTrace_5746053 : CollatzResearch.WordTrace tailWord_5746053 prefixEnd_5746053 983495685069770758303963 := by
  unfold tailWord_5746053
  simp only [CollatzResearch.WordTrace]
  refine ⟨209575770252038803568426813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139717180168025869045617875 209575770252038803568426813)
  ·
    refine ⟨78590913844514551338160055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209575770252038803568426813 78590913844514551338160055)
    ·
      refine ⟨117886370766771827007240083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78590913844514551338160055 117886370766771827007240083)
      ·
        refine ⟨176829556150157740510860125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117886370766771827007240083 176829556150157740510860125)
        ·
          refine ⟨66311083556309152691572547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176829556150157740510860125 66311083556309152691572547)
          ·
            refine ⟨99466625334463729037358821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66311083556309152691572547 99466625334463729037358821)
            ·
              refine ⟨18649992250211949194504779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99466625334463729037358821 18649992250211949194504779)
              ·
                refine ⟨27974988375317923791757169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18649992250211949194504779 27974988375317923791757169)
                ·
                  refine ⟨20981241281488442843817877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27974988375317923791757169 20981241281488442843817877)
                  ·
                    refine ⟨983495685069770758303963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20981241281488442843817877 983495685069770758303963)
                    ·
                      rfl

theorem cell23_5746053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_5746053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746053 prefixEnd_5746053 := by exact prefixLift 5746053
  have htrace : WordTrace (prefixWord ++ tailWord_5746053) baseStart_5746053 baseEnd_5746053 := by
    simpa [prefixWord, tailWord_5746053, baseEnd_5746053] using wordTrace_append hprefix tailTrace_5746053
  have hstable : (prefixWord ++ tailWord_5746053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746053).length < 2 ^ (prefixWord ++ tailWord_5746053).sum := by decide
  have hdescent : baseEnd_5746053 < baseStart_5746053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746110 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_5746110 : Nat := 118140960795 + 5746110 * 2 ^ 59
def prefixEnd_5746110 : Nat := 4983230072969 + 3 ^ 40 * 5746110 * 2
def baseEnd_5746110 : Nat := 2950516323606618551899127

theorem tailTrace_5746110 : CollatzResearch.WordTrace tailWord_5746110 prefixEnd_5746110 2950516323606618551899127 := by
  unfold tailWord_5746110
  simp only [CollatzResearch.WordTrace]
  refine ⟨26197231151604037787906473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139718566141888201535501189 26197231151604037787906473)
  ·
    refine ⟨19647923363703028340929855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26197231151604037787906473 19647923363703028340929855)
    ·
      refine ⟨29471885045554542511394783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19647923363703028340929855 29471885045554542511394783)
      ·
        refine ⟨44207827568331813767092175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29471885045554542511394783 44207827568331813767092175)
        ·
          refine ⟨66311741352497720650638263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44207827568331813767092175 66311741352497720650638263)
          ·
            refine ⟨99467612028746580975957395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66311741352497720650638263 99467612028746580975957395)
            ·
              refine ⟨149201418043119871463936093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99467612028746580975957395 149201418043119871463936093)
              ·
                refine ⟨55950531766169951798976035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149201418043119871463936093 55950531766169951798976035)
                ·
                  refine ⟨83925797649254927698464053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55950531766169951798976035 83925797649254927698464053)
                  ·
                    refine ⟨7868043529617649471731005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83925797649254927698464053 7868043529617649471731005)
                    ·
                      refine ⟨2950516323606618551899127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868043529617649471731005 2950516323606618551899127)
                      ·
                        rfl

theorem cell23_5746110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_5746110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746110 prefixEnd_5746110 := by exact prefixLift 5746110
  have htrace : WordTrace (prefixWord ++ tailWord_5746110) baseStart_5746110 baseEnd_5746110 := by
    simpa [prefixWord, tailWord_5746110, baseEnd_5746110] using wordTrace_append hprefix tailTrace_5746110
  have hstable : (prefixWord ++ tailWord_5746110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746110).length < 2 ^ (prefixWord ++ tailWord_5746110).sum := by decide
  have hdescent : baseEnd_5746110 < baseStart_5746110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746163 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_5746163 : Nat := 118140960795 + 5746163 * 2 ^ 59
def prefixEnd_5746163 : Nat := 4983230072969 + 3 ^ 40 * 5746163 * 2
def baseEnd_5746163 : Nat := 2950543538081306844536383

theorem tailTrace_5746163 : CollatzResearch.WordTrace tailWord_5746163 prefixEnd_5746163 2950543538081306844536383 := by
  unfold tailWord_5746163
  simp only [CollatzResearch.WordTrace]
  refine ⟨209579782281640292354931143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139719854854426861569954095 209579782281640292354931143)
  ·
    refine ⟨314369673422460438532396715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209579782281640292354931143 314369673422460438532396715)
    ·
      refine ⟨471554510133690657798595073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314369673422460438532396715 471554510133690657798595073)
      ·
        refine ⟨353665882600267993348946305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471554510133690657798595073 353665882600267993348946305)
        ·
          refine ⟨265249411950200995011709729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353665882600267993348946305 265249411950200995011709729)
          ·
            refine ⟨198937058962650746258782297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265249411950200995011709729 198937058962650746258782297)
            ·
              refine ⟨149202794221988059694086723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198937058962650746258782297 149202794221988059694086723)
              ·
                refine ⟨223804191332982089541130085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149202794221988059694086723 223804191332982089541130085)
                ·
                  refine ⟨41963285874934141788961891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223804191332982089541130085 41963285874934141788961891)
                  ·
                    refine ⟨62944928812401212683442837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41963285874934141788961891 62944928812401212683442837)
                    ·
                      refine ⟨2950543538081306844536383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62944928812401212683442837 2950543538081306844536383)
                      ·
                        rfl

theorem cell23_5746163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_5746163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746163 prefixEnd_5746163 := by exact prefixLift 5746163
  have htrace : WordTrace (prefixWord ++ tailWord_5746163) baseStart_5746163 baseEnd_5746163 := by
    simpa [prefixWord, tailWord_5746163, baseEnd_5746163] using wordTrace_append hprefix tailTrace_5746163
  have hstable : (prefixWord ++ tailWord_5746163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746163).length < 2 ^ (prefixWord ++ tailWord_5746163).sum := by decide
  have hdescent : baseEnd_5746163 < baseStart_5746163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746170 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_5746170 : Nat := 118140960795 + 5746170 * 2 ^ 59
def prefixEnd_5746170 : Nat := 4983230072969 + 3 ^ 40 * 5746170 * 2
def baseEnd_5746170 : Nat := 2950547132445888317148851

theorem tailTrace_5746170 : CollatzResearch.WordTrace tailWord_5746170 prefixEnd_5746170 2950547132445888317148851 := by
  unfold tailWord_5746170
  simp only [CollatzResearch.WordTrace]
  refine ⟨52395009398153733137608991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139720025061743288366957309 52395009398153733137608991)
  ·
    refine ⟨78592514097230599706413487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52395009398153733137608991 78592514097230599706413487)
    ·
      refine ⟨117888771145845899559620231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78592514097230599706413487 117888771145845899559620231)
      ·
        refine ⟨176833156718768849339430347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117888771145845899559620231 176833156718768849339430347)
        ·
          refine ⟨265249735078153274009145521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176833156718768849339430347 265249735078153274009145521)
          ·
            refine ⟨198937301308614955506859141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265249735078153274009145521 198937301308614955506859141)
            ·
              refine ⟨37300743995365304157536089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198937301308614955506859141 37300743995365304157536089)
              ·
                refine ⟨27975557996523978118152067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37300743995365304157536089 27975557996523978118152067)
                ·
                  refine ⟨41963336994785967177228101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27975557996523978118152067 41963336994785967177228101)
                  ·
                    refine ⟨7868125686522368845730269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41963336994785967177228101 7868125686522368845730269)
                    ·
                      refine ⟨2950547132445888317148851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868125686522368845730269 2950547132445888317148851)
                      ·
                        rfl

theorem cell23_5746170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_5746170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746170 prefixEnd_5746170 := by exact prefixLift 5746170
  have htrace : WordTrace (prefixWord ++ tailWord_5746170) baseStart_5746170 baseEnd_5746170 := by
    simpa [prefixWord, tailWord_5746170, baseEnd_5746170] using wordTrace_append hprefix tailTrace_5746170
  have hstable : (prefixWord ++ tailWord_5746170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746170).length < 2 ^ (prefixWord ++ tailWord_5746170).sum := by decide
  have hdescent : baseEnd_5746170 < baseStart_5746170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746187 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 3]
def baseStart_5746187 : Nat := 118140960795 + 5746187 * 2 ^ 59
def prefixEnd_5746187 : Nat := 4983230072969 + 3 ^ 40 * 5746187 * 2
def baseEnd_5746187 : Nat := 2950555861617014750636273

theorem tailTrace_5746187 : CollatzResearch.WordTrace tailWord_5746187 prefixEnd_5746187 2950555861617014750636273 := by
  unfold tailWord_5746187
  simp only [CollatzResearch.WordTrace]
  refine ⟨209580657633553344453804815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139720438422368896302536543 209580657633553344453804815)
  ·
    refine ⟨314370986450330016680707223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209580657633553344453804815 314370986450330016680707223)
    ·
      refine ⟨471556479675495025021060835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314370986450330016680707223 471556479675495025021060835)
      ·
        refine ⟨707334719513242537531591253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471556479675495025021060835 707334719513242537531591253)
        ·
          refine ⟨8289078744295810986698335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 707334719513242537531591253 8289078744295810986698335)
          ·
            refine ⟨12433618116443716480047503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289078744295810986698335 12433618116443716480047503)
            ·
              refine ⟨18650427174665574720071255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12433618116443716480047503 18650427174665574720071255)
              ·
                refine ⟨27975640761998362080106883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18650427174665574720071255 27975640761998362080106883)
                ·
                  refine ⟨41963461142997543120160325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27975640761998362080106883 41963461142997543120160325)
                  ·
                    refine ⟨7868148964312039335030061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41963461142997543120160325 7868148964312039335030061)
                    ·
                      refine ⟨2950555861617014750636273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868148964312039335030061 2950555861617014750636273)
                      ·
                        rfl

theorem cell23_5746187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 3].length) (baseStart_5746187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746187 prefixEnd_5746187 := by exact prefixLift 5746187
  have htrace : WordTrace (prefixWord ++ tailWord_5746187) baseStart_5746187 baseEnd_5746187 := by
    simpa [prefixWord, tailWord_5746187, baseEnd_5746187] using wordTrace_append hprefix tailTrace_5746187
  have hstable : (prefixWord ++ tailWord_5746187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746187).length < 2 ^ (prefixWord ++ tailWord_5746187).sum := by decide
  have hdescent : baseEnd_5746187 < baseStart_5746187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746210 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_5746210 : Nat := 118140960795 + 5746210 * 2 ^ 59
def prefixEnd_5746210 : Nat := 4983230072969 + 3 ^ 40 * 5746210 * 2
def baseEnd_5746210 : Nat := 2950567671672068160648667

theorem tailTrace_5746210 : CollatzResearch.WordTrace tailWord_5746210 prefixEnd_5746210 2950567671672068160648667 := by
  unfold tailWord_5746210
  simp only [CollatzResearch.WordTrace]
  refine ⟨52395374128117504845473021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139720997674980012921261389 52395374128117504845473021)
  ·
    refine ⟨19648265298044064317052383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52395374128117504845473021 19648265298044064317052383)
    ·
      refine ⟨29472397947066096475578575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19648265298044064317052383 29472397947066096475578575)
      ·
        refine ⟨44208596920599144713367863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29472397947066096475578575 44208596920599144713367863)
        ·
          refine ⟨66312895380898717070051795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44208596920599144713367863 66312895380898717070051795)
          ·
            refine ⟨99469343071348075605077693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66312895380898717070051795 99469343071348075605077693)
            ·
              refine ⟨37301003651755528351904135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99469343071348075605077693 37301003651755528351904135)
              ·
                refine ⟨55951505477633292527856203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37301003651755528351904135 55951505477633292527856203)
                ·
                  refine ⟨83927258216449938791784305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55951505477633292527856203 83927258216449938791784305)
                  ·
                    refine ⟨62945443662337454093838229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83927258216449938791784305 62945443662337454093838229)
                    ·
                      refine ⟨2950567671672068160648667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62945443662337454093838229 2950567671672068160648667)
                      ·
                        rfl

theorem cell23_5746210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_5746210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746210 prefixEnd_5746210 := by exact prefixLift 5746210
  have htrace : WordTrace (prefixWord ++ tailWord_5746210) baseStart_5746210 baseEnd_5746210 := by
    simpa [prefixWord, tailWord_5746210, baseEnd_5746210] using wordTrace_append hprefix tailTrace_5746210
  have hstable : (prefixWord ++ tailWord_5746210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746210).length < 2 ^ (prefixWord ++ tailWord_5746210).sum := by decide
  have hdescent : baseEnd_5746210 < baseStart_5746210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746227 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 1, 5, 2]
def baseStart_5746227 : Nat := 118140960795 + 5746227 * 2 ^ 59
def prefixEnd_5746227 : Nat := 4983230072969 + 3 ^ 40 * 5746227 * 2
def baseEnd_5746227 : Nat := 2950576400843194594136089

theorem tailTrace_5746227 : CollatzResearch.WordTrace tailWord_5746227 prefixEnd_5746227 2950576400843194594136089 := by
  unfold tailWord_5746227
  simp only [CollatzResearch.WordTrace]
  refine ⟨209582116553408431285260935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139721411035605620856840623 209582116553408431285260935)
  ·
    refine ⟨314373174830112646927891403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209582116553408431285260935 314373174830112646927891403)
    ·
      refine ⟨471559762245168970391837105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314373174830112646927891403 471559762245168970391837105)
      ·
        refine ⟨353669821683876727793877829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471559762245168970391837105 353669821683876727793877829)
        ·
          refine ⟨66313091565726886461352093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353669821683876727793877829 66313091565726886461352093)
          ·
            refine ⟨24867409337147582423007035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66313091565726886461352093 24867409337147582423007035)
            ·
              refine ⟨37301114005721373634510553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24867409337147582423007035 37301114005721373634510553)
              ·
                refine ⟨27975835504291030225882915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37301114005721373634510553 27975835504291030225882915)
                ·
                  refine ⟨41963753256436545338824373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27975835504291030225882915 41963753256436545338824373)
                  ·
                    refine ⟨3934101867790926125514785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41963753256436545338824373 3934101867790926125514785)
                    ·
                      refine ⟨2950576400843194594136089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934101867790926125514785 2950576400843194594136089)
                      ·
                        rfl

theorem cell23_5746227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5, 2].length) (baseStart_5746227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746227 prefixEnd_5746227 := by exact prefixLift 5746227
  have htrace : WordTrace (prefixWord ++ tailWord_5746227) baseStart_5746227 baseEnd_5746227 := by
    simpa [prefixWord, tailWord_5746227, baseEnd_5746227] using wordTrace_append hprefix tailTrace_5746227
  have hstable : (prefixWord ++ tailWord_5746227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746227).length < 2 ^ (prefixWord ++ tailWord_5746227).sum := by decide
  have hdescent : baseEnd_5746227 < baseStart_5746227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746250 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_5746250 : Nat := 118140960795 + 5746250 * 2 ^ 59
def prefixEnd_5746250 : Nat := 4983230072969 + 3 ^ 40 * 5746250 * 2
def baseEnd_5746250 : Nat := 983529403632749334716161

theorem tailTrace_5746250 : CollatzResearch.WordTrace tailWord_5746250 prefixEnd_5746250 983529403632749334716161 := by
  unfold tailWord_5746250
  simp only [CollatzResearch.WordTrace]
  refine ⟨52395738858081276553337051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139721970288216737475565469 52395738858081276553337051)
  ·
    refine ⟨78593608287121914830005577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52395738858081276553337051 78593608287121914830005577)
    ·
      refine ⟨58945206215341436122504183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78593608287121914830005577 58945206215341436122504183)
      ·
        refine ⟨88417809323012154183756275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58945206215341436122504183 88417809323012154183756275)
        ·
          refine ⟨132626713984518231275634413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88417809323012154183756275 132626713984518231275634413)
          ·
            refine ⟨49735017744194336728362905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132626713984518231275634413 49735017744194336728362905)
            ·
              refine ⟨37301263308145752546272179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49735017744194336728362905 37301263308145752546272179)
              ·
                refine ⟨55951894962218628819408269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37301263308145752546272179 55951894962218628819408269)
                ·
                  refine ⟨20981960610831985807278101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55951894962218628819408269 20981960610831985807278101)
                  ·
                    refine ⟨983529403632749334716161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20981960610831985807278101 983529403632749334716161)
                    ·
                      rfl

theorem cell23_5746250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_5746250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746250 prefixEnd_5746250 := by exact prefixLift 5746250
  have htrace : WordTrace (prefixWord ++ tailWord_5746250) baseStart_5746250 baseEnd_5746250 := by
    simpa [prefixWord, tailWord_5746250, baseEnd_5746250] using wordTrace_append hprefix tailTrace_5746250
  have hstable : (prefixWord ++ tailWord_5746250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746250).length < 2 ^ (prefixWord ++ tailWord_5746250).sum := by decide
  have hdescent : baseEnd_5746250 < baseStart_5746250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746257 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_5746257 : Nat := 118140960795 + 5746257 * 2 ^ 59
def prefixEnd_5746257 : Nat := 4983230072969 + 3 ^ 40 * 5746257 * 2
def baseEnd_5746257 : Nat := 2950591805262829476760951

theorem tailTrace_5746257 : CollatzResearch.WordTrace tailWord_5746257 prefixEnd_5746257 2950591805262829476760951 := by
  unfold tailWord_5746257
  simp only [CollatzResearch.WordTrace]
  refine ⟨209583210743299746408853025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139722140495533164272568683 209583210743299746408853025)
  ·
    refine ⟨157187408057474809806639769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209583210743299746408853025 157187408057474809806639769)
    ·
      refine ⟨117890556043106107354979827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157187408057474809806639769 117890556043106107354979827)
      ·
        refine ⟨176835834064659161032469741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117890556043106107354979827 176835834064659161032469741)
        ·
          refine ⟨66313437774247185387176153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176835834064659161032469741 66313437774247185387176153)
          ·
            refine ⟨49735078330685389040382115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66313437774247185387176153 49735078330685389040382115)
            ·
              refine ⟨74602617496028083560573173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49735078330685389040382115 74602617496028083560573173)
              ·
                refine ⟨6993995390252632833803735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74602617496028083560573173 6993995390252632833803735)
                ·
                  refine ⟨10490993085378949250705603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6993995390252632833803735 10490993085378949250705603)
                  ·
                    refine ⟨15736489628068423876058405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10490993085378949250705603 15736489628068423876058405)
                    ·
                      refine ⟨2950591805262829476760951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15736489628068423876058405 2950591805262829476760951)
                      ·
                        rfl

theorem cell23_5746257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_5746257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746257 prefixEnd_5746257 := by exact prefixLift 5746257
  have htrace : WordTrace (prefixWord ++ tailWord_5746257) baseStart_5746257 baseEnd_5746257 := by
    simpa [prefixWord, tailWord_5746257, baseEnd_5746257] using wordTrace_append hprefix tailTrace_5746257
  have hstable : (prefixWord ++ tailWord_5746257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746257).length < 2 ^ (prefixWord ++ tailWord_5746257).sum := by decide
  have hdescent : baseEnd_5746257 < baseStart_5746257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746262 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5746262 : Nat := 118140960795 + 5746262 * 2 ^ 59
def prefixEnd_5746262 : Nat := 4983230072969 + 3 ^ 40 * 5746262 * 2
def baseEnd_5746262 : Nat := 983531457555367319066143

theorem tailTrace_5746262 : CollatzResearch.WordTrace tailWord_5746262 prefixEnd_5746262 983531457555367319066143 := by
  unfold tailWord_5746262
  simp only [CollatzResearch.WordTrace]
  refine ⟨13098962069267602016424065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139722262072187754841856693 13098962069267602016424065)
  ·
    refine ⟨9824221551950701512318049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13098962069267602016424065 9824221551950701512318049)
    ·
      refine ⟨7368166163963026134238537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9824221551950701512318049 7368166163963026134238537)
      ·
        refine ⟨5526124622972269600678903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7368166163963026134238537 5526124622972269600678903)
        ·
          refine ⟨8289186934458404401018355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526124622972269600678903 8289186934458404401018355)
          ·
            refine ⟨12433780401687606601527533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289186934458404401018355 12433780401687606601527533)
            ·
              refine ⟨4662667650632852475572825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12433780401687606601527533 4662667650632852475572825)
              ·
                refine ⟨3497000737974639356679619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662667650632852475572825 3497000737974639356679619)
                ·
                  refine ⟨5245501106961959035019429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497000737974639356679619 5245501106961959035019429)
                  ·
                    refine ⟨983531457555367319066143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245501106961959035019429 983531457555367319066143)
                    ·
                      rfl

theorem cell23_5746262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5746262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746262 prefixEnd_5746262 := by exact prefixLift 5746262
  have htrace : WordTrace (prefixWord ++ tailWord_5746262) baseStart_5746262 baseEnd_5746262 := by
    simpa [prefixWord, tailWord_5746262, baseEnd_5746262] using wordTrace_append hprefix tailTrace_5746262
  have hstable : (prefixWord ++ tailWord_5746262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746262).length < 2 ^ (prefixWord ++ tailWord_5746262).sum := by decide
  have hdescent : baseEnd_5746262 < baseStart_5746262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746277 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_5746277 : Nat := 118140960795 + 5746277 * 2 ^ 59
def prefixEnd_5746277 : Nat := 4983230072969 + 3 ^ 40 * 5746277 * 2
def baseEnd_5746277 : Nat := 2950602074875919398510859

theorem tailTrace_5746277 : CollatzResearch.WordTrace tailWord_5746277 prefixEnd_5746277 2950602074875919398510859 := by
  unfold tailWord_5746277
  simp only [CollatzResearch.WordTrace]
  refine ⟨209583940203227289824581085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139722626802151526549720723 209583940203227289824581085)
  ·
    refine ⟨78593977576210233684217907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209583940203227289824581085 78593977576210233684217907)
    ·
      refine ⟨117890966364315350526326861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78593977576210233684217907 117890966364315350526326861)
      ·
        refine ⟨44209112386618256447372573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117890966364315350526326861 44209112386618256447372573)
        ·
          refine ⟨16578417144981846167764715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44209112386618256447372573 16578417144981846167764715)
          ·
            refine ⟨24867625717472769251647073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16578417144981846167764715 24867625717472769251647073)
            ·
              refine ⟨18650719288104576938735305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24867625717472769251647073 18650719288104576938735305)
              ·
                refine ⟨13988039466078432704051479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18650719288104576938735305 13988039466078432704051479)
                ·
                  refine ⟨20982059199117649056077219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13988039466078432704051479 20982059199117649056077219)
                  ·
                    refine ⟨31473088798676473584115829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20982059199117649056077219 31473088798676473584115829)
                    ·
                      refine ⟨2950602074875919398510859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31473088798676473584115829 2950602074875919398510859)
                      ·
                        rfl

theorem cell23_5746277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_5746277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746277 prefixEnd_5746277 := by exact prefixLift 5746277
  have htrace : WordTrace (prefixWord ++ tailWord_5746277) baseStart_5746277 baseEnd_5746277 := by
    simpa [prefixWord, tailWord_5746277, baseEnd_5746277] using wordTrace_append hprefix tailTrace_5746277
  have hstable : (prefixWord ++ tailWord_5746277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746277).length < 2 ^ (prefixWord ++ tailWord_5746277).sum := by decide
  have hdescent : baseEnd_5746277 < baseStart_5746277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746311 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_5746311 : Nat := 118140960795 + 5746311 * 2 ^ 59
def prefixEnd_5746311 : Nat := 4983230072969 + 3 ^ 40 * 5746311 * 2
def baseEnd_5746311 : Nat := 2950619533218172265485703

theorem tailTrace_5746311 : CollatzResearch.WordTrace tailWord_5746311 prefixEnd_5746311 2950619533218172265485703 := by
  unfold tailWord_5746311
  simp only [CollatzResearch.WordTrace]
  refine ⟨209585180285104113631318787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139723453523402742420879191 209585180285104113631318787)
  ·
    refine ⟨314377770427656170446978181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209585180285104113631318787 314377770427656170446978181)
    ·
      refine ⟨58945831955185531958808409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314377770427656170446978181 58945831955185531958808409)
      ·
        refine ⟨44209373966389148969106307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58945831955185531958808409 44209373966389148969106307)
        ·
          refine ⟨66314060949583723453659461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44209373966389148969106307 66314060949583723453659461)
          ·
            refine ⟨12433886428046948147561149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66314060949583723453659461 12433886428046948147561149)
            ·
              refine ⟨4662707410517605555335431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12433886428046948147561149 4662707410517605555335431)
              ·
                refine ⟨6994061115776408333003147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662707410517605555335431 6994061115776408333003147)
                ·
                  refine ⟨10491091673664612499504721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6994061115776408333003147 10491091673664612499504721)
                  ·
                    refine ⟨7868318755248459374628541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10491091673664612499504721 7868318755248459374628541)
                    ·
                      refine ⟨2950619533218172265485703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868318755248459374628541 2950619533218172265485703)
                      ·
                        rfl

theorem cell23_5746311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_5746311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746311 prefixEnd_5746311 := by exact prefixLift 5746311
  have htrace : WordTrace (prefixWord ++ tailWord_5746311) baseStart_5746311 baseEnd_5746311 := by
    simpa [prefixWord, tailWord_5746311, baseEnd_5746311] using wordTrace_append hprefix tailTrace_5746311
  have hstable : (prefixWord ++ tailWord_5746311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746311).length < 2 ^ (prefixWord ++ tailWord_5746311).sum := by decide
  have hdescent : baseEnd_5746311 < baseStart_5746311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746320 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_5746320 : Nat := 118140960795 + 5746320 * 2 ^ 59
def prefixEnd_5746320 : Nat := 4983230072969 + 3 ^ 40 * 5746320 * 2
def baseEnd_5746320 : Nat := 2950624154544062730273161

theorem tailTrace_5746320 : CollatzResearch.WordTrace tailWord_5746320 prefixEnd_5746320 2950624154544062730273161 := by
  unfold tailWord_5746320
  simp only [CollatzResearch.WordTrace]
  refine ⟨104792754271035754084198207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139723672361381005445597609 104792754271035754084198207)
  ·
    refine ⟨157189131406553631126297311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104792754271035754084198207 157189131406553631126297311)
    ·
      refine ⟨235783697109830446689445967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157189131406553631126297311 235783697109830446689445967)
      ·
        refine ⟨353675545664745670034168951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235783697109830446689445967 353675545664745670034168951)
        ·
          refine ⟨530513318497118505051253427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353675545664745670034168951 530513318497118505051253427)
          ·
            refine ⟨795769977745677757576880141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530513318497118505051253427 795769977745677757576880141)
            ·
              refine ⟨298413741654629159091330053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795769977745677757576880141 298413741654629159091330053)
              ·
                refine ⟨55952576560242967329624385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 298413741654629159091330053 55952576560242967329624385)
                ·
                  refine ⟨41964432420182225497218289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55952576560242967329624385 41964432420182225497218289)
                  ·
                    refine ⟨31473324315136669122913717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41964432420182225497218289 31473324315136669122913717)
                    ·
                      refine ⟨2950624154544062730273161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31473324315136669122913717 2950624154544062730273161)
                      ·
                        rfl

theorem cell23_5746320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_5746320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746320 prefixEnd_5746320 := by exact prefixLift 5746320
  have htrace : WordTrace (prefixWord ++ tailWord_5746320) baseStart_5746320 baseEnd_5746320 := by
    simpa [prefixWord, tailWord_5746320, baseEnd_5746320] using wordTrace_append hprefix tailTrace_5746320
  have hstable : (prefixWord ++ tailWord_5746320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746320).length < 2 ^ (prefixWord ++ tailWord_5746320).sum := by decide
  have hdescent : baseEnd_5746320 < baseStart_5746320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746417 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_5746417 : Nat := 118140960795 + 5746417 * 2 ^ 59
def prefixEnd_5746417 : Nat := 4983230072969 + 3 ^ 40 * 5746417 * 2
def baseEnd_5746417 : Nat := 983557987389182950253405

theorem tailTrace_5746417 : CollatzResearch.WordTrace tailWord_5746417 prefixEnd_5746417 983557987389182950253405 := by
  unfold tailWord_5746417
  simp only [CollatzResearch.WordTrace]
  refine ⟨209589046422720093734677505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139726030948480062489785003 209589046422720093734677505)
  ·
    refine ⟨157191784817040070301008129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209589046422720093734677505 157191784817040070301008129)
    ·
      refine ⟨117893838612780052725756097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157191784817040070301008129 117893838612780052725756097)
      ·
        refine ⟨88420378959585039544317073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117893838612780052725756097 88420378959585039544317073)
        ·
          refine ⟨66315284219688779658237805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88420378959585039544317073 66315284219688779658237805)
          ·
            refine ⟨24868231582383292371839177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66315284219688779658237805 24868231582383292371839177)
            ·
              refine ⟨18651173686787469278879383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24868231582383292371839177 18651173686787469278879383)
              ·
                refine ⟨27976760530181203918319075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18651173686787469278879383 27976760530181203918319075)
                ·
                  refine ⟨41965140795271805877478613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27976760530181203918319075 41965140795271805877478613)
                  ·
                    refine ⟨983557987389182950253405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41965140795271805877478613 983557987389182950253405)
                    ·
                      rfl

theorem cell23_5746417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_5746417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746417 prefixEnd_5746417 := by exact prefixLift 5746417
  have htrace : WordTrace (prefixWord ++ tailWord_5746417) baseStart_5746417 baseEnd_5746417 := by
    simpa [prefixWord, tailWord_5746417, baseEnd_5746417] using wordTrace_append hprefix tailTrace_5746417
  have hstable : (prefixWord ++ tailWord_5746417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746417).length < 2 ^ (prefixWord ++ tailWord_5746417).sum := by decide
  have hdescent : baseEnd_5746417 < baseStart_5746417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746464 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 5, 4]
def baseStart_5746464 : Nat := 118140960795 + 5746464 * 2 ^ 59
def prefixEnd_5746464 : Nat := 4983230072969 + 3 ^ 40 * 5746464 * 2
def baseEnd_5746464 : Nat := 983566031919436722290833

theorem tailTrace_5746464 : CollatzResearch.WordTrace tailWord_5746464 prefixEnd_5746464 983566031919436722290833 := by
  unfold tailWord_5746464
  simp only [CollatzResearch.WordTrace]
  refine ⟨104795380326774910380819223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139727173769033213841092297 104795380326774910380819223)
  ·
    refine ⟨157193070490162365571228835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104795380326774910380819223 157193070490162365571228835)
    ·
      refine ⟨235789605735243548356843253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157193070490162365571228835 235789605735243548356843253)
      ·
        refine ⟨22105275537679082658454055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235789605735243548356843253 22105275537679082658454055)
        ·
          refine ⟨33157913306518623987681083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22105275537679082658454055 33157913306518623987681083)
          ·
            refine ⟨49736869959777935981521625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33157913306518623987681083 49736869959777935981521625)
            ·
              refine ⟨37302652469833451986141219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49736869959777935981521625 37302652469833451986141219)
              ·
                refine ⟨55953978704750177979211829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37302652469833451986141219 55953978704750177979211829)
                ·
                  refine ⟨5245685503570329185551109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55953978704750177979211829 5245685503570329185551109)
                  ·
                    refine ⟨983566031919436722290833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245685503570329185551109 983566031919436722290833)
                    ·
                      rfl

theorem cell23_5746464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_5746464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746464 prefixEnd_5746464 := by exact prefixLift 5746464
  have htrace : WordTrace (prefixWord ++ tailWord_5746464) baseStart_5746464 baseEnd_5746464 := by
    simpa [prefixWord, tailWord_5746464, baseEnd_5746464] using wordTrace_append hprefix tailTrace_5746464
  have hstable : (prefixWord ++ tailWord_5746464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746464).length < 2 ^ (prefixWord ++ tailWord_5746464).sum := by decide
  have hdescent : baseEnd_5746464 < baseStart_5746464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746467 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4]
def baseStart_5746467 : Nat := 118140960795 + 5746467 * 2 ^ 59
def prefixEnd_5746467 : Nat := 4983230072969 + 3 ^ 40 * 5746467 * 2
def baseEnd_5746467 : Nat := 2950699636200273655134985

theorem tailTrace_5746467 : CollatzResearch.WordTrace tailWord_5746467 prefixEnd_5746467 2950699636200273655134985 := by
  unfold tailWord_5746467
  simp only [CollatzResearch.WordTrace]
  refine ⟨209590870072538952273997655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139727246715025968182665103 209590870072538952273997655)
  ·
    refine ⟨314386305108808428410996483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209590870072538952273997655 314386305108808428410996483)
    ·
      refine ⟨471579457663212642616494725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314386305108808428410996483 471579457663212642616494725)
      ·
        refine ⟨88421148311852370490592761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471579457663212642616494725 88421148311852370490592761)
        ·
          refine ⟨66315861233889277867944571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88421148311852370490592761 66315861233889277867944571)
          ·
            refine ⟨99473791850833916801916857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66315861233889277867944571 99473791850833916801916857)
            ·
              refine ⟨74605343888125437601437643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99473791850833916801916857 74605343888125437601437643)
              ·
                refine ⟨111908015832188156402156465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74605343888125437601437643 111908015832188156402156465)
                ·
                  refine ⟨83931011874141117301617349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111908015832188156402156465 83931011874141117301617349)
                  ·
                    refine ⟨15737064726401459494053253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83931011874141117301617349 15737064726401459494053253)
                    ·
                      refine ⟨2950699636200273655134985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15737064726401459494053253 2950699636200273655134985)
                      ·
                        rfl

theorem cell23_5746467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_5746467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746467 prefixEnd_5746467 := by exact prefixLift 5746467
  have htrace : WordTrace (prefixWord ++ tailWord_5746467) baseStart_5746467 baseEnd_5746467 := by
    simpa [prefixWord, tailWord_5746467, baseEnd_5746467] using wordTrace_append hprefix tailTrace_5746467
  have hstable : (prefixWord ++ tailWord_5746467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746467).length < 2 ^ (prefixWord ++ tailWord_5746467).sum := by decide
  have hdescent : baseEnd_5746467 < baseStart_5746467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746521 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 3]
def baseStart_5746521 : Nat := 118140960795 + 5746521 * 2 ^ 59
def prefixEnd_5746521 : Nat := 4983230072969 + 3 ^ 40 * 5746521 * 2
def baseEnd_5746521 : Nat := 2950727364155616443859737

theorem tailTrace_5746521 : CollatzResearch.WordTrace tailWord_5746521 prefixEnd_5746521 2950727364155616443859737 := by
  unfold tailWord_5746521
  simp only [CollatzResearch.WordTrace]
  refine ⟨209592839614343319496463417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139728559742895546330975611 209592839614343319496463417)
  ·
    refine ⟨157194629710757489622347563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209592839614343319496463417 157194629710757489622347563)
    ·
      refine ⟨235791944566136234433521345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157194629710757489622347563 235791944566136234433521345)
      ·
        refine ⟨176843958424602175825141009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235791944566136234433521345 176843958424602175825141009)
        ·
          refine ⟨132632968818451631868855757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176843958424602175825141009 132632968818451631868855757)
          ·
            refine ⟨49737363306919361950820909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132632968818451631868855757 49737363306919361950820909)
            ·
              refine ⟨18651511240094760731557841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49737363306919361950820909 18651511240094760731557841)
              ·
                refine ⟨13988633430071070548668381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18651511240094760731557841 13988633430071070548668381)
                ·
                  refine ⟨5245737536276651455750643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13988633430071070548668381 5245737536276651455750643)
                  ·
                    refine ⟨7868606304414977183625965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245737536276651455750643 7868606304414977183625965)
                    ·
                      refine ⟨2950727364155616443859737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868606304414977183625965 2950727364155616443859737)
                      ·
                        rfl

theorem cell23_5746521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_5746521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746521 prefixEnd_5746521 := by exact prefixLift 5746521
  have htrace : WordTrace (prefixWord ++ tailWord_5746521) baseStart_5746521 baseEnd_5746521 := by
    simpa [prefixWord, tailWord_5746521, baseEnd_5746521] using wordTrace_append hprefix tailTrace_5746521
  have hstable : (prefixWord ++ tailWord_5746521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746521).length < 2 ^ (prefixWord ++ tailWord_5746521).sum := by decide
  have hdescent : baseEnd_5746521 < baseStart_5746521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746564 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5746564 : Nat := 118140960795 + 5746564 * 2 ^ 59
def prefixEnd_5746564 : Nat := 4983230072969 + 3 ^ 40 * 5746564 * 2
def baseEnd_5746564 : Nat := 2950749443823759775622039

theorem tailTrace_5746564 : CollatzResearch.WordTrace tailWord_5746564 prefixEnd_5746564 2950749443823759775622039 := by
  unfold tailWord_5746564
  simp only [CollatzResearch.WordTrace]
  refine ⟨104797203976593768920139373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139729605302125025226852497 104797203976593768920139373)
  ·
    refine ⟨39298951491222663345052265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104797203976593768920139373 39298951491222663345052265)
    ·
      refine ⟨29474213618416997508789199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39298951491222663345052265 29474213618416997508789199)
      ·
        refine ⟨44211320427625496263183799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29474213618416997508789199 44211320427625496263183799)
        ·
          refine ⟨66316980641438244394775699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44211320427625496263183799 66316980641438244394775699)
          ·
            refine ⟨99475470962157366592163549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66316980641438244394775699 99475470962157366592163549)
            ·
              refine ⟨37303301610809012472061331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99475470962157366592163549 37303301610809012472061331)
              ·
                refine ⟨55954952416213518708091997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37303301610809012472061331 55954952416213518708091997)
                ·
                  refine ⟨20983107156080069515534499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55954952416213518708091997 20983107156080069515534499)
                  ·
                    refine ⟨31474660734120104273301749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20983107156080069515534499 31474660734120104273301749)
                    ·
                      refine ⟨2950749443823759775622039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31474660734120104273301749 2950749443823759775622039)
                      ·
                        rfl

theorem cell23_5746564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5746564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746564 prefixEnd_5746564 := by exact prefixLift 5746564
  have htrace : WordTrace (prefixWord ++ tailWord_5746564) baseStart_5746564 baseEnd_5746564 := by
    simpa [prefixWord, tailWord_5746564, baseEnd_5746564] using wordTrace_append hprefix tailTrace_5746564
  have hstable : (prefixWord ++ tailWord_5746564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746564).length < 2 ^ (prefixWord ++ tailWord_5746564).sum := by decide
  have hdescent : baseEnd_5746564 < baseStart_5746564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746578 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5746578 : Nat := 118140960795 + 5746578 * 2 ^ 59
def prefixEnd_5746578 : Nat := 4983230072969 + 3 ^ 40 * 5746578 * 2
def baseEnd_5746578 : Nat := 2950756632552922720846975

theorem tailTrace_5746578 : CollatzResearch.WordTrace tailWord_5746578 prefixEnd_5746578 2950756632552922720846975 := by
  unfold tailWord_5746578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52398729643784204557822097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139729945716757878820858925 52398729643784204557822097)
  ·
    refine ⟨39299047232838153418366573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52398729643784204557822097 39299047232838153418366573)
    ·
      refine ⟨14737142712314307531887465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39299047232838153418366573 14737142712314307531887465)
      ·
        refine ⟨11052857034235730648915599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14737142712314307531887465 11052857034235730648915599)
        ·
          refine ⟨16579285551353595973373399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11052857034235730648915599 16579285551353595973373399)
          ·
            refine ⟨24868928327030393960060099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16579285551353595973373399 24868928327030393960060099)
            ·
              refine ⟨37303392490545590940090149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24868928327030393960060099 37303392490545590940090149)
              ·
                refine ⟨6994386091977298301266903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37303392490545590940090149 6994386091977298301266903)
                ·
                  refine ⟨10491579137965947451900355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6994386091977298301266903 10491579137965947451900355)
                  ·
                    refine ⟨15737368706948921177850533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10491579137965947451900355 15737368706948921177850533)
                    ·
                      refine ⟨2950756632552922720846975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15737368706948921177850533 2950756632552922720846975)
                      ·
                        rfl

theorem cell23_5746578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5746578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746578 prefixEnd_5746578 := by exact prefixLift 5746578
  have htrace : WordTrace (prefixWord ++ tailWord_5746578) baseStart_5746578 baseEnd_5746578 := by
    simpa [prefixWord, tailWord_5746578, baseEnd_5746578] using wordTrace_append hprefix tailTrace_5746578
  have hstable : (prefixWord ++ tailWord_5746578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746578).length < 2 ^ (prefixWord ++ tailWord_5746578).sum := by decide
  have hdescent : baseEnd_5746578 < baseStart_5746578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746606 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5746606 : Nat := 118140960795 + 5746606 * 2 ^ 59
def prefixEnd_5746606 : Nat := 4983230072969 + 3 ^ 40 * 5746606 * 2
def baseEnd_5746606 : Nat := 2950771010011248611296847

theorem tailTrace_5746606 : CollatzResearch.WordTrace tailWord_5746606 prefixEnd_5746606 2950771010011248611296847 := by
  unfold tailWord_5746606
  simp only [CollatzResearch.WordTrace]
  refine ⟨26199492477379422376663459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139730626546023586008871781 26199492477379422376663459)
  ·
    refine ⟨39299238716069133564995189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26199492477379422376663459 39299238716069133564995189)
    ·
      refine ⟨3684303629631481271718299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39299238716069133564995189 3684303629631481271718299)
      ·
        refine ⟨5526455444447221907577449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684303629631481271718299 5526455444447221907577449)
        ·
          refine ⟨4144841583335416430683087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5526455444447221907577449 4144841583335416430683087)
          ·
            refine ⟨6217262375003124646024631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4144841583335416430683087 6217262375003124646024631)
            ·
              refine ⟨9325893562504686969036947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6217262375003124646024631 9325893562504686969036947)
              ·
                refine ⟨13988840343757030453555421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9325893562504686969036947 13988840343757030453555421)
                ·
                  refine ⟨5245815128908886420083283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13988840343757030453555421 5245815128908886420083283)
                  ·
                    refine ⟨7868722693363329630124925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245815128908886420083283 7868722693363329630124925)
                    ·
                      refine ⟨2950771010011248611296847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868722693363329630124925 2950771010011248611296847)
                      ·
                        rfl

theorem cell23_5746606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5746606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746606 prefixEnd_5746606 := by exact prefixLift 5746606
  have htrace : WordTrace (prefixWord ++ tailWord_5746606) baseStart_5746606 baseEnd_5746606 := by
    simpa [prefixWord, tailWord_5746606, baseEnd_5746606] using wordTrace_append hprefix tailTrace_5746606
  have hstable : (prefixWord ++ tailWord_5746606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746606).length < 2 ^ (prefixWord ++ tailWord_5746606).sum := by decide
  have hdescent : baseEnd_5746606 < baseStart_5746606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746611 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 3]
def baseStart_5746611 : Nat := 118140960795 + 5746611 * 2 ^ 59
def prefixEnd_5746611 : Nat := 4983230072969 + 3 ^ 40 * 5746611 * 2
def baseEnd_5746611 : Nat := 2950773577414521091734323

theorem tailTrace_5746611 : CollatzResearch.WordTrace tailWord_5746611 prefixEnd_5746611 2950773577414521091734323 := by
  unfold tailWord_5746611
  simp only [CollatzResearch.WordTrace]
  refine ⟨209596122184017264867239687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139730748122678176578159791 209596122184017264867239687)
  ·
    refine ⟨314394183276025897300859531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209596122184017264867239687 314394183276025897300859531)
    ·
      refine ⟨471591274914038845951289297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314394183276025897300859531 471591274914038845951289297)
      ·
        refine ⟨353693456185529134463466973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471591274914038845951289297 353693456185529134463466973)
        ·
          refine ⟨132635046069573425423800115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353693456185529134463466973 132635046069573425423800115)
          ·
            refine ⟨198952569104360138135700173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132635046069573425423800115 198952569104360138135700173)
            ·
              refine ⟨74607213414135051800887565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198952569104360138135700173 74607213414135051800887565)
              ·
                refine ⟨27977705030300644425332837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74607213414135051800887565 27977705030300644425332837)
                ·
                  refine ⟨5245819693181370829749907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27977705030300644425332837 5245819693181370829749907)
                  ·
                    refine ⟨7868729539772056244624861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245819693181370829749907 7868729539772056244624861)
                    ·
                      refine ⟨2950773577414521091734323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868729539772056244624861 2950773577414521091734323)
                      ·
                        rfl

theorem cell23_5746611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_5746611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746611 prefixEnd_5746611 := by exact prefixLift 5746611
  have htrace : WordTrace (prefixWord ++ tailWord_5746611) baseStart_5746611 baseEnd_5746611 := by
    simpa [prefixWord, tailWord_5746611, baseEnd_5746611] using wordTrace_append hprefix tailTrace_5746611
  have hstable : (prefixWord ++ tailWord_5746611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746611).length < 2 ^ (prefixWord ++ tailWord_5746611).sum := by decide
  have hdescent : baseEnd_5746611 < baseStart_5746611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746638 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_5746638 : Nat := 118140960795 + 5746638 * 2 ^ 59
def prefixEnd_5746638 : Nat := 4983230072969 + 3 ^ 40 * 5746638 * 2
def baseEnd_5746638 : Nat := 2950787441392192486096699

theorem tailTrace_5746638 : CollatzResearch.WordTrace tailWord_5746638 prefixEnd_5746638 2950787441392192486096699 := by
  unfold tailWord_5746638
  simp only [CollatzResearch.WordTrace]
  refine ⟨26199638369364931059809071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139731404636612965652315045 26199638369364931059809071)
  ·
    refine ⟨39299457554047396589713607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26199638369364931059809071 39299457554047396589713607)
    ·
      refine ⟨58949186331071094884570411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39299457554047396589713607 58949186331071094884570411)
      ·
        refine ⟨88423779496606642326855617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58949186331071094884570411 88423779496606642326855617)
        ·
          refine ⟨66317834622454981745141713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88423779496606642326855617 66317834622454981745141713)
          ·
            refine ⟨49738375966841236308856285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66317834622454981745141713 49738375966841236308856285)
            ·
              refine ⟨18651890987565463615821107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49738375966841236308856285 18651890987565463615821107)
              ·
                refine ⟨27977836481348195423731661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18651890987565463615821107 27977836481348195423731661)
                ·
                  refine ⟨10491688680505573283899373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27977836481348195423731661 10491688680505573283899373)
                  ·
                    refine ⟨3934383255189589981462265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10491688680505573283899373 3934383255189589981462265)
                    ·
                      refine ⟨2950787441392192486096699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934383255189589981462265 2950787441392192486096699)
                      ·
                        rfl

theorem cell23_5746638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_5746638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746638 prefixEnd_5746638 := by exact prefixLift 5746638
  have htrace : WordTrace (prefixWord ++ tailWord_5746638) baseStart_5746638 baseEnd_5746638 := by
    simpa [prefixWord, tailWord_5746638, baseEnd_5746638] using wordTrace_append hprefix tailTrace_5746638
  have hstable : (prefixWord ++ tailWord_5746638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746638).length < 2 ^ (prefixWord ++ tailWord_5746638).sum := by decide
  have hdescent : baseEnd_5746638 < baseStart_5746638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746664 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5746664 : Nat := 118140960795 + 5746664 * 2 ^ 59
def prefixEnd_5746664 : Nat := 4983230072969 + 3 ^ 40 * 5746664 * 2
def baseEnd_5746664 : Nat := 2950800791889209384371579

theorem tailTrace_5746664 : CollatzResearch.WordTrace tailWord_5746664 prefixEnd_5746664 2950800791889209384371579 := by
  unfold tailWord_5746664
  simp only [CollatzResearch.WordTrace]
  refine ⟨104799027626412627459459523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139732036835216836612612697 104799027626412627459459523)
  ·
    refine ⟨157198541439618941189189285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104799027626412627459459523 157198541439618941189189285)
    ·
      refine ⟨29474726519928551472972991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157198541439618941189189285 29474726519928551472972991)
      ·
        refine ⟨44212089779892827209459487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29474726519928551472972991 44212089779892827209459487)
        ·
          refine ⟨66318134669839240814189231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44212089779892827209459487 66318134669839240814189231)
          ·
            refine ⟨99477202004758861221283847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66318134669839240814189231 99477202004758861221283847)
            ·
              refine ⟨149215803007138291831925771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99477202004758861221283847 149215803007138291831925771)
              ·
                refine ⟨223823704510707437747888657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149215803007138291831925771 223823704510707437747888657)
                ·
                  refine ⟨167867778383030578310916493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223823704510707437747888657 167867778383030578310916493)
                  ·
                    refine ⟨62950416893636466866593685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167867778383030578310916493 62950416893636466866593685)
                    ·
                      refine ⟨2950800791889209384371579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62950416893636466866593685 2950800791889209384371579)
                      ·
                        rfl

theorem cell23_5746664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5746664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746664 prefixEnd_5746664 := by exact prefixLift 5746664
  have htrace : WordTrace (prefixWord ++ tailWord_5746664) baseStart_5746664 baseEnd_5746664 := by
    simpa [prefixWord, tailWord_5746664, baseEnd_5746664] using wordTrace_append hprefix tailTrace_5746664
  have hstable : (prefixWord ++ tailWord_5746664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746664).length < 2 ^ (prefixWord ++ tailWord_5746664).sum := by decide
  have hdescent : baseEnd_5746664 < baseStart_5746664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746668 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 4, 2, 2]
def baseStart_5746668 : Nat := 118140960795 + 5746668 * 2 ^ 59
def prefixEnd_5746668 : Nat := 4983230072969 + 3 ^ 40 * 5746668 * 2
def baseEnd_5746668 : Nat := 2950802845811827368721561

theorem tailTrace_5746668 : CollatzResearch.WordTrace tailWord_5746668 prefixEnd_5746668 2950802845811827368721561 := by
  unfold tailWord_5746668
  simp only [CollatzResearch.WordTrace]
  refine ⟨104799100572405381801032329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139732134096540509068043105 104799100572405381801032329)
  ·
    refine ⟨78599325429304036350774247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104799100572405381801032329 78599325429304036350774247)
    ·
      refine ⟨117898988143956054526161371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78599325429304036350774247 117898988143956054526161371)
      ·
        refine ⟨176848482215934081789242057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117898988143956054526161371 176848482215934081789242057)
        ·
          refine ⟨132636361661950561341931543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176848482215934081789242057 132636361661950561341931543)
          ·
            refine ⟨198954542492925842012897315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132636361661950561341931543 198954542492925842012897315)
            ·
              refine ⟨298431813739388763019345973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198954542492925842012897315 298431813739388763019345973)
              ·
                refine ⟨27977982538067696533063685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298431813739388763019345973 27977982538067696533063685)
                ·
                  refine ⟨5245871725887693099949441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27977982538067696533063685 5245871725887693099949441)
                  ·
                    refine ⟨3934403794415769824962081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5245871725887693099949441 3934403794415769824962081)
                    ·
                      refine ⟨2950802845811827368721561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934403794415769824962081 2950802845811827368721561)
                      ·
                        rfl

theorem cell23_5746668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_5746668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746668 prefixEnd_5746668 := by exact prefixLift 5746668
  have htrace : WordTrace (prefixWord ++ tailWord_5746668) baseStart_5746668 baseEnd_5746668 := by
    simpa [prefixWord, tailWord_5746668, baseEnd_5746668] using wordTrace_append hprefix tailTrace_5746668
  have hstable : (prefixWord ++ tailWord_5746668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746668).length < 2 ^ (prefixWord ++ tailWord_5746668).sum := by decide
  have hdescent : baseEnd_5746668 < baseStart_5746668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746678 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_5746678 : Nat := 118140960795 + 5746678 * 2 ^ 59
def prefixEnd_5746678 : Nat := 4983230072969 + 3 ^ 40 * 5746678 * 2
def baseEnd_5746678 : Nat := 983602660206124109865505

theorem tailTrace_5746678 : CollatzResearch.WordTrace tailWord_5746678 prefixEnd_5746678 983602660206124109865505 := by
  unfold tailWord_5746678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13099910367173408456870543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139732377249849690206619125 13099910367173408456870543)
  ·
    refine ⟨19649865550760112685305815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13099910367173408456870543 19649865550760112685305815)
    ·
      refine ⟨29474798326140169027958723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19649865550760112685305815 29474798326140169027958723)
      ·
        refine ⟨44212197489210253541938085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29474798326140169027958723 44212197489210253541938085)
        ·
          refine ⟨8289787029226922539113391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44212197489210253541938085 8289787029226922539113391)
          ·
            refine ⟨12434680543840383808670087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289787029226922539113391 12434680543840383808670087)
            ·
              refine ⟨18652020815760575713005131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12434680543840383808670087 18652020815760575713005131)
              ·
                refine ⟨27978031223640863569507697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18652020815760575713005131 27978031223640863569507697)
                ·
                  refine ⟨20983523417730647677130773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27978031223640863569507697 20983523417730647677130773)
                  ·
                    refine ⟨983602660206124109865505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20983523417730647677130773 983602660206124109865505)
                    ·
                      rfl

theorem cell23_5746678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_5746678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746678 prefixEnd_5746678 := by exact prefixLift 5746678
  have htrace : WordTrace (prefixWord ++ tailWord_5746678) baseStart_5746678 baseEnd_5746678 := by
    simpa [prefixWord, tailWord_5746678, baseEnd_5746678] using wordTrace_append hprefix tailTrace_5746678
  have hstable : (prefixWord ++ tailWord_5746678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746678).length < 2 ^ (prefixWord ++ tailWord_5746678).sum := by decide
  have hdescent : baseEnd_5746678 < baseStart_5746678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746681 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_5746681 : Nat := 118140960795 + 5746681 * 2 ^ 59
def prefixEnd_5746681 : Nat := 4983230072969 + 3 ^ 40 * 5746681 * 2
def baseEnd_5746681 : Nat := 2950809521060335817859001

theorem tailTrace_5746681 : CollatzResearch.WordTrace tailWord_5746681 prefixEnd_5746681 2950809521060335817859001 := by
  unfold tailWord_5746681
  simp only [CollatzResearch.WordTrace]
  refine ⟨209598675293763666822287897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139732450195842444548191931 209598675293763666822287897)
  ·
    refine ⟨157199006470322750116715923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209598675293763666822287897 157199006470322750116715923)
    ·
      refine ⟨235798509705484125175073885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157199006470322750116715923 235798509705484125175073885)
      ·
        refine ⟨88424441139556546940652707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235798509705484125175073885 88424441139556546940652707)
        ·
          refine ⟨132636661709334820410979061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88424441139556546940652707 132636661709334820410979061)
          ·
            refine ⟨12434687035250139413529287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132636661709334820410979061 12434687035250139413529287)
            ·
              refine ⟨18652030552875209120293931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12434687035250139413529287 18652030552875209120293931)
              ·
                refine ⟨27978045829312813680440897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18652030552875209120293931 27978045829312813680440897)
                ·
                  refine ⟨20983534371984610260330673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27978045829312813680440897 20983534371984610260330673)
                  ·
                    refine ⟨15737650778988457695248005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20983534371984610260330673 15737650778988457695248005)
                    ·
                      refine ⟨2950809521060335817859001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15737650778988457695248005 2950809521060335817859001)
                      ·
                        rfl

theorem cell23_5746681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_5746681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746681 prefixEnd_5746681 := by exact prefixLift 5746681
  have htrace : WordTrace (prefixWord ++ tailWord_5746681) baseStart_5746681 baseEnd_5746681 := by
    simpa [prefixWord, tailWord_5746681, baseEnd_5746681] using wordTrace_append hprefix tailTrace_5746681
  have hstable : (prefixWord ++ tailWord_5746681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746681).length < 2 ^ (prefixWord ++ tailWord_5746681).sum := by decide
  have hdescent : baseEnd_5746681 < baseStart_5746681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746685 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_5746685 : Nat := 118140960795 + 5746685 * 2 ^ 59
def prefixEnd_5746685 : Nat := 4983230072969 + 3 ^ 40 * 5746685 * 2
def baseEnd_5746685 : Nat := 2950811574982953802208983

theorem tailTrace_5746685 : CollatzResearch.WordTrace tailWord_5746685 prefixEnd_5746685 2950811574982953802208983 := by
  unfold tailWord_5746685
  simp only [CollatzResearch.WordTrace]
  refine ⟨209598821185749175505433509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139732547457166117003622339 209598821185749175505433509)
  ·
    refine ⟨39299778972327970407268783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209598821185749175505433509 39299778972327970407268783)
    ·
      refine ⟨58949668458491955610903175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39299778972327970407268783 58949668458491955610903175)
      ·
        refine ⟨88424502687737933416354763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58949668458491955610903175 88424502687737933416354763)
        ·
          refine ⟨132636754031606900124532145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88424502687737933416354763 132636754031606900124532145)
          ·
            refine ⟨99477565523705175093399109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132636754031606900124532145 99477565523705175093399109)
            ·
              refine ⟨18652043535694720330012333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99477565523705175093399109 18652043535694720330012333)
              ·
                refine ⟨6994516325885520123754625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18652043535694720330012333 6994516325885520123754625)
                ·
                  refine ⟨5245887244414140092815969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6994516325885520123754625 5245887244414140092815969)
                  ·
                    refine ⟨3934415433310605069611977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5245887244414140092815969 3934415433310605069611977)
                    ·
                      refine ⟨2950811574982953802208983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934415433310605069611977 2950811574982953802208983)
                      ·
                        rfl

theorem cell23_5746685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_5746685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746685 prefixEnd_5746685 := by exact prefixLift 5746685
  have htrace : WordTrace (prefixWord ++ tailWord_5746685) baseStart_5746685 baseEnd_5746685 := by
    simpa [prefixWord, tailWord_5746685, baseEnd_5746685] using wordTrace_append hprefix tailTrace_5746685
  have hstable : (prefixWord ++ tailWord_5746685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746685).length < 2 ^ (prefixWord ++ tailWord_5746685).sum := by decide
  have hdescent : baseEnd_5746685 < baseStart_5746685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746704 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_5746704 : Nat := 118140960795 + 5746704 * 2 ^ 59
def prefixEnd_5746704 : Nat := 4983230072969 + 3 ^ 40 * 5746704 * 2
def baseEnd_5746704 : Nat := 983607110371796409290465

theorem tailTrace_5746704 : CollatzResearch.WordTrace tailWord_5746704 prefixEnd_5746704 983607110371796409290465 := by
  unfold tailWord_5746704
  simp only [CollatzResearch.WordTrace]
  refine ⟨104799757086340170875187583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139733009448453561166916777 104799757086340170875187583)
  ·
    refine ⟨157199635629510256312781375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104799757086340170875187583 157199635629510256312781375)
    ·
      refine ⟨235799453444265384469172063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157199635629510256312781375 235799453444265384469172063)
      ·
        refine ⟨353699180166398076703758095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235799453444265384469172063 353699180166398076703758095)
        ·
          refine ⟨530548770249597115055637143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353699180166398076703758095 530548770249597115055637143)
          ·
            refine ⟨795823155374395672583455715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530548770249597115055637143 795823155374395672583455715)
            ·
              refine ⟨1193734733061593508875183573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795823155374395672583455715 1193734733061593508875183573)
              ·
                refine ⟨27978157806131097864262115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1193734733061593508875183573 27978157806131097864262115)
                ·
                  refine ⟨41967236709196646796393173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27978157806131097864262115 41967236709196646796393173)
                  ·
                    refine ⟨983607110371796409290465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41967236709196646796393173 983607110371796409290465)
                    ·
                      rfl

theorem cell23_5746704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_5746704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746704 prefixEnd_5746704 := by exact prefixLift 5746704
  have htrace : WordTrace (prefixWord ++ tailWord_5746704) baseStart_5746704 baseEnd_5746704 := by
    simpa [prefixWord, tailWord_5746704, baseEnd_5746704] using wordTrace_append hprefix tailTrace_5746704
  have hstable : (prefixWord ++ tailWord_5746704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746704).length < 2 ^ (prefixWord ++ tailWord_5746704).sum := by decide
  have hdescent : baseEnd_5746704 < baseStart_5746704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746741 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_5746741 : Nat := 118140960795 + 5746741 * 2 ^ 59
def prefixEnd_5746741 : Nat := 4983230072969 + 3 ^ 40 * 5746741 * 2
def baseEnd_5746741 : Nat := 2950840329899605583108725

theorem tailTrace_5746741 : CollatzResearch.WordTrace tailWord_5746741 prefixEnd_5746741 2950840329899605583108725 := by
  unfold tailWord_5746741
  simp only [CollatzResearch.WordTrace]
  refine ⟨209600863673546297069472077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139733909115697531379648051 209600863673546297069472077)
  ·
    refine ⟨78600323877579861401052029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209600863673546297069472077 78600323877579861401052029)
    ·
      refine ⟨29475121454092448025394511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78600323877579861401052029 29475121454092448025394511)
      ·
        refine ⟨44212682181138672038091767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29475121454092448025394511 44212682181138672038091767)
        ·
          refine ⟨66319023271708008057137651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44212682181138672038091767 66319023271708008057137651)
          ·
            refine ⟨99478534907562012085706477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66319023271708008057137651 99478534907562012085706477)
            ·
              refine ⟨37304450590335754532139929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99478534907562012085706477 37304450590335754532139929)
              ·
                refine ⟨27978337942751815899104947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37304450590335754532139929 27978337942751815899104947)
                ·
                  refine ⟨41967506914127723848657421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27978337942751815899104947 41967506914127723848657421)
                  ·
                    refine ⟨15737815092797896443246533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41967506914127723848657421 15737815092797896443246533)
                    ·
                      refine ⟨2950840329899605583108725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15737815092797896443246533 2950840329899605583108725)
                      ·
                        rfl

theorem cell23_5746741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_5746741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746741 prefixEnd_5746741 := by exact prefixLift 5746741
  have htrace : WordTrace (prefixWord ++ tailWord_5746741) baseStart_5746741 baseEnd_5746741 := by
    simpa [prefixWord, tailWord_5746741, baseEnd_5746741] using wordTrace_append hprefix tailTrace_5746741
  have hstable : (prefixWord ++ tailWord_5746741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746741).length < 2 ^ (prefixWord ++ tailWord_5746741).sum := by decide
  have hdescent : baseEnd_5746741 < baseStart_5746741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746761 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_5746761 : Nat := 118140960795 + 5746761 * 2 ^ 59
def prefixEnd_5746761 : Nat := 4983230072969 + 3 ^ 40 * 5746761 * 2
def baseEnd_5746761 : Nat := 2950850599512695504858633

theorem tailTrace_5746761 : CollatzResearch.WordTrace tailWord_5746761 prefixEnd_5746761 2950850599512695504858633 := by
  unfold tailWord_5746761
  simp only [CollatzResearch.WordTrace]
  refine ⟨209601593133473840485200137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139734395422315893656800091 209601593133473840485200137)
  ·
    refine ⟨157201194850105380363900103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209601593133473840485200137 157201194850105380363900103)
    ·
      refine ⟨235801792275158070545850155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157201194850105380363900103 235801792275158070545850155)
      ·
        refine ⟨353702688412737105818775233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235801792275158070545850155 353702688412737105818775233)
        ·
          refine ⟨265277016309552829364081425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353702688412737105818775233 265277016309552829364081425)
          ·
            refine ⟨198957762232164622023061069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265277016309552829364081425 198957762232164622023061069)
            ·
              refine ⟨74609160837061733258647901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198957762232164622023061069 74609160837061733258647901)
              ·
                refine ⟨27978435313898149971992963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74609160837061733258647901 27978435313898149971992963)
                ·
                  refine ⟨41967652970847224957989445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27978435313898149971992963 41967652970847224957989445)
                  ·
                    refine ⟨7868934932033854679623021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41967652970847224957989445 7868934932033854679623021)
                    ·
                      refine ⟨2950850599512695504858633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868934932033854679623021 2950850599512695504858633)
                      ·
                        rfl

theorem cell23_5746761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_5746761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746761 prefixEnd_5746761 := by exact prefixLift 5746761
  have htrace : WordTrace (prefixWord ++ tailWord_5746761) baseStart_5746761 baseEnd_5746761 := by
    simpa [prefixWord, tailWord_5746761, baseEnd_5746761] using wordTrace_append hprefix tailTrace_5746761
  have hstable : (prefixWord ++ tailWord_5746761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746761).length < 2 ^ (prefixWord ++ tailWord_5746761).sum := by decide
  have hdescent : baseEnd_5746761 < baseStart_5746761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746778 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_5746778 : Nat := 118140960795 + 5746778 * 2 ^ 59
def prefixEnd_5746778 : Nat := 4983230072969 + 3 ^ 40 * 5746778 * 2
def baseEnd_5746778 : Nat := 2950859328683821938346055

theorem tailTrace_5746778 : CollatzResearch.WordTrace tailWord_5746778 prefixEnd_5746778 2950859328683821938346055 := by
  unfold tailWord_5746778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52400553293603063097142247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139734808782941501592379325 52400553293603063097142247)
  ·
    refine ⟨78600829940404594645713371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52400553293603063097142247 78600829940404594645713371)
    ·
      refine ⟨117901244910606891968570057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78600829940404594645713371 117901244910606891968570057)
      ·
        refine ⟨88425933682955168976427543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117901244910606891968570057 88425933682955168976427543)
        ·
          refine ⟨132638900524432753464641315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88425933682955168976427543 132638900524432753464641315)
          ·
            refine ⟨198958350786649130196961973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132638900524432753464641315 198958350786649130196961973)
            ·
              refine ⟨18652345386248355955965185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198958350786649130196961973 18652345386248355955965185)
              ·
                refine ⟨13989259039686266966973889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18652345386248355955965185 13989259039686266966973889)
                ·
                  refine ⟨10491944279764700225230417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13989259039686266966973889 10491944279764700225230417)
                  ·
                    refine ⟨7868958209823525168922813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10491944279764700225230417 7868958209823525168922813)
                    ·
                      refine ⟨2950859328683821938346055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868958209823525168922813 2950859328683821938346055)
                      ·
                        rfl

theorem cell23_5746778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_5746778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746778 prefixEnd_5746778 := by exact prefixLift 5746778
  have htrace : WordTrace (prefixWord ++ tailWord_5746778) baseStart_5746778 baseEnd_5746778 := by
    simpa [prefixWord, tailWord_5746778, baseEnd_5746778] using wordTrace_append hprefix tailTrace_5746778
  have hstable : (prefixWord ++ tailWord_5746778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746778).length < 2 ^ (prefixWord ++ tailWord_5746778).sum := by decide
  have hdescent : baseEnd_5746778 < baseStart_5746778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746782 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5746782 : Nat := 118140960795 + 5746782 * 2 ^ 59
def prefixEnd_5746782 : Nat := 4983230072969 + 3 ^ 40 * 5746782 * 2
def baseEnd_5746782 : Nat := 2950861382606439922696037

theorem tailTrace_5746782 : CollatzResearch.WordTrace tailWord_5746782 prefixEnd_5746782 2950861382606439922696037 := by
  unfold tailWord_5746782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26200294883299720133964325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139734906044265174047809733 26200294883299720133964325)
  ·
    refine ⟨4912555290618697525118311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26200294883299720133964325 4912555290618697525118311)
    ·
      refine ⟨7368832935928046287677467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4912555290618697525118311 7368832935928046287677467)
      ·
        refine ⟨11053249403892069431516201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7368832935928046287677467 11053249403892069431516201)
        ·
          refine ⟨8289937052919052073637151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11053249403892069431516201 8289937052919052073637151)
          ·
            refine ⟨12434905579378578110455727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289937052919052073637151 12434905579378578110455727)
            ·
              refine ⟨18652358369067867165683591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12434905579378578110455727 18652358369067867165683591)
              ·
                refine ⟨27978537553601800748525387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18652358369067867165683591 27978537553601800748525387)
                ·
                  refine ⟨41967806330402701122788081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27978537553601800748525387 41967806330402701122788081)
                  ·
                    refine ⟨31475854747802025842091061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41967806330402701122788081 31475854747802025842091061)
                    ·
                      refine ⟨2950861382606439922696037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31475854747802025842091061 2950861382606439922696037)
                      ·
                        rfl

theorem cell23_5746782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5746782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746782 prefixEnd_5746782 := by exact prefixLift 5746782
  have htrace : WordTrace (prefixWord ++ tailWord_5746782) baseStart_5746782 baseEnd_5746782 := by
    simpa [prefixWord, tailWord_5746782, baseEnd_5746782] using wordTrace_append hprefix tailTrace_5746782
  have hstable : (prefixWord ++ tailWord_5746782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746782).length < 2 ^ (prefixWord ++ tailWord_5746782).sum := by decide
  have hdescent : baseEnd_5746782 < baseStart_5746782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746798 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_5746798 : Nat := 118140960795 + 5746798 * 2 ^ 59
def prefixEnd_5746798 : Nat := 4983230072969 + 3 ^ 40 * 5746798 * 2
def baseEnd_5746798 : Nat := 327874399810767984455107

theorem tailTrace_5746798 : CollatzResearch.WordTrace tailWord_5746798 prefixEnd_5746798 327874399810767984455107 := by
  unfold tailWord_5746798
  simp only [CollatzResearch.WordTrace]
  refine ⟨26200367829292474475537131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139735295089559863869531365 26200367829292474475537131)
  ·
    refine ⟨39300551743938711713305697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26200367829292474475537131 39300551743938711713305697)
    ·
      refine ⟨29475413807954033784979273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39300551743938711713305697 29475413807954033784979273)
      ·
        refine ⟨22106560355965525338734455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29475413807954033784979273 22106560355965525338734455)
        ·
          refine ⟨33159840533948288008101683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22106560355965525338734455 33159840533948288008101683)
          ·
            refine ⟨49739760800922432012152525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33159840533948288008101683 49739760800922432012152525)
            ·
              refine ⟨18652410300345912004557197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49739760800922432012152525 18652410300345912004557197)
              ·
                refine ⟨6994653862629717001708949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18652410300345912004557197 6994653862629717001708949)
                ·
                  refine ⟨327874399810767984455107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6994653862629717001708949 327874399810767984455107)
                  ·
                    rfl

theorem cell23_5746798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_5746798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746798 prefixEnd_5746798 := by exact prefixLift 5746798
  have htrace : WordTrace (prefixWord ++ tailWord_5746798) baseStart_5746798 baseEnd_5746798 := by
    simpa [prefixWord, tailWord_5746798, baseEnd_5746798] using wordTrace_append hprefix tailTrace_5746798
  have hstable : (prefixWord ++ tailWord_5746798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746798).length < 2 ^ (prefixWord ++ tailWord_5746798).sum := by decide
  have hdescent : baseEnd_5746798 < baseStart_5746798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746808 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_5746808 : Nat := 118140960795 + 5746808 * 2 ^ 59
def prefixEnd_5746808 : Nat := 4983230072969 + 3 ^ 40 * 5746808 * 2
def baseEnd_5746808 : Nat := 2950874733103456820970917

theorem tailTrace_5746808 : CollatzResearch.WordTrace tailWord_5746808 prefixEnd_5746808 2950874733103456820970917 := by
  unfold tailWord_5746808
  simp only [CollatzResearch.WordTrace]
  refine ⟨104801653682151783756080539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139735538242869045008107385 104801653682151783756080539)
  ·
    refine ⟨157202480523227675634120809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104801653682151783756080539 157202480523227675634120809)
    ·
      refine ⟨117901860392420756725590607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157202480523227675634120809 117901860392420756725590607)
      ·
        refine ⟨176852790588631135088385911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117901860392420756725590607 176852790588631135088385911)
        ·
          refine ⟨265279185882946702632578867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176852790588631135088385911 265279185882946702632578867)
          ·
            refine ⟨397918778824420053948868301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265279185882946702632578867 397918778824420053948868301)
            ·
              refine ⟨149219542059157520230825613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397918778824420053948868301 149219542059157520230825613)
              ·
                refine ⟨55957328272184070086559605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149219542059157520230825613 55957328272184070086559605)
                ·
                  refine ⟨5245999525517256570614963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55957328272184070086559605 5245999525517256570614963)
                  ·
                    refine ⟨7868999288275884855922445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5245999525517256570614963 7868999288275884855922445)
                    ·
                      refine ⟨2950874733103456820970917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7868999288275884855922445 2950874733103456820970917)
                      ·
                        rfl

theorem cell23_5746808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_5746808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746808 prefixEnd_5746808 := by exact prefixLift 5746808
  have htrace : WordTrace (prefixWord ++ tailWord_5746808) baseStart_5746808 baseEnd_5746808 := by
    simpa [prefixWord, tailWord_5746808, baseEnd_5746808] using wordTrace_append hprefix tailTrace_5746808
  have hstable : (prefixWord ++ tailWord_5746808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746808).length < 2 ^ (prefixWord ++ tailWord_5746808).sum := by decide
  have hdescent : baseEnd_5746808 < baseStart_5746808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746848 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_5746848 : Nat := 118140960795 + 5746848 * 2 ^ 59
def prefixEnd_5746848 : Nat := 4983230072969 + 3 ^ 40 * 5746848 * 2
def baseEnd_5746848 : Nat := 2950895272329636664470733

theorem tailTrace_5746848 : CollatzResearch.WordTrace tailWord_5746848 prefixEnd_5746848 2950895272329636664470733 := by
  unfold tailWord_5746848
  simp only [CollatzResearch.WordTrace]
  refine ⟨104802383142079327171808599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139736510856105769562411465 104802383142079327171808599)
  ·
    refine ⟨157203574713118990757712899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104802383142079327171808599 157203574713118990757712899)
    ·
      refine ⟨235805362069678486136569349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157203574713118990757712899 235805362069678486136569349)
      ·
        refine ⟨44213505388064716150606753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235805362069678486136569349 44213505388064716150606753)
        ·
          refine ⟨33160129041048537112955065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44213505388064716150606753 33160129041048537112955065)
          ·
            refine ⟨24870096780786402834716299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33160129041048537112955065 24870096780786402834716299)
            ·
              refine ⟨37305145171179604252074449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24870096780786402834716299 37305145171179604252074449)
              ·
                refine ⟨27978858878384703189055837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37305145171179604252074449 27978858878384703189055837)
                ·
                  refine ⟨10492072079394263695895939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27978858878384703189055837 10492072079394263695895939)
                  ·
                    refine ⟨15738108119091395543843909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10492072079394263695895939 15738108119091395543843909)
                    ·
                      refine ⟨2950895272329636664470733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15738108119091395543843909 2950895272329636664470733)
                      ·
                        rfl

theorem cell23_5746848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_5746848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746848 prefixEnd_5746848 := by exact prefixLift 5746848
  have htrace : WordTrace (prefixWord ++ tailWord_5746848) baseStart_5746848 baseEnd_5746848 := by
    simpa [prefixWord, tailWord_5746848, baseEnd_5746848] using wordTrace_append hprefix tailTrace_5746848
  have hstable : (prefixWord ++ tailWord_5746848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746848).length < 2 ^ (prefixWord ++ tailWord_5746848).sum := by decide
  have hdescent : baseEnd_5746848 < baseStart_5746848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746892 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_5746892 : Nat := 118140960795 + 5746892 * 2 ^ 59
def prefixEnd_5746892 : Nat := 4983230072969 + 3 ^ 40 * 5746892 * 2
def baseEnd_5746892 : Nat := 983639288492811497440177

theorem tailTrace_5746892 : CollatzResearch.WordTrace tailWord_5746892 prefixEnd_5746892 983639288492811497440177 := by
  unfold tailWord_5746892
  simp only [CollatzResearch.WordTrace]
  refine ⟨104803185547999624929109465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139737580730666166572145953 104803185547999624929109465)
  ·
    refine ⟨78602389160999718696832099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104803185547999624929109465 78602389160999718696832099)
    ·
      refine ⟨117903583741499578045248149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78602389160999718696832099 117903583741499578045248149)
      ·
        refine ⟨5526730487882792720871007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117903583741499578045248149 5526730487882792720871007)
        ·
          refine ⟨8290095731824189081306511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526730487882792720871007 8290095731824189081306511)
          ·
            refine ⟨12435143597736283621959767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8290095731824189081306511 12435143597736283621959767)
            ·
              refine ⟨18652715396604425432939651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435143597736283621959767 18652715396604425432939651)
              ·
                refine ⟨27979073094906638149409477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18652715396604425432939651 27979073094906638149409477)
                ·
                  refine ⟨5246076205294994653014277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27979073094906638149409477 5246076205294994653014277)
                  ·
                    refine ⟨983639288492811497440177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246076205294994653014277 983639288492811497440177)
                    ·
                      rfl

theorem cell23_5746892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_5746892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746892 prefixEnd_5746892 := by exact prefixLift 5746892
  have htrace : WordTrace (prefixWord ++ tailWord_5746892) baseStart_5746892 baseEnd_5746892 := by
    simpa [prefixWord, tailWord_5746892, baseEnd_5746892] using wordTrace_append hprefix tailTrace_5746892
  have hstable : (prefixWord ++ tailWord_5746892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746892).length < 2 ^ (prefixWord ++ tailWord_5746892).sum := by decide
  have hdescent : baseEnd_5746892 < baseStart_5746892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746902 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5746902 : Nat := 118140960795 + 5746902 * 2 ^ 59
def prefixEnd_5746902 : Nat := 4983230072969 + 3 ^ 40 * 5746902 * 2
def baseEnd_5746902 : Nat := 2950923000284979453195485

theorem tailTrace_5746902 : CollatzResearch.WordTrace tailWord_5746902 prefixEnd_5746902 2950923000284979453195485 := by
  unfold tailWord_5746902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13100420989122688847880185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139737823883975347710721973 13100420989122688847880185)
  ·
    refine ⟨9825315741842016635910139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13100420989122688847880185 9825315741842016635910139)
    ·
      refine ⟨14737973612763024953865209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9825315741842016635910139 14737973612763024953865209)
      ·
        refine ⟨11053480209572268715398907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14737973612763024953865209 11053480209572268715398907)
        ·
          refine ⟨16580220314358403073098361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11053480209572268715398907 16580220314358403073098361)
          ·
            refine ⟨12435165235768802304823771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16580220314358403073098361 12435165235768802304823771)
            ·
              refine ⟨18652747853653203457235657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435165235768802304823771 18652747853653203457235657)
              ·
                refine ⟨13989560890239902592926743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18652747853653203457235657 13989560890239902592926743)
                ·
                  refine ⟨20984341335359853889390115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13989560890239902592926743 20984341335359853889390115)
                  ·
                    refine ⟨31476512003039780834085173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20984341335359853889390115 31476512003039780834085173)
                    ·
                      refine ⟨2950923000284979453195485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31476512003039780834085173 2950923000284979453195485)
                      ·
                        rfl

theorem cell23_5746902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5746902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746902 prefixEnd_5746902 := by exact prefixLift 5746902
  have htrace : WordTrace (prefixWord ++ tailWord_5746902) baseStart_5746902 baseEnd_5746902 := by
    simpa [prefixWord, tailWord_5746902, baseEnd_5746902] using wordTrace_append hprefix tailTrace_5746902
  have hstable : (prefixWord ++ tailWord_5746902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746902).length < 2 ^ (prefixWord ++ tailWord_5746902).sum := by decide
  have hdescent : baseEnd_5746902 < baseStart_5746902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746909 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5746909 : Nat := 118140960795 + 5746909 * 2 ^ 59
def prefixEnd_5746909 : Nat := 4983230072969 + 3 ^ 40 * 5746909 * 2
def baseEnd_5746909 : Nat := 983642198216520308602651

theorem tailTrace_5746909 : CollatzResearch.WordTrace tailWord_5746909 prefixEnd_5746909 983642198216520308602651 := by
  unfold tailWord_5746909
  simp only [CollatzResearch.WordTrace]
  refine ⟨209606991136937661761587781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139737994091291774507725187 209606991136937661761587781)
  ·
    refine ⟨39301310838175811580297709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209606991136937661761587781 39301310838175811580297709)
    ·
      refine ⟨14737991564315929342611641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39301310838175811580297709 14737991564315929342611641)
      ·
        refine ⟨11053493673236947006958731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14737991564315929342611641 11053493673236947006958731)
        ·
          refine ⟨16580240509855420510438097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11053493673236947006958731 16580240509855420510438097)
          ·
            refine ⟨12435180382391565382828573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16580240509855420510438097 12435180382391565382828573)
            ·
              refine ⟨4663192643396837018560715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12435180382391565382828573 4663192643396837018560715)
              ·
                refine ⟨6994788965095255527841073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663192643396837018560715 6994788965095255527841073)
                ·
                  refine ⟨5246091723821441645880805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6994788965095255527841073 5246091723821441645880805)
                  ·
                    refine ⟨983642198216520308602651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246091723821441645880805 983642198216520308602651)
                    ·
                      rfl

theorem cell23_5746909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5746909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746909 prefixEnd_5746909 := by exact prefixLift 5746909
  have htrace : WordTrace (prefixWord ++ tailWord_5746909) baseStart_5746909 baseEnd_5746909 := by
    simpa [prefixWord, tailWord_5746909, baseEnd_5746909] using wordTrace_append hprefix tailTrace_5746909
  have hstable : (prefixWord ++ tailWord_5746909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746909).length < 2 ^ (prefixWord ++ tailWord_5746909).sum := by decide
  have hdescent : baseEnd_5746909 < baseStart_5746909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746958 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5746958 : Nat := 118140960795 + 5746958 * 2 ^ 59
def prefixEnd_5746958 : Nat := 4983230072969 + 3 ^ 40 * 5746958 * 2
def baseEnd_5746958 : Nat := 2950951755201631234095227

theorem tailTrace_5746958 : CollatzResearch.WordTrace tailWord_5746958 prefixEnd_5746958 2950951755201631234095227 := by
  unfold tailWord_5746958
  simp only [CollatzResearch.WordTrace]
  refine ⟨26201097289220017891265191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139739185542506762086747685 26201097289220017891265191)
  ·
    refine ⟨39301645933830026836897787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26201097289220017891265191 39301645933830026836897787)
    ·
      refine ⟨58952468900745040255346681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39301645933830026836897787 58952468900745040255346681)
      ·
        refine ⟨44214351675558780191510011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58952468900745040255346681 44214351675558780191510011)
        ·
          refine ⟨66321527513338170287265017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44214351675558780191510011 66321527513338170287265017)
          ·
            refine ⟨49741145635003627715448763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66321527513338170287265017 49741145635003627715448763)
            ·
              refine ⟨74611718452505441573173145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49741145635003627715448763 74611718452505441573173145)
              ·
                refine ⟨55958788839379081179879859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74611718452505441573173145 55958788839379081179879859)
                ·
                  refine ⟨83938183259068621769819789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55958788839379081179879859 83938183259068621769819789)
                  ·
                    refine ⟨31476818722150733163682421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83938183259068621769819789 31476818722150733163682421)
                    ·
                      refine ⟨2950951755201631234095227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31476818722150733163682421 2950951755201631234095227)
                      ·
                        rfl

theorem cell23_5746958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5746958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746958 prefixEnd_5746958 := by exact prefixLift 5746958
  have htrace : WordTrace (prefixWord ++ tailWord_5746958) baseStart_5746958 baseEnd_5746958 := by
    simpa [prefixWord, tailWord_5746958, baseEnd_5746958] using wordTrace_append hprefix tailTrace_5746958
  have hstable : (prefixWord ++ tailWord_5746958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746958).length < 2 ^ (prefixWord ++ tailWord_5746958).sum := by decide
  have hdescent : baseEnd_5746958 < baseStart_5746958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746968 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5746968 : Nat := 118140960795 + 5746968 * 2 ^ 59
def prefixEnd_5746968 : Nat := 4983230072969 + 3 ^ 40 * 5746968 * 2
def baseEnd_5746968 : Nat := 2950956890008176194970181

theorem tailTrace_5746968 : CollatzResearch.WordTrace tailWord_5746968 prefixEnd_5746968 2950956890008176194970181 := by
  unfold tailWord_5746968
  simp only [CollatzResearch.WordTrace]
  refine ⟨104804571521861957418992779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139739428695815943225323705 104804571521861957418992779)
  ·
    refine ⟨157206857282792936128489169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104804571521861957418992779 157206857282792936128489169)
    ·
      refine ⟨117905142962094702096366877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157206857282792936128489169 117905142962094702096366877)
      ·
        refine ⟨44214428610785513286137579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117905142962094702096366877 44214428610785513286137579)
        ·
          refine ⟨66321642916178269929206369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44214428610785513286137579 66321642916178269929206369)
          ·
            refine ⟨49741232187133702446904777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66321642916178269929206369 49741232187133702446904777)
            ·
              refine ⟨37305924140350276835178583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49741232187133702446904777 37305924140350276835178583)
              ·
                refine ⟨55958886210525415252767875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37305924140350276835178583 55958886210525415252767875)
                ·
                  refine ⟨83938329315788122879151813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55958886210525415252767875 83938329315788122879151813)
                  ·
                    refine ⟨15738436746710273039840965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83938329315788122879151813 15738436746710273039840965)
                    ·
                      refine ⟨2950956890008176194970181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15738436746710273039840965 2950956890008176194970181)
                      ·
                        rfl

theorem cell23_5746968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5746968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746968 prefixEnd_5746968 := by exact prefixLift 5746968
  have htrace : WordTrace (prefixWord ++ tailWord_5746968) baseStart_5746968 baseEnd_5746968 := by
    simpa [prefixWord, tailWord_5746968, baseEnd_5746968] using wordTrace_append hprefix tailTrace_5746968
  have hstable : (prefixWord ++ tailWord_5746968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746968).length < 2 ^ (prefixWord ++ tailWord_5746968).sum := by decide
  have hdescent : baseEnd_5746968 < baseStart_5746968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5746995 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 5]
def baseStart_5746995 : Nat := 118140960795 + 5746995 * 2 ^ 59
def prefixEnd_5746995 : Nat := 4983230072969 + 3 ^ 40 * 5746995 * 2
def baseEnd_5746995 : Nat := 327885639331760843259173

theorem tailTrace_5746995 : CollatzResearch.WordTrace tailWord_5746995 prefixEnd_5746995 327885639331760843259173 := by
  unfold tailWord_5746995
  simp only [CollatzResearch.WordTrace]
  refine ⟨209610127814626098449218439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139740085209750732299478959 209610127814626098449218439)
  ·
    refine ⟨314415191721939147673827659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209610127814626098449218439 314415191721939147673827659)
    ·
      refine ⟨471622787582908721510741489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314415191721939147673827659 471622787582908721510741489)
      ·
        refine ⟨353717090687181541133056117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471622787582908721510741489 353717090687181541133056117)
        ·
          refine ⟨33160977251923269481224011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 353717090687181541133056117 33160977251923269481224011)
          ·
            refine ⟨49741465877884904221836017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33160977251923269481224011 49741465877884904221836017)
            ·
              refine ⟨37306099408413678166377013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49741465877884904221836017 37306099408413678166377013)
              ·
                refine ⟨3497446819538782328097845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37306099408413678166377013 3497446819538782328097845)
                ·
                  refine ⟨327885639331760843259173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3497446819538782328097845 327885639331760843259173)
                  ·
                    rfl

theorem cell23_5746995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 5].length) (baseStart_5746995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5746995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5746995 prefixEnd_5746995 := by exact prefixLift 5746995
  have htrace : WordTrace (prefixWord ++ tailWord_5746995) baseStart_5746995 baseEnd_5746995 := by
    simpa [prefixWord, tailWord_5746995, baseEnd_5746995] using wordTrace_append hprefix tailTrace_5746995
  have hstable : (prefixWord ++ tailWord_5746995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5746995).length < 2 ^ (prefixWord ++ tailWord_5746995).sum := by decide
  have hdescent : baseEnd_5746995 < baseStart_5746995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5746995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747006 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_5747006 : Nat := 118140960795 + 5747006 * 2 ^ 59
def prefixEnd_5747006 : Nat := 4983230072969 + 3 ^ 40 * 5747006 * 2
def baseEnd_5747006 : Nat := 2950976402273047046295007

theorem tailTrace_5747006 : CollatzResearch.WordTrace tailWord_5747006 prefixEnd_5747006 2950976402273047046295007 := by
  unfold tailWord_5747006
  simp only [CollatzResearch.WordTrace]
  refine ⟨26201316127198280915983609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139740352678390831551912581 26201316127198280915983609)
  ·
    refine ⟨19650987095398710686987707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26201316127198280915983609 19650987095398710686987707)
    ·
      refine ⟨29476480643098066030481561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19650987095398710686987707 29476480643098066030481561)
      ·
        refine ⟨22107360482323549522861171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29476480643098066030481561 22107360482323549522861171)
        ·
          refine ⟨33161040723485324284291757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22107360482323549522861171 33161040723485324284291757)
          ·
            refine ⟨12435390271306996606609409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33161040723485324284291757 12435390271306996606609409)
            ·
              refine ⟨9326542703480247454957057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12435390271306996606609409 9326542703480247454957057)
              ·
                refine ⟨6994907027610185591217793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9326542703480247454957057 6994907027610185591217793)
                ·
                  refine ⟨5246180270707639193413345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6994907027610185591217793 5246180270707639193413345)
                  ·
                    refine ⟨3934635203030729395060009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5246180270707639193413345 3934635203030729395060009)
                    ·
                      refine ⟨2950976402273047046295007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934635203030729395060009 2950976402273047046295007)
                      ·
                        rfl

theorem cell23_5747006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_5747006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747006 prefixEnd_5747006 := by exact prefixLift 5747006
  have htrace : WordTrace (prefixWord ++ tailWord_5747006) baseStart_5747006 baseEnd_5747006 := by
    simpa [prefixWord, tailWord_5747006, baseEnd_5747006] using wordTrace_append hprefix tailTrace_5747006
  have hstable : (prefixWord ++ tailWord_5747006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747006).length < 2 ^ (prefixWord ++ tailWord_5747006).sum := by decide
  have hdescent : baseEnd_5747006 < baseStart_5747006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747008 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_5747008 : Nat := 118140960795 + 5747008 * 2 ^ 59
def prefixEnd_5747008 : Nat := 4983230072969 + 3 ^ 40 * 5747008 * 2
def baseEnd_5747008 : Nat := 983659143078118679489999

theorem tailTrace_5747008 : CollatzResearch.WordTrace tailWord_5747008 prefixEnd_5747008 983659143078118679489999 := by
  unfold tailWord_5747008
  simp only [CollatzResearch.WordTrace]
  refine ⟨104805300981789500834720839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139740401309052667779627785 104805300981789500834720839)
  ·
    refine ⟨157207951472684251252081259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104805300981789500834720839 157207951472684251252081259)
    ·
      refine ⟨235811927209026376878121889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157207951472684251252081259 235811927209026376878121889)
      ·
        refine ⟨176858945406769782658591417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235811927209026376878121889 176858945406769782658591417)
        ·
          refine ⟨132644209055077336993943563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176858945406769782658591417 132644209055077336993943563)
          ·
            refine ⟨198966313582616005490915345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132644209055077336993943563 198966313582616005490915345)
            ·
              refine ⟨149224735186962004118186509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198966313582616005490915345 149224735186962004118186509)
              ·
                refine ⟨55959275695110751544319941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149224735186962004118186509 55959275695110751544319941)
                ·
                  refine ⟨10492364192833265914559989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55959275695110751544319941 10492364192833265914559989)
                  ·
                    refine ⟨983659143078118679489999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10492364192833265914559989 983659143078118679489999)
                    ·
                      rfl

theorem cell23_5747008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_5747008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747008 prefixEnd_5747008 := by exact prefixLift 5747008
  have htrace : WordTrace (prefixWord ++ tailWord_5747008) baseStart_5747008 baseEnd_5747008 := by
    simpa [prefixWord, tailWord_5747008, baseEnd_5747008] using wordTrace_append hprefix tailTrace_5747008
  have hstable : (prefixWord ++ tailWord_5747008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747008).length < 2 ^ (prefixWord ++ tailWord_5747008).sum := by decide
  have hdescent : baseEnd_5747008 < baseStart_5747008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747015 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_5747015 : Nat := 118140960795 + 5747015 * 2 ^ 59
def prefixEnd_5747015 : Nat := 4983230072969 + 3 ^ 40 * 5747015 * 2
def baseEnd_5747015 : Nat := 2950981023598937511082465

theorem tailTrace_5747015 : CollatzResearch.WordTrace tailWord_5747015 prefixEnd_5747015 2950981023598937511082465 := by
  unfold tailWord_5747015
  simp only [CollatzResearch.WordTrace]
  refine ⟨209610857274553641864946499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139740571516369094576630999 209610857274553641864946499)
  ·
    refine ⟨314416285911830462797419749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209610857274553641864946499 314416285911830462797419749)
    ·
      refine ⟨58953053608468211774516203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314416285911830462797419749 58953053608468211774516203)
      ·
        refine ⟨88429580412702317661774305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58953053608468211774516203 88429580412702317661774305)
        ·
          refine ⟨66322185309526738246330729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88429580412702317661774305 66322185309526738246330729)
          ·
            refine ⟨49741638982145053684748047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66322185309526738246330729 49741638982145053684748047)
            ·
              refine ⟨74612458473217580527122071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49741638982145053684748047 74612458473217580527122071)
              ·
                refine ⟨111918687709826370790683107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74612458473217580527122071 111918687709826370790683107)
                ·
                  refine ⟨167878031564739556186024661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111918687709826370790683107 167878031564739556186024661)
                  ·
                    refine ⟨3934641364798583348109953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167878031564739556186024661 3934641364798583348109953)
                    ·
                      refine ⟨2950981023598937511082465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934641364798583348109953 2950981023598937511082465)
                      ·
                        rfl

theorem cell23_5747015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_5747015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747015 prefixEnd_5747015 := by exact prefixLift 5747015
  have htrace : WordTrace (prefixWord ++ tailWord_5747015) baseStart_5747015 baseEnd_5747015 := by
    simpa [prefixWord, tailWord_5747015, baseEnd_5747015] using wordTrace_append hprefix tailTrace_5747015
  have hstable : (prefixWord ++ tailWord_5747015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747015).length < 2 ^ (prefixWord ++ tailWord_5747015).sum := by decide
  have hdescent : baseEnd_5747015 < baseStart_5747015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747042 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5747042 : Nat := 118140960795 + 5747042 * 2 ^ 59
def prefixEnd_5747042 : Nat := 4983230072969 + 3 ^ 40 * 5747042 * 2
def baseEnd_5747042 : Nat := 983664962525536301814947

theorem tailTrace_5747042 : CollatzResearch.WordTrace tailWord_5747042 prefixEnd_5747042 983664962525536301814947 := by
  unfold tailWord_5747042
  simp only [CollatzResearch.WordTrace]
  refine ⟨52402960511363956369044845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139741228030303883650786253 52402960511363956369044845)
  ·
    refine ⟨19651110191761483638391817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52402960511363956369044845 19651110191761483638391817)
    ·
      refine ⟨14738332643821112728793863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19651110191761483638391817 14738332643821112728793863)
      ·
        refine ⟨22107498965731669093190795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14738332643821112728793863 22107498965731669093190795)
        ·
          refine ⟨33161248448597503639786193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22107498965731669093190795 33161248448597503639786193)
          ·
            refine ⟨24870936336448127729839645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33161248448597503639786193 24870936336448127729839645)
            ·
              refine ⟨9326601126168047898689867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24870936336448127729839645 9326601126168047898689867)
              ·
                refine ⟨13989901689252071848034801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9326601126168047898689867 13989901689252071848034801)
                ·
                  refine ⟨10492426266939053886026101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13989901689252071848034801 10492426266939053886026101)
                  ·
                    refine ⟨983664962525536301814947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10492426266939053886026101 983664962525536301814947)
                    ·
                      rfl

theorem cell23_5747042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5747042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747042 prefixEnd_5747042 := by exact prefixLift 5747042
  have htrace : WordTrace (prefixWord ++ tailWord_5747042) baseStart_5747042 baseEnd_5747042 := by
    simpa [prefixWord, tailWord_5747042, baseEnd_5747042] using wordTrace_append hprefix tailTrace_5747042
  have hstable : (prefixWord ++ tailWord_5747042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747042).length < 2 ^ (prefixWord ++ tailWord_5747042).sum := by decide
  have hdescent : baseEnd_5747042 < baseStart_5747042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747045 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_5747045 : Nat := 118140960795 + 5747045 * 2 ^ 59
def prefixEnd_5747045 : Nat := 4983230072969 + 3 ^ 40 * 5747045 * 2
def baseEnd_5747045 : Nat := 2950996428018572393707327

theorem tailTrace_5747045 : CollatzResearch.WordTrace tailWord_5747045 prefixEnd_5747045 2950996428018572393707327 := by
  unfold tailWord_5747045
  simp only [CollatzResearch.WordTrace]
  refine ⟨209611951464444956988538589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139741300976296637992359059 209611951464444956988538589)
  ·
    refine ⟨78604481799166858870701971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209611951464444956988538589 78604481799166858870701971)
    ·
      refine ⟨117906722698750288306052957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78604481799166858870701971 117906722698750288306052957)
      ·
        refine ⟨44215021012031358114769859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117906722698750288306052957 44215021012031358114769859)
        ·
          refine ⟨66322531518047037172154789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44215021012031358114769859 66322531518047037172154789)
          ·
            refine ⟨12435474659633819469779023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66322531518047037172154789 12435474659633819469779023)
            ·
              refine ⟨18653211989450729204668535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435474659633819469779023 18653211989450729204668535)
              ·
                refine ⟨27979817984176093807002803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18653211989450729204668535 27979817984176093807002803)
                ·
                  refine ⟨41969726976264140710504205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27979817984176093807002803 41969726976264140710504205)
                  ·
                    refine ⟨15738647616099052766439077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41969726976264140710504205 15738647616099052766439077)
                    ·
                      refine ⟨2950996428018572393707327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15738647616099052766439077 2950996428018572393707327)
                      ·
                        rfl

theorem cell23_5747045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_5747045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747045 prefixEnd_5747045 := by exact prefixLift 5747045
  have htrace : WordTrace (prefixWord ++ tailWord_5747045) baseStart_5747045 baseEnd_5747045 := by
    simpa [prefixWord, tailWord_5747045, baseEnd_5747045] using wordTrace_append hprefix tailTrace_5747045
  have hstable : (prefixWord ++ tailWord_5747045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747045).length < 2 ^ (prefixWord ++ tailWord_5747045).sum := by decide
  have hdescent : baseEnd_5747045 < baseStart_5747045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747065 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_5747065 : Nat := 118140960795 + 5747065 * 2 ^ 59
def prefixEnd_5747065 : Nat := 4983230072969 + 3 ^ 40 * 5747065 * 2
def baseEnd_5747065 : Nat := 2951006697631662315457235

theorem tailTrace_5747065 : CollatzResearch.WordTrace tailWord_5747065 prefixEnd_5747065 2951006697631662315457235 := by
  unfold tailWord_5747065
  simp only [CollatzResearch.WordTrace]
  refine ⟨209612680924372500404266649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139741787282915000269511099 209612680924372500404266649)
  ·
    refine ⟨157209510693279375303199987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209612680924372500404266649 157209510693279375303199987)
    ·
      refine ⟨235814266039919062954799981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157209510693279375303199987 235814266039919062954799981)
      ·
        refine ⟨88430349764969648608049993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235814266039919062954799981 88430349764969648608049993)
        ·
          refine ⟨66322762323727236456037495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88430349764969648608049993 66322762323727236456037495)
          ·
            refine ⟨99484143485590854684056243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66322762323727236456037495 99484143485590854684056243)
            ·
              refine ⟨149226215228386282026084365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99484143485590854684056243 149226215228386282026084365)
              ·
                refine ⟨55959830710644855759781637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149226215228386282026084365 55959830710644855759781637)
                ·
                  refine ⟨10492468258245910454959057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55959830710644855759781637 10492468258245910454959057)
                  ·
                    refine ⟨7869351193684432841219293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10492468258245910454959057 7869351193684432841219293)
                    ·
                      refine ⟨2951006697631662315457235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7869351193684432841219293 2951006697631662315457235)
                      ·
                        rfl

theorem cell23_5747065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_5747065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747065 prefixEnd_5747065 := by exact prefixLift 5747065
  have htrace : WordTrace (prefixWord ++ tailWord_5747065) baseStart_5747065 baseEnd_5747065 := by
    simpa [prefixWord, tailWord_5747065, baseEnd_5747065] using wordTrace_append hprefix tailTrace_5747065
  have hstable : (prefixWord ++ tailWord_5747065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747065).length < 2 ^ (prefixWord ++ tailWord_5747065).sum := by decide
  have hdescent : baseEnd_5747065 < baseStart_5747065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747102 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_5747102 : Nat := 118140960795 + 5747102 * 2 ^ 59
def prefixEnd_5747102 : Nat := 4983230072969 + 3 ^ 40 * 5747102 * 2
def baseEnd_5747102 : Nat := 327891744046208741188285

theorem tailTrace_5747102 : CollatzResearch.WordTrace tailWord_5747102 prefixEnd_5747102 327891744046208741188285 := by
  unfold tailWord_5747102
  simp only [CollatzResearch.WordTrace]
  refine ⟨26201753803154806965420445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139742686950158970482242373 26201753803154806965420445)
  ·
    refine ⟨9825657676183052612032667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26201753803154806965420445 9825657676183052612032667)
    ·
      refine ⟨14738486514274578918049001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9825657676183052612032667 14738486514274578918049001)
      ·
        refine ⟨11053864885705934188536751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14738486514274578918049001 11053864885705934188536751)
        ·
          refine ⟨16580797328558901282805127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11053864885705934188536751 16580797328558901282805127)
          ·
            refine ⟨24871195992838351924207691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16580797328558901282805127 24871195992838351924207691)
            ·
              refine ⟨37306793989257527886311537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24871195992838351924207691 37306793989257527886311537)
              ·
                refine ⟨27980095491943145914733653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37306793989257527886311537 27980095491943145914733653)
                ·
                  refine ⟨327891744046208741188285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27980095491943145914733653 327891744046208741188285)
                  ·
                    rfl

theorem cell23_5747102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_5747102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747102 prefixEnd_5747102 := by exact prefixLift 5747102
  have htrace : WordTrace (prefixWord ++ tailWord_5747102) baseStart_5747102 baseEnd_5747102 := by
    simpa [prefixWord, tailWord_5747102, baseEnd_5747102] using wordTrace_append hprefix tailTrace_5747102
  have hstable : (prefixWord ++ tailWord_5747102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747102).length < 2 ^ (prefixWord ++ tailWord_5747102).sum := by decide
  have hdescent : baseEnd_5747102 < baseStart_5747102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747129 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 3]
def baseStart_5747129 : Nat := 118140960795 + 5747129 * 2 ^ 59
def prefixEnd_5747129 : Nat := 4983230072969 + 3 ^ 40 * 5747129 * 2
def baseEnd_5747129 : Nat := 2951039560393550065056941

theorem tailTrace_5747129 : CollatzResearch.WordTrace tailWord_5747129 prefixEnd_5747129 2951039560393550065056941 := by
  unfold tailWord_5747129
  simp only [CollatzResearch.WordTrace]
  refine ⟨209615015196140639334596441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139743343464093759556397627 209615015196140639334596441)
  ·
    refine ⟨157211261397105479500947331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209615015196140639334596441 157211261397105479500947331)
    ·
      refine ⟨235816892095658219251420997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157211261397105479500947331 235816892095658219251420997)
      ·
        refine ⟨44215667267935916109641437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235816892095658219251420997 44215667267935916109641437)
        ·
          refine ⟨16580875225475968541115539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44215667267935916109641437 16580875225475968541115539)
          ·
            refine ⟨24871312838213952811673309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16580875225475968541115539 24871312838213952811673309)
            ·
              refine ⟨9326742314330232304377491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24871312838213952811673309 9326742314330232304377491)
              ·
                refine ⟨13990113471495348456566237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9326742314330232304377491 13990113471495348456566237)
                ·
                  refine ⟨5246292551810755671212339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13990113471495348456566237 5246292551810755671212339)
                  ·
                    refine ⟨7869438827716133506818509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5246292551810755671212339 7869438827716133506818509)
                    ·
                      refine ⟨2951039560393550065056941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7869438827716133506818509 2951039560393550065056941)
                      ·
                        rfl

theorem cell23_5747129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_5747129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747129 prefixEnd_5747129 := by exact prefixLift 5747129
  have htrace : WordTrace (prefixWord ++ tailWord_5747129) baseStart_5747129 baseEnd_5747129 := by
    simpa [prefixWord, tailWord_5747129, baseEnd_5747129] using wordTrace_append hprefix tailTrace_5747129
  have hstable : (prefixWord ++ tailWord_5747129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747129).length < 2 ^ (prefixWord ++ tailWord_5747129).sum := by decide
  have hdescent : baseEnd_5747129 < baseStart_5747129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747156 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_5747156 : Nat := 118140960795 + 5747156 * 2 ^ 59
def prefixEnd_5747156 : Nat := 4983230072969 + 3 ^ 40 * 5747156 * 2
def baseEnd_5747156 : Nat := 2951053424371221459419317

theorem tailTrace_5747156 : CollatzResearch.WordTrace tailWord_5747156 prefixEnd_5747156 2951053424371221459419317 := by
  unfold tailWord_5747156
  simp only [CollatzResearch.WordTrace]
  refine ⟨104807999983521411472914661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139743999978028548630552881 104807999983521411472914661)
  ·
    refine ⟨19651499996910264651171499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104807999983521411472914661 19651499996910264651171499)
    ·
      refine ⟨29477249995365396976757249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19651499996910264651171499 29477249995365396976757249)
      ·
        refine ⟨22107937496524047732567937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29477249995365396976757249 22107937496524047732567937)
        ·
          refine ⟨16580953122393035799425953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22107937496524047732567937 16580953122393035799425953)
          ·
            refine ⟨12435714841794776849569465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16580953122393035799425953 12435714841794776849569465)
            ·
              refine ⟨9326786131346082637177099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12435714841794776849569465 9326786131346082637177099)
              ·
                refine ⟨13990179197019123955765649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9326786131346082637177099 13990179197019123955765649)
                ·
                  refine ⟨10492634397764342966824237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13990179197019123955765649 10492634397764342966824237)
                  ·
                    refine ⟨3934737899161628612559089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10492634397764342966824237 3934737899161628612559089)
                    ·
                      refine ⟨2951053424371221459419317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934737899161628612559089 2951053424371221459419317)
                      ·
                        rfl

theorem cell23_5747156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_5747156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747156 prefixEnd_5747156 := by exact prefixLift 5747156
  have htrace : WordTrace (prefixWord ++ tailWord_5747156) baseStart_5747156 baseEnd_5747156 := by
    simpa [prefixWord, tailWord_5747156, baseEnd_5747156] using wordTrace_append hprefix tailTrace_5747156
  have hstable : (prefixWord ++ tailWord_5747156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747156).length < 2 ^ (prefixWord ++ tailWord_5747156).sum := by decide
  have hdescent : baseEnd_5747156 < baseStart_5747156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747169 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_5747169 : Nat := 118140960795 + 5747169 * 2 ^ 59
def prefixEnd_5747169 : Nat := 4983230072969 + 3 ^ 40 * 5747169 * 2
def baseEnd_5747169 : Nat := 2951060099619729908556757

theorem tailTrace_5747169 : CollatzResearch.WordTrace tailWord_5747169 prefixEnd_5747169 2951060099619729908556757 := by
  unfold tailWord_5747169
  simp only [CollatzResearch.WordTrace]
  refine ⟨209616474115995726166052561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139744316077330484110701707 209616474115995726166052561)
  ·
    refine ⟨157212355586996794624539421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209616474115995726166052561 157212355586996794624539421)
    ·
      refine ⟨58954633345123797984202283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157212355586996794624539421 58954633345123797984202283)
      ·
        refine ⟨88431950017685696976303425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58954633345123797984202283 88431950017685696976303425)
        ·
          refine ⟨66323962513264272732227569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88431950017685696976303425 66323962513264272732227569)
          ·
            refine ⟨49742971884948204549170677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66323962513264272732227569 49742971884948204549170677)
            ·
              refine ⟨4663403614213894176484751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49742971884948204549170677 4663403614213894176484751)
              ·
                refine ⟨6995105421320841264727127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663403614213894176484751 6995105421320841264727127)
                ·
                  refine ⟨10492658131981261897090691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6995105421320841264727127 10492658131981261897090691)
                  ·
                    refine ⟨15738987197971892845636037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10492658131981261897090691 15738987197971892845636037)
                    ·
                      refine ⟨2951060099619729908556757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15738987197971892845636037 2951060099619729908556757)
                      ·
                        rfl

theorem cell23_5747169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_5747169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747169 prefixEnd_5747169 := by exact prefixLift 5747169
  have htrace : WordTrace (prefixWord ++ tailWord_5747169) baseStart_5747169 baseEnd_5747169 := by
    simpa [prefixWord, tailWord_5747169, baseEnd_5747169] using wordTrace_append hprefix tailTrace_5747169
  have hstable : (prefixWord ++ tailWord_5747169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747169).length < 2 ^ (prefixWord ++ tailWord_5747169).sum := by decide
  have hdescent : baseEnd_5747169 < baseStart_5747169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747220 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_5747220 : Nat := 118140960795 + 5747220 * 2 ^ 59
def prefixEnd_5747220 : Nat := 4983230072969 + 3 ^ 40 * 5747220 * 2
def baseEnd_5747220 : Nat := 2951086287133109209019023

theorem tailTrace_5747220 : CollatzResearch.WordTrace tailWord_5747220 prefixEnd_5747220 2951086287133109209019023 := by
  unfold tailWord_5747220
  simp only [CollatzResearch.WordTrace]
  refine ⟨104809167119405480938079557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139745556159207307917439409 104809167119405480938079557)
  ·
    refine ⟨19651718834888527675889917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104809167119405480938079557 19651718834888527675889917)
    ·
      refine ⟨7369394563083197878458719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19651718834888527675889917 7369394563083197878458719)
      ·
        refine ⟨11054091844624796817688079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369394563083197878458719 11054091844624796817688079)
        ·
          refine ⟨16581137766937195226532119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11054091844624796817688079 16581137766937195226532119)
          ·
            refine ⟨24871706650405792839798179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16581137766937195226532119 24871706650405792839798179)
            ·
              refine ⟨37307559975608689259697269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24871706650405792839798179 37307559975608689259697269)
              ·
                refine ⟨3497583747713314618096619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37307559975608689259697269 3497583747713314618096619)
                ·
                  refine ⟨5246375621569971927144929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497583747713314618096619 5246375621569971927144929)
                  ·
                    refine ⟨3934781716177478945358697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5246375621569971927144929 3934781716177478945358697)
                    ·
                      refine ⟨2951086287133109209019023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934781716177478945358697 2951086287133109209019023)
                      ·
                        rfl

theorem cell23_5747220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_5747220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747220 prefixEnd_5747220 := by exact prefixLift 5747220
  have htrace : WordTrace (prefixWord ++ tailWord_5747220) baseStart_5747220 baseEnd_5747220 := by
    simpa [prefixWord, tailWord_5747220, baseEnd_5747220] using wordTrace_append hprefix tailTrace_5747220
  have hstable : (prefixWord ++ tailWord_5747220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747220).length < 2 ^ (prefixWord ++ tailWord_5747220).sum := by decide
  have hdescent : baseEnd_5747220 < baseStart_5747220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747225 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_5747225 : Nat := 118140960795 + 5747225 * 2 ^ 59
def prefixEnd_5747225 : Nat := 4983230072969 + 3 ^ 40 * 5747225 * 2
def baseEnd_5747225 : Nat := 2951088854536381689456499

theorem tailTrace_5747225 : CollatzResearch.WordTrace tailWord_5747225 prefixEnd_5747225 2951088854536381689456499 := by
  unfold tailWord_5747225
  simp only [CollatzResearch.WordTrace]
  refine ⟨209618516603792847730091129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139745677735861898486727419 209618516603792847730091129)
  ·
    refine ⟨157213887452844635797568347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209618516603792847730091129 157213887452844635797568347)
    ·
      refine ⟨235820831179266953696352521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157213887452844635797568347 235820831179266953696352521)
      ·
        refine ⟨176865623384450215272264391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235820831179266953696352521 176865623384450215272264391)
        ·
          refine ⟨265298435076675322908396587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176865623384450215272264391 265298435076675322908396587)
          ·
            refine ⟨397947652615012984362594881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265298435076675322908396587 397947652615012984362594881)
            ·
              refine ⟨298460739461259738271946161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397947652615012984362594881 298460739461259738271946161)
              ·
                refine ⟨223845554595944803703959621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298460739461259738271946161 223845554595944803703959621)
                ·
                  refine ⟨41971041486739650694492429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223845554595944803703959621 41971041486739650694492429)
                  ·
                    refine ⟨15739140557527369010434661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41971041486739650694492429 15739140557527369010434661)
                    ·
                      refine ⟨2951088854536381689456499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15739140557527369010434661 2951088854536381689456499)
                      ·
                        rfl

theorem cell23_5747225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_5747225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747225 prefixEnd_5747225 := by exact prefixLift 5747225
  have htrace : WordTrace (prefixWord ++ tailWord_5747225) baseStart_5747225 baseEnd_5747225 := by
    simpa [prefixWord, tailWord_5747225, baseEnd_5747225] using wordTrace_append hprefix tailTrace_5747225
  have hstable : (prefixWord ++ tailWord_5747225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747225).length < 2 ^ (prefixWord ++ tailWord_5747225).sum := by decide
  have hdescent : baseEnd_5747225 < baseStart_5747225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747310 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5747310 : Nat := 118140960795 + 5747310 * 2 ^ 59
def prefixEnd_5747310 : Nat := 4983230072969 + 3 ^ 40 * 5747310 * 2
def baseEnd_5747310 : Nat := 2951132500392013856893609

theorem tailTrace_5747310 : CollatzResearch.WordTrace tailWord_5747310 prefixEnd_5747310 2951132500392013856893609 := by
  unfold tailWord_5747310
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202702101060613405866923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139747744538989938164623589 26202702101060613405866923)
  ·
    refine ⟨39304053151590920108800385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26202702101060613405866923 39304053151590920108800385)
    ·
      refine ⟨29478039863693190081600289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39304053151590920108800385 29478039863693190081600289)
      ·
        refine ⟨22108529897769892561200217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29478039863693190081600289 22108529897769892561200217)
        ·
          refine ⟨16581397423327419420900163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22108529897769892561200217 16581397423327419420900163)
          ·
            refine ⟨24872096134991129131350245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16581397423327419420900163 24872096134991129131350245)
            ·
              refine ⟨4663518025310836712128171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24872096134991129131350245 4663518025310836712128171)
              ·
                refine ⟨6995277037966255068192257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663518025310836712128171 6995277037966255068192257)
                ·
                  refine ⟨5246457778474691301144193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6995277037966255068192257 5246457778474691301144193)
                  ·
                    refine ⟨3934843333856018475858145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5246457778474691301144193 3934843333856018475858145)
                    ·
                      refine ⟨2951132500392013856893609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934843333856018475858145 2951132500392013856893609)
                      ·
                        rfl

theorem cell23_5747310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5747310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747310 prefixEnd_5747310 := by exact prefixLift 5747310
  have htrace : WordTrace (prefixWord ++ tailWord_5747310) baseStart_5747310 baseEnd_5747310 := by
    simpa [prefixWord, tailWord_5747310, baseEnd_5747310] using wordTrace_append hprefix tailTrace_5747310
  have hstable : (prefixWord ++ tailWord_5747310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747310).length < 2 ^ (prefixWord ++ tailWord_5747310).sum := by decide
  have hdescent : baseEnd_5747310 < baseStart_5747310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747329 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 2, 5]
def baseStart_5747329 : Nat := 118140960795 + 5747329 * 2 ^ 59
def prefixEnd_5747329 : Nat := 4983230072969 + 3 ^ 40 * 5747329 * 2
def baseEnd_5747329 : Nat := 983714085508149760852007

theorem tailTrace_5747329 : CollatzResearch.WordTrace tailWord_5747329 prefixEnd_5747329 983714085508149760852007 := by
  unfold tailWord_5747329
  simp only [CollatzResearch.WordTrace]
  refine ⟨209622309795416073491877041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139748206530277382327918027 209622309795416073491877041)
  ·
    refine ⟨157216732346562055118907781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209622309795416073491877041 157216732346562055118907781)
    ·
      refine ⟨29478137314980385334795209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157216732346562055118907781 29478137314980385334795209)
      ·
        refine ⟨22108602986235289001096407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29478137314980385334795209 22108602986235289001096407)
        ·
          refine ⟨33162904479352933501644611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22108602986235289001096407 33162904479352933501644611)
          ·
            refine ⟨49744356719029400252466917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33162904479352933501644611 49744356719029400252466917)
            ·
              refine ⟨9327066884818012547337547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49744356719029400252466917 9327066884818012547337547)
              ·
                refine ⟨13990600327227018821006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9327066884818012547337547 13990600327227018821006321)
                ·
                  refine ⟨10492950245420264115754741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13990600327227018821006321 10492950245420264115754741)
                  ·
                    refine ⟨983714085508149760852007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10492950245420264115754741 983714085508149760852007)
                    ·
                      rfl

theorem cell23_5747329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_5747329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747329 prefixEnd_5747329 := by exact prefixLift 5747329
  have htrace : WordTrace (prefixWord ++ tailWord_5747329) baseStart_5747329 baseEnd_5747329 := by
    simpa [prefixWord, tailWord_5747329, baseEnd_5747329] using wordTrace_append hprefix tailTrace_5747329
  have hstable : (prefixWord ++ tailWord_5747329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747329).length < 2 ^ (prefixWord ++ tailWord_5747329).sum := by decide
  have hdescent : baseEnd_5747329 < baseStart_5747329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747352 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5747352 : Nat := 118140960795 + 5747352 * 2 ^ 59
def prefixEnd_5747352 : Nat := 4983230072969 + 3 ^ 40 * 5747352 * 2
def baseEnd_5747352 : Nat := 2951154066579502692568415

theorem tailTrace_5747352 : CollatzResearch.WordTrace tailWord_5747352 prefixEnd_5747352 2951154066579502692568415 := by
  unfold tailWord_5747352
  simp only [CollatzResearch.WordTrace]
  refine ⟨104811574337166374209982155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139748765782888498946642873 104811574337166374209982155)
  ·
    refine ⟨157217361505749561314973233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104811574337166374209982155 157217361505749561314973233)
    ·
      refine ⟨117913021129312170986229925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157217361505749561314973233 117913021129312170986229925)
      ·
        refine ⟨22108691461746032059918111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117913021129312170986229925 22108691461746032059918111)
        ·
          refine ⟨33163037192619048089877167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22108691461746032059918111 33163037192619048089877167)
          ·
            refine ⟨49744555788928572134815751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33163037192619048089877167 49744555788928572134815751)
            ·
              refine ⟨74616833683392858202223627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49744555788928572134815751 74616833683392858202223627)
              ·
                refine ⟨111925250525089287303335441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74616833683392858202223627 111925250525089287303335441)
                ·
                  refine ⟨83943937893816965477501581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111925250525089287303335441 83943937893816965477501581)
                  ·
                    refine ⟨31478976710181362054063093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83943937893816965477501581 31478976710181362054063093)
                    ·
                      refine ⟨2951154066579502692568415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31478976710181362054063093 2951154066579502692568415)
                      ·
                        rfl

theorem cell23_5747352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5747352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747352 prefixEnd_5747352 := by exact prefixLift 5747352
  have htrace : WordTrace (prefixWord ++ tailWord_5747352) baseStart_5747352 baseEnd_5747352 := by
    simpa [prefixWord, tailWord_5747352, baseEnd_5747352] using wordTrace_append hprefix tailTrace_5747352
  have hstable : (prefixWord ++ tailWord_5747352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747352).length < 2 ^ (prefixWord ++ tailWord_5747352).sum := by decide
  have hdescent : baseEnd_5747352 < baseStart_5747352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747383 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 2, 1, 4]
def baseStart_5747383 : Nat := 118140960795 + 5747383 * 2 ^ 59
def prefixEnd_5747383 : Nat := 4983230072969 + 3 ^ 40 * 5747383 * 2
def baseEnd_5747383 : Nat := 2951169984479792071280773

theorem tailTrace_5747383 : CollatzResearch.WordTrace tailWord_5747383 prefixEnd_5747383 2951169984479792071280773 := by
  unfold tailWord_5747383
  simp only [CollatzResearch.WordTrace]
  refine ⟨209624279337220440714342803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139749519558146960476228535 209624279337220440714342803)
  ·
    refine ⟨314436419005830661071514205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209624279337220440714342803 314436419005830661071514205)
    ·
      refine ⟨117913657127186497901817827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314436419005830661071514205 117913657127186497901817827)
      ·
        refine ⟨176870485690779746852726741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117913657127186497901817827 176870485690779746852726741)
        ·
          refine ⟨4145402008377650316860783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 176870485690779746852726741 4145402008377650316860783)
          ·
            refine ⟨6218103012566475475291175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145402008377650316860783 6218103012566475475291175)
            ·
              refine ⟨9327154518849713212936763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218103012566475475291175 9327154518849713212936763)
              ·
                refine ⟨13990731778274569819405145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9327154518849713212936763 13990731778274569819405145)
                ·
                  refine ⟨10493048833705927364553859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13990731778274569819405145 10493048833705927364553859)
                  ·
                    refine ⟨15739573250558891046830789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10493048833705927364553859 15739573250558891046830789)
                    ·
                      refine ⟨2951169984479792071280773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15739573250558891046830789 2951169984479792071280773)
                      ·
                        rfl

theorem cell23_5747383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_5747383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747383 prefixEnd_5747383 := by exact prefixLift 5747383
  have htrace : WordTrace (prefixWord ++ tailWord_5747383) baseStart_5747383 baseEnd_5747383 := by
    simpa [prefixWord, tailWord_5747383, baseEnd_5747383] using wordTrace_append hprefix tailTrace_5747383
  have hstable : (prefixWord ++ tailWord_5747383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747383).length < 2 ^ (prefixWord ++ tailWord_5747383).sum := by decide
  have hdescent : baseEnd_5747383 < baseStart_5747383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747406 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_5747406 : Nat := 118140960795 + 5747406 * 2 ^ 59
def prefixEnd_5747406 : Nat := 4983230072969 + 3 ^ 40 * 5747406 * 2
def baseEnd_5747406 : Nat := 327909088281649497921463

theorem tailTrace_5747406 : CollatzResearch.WordTrace tailWord_5747406 prefixEnd_5747406 327909088281649497921463 := by
  unfold tailWord_5747406
  simp only [CollatzResearch.WordTrace]
  refine ⟨26203139777017139455303759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139750078810758077094953381 26203139777017139455303759)
  ·
    refine ⟨39304709665525709182955639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26203139777017139455303759 39304709665525709182955639)
    ·
      refine ⟨58957064498288563774433459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39304709665525709182955639 58957064498288563774433459)
      ·
        refine ⟨88435596747432845661650189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58957064498288563774433459 88435596747432845661650189)
        ·
          refine ⟨33163348780287317123118821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88435596747432845661650189 33163348780287317123118821)
          ·
            refine ⟨6218127896303871960584779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33163348780287317123118821 6218127896303871960584779)
            ·
              refine ⟨9327191844455807940877169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218127896303871960584779 9327191844455807940877169)
              ·
                refine ⟨6995393883341855955657877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9327191844455807940877169 6995393883341855955657877)
                ·
                  refine ⟨327909088281649497921463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6995393883341855955657877 327909088281649497921463)
                  ·
                    rfl

theorem cell23_5747406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_5747406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747406 prefixEnd_5747406 := by exact prefixLift 5747406
  have htrace : WordTrace (prefixWord ++ tailWord_5747406) baseStart_5747406 baseEnd_5747406 := by
    simpa [prefixWord, tailWord_5747406, baseEnd_5747406] using wordTrace_append hprefix tailTrace_5747406
  have hstable : (prefixWord ++ tailWord_5747406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747406).length < 2 ^ (prefixWord ++ tailWord_5747406).sum := by decide
  have hdescent : baseEnd_5747406 < baseStart_5747406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747416 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_5747416 : Nat := 118140960795 + 5747416 * 2 ^ 59
def prefixEnd_5747416 : Nat := 4983230072969 + 3 ^ 40 * 5747416 * 2
def baseEnd_5747416 : Nat := 2951186929341390442168121

theorem tailTrace_5747416 : CollatzResearch.WordTrace tailWord_5747416 prefixEnd_5747416 2951186929341390442168121 := by
  unfold tailWord_5747416
  simp only [CollatzResearch.WordTrace]
  refine ⟨104812741473050443675147051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139750321964067258233529401 104812741473050443675147051)
  ·
    refine ⟨157219112209575665512720577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104812741473050443675147051 157219112209575665512720577)
    ·
      refine ⟨117914334157181749134540433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157219112209575665512720577 117914334157181749134540433)
      ·
        refine ⟨88435750617886311850905325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117914334157181749134540433 88435750617886311850905325)
        ·
          refine ⟨33163406481707366944089497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88435750617886311850905325 33163406481707366944089497)
          ·
            refine ⟨24872554861280525208067123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33163406481707366944089497 24872554861280525208067123)
            ·
              refine ⟨37308832291920787812100685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24872554861280525208067123 37308832291920787812100685)
              ·
                refine ⟨13990812109470295429537757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37308832291920787812100685 13990812109470295429537757)
                ·
                  refine ⟨5246554541051360786076659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13990812109470295429537757 5246554541051360786076659)
                  ·
                    refine ⟨7869831811577041179114989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5246554541051360786076659 7869831811577041179114989)
                    ·
                      refine ⟨2951186929341390442168121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7869831811577041179114989 2951186929341390442168121)
                      ·
                        rfl

theorem cell23_5747416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_5747416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747416 prefixEnd_5747416 := by exact prefixLift 5747416
  have htrace : WordTrace (prefixWord ++ tailWord_5747416) baseStart_5747416 baseEnd_5747416 := by
    simpa [prefixWord, tailWord_5747416, baseEnd_5747416] using wordTrace_append hprefix tailTrace_5747416
  have hstable : (prefixWord ++ tailWord_5747416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747416).length < 2 ^ (prefixWord ++ tailWord_5747416).sum := by decide
  have hdescent : baseEnd_5747416 < baseStart_5747416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747444 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5747444 : Nat := 118140960795 + 5747444 * 2 ^ 59
def prefixEnd_5747444 : Nat := 4983230072969 + 3 ^ 40 * 5747444 * 2
def baseEnd_5747444 : Nat := 983733768933238777539331

theorem tailTrace_5747444 : CollatzResearch.WordTrace tailWord_5747444 prefixEnd_5747444 983733768933238777539331 := by
  unfold tailWord_5747444
  simp only [CollatzResearch.WordTrace]
  refine ⟨104813252094999724066156693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139751002793332965421542257 104813252094999724066156693)
  ·
    refine ⟨4913121191953112065601095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104813252094999724066156693 4913121191953112065601095)
    ·
      refine ⟨7369681787929668098401643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913121191953112065601095 7369681787929668098401643)
      ·
        refine ⟨11054522681894502147602465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369681787929668098401643 11054522681894502147602465)
        ·
          refine ⟨8290892011420876610701849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11054522681894502147602465 8290892011420876610701849)
          ·
            refine ⟨6218169008565657458026387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8290892011420876610701849 6218169008565657458026387)
            ·
              refine ⟨9327253512848486187039581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218169008565657458026387 9327253512848486187039581)
              ·
                refine ⟨3497720067318182320139843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9327253512848486187039581 3497720067318182320139843)
                ·
                  refine ⟨5246580100977273480209765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497720067318182320139843 5246580100977273480209765)
                  ·
                    refine ⟨983733768933238777539331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246580100977273480209765 983733768933238777539331)
                    ·
                      rfl

theorem cell23_5747444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5747444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747444 prefixEnd_5747444 := by exact prefixLift 5747444
  have htrace : WordTrace (prefixWord ++ tailWord_5747444) baseStart_5747444 baseEnd_5747444 := by
    simpa [prefixWord, tailWord_5747444, baseEnd_5747444] using wordTrace_append hprefix tailTrace_5747444
  have hstable : (prefixWord ++ tailWord_5747444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747444).length < 2 ^ (prefixWord ++ tailWord_5747444).sum := by decide
  have hdescent : baseEnd_5747444 < baseStart_5747444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747459 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 3]
def baseStart_5747459 : Nat := 118140960795 + 5747459 * 2 ^ 59
def prefixEnd_5747459 : Nat := 4983230072969 + 3 ^ 40 * 5747459 * 2
def baseEnd_5747459 : Nat := 2951209009009533773930423

theorem tailTrace_5747459 : CollatzResearch.WordTrace tailWord_5747459 prefixEnd_5747459 2951209009009533773930423 := by
  unfold tailWord_5747459
  simp only [CollatzResearch.WordTrace]
  refine ⟨209627051284945105694109431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139751367523296737129406287 209627051284945105694109431)
  ·
    refine ⟨314440576927417658541164147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209627051284945105694109431 314440576927417658541164147)
    ·
      refine ⟨471660865391126487811746221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314440576927417658541164147 471660865391126487811746221)
      ·
        refine ⟨176872824521672432929404833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471660865391126487811746221 176872824521672432929404833)
        ·
          refine ⟨132654618391254324697053625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176872824521672432929404833 132654618391254324697053625)
          ·
            refine ⟨99490963793440743522790219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132654618391254324697053625 99490963793440743522790219)
            ·
              refine ⟨149236445690161115284185329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99490963793440743522790219 149236445690161115284185329)
              ·
                refine ⟨111927334267620836463138997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149236445690161115284185329 111927334267620836463138997)
                ·
                  refine ⟨10493187587589453418419281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111927334267620836463138997 10493187587589453418419281)
                  ·
                    refine ⟨7869890690692090063814461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10493187587589453418419281 7869890690692090063814461)
                    ·
                      refine ⟨2951209009009533773930423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7869890690692090063814461 2951209009009533773930423)
                      ·
                        rfl

theorem cell23_5747459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_5747459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747459 prefixEnd_5747459 := by exact prefixLift 5747459
  have htrace : WordTrace (prefixWord ++ tailWord_5747459) baseStart_5747459 baseEnd_5747459 := by
    simpa [prefixWord, tailWord_5747459, baseEnd_5747459] using wordTrace_append hprefix tailTrace_5747459
  have hstable : (prefixWord ++ tailWord_5747459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747459).length < 2 ^ (prefixWord ++ tailWord_5747459).sum := by decide
  have hdescent : baseEnd_5747459 < baseStart_5747459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747466 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_5747466 : Nat := 118140960795 + 5747466 * 2 ^ 59
def prefixEnd_5747466 : Nat := 4983230072969 + 3 ^ 40 * 5747466 * 2
def baseEnd_5747466 : Nat := 983737534458038415514297

theorem tailTrace_5747466 : CollatzResearch.WordTrace tailWord_5747466 prefixEnd_5747466 983737534458038415514297 := by
  unfold tailWord_5747466
  simp only [CollatzResearch.WordTrace]
  refine ⟨52406826648979936472403563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139751537730613163926409501 52406826648979936472403563)
  ·
    refine ⟨78610239973469904708605345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52406826648979936472403563 78610239973469904708605345)
    ·
      refine ⟨58957679980102428531454009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78610239973469904708605345 58957679980102428531454009)
      ·
        refine ⟨44218259985076821398590507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58957679980102428531454009 44218259985076821398590507)
        ·
          refine ⟨66327389977615232097885761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44218259985076821398590507 66327389977615232097885761)
          ·
            refine ⟨49745542483211424073414321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66327389977615232097885761 49745542483211424073414321)
            ·
              refine ⟨37309156862408568055060741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49745542483211424073414321 37309156862408568055060741)
              ·
                refine ⟨6995466911701606510323889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37309156862408568055060741 6995466911701606510323889)
                ·
                  refine ⟨5246600183776204882742917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6995466911701606510323889 5246600183776204882742917)
                  ·
                    refine ⟨983737534458038415514297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246600183776204882742917 983737534458038415514297)
                    ·
                      rfl

theorem cell23_5747466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_5747466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747466 prefixEnd_5747466 := by exact prefixLift 5747466
  have htrace : WordTrace (prefixWord ++ tailWord_5747466) baseStart_5747466 baseEnd_5747466 := by
    simpa [prefixWord, tailWord_5747466, baseEnd_5747466] using wordTrace_append hprefix tailTrace_5747466
  have hstable : (prefixWord ++ tailWord_5747466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747466).length < 2 ^ (prefixWord ++ tailWord_5747466).sum := by decide
  have hdescent : baseEnd_5747466 < baseStart_5747466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747473 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 3, 2, 2]
def baseStart_5747473 : Nat := 118140960795 + 5747473 * 2 ^ 59
def prefixEnd_5747473 : Nat := 4983230072969 + 3 ^ 40 * 5747473 * 2
def baseEnd_5747473 : Nat := 2951216197738696719155359

theorem tailTrace_5747473 : CollatzResearch.WordTrace tailWord_5747473 prefixEnd_5747473 2951216197738696719155359 := by
  unfold tailWord_5747473
  simp only [CollatzResearch.WordTrace]
  refine ⟨209627561906894386085119073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139751707937929590723412715 209627561906894386085119073)
  ·
    refine ⟨157220671430170789563839305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209627561906894386085119073 157220671430170789563839305)
    ·
      refine ⟨117915503572628092172879479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157220671430170789563839305 117915503572628092172879479)
      ·
        refine ⟨176873255358942138259319219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117915503572628092172879479 176873255358942138259319219)
        ·
          refine ⟨265309883038413207388978829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176873255358942138259319219 265309883038413207388978829)
          ·
            refine ⟨99491206139404952770867061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265309883038413207388978829 99491206139404952770867061)
            ·
              refine ⟨9327300575569214322268787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99491206139404952770867061 9327300575569214322268787)
              ·
                refine ⟨13990950863353821483403181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9327300575569214322268787 13990950863353821483403181)
                ·
                  refine ⟨5246606573757683056276193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13990950863353821483403181 5246606573757683056276193)
                  ·
                    refine ⟨3934954930318262292207145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5246606573757683056276193 3934954930318262292207145)
                    ·
                      refine ⟨2951216197738696719155359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3934954930318262292207145 2951216197738696719155359)
                      ·
                        rfl

theorem cell23_5747473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_5747473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747473 prefixEnd_5747473 := by exact prefixLift 5747473
  have htrace : WordTrace (prefixWord ++ tailWord_5747473) baseStart_5747473 baseEnd_5747473 := by
    simpa [prefixWord, tailWord_5747473, baseEnd_5747473] using wordTrace_append hprefix tailTrace_5747473
  have hstable : (prefixWord ++ tailWord_5747473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747473).length < 2 ^ (prefixWord ++ tailWord_5747473).sum := by decide
  have hdescent : baseEnd_5747473 < baseStart_5747473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747506 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_5747506 : Nat := 118140960795 + 5747506 * 2 ^ 59
def prefixEnd_5747506 : Nat := 4983230072969 + 3 ^ 40 * 5747506 * 2
def baseEnd_5747506 : Nat := 2951233142600295090042707

theorem tailTrace_5747506 : CollatzResearch.WordTrace tailWord_5747506 prefixEnd_5747506 2951233142600295090042707 := by
  unfold tailWord_5747506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52407191378943708180267593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139752510343849888480713581 52407191378943708180267593)
  ·
    refine ⟨39305393534207781135200695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52407191378943708180267593 39305393534207781135200695)
    ·
      refine ⟨58958090301311671702801043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39305393534207781135200695 58958090301311671702801043)
      ·
        refine ⟨88437135451967507554201565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58958090301311671702801043 88437135451967507554201565)
        ·
          refine ⟨33163925794487815332825587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88437135451967507554201565 33163925794487815332825587)
          ·
            refine ⟨49745888691731722999238381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33163925794487815332825587 49745888691731722999238381)
            ·
              refine ⟨18654708259399396124714393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49745888691731722999238381 18654708259399396124714393)
              ·
                refine ⟨13991031194549547093535795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18654708259399396124714393 13991031194549547093535795)
                ·
                  refine ⟨20986546791824320640303693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13991031194549547093535795 20986546791824320640303693)
                  ·
                    refine ⟨7869955046934120240113885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20986546791824320640303693 7869955046934120240113885)
                    ·
                      refine ⟨2951233142600295090042707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7869955046934120240113885 2951233142600295090042707)
                      ·
                        rfl

theorem cell23_5747506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_5747506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747506 prefixEnd_5747506 := by exact prefixLift 5747506
  have htrace : WordTrace (prefixWord ++ tailWord_5747506) baseStart_5747506 baseEnd_5747506 := by
    simpa [prefixWord, tailWord_5747506, baseEnd_5747506] using wordTrace_append hprefix tailTrace_5747506
  have hstable : (prefixWord ++ tailWord_5747506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747506).length < 2 ^ (prefixWord ++ tailWord_5747506).sum := by decide
  have hdescent : baseEnd_5747506 < baseStart_5747506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747510 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5747510 : Nat := 118140960795 + 5747510 * 2 ^ 59
def prefixEnd_5747510 : Nat := 4983230072969 + 3 ^ 40 * 5747510 * 2
def baseEnd_5747510 : Nat := 2951235196522913074392689

theorem tailTrace_5747510 : CollatzResearch.WordTrace tailWord_5747510 prefixEnd_5747510 2951235196522913074392689 := by
  unfold tailWord_5747510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13101806962985021337763499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139752607605173560936143989 13101806962985021337763499)
  ·
    refine ⟨19652710444477532006645249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13101806962985021337763499 19652710444477532006645249)
    ·
      refine ⟨14739532833358149004983937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19652710444477532006645249 14739532833358149004983937)
      ·
        refine ⟨11054649625018611753737953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14739532833358149004983937 11054649625018611753737953)
        ·
          refine ⟨8290987218763958815303465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11054649625018611753737953 8290987218763958815303465)
          ·
            refine ⟨6218240414072969111477599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8290987218763958815303465 6218240414072969111477599)
            ·
              refine ⟨9327360621109453667216399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218240414072969111477599 9327360621109453667216399)
              ·
                refine ⟨13991040931664180500824599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9327360621109453667216399 13991040931664180500824599)
                ·
                  refine ⟨20986561397496270751236899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13991040931664180500824599 20986561397496270751236899)
                  ·
                    refine ⟨31479842096244406126855349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20986561397496270751236899 31479842096244406126855349)
                    ·
                      refine ⟨2951235196522913074392689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31479842096244406126855349 2951235196522913074392689)
                      ·
                        rfl

theorem cell23_5747510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5747510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747510 prefixEnd_5747510 := by exact prefixLift 5747510
  have htrace : WordTrace (prefixWord ++ tailWord_5747510) baseStart_5747510 baseEnd_5747510 := by
    simpa [prefixWord, tailWord_5747510, baseEnd_5747510] using wordTrace_append hprefix tailTrace_5747510
  have hstable : (prefixWord ++ tailWord_5747510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747510).length < 2 ^ (prefixWord ++ tailWord_5747510).sum := by decide
  have hdescent : baseEnd_5747510 < baseStart_5747510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747523 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 3]
def baseStart_5747523 : Nat := 118140960795 + 5747523 * 2 ^ 59
def prefixEnd_5747523 : Nat := 4983230072969 + 3 ^ 40 * 5747523 * 2
def baseEnd_5747523 : Nat := 2951241871771421523530129

theorem tailTrace_5747523 : CollatzResearch.WordTrace tailWord_5747523 prefixEnd_5747523 2951241871771421523530129 := by
  unfold tailWord_5747523
  simp only [CollatzResearch.WordTrace]
  refine ⟨209629385556713244624439223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139752923704475496416292815 209629385556713244624439223)
  ·
    refine ⟨314444078335069866936658835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209629385556713244624439223 314444078335069866936658835)
    ·
      refine ⟨471666117502604800404988253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314444078335069866936658835 471666117502604800404988253)
      ·
        refine ⟨176874794063476800151870595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471666117502604800404988253 176874794063476800151870595)
        ·
          refine ⟨265312191095215200227805893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176874794063476800151870595 265312191095215200227805893)
          ·
            refine ⟨49746035830352850042713605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265312191095215200227805893 49746035830352850042713605)
            ·
              refine ⟨9327381718191159383008801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49746035830352850042713605 9327381718191159383008801)
              ·
                refine ⟨6995536288643369537256601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9327381718191159383008801 6995536288643369537256601)
                ·
                  refine ⟨5246652216482527152942451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6995536288643369537256601 5246652216482527152942451)
                  ·
                    refine ⟨7869978324723790729413677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5246652216482527152942451 7869978324723790729413677)
                    ·
                      refine ⟨2951241871771421523530129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7869978324723790729413677 2951241871771421523530129)
                      ·
                        rfl

theorem cell23_5747523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_5747523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747523 prefixEnd_5747523 := by exact prefixLift 5747523
  have htrace : WordTrace (prefixWord ++ tailWord_5747523) baseStart_5747523 baseEnd_5747523 := by
    simpa [prefixWord, tailWord_5747523, baseEnd_5747523] using wordTrace_append hprefix tailTrace_5747523
  have hstable : (prefixWord ++ tailWord_5747523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747523).length < 2 ^ (prefixWord ++ tailWord_5747523).sum := by decide
  have hdescent : baseEnd_5747523 < baseStart_5747523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747529 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_5747529 : Nat := 118140960795 + 5747529 * 2 ^ 59
def prefixEnd_5747529 : Nat := 4983230072969 + 3 ^ 40 * 5747529 * 2
def baseEnd_5747529 : Nat := 2951244952655348500055101

theorem tailTrace_5747529 : CollatzResearch.WordTrace tailWord_5747529 prefixEnd_5747529 2951244952655348500055101 := by
  unfold tailWord_5747529
  simp only [CollatzResearch.WordTrace]
  refine ⟨209629604394691507649157641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139753069596461005099438427 209629604394691507649157641)
  ·
    refine ⟨157222203296018630736868231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209629604394691507649157641 157222203296018630736868231)
    ·
      refine ⟨235833304944027946105302347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157222203296018630736868231 235833304944027946105302347)
      ·
        refine ⟨353749957416041919157953521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235833304944027946105302347 353749957416041919157953521)
        ·
          refine ⟨265312468062031439368465141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353749957416041919157953521 265312468062031439368465141)
          ·
            refine ⟨24873043880815447440793607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 265312468062031439368465141 24873043880815447440793607)
            ·
              refine ⟨37309565821223171161190411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24873043880815447440793607 37309565821223171161190411)
              ·
                refine ⟨55964348731834756741785617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37309565821223171161190411 55964348731834756741785617)
                ·
                  refine ⟨41973261548876067556339213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55964348731834756741785617 41973261548876067556339213)
                  ·
                    refine ⟨15739973080828525333627205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41973261548876067556339213 15739973080828525333627205)
                    ·
                      refine ⟨2951244952655348500055101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15739973080828525333627205 2951244952655348500055101)
                      ·
                        rfl

theorem cell23_5747529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_5747529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747529 prefixEnd_5747529 := by exact prefixLift 5747529
  have htrace : WordTrace (prefixWord ++ tailWord_5747529) baseStart_5747529 baseEnd_5747529 := by
    simpa [prefixWord, tailWord_5747529, baseEnd_5747529] using wordTrace_append hprefix tailTrace_5747529
  have hstable : (prefixWord ++ tailWord_5747529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747529).length < 2 ^ (prefixWord ++ tailWord_5747529).sum := by decide
  have hdescent : baseEnd_5747529 < baseStart_5747529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747596 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_5747596 : Nat := 118140960795 + 5747596 * 2 ^ 59
def prefixEnd_5747596 : Nat := 4983230072969 + 3 ^ 40 * 5747596 * 2
def baseEnd_5747596 : Nat := 2951279355859199737917293

theorem tailTrace_5747596 : CollatzResearch.WordTrace tailWord_5747596 prefixEnd_5747596 2951279355859199737917293 := by
  unfold tailWord_5747596
  simp only [CollatzResearch.WordTrace]
  refine ⟨104816024042724389045923321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139754698723632518727897761 104816024042724389045923321)
  ·
    refine ⟨78612018032043291784442491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104816024042724389045923321 78612018032043291784442491)
    ·
      refine ⟨117918027048064937676663737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78612018032043291784442491 117918027048064937676663737)
      ·
        refine ⟨88438520286048703257497803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117918027048064937676663737 88438520286048703257497803)
        ·
          refine ⟨132657780429073054886246705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88438520286048703257497803 132657780429073054886246705)
          ·
            refine ⟨99493335321804791164685029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132657780429073054886246705 99493335321804791164685029)
            ·
              refine ⟨18655000372838398343378443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99493335321804791164685029 18655000372838398343378443)
              ·
                refine ⟨27982500559257597515067665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18655000372838398343378443 27982500559257597515067665)
                ·
                  refine ⟨20986875419443198136300749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27982500559257597515067665 20986875419443198136300749)
                  ·
                    refine ⟨7870078282291199301112781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20986875419443198136300749 7870078282291199301112781)
                    ·
                      refine ⟨2951279355859199737917293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870078282291199301112781 2951279355859199737917293)
                      ·
                        rfl

theorem cell23_5747596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_5747596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747596 prefixEnd_5747596 := by exact prefixLift 5747596
  have htrace : WordTrace (prefixWord ++ tailWord_5747596) baseStart_5747596 baseEnd_5747596 := by
    simpa [prefixWord, tailWord_5747596, baseEnd_5747596] using wordTrace_append hprefix tailTrace_5747596
  have hstable : (prefixWord ++ tailWord_5747596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747596).length < 2 ^ (prefixWord ++ tailWord_5747596).sum := by decide
  have hdescent : baseEnd_5747596 < baseStart_5747596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747609 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_5747609 : Nat := 118140960795 + 5747609 * 2 ^ 59
def prefixEnd_5747609 : Nat := 4983230072969 + 3 ^ 40 * 5747609 * 2
def baseEnd_5747609 : Nat := 2951286031107708187054733

theorem tailTrace_5747609 : CollatzResearch.WordTrace tailWord_5747609 prefixEnd_5747609 2951286031107708187054733 := by
  unfold tailWord_5747609
  simp only [CollatzResearch.WordTrace]
  refine ⟨209632522234401681312069881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139755014822934454208046587 209632522234401681312069881)
  ·
    refine ⟨157224391675801260984052411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209632522234401681312069881 157224391675801260984052411)
    ·
      refine ⟨235836587513701891476078617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157224391675801260984052411 235836587513701891476078617)
      ·
        refine ⟨176877440635276418607058963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235836587513701891476078617 176877440635276418607058963)
        ·
          refine ⟨265316160952914627910588445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176877440635276418607058963 265316160952914627910588445)
          ·
            refine ⟨99493560357342985466470667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265316160952914627910588445 99493560357342985466470667)
            ·
              refine ⟨149240340536014478199706001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99493560357342985466470667 149240340536014478199706001)
              ·
                refine ⟨111930255402010858649779501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149240340536014478199706001 111930255402010858649779501)
                ·
                  refine ⟨41973845775754071993667313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111930255402010858649779501 41973845775754071993667313)
                  ·
                    refine ⟨31480384331815553995250485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41973845775754071993667313 31480384331815553995250485)
                    ·
                      refine ⟨2951286031107708187054733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31480384331815553995250485 2951286031107708187054733)
                      ·
                        rfl

theorem cell23_5747609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_5747609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747609 prefixEnd_5747609 := by exact prefixLift 5747609
  have htrace : WordTrace (prefixWord ++ tailWord_5747609) baseStart_5747609 baseEnd_5747609 := by
    simpa [prefixWord, tailWord_5747609, baseEnd_5747609] using wordTrace_append hprefix tailTrace_5747609
  have hstable : (prefixWord ++ tailWord_5747609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747609).length < 2 ^ (prefixWord ++ tailWord_5747609).sum := by decide
  have hdescent : baseEnd_5747609 < baseStart_5747609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747633 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 2, 5]
def baseStart_5747633 : Nat := 118140960795 + 5747633 * 2 ^ 59
def prefixEnd_5747633 : Nat := 4983230072969 + 3 ^ 40 * 5747633 * 2
def baseEnd_5747633 : Nat := 983766118214472031051541

theorem tailTrace_5747633 : CollatzResearch.WordTrace tailWord_5747633 prefixEnd_5747633 983766118214472031051541 := by
  unfold tailWord_5747633
  simp only [CollatzResearch.WordTrace]
  refine ⟨209633397586314733410943553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139755598390876488940629035 209633397586314733410943553)
  ·
    refine ⟨157225048189736050058207665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209633397586314733410943553 157225048189736050058207665)
    ·
      refine ⟨117918786142302037543655749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157225048189736050058207665 117918786142302037543655749)
      ·
        refine ⟨22109772401681632039435453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117918786142302037543655749 22109772401681632039435453)
        ·
          refine ⟨8291164650630612014788295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22109772401681632039435453 8291164650630612014788295)
          ·
            refine ⟨12436746975945918022182443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8291164650630612014788295 12436746975945918022182443)
            ·
              refine ⟨18655120463918877033273665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12436746975945918022182443 18655120463918877033273665)
              ·
                refine ⟨13991340347939157774955249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18655120463918877033273665 13991340347939157774955249)
                ·
                  refine ⟨10493505260954368331216437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13991340347939157774955249 10493505260954368331216437)
                  ·
                    refine ⟨983766118214472031051541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10493505260954368331216437 983766118214472031051541)
                    ·
                      rfl

theorem cell23_5747633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_5747633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747633 prefixEnd_5747633 := by exact prefixLift 5747633
  have htrace : WordTrace (prefixWord ++ tailWord_5747633) baseStart_5747633 baseEnd_5747633 := by
    simpa [prefixWord, tailWord_5747633, baseEnd_5747633] using wordTrace_append hprefix tailTrace_5747633
  have hstable : (prefixWord ++ tailWord_5747633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747633).length < 2 ^ (prefixWord ++ tailWord_5747633).sum := by decide
  have hdescent : baseEnd_5747633 < baseStart_5747633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747670 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5747670 : Nat := 118140960795 + 5747670 * 2 ^ 59
def prefixEnd_5747670 : Nat := 4983230072969 + 3 ^ 40 * 5747670 * 2
def baseEnd_5747670 : Nat := 2951317353427632448391953

theorem tailTrace_5747670 : CollatzResearch.WordTrace tailWord_5747670 prefixEnd_5747670 2951317353427632448391953 := by
  unfold tailWord_5747670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102171692948793045627529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139756498058120459153360309 13102171692948793045627529)
  ·
    refine ⟨9826628769711594784220647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13102171692948793045627529 9826628769711594784220647)
    ·
      refine ⟨14739943154567392176330971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826628769711594784220647 14739943154567392176330971)
      ·
        refine ⟨22109914731851088264496457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14739943154567392176330971 22109914731851088264496457)
        ·
          refine ⟨16582436048888316198372343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22109914731851088264496457 16582436048888316198372343)
          ·
            refine ⟨24873654073332474297558515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582436048888316198372343 24873654073332474297558515)
            ·
              refine ⟨37310481109998711446337773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24873654073332474297558515 37310481109998711446337773)
              ·
                refine ⟨13991430416249516792376665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37310481109998711446337773 13991430416249516792376665)
                ·
                  refine ⟨10493572812187137594282499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13991430416249516792376665 10493572812187137594282499)
                  ·
                    refine ⟨15740359218280706391423749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10493572812187137594282499 15740359218280706391423749)
                    ·
                      refine ⟨2951317353427632448391953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15740359218280706391423749 2951317353427632448391953)
                      ·
                        rfl

theorem cell23_5747670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5747670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747670 prefixEnd_5747670 := by exact prefixLift 5747670
  have htrace : WordTrace (prefixWord ++ tailWord_5747670) baseStart_5747670 baseEnd_5747670 := by
    simpa [prefixWord, tailWord_5747670, baseEnd_5747670] using wordTrace_append hprefix tailTrace_5747670
  have hstable : (prefixWord ++ tailWord_5747670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747670).length < 2 ^ (prefixWord ++ tailWord_5747670).sum := by decide
  have hdescent : baseEnd_5747670 < baseStart_5747670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747673 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_5747673 : Nat := 118140960795 + 5747673 * 2 ^ 59
def prefixEnd_5747673 : Nat := 4983230072969 + 3 ^ 40 * 5747673 * 2
def baseEnd_5747673 : Nat := 2951318893869595936654439

theorem tailTrace_5747673 : CollatzResearch.WordTrace tailWord_5747673 prefixEnd_5747673 2951318893869595936654439 := by
  unfold tailWord_5747673
  simp only [CollatzResearch.WordTrace]
  refine ⟨209634856506169820242399673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139756571004113213494933115 209634856506169820242399673)
  ·
    refine ⟨157226142379627365181799755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209634856506169820242399673 157226142379627365181799755)
    ·
      refine ⟨235839213569441047772699633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157226142379627365181799755 235839213569441047772699633)
      ·
        refine ⟨176879410177080785829524725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235839213569441047772699633 176879410177080785829524725)
        ·
          refine ⟨16582444704101323671517943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176879410177080785829524725 16582444704101323671517943)
          ·
            refine ⟨24873667056151985507276915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582444704101323671517943 24873667056151985507276915)
            ·
              refine ⟨37310500584227978260915373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24873667056151985507276915 37310500584227978260915373)
              ·
                refine ⟨13991437719085491847843265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37310500584227978260915373 13991437719085491847843265)
                ·
                  refine ⟨10493578289314118885882449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13991437719085491847843265 10493578289314118885882449)
                  ·
                    refine ⟨7870183716985589164411837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10493578289314118885882449 7870183716985589164411837)
                    ·
                      refine ⟨2951318893869595936654439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870183716985589164411837 2951318893869595936654439)
                      ·
                        rfl

theorem cell23_5747673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_5747673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747673 prefixEnd_5747673 := by exact prefixLift 5747673
  have htrace : WordTrace (prefixWord ++ tailWord_5747673) baseStart_5747673 baseEnd_5747673 := by
    simpa [prefixWord, tailWord_5747673, baseEnd_5747673] using wordTrace_append hprefix tailTrace_5747673
  have hstable : (prefixWord ++ tailWord_5747673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747673).length < 2 ^ (prefixWord ++ tailWord_5747673).sum := by decide
  have hdescent : baseEnd_5747673 < baseStart_5747673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747697 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 1, 4]
def baseStart_5747697 : Nat := 118140960795 + 5747697 * 2 ^ 59
def prefixEnd_5747697 : Nat := 4983230072969 + 3 ^ 40 * 5747697 * 2
def baseEnd_5747697 : Nat := 983777072468434614251443

theorem tailTrace_5747697 : CollatzResearch.WordTrace tailWord_5747697 prefixEnd_5747697 983777072468434614251443 := by
  unfold tailWord_5747697
  simp only [CollatzResearch.WordTrace]
  refine ⟨209635731858082872341273345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139757154572055248227515563 209635731858082872341273345)
  ·
    refine ⟨157226798893562154255955009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209635731858082872341273345 157226798893562154255955009)
    ·
      refine ⟨117920099170171615691966257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157226798893562154255955009 117920099170171615691966257)
      ·
        refine ⟨88440074377628711768974693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117920099170171615691966257 88440074377628711768974693)
        ·
          refine ⟨16582513945805383456682755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88440074377628711768974693 16582513945805383456682755)
          ·
            refine ⟨24873770918708075185024133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582513945805383456682755 24873770918708075185024133)
            ·
              refine ⟨4663832047257764097192025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24873770918708075185024133 4663832047257764097192025)
              ·
                refine ⟨3497874035443323072894019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4663832047257764097192025 3497874035443323072894019)
                ·
                  refine ⟨5246811053164984609341029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497874035443323072894019 5246811053164984609341029)
                  ·
                    refine ⟨983777072468434614251443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246811053164984609341029 983777072468434614251443)
                    ·
                      rfl

theorem cell23_5747697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_5747697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747697 prefixEnd_5747697 := by exact prefixLift 5747697
  have htrace : WordTrace (prefixWord ++ tailWord_5747697) baseStart_5747697 baseEnd_5747697 := by
    simpa [prefixWord, tailWord_5747697, baseEnd_5747697] using wordTrace_append hprefix tailTrace_5747697
  have hstable : (prefixWord ++ tailWord_5747697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747697).length < 2 ^ (prefixWord ++ tailWord_5747697).sum := by decide
  have hdescent : baseEnd_5747697 < baseStart_5747697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747720 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_5747720 : Nat := 118140960795 + 5747720 * 2 ^ 59
def prefixEnd_5747720 : Nat := 4983230072969 + 3 ^ 40 * 5747720 * 2
def baseEnd_5747720 : Nat := 2951343027460357252766723

theorem tailTrace_5747720 : CollatzResearch.WordTrace tailWord_5747720 prefixEnd_5747720 2951343027460357252766723 := by
  unfold tailWord_5747720
  simp only [CollatzResearch.WordTrace]
  refine ⟨104818285368499773634680307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139757713824666364846240409 104818285368499773634680307)
  ·
    refine ⟨157227428052749660452020461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104818285368499773634680307 157227428052749660452020461)
    ·
      refine ⟨58960285519781122669507673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157227428052749660452020461 58960285519781122669507673)
      ·
        refine ⟨44220214139835842002130755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58960285519781122669507673 44220214139835842002130755)
        ·
          refine ⟨66330321209753763003196133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44220214139835842002130755 66330321209753763003196133)
          ·
            refine ⟨12436935226828830563099275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66330321209753763003196133 12436935226828830563099275)
            ·
              refine ⟨18655402840243245844648913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12436935226828830563099275 18655402840243245844648913)
              ·
                refine ⟨13991552130182434383486685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18655402840243245844648913 13991552130182434383486685)
                ·
                  refine ⟨5246832048818412893807507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13991552130182434383486685 5246832048818412893807507)
                  ·
                    refine ⟨7870248073227619340711261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5246832048818412893807507 7870248073227619340711261)
                    ·
                      refine ⟨2951343027460357252766723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870248073227619340711261 2951343027460357252766723)
                      ·
                        rfl

theorem cell23_5747720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_5747720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747720 prefixEnd_5747720 := by exact prefixLift 5747720
  have htrace : WordTrace (prefixWord ++ tailWord_5747720) baseStart_5747720 baseEnd_5747720 := by
    simpa [prefixWord, tailWord_5747720, baseEnd_5747720] using wordTrace_append hprefix tailTrace_5747720
  have hstable : (prefixWord ++ tailWord_5747720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747720).length < 2 ^ (prefixWord ++ tailWord_5747720).sum := by decide
  have hdescent : baseEnd_5747720 < baseStart_5747720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747740 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_5747740 : Nat := 118140960795 + 5747740 * 2 ^ 59
def prefixEnd_5747740 : Nat := 4983230072969 + 3 ^ 40 * 5747740 * 2
def baseEnd_5747740 : Nat := 983784432357815724838877

theorem tailTrace_5747740 : CollatzResearch.WordTrace tailWord_5747740 prefixEnd_5747740 983784432357815724838877 := by
  unfold tailWord_5747740
  simp only [CollatzResearch.WordTrace]
  refine ⟨104818650098463545342544337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139758200131284727123392449 104818650098463545342544337)
  ·
    refine ⟨78613987573847659006908253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104818650098463545342544337 78613987573847659006908253)
    ·
      refine ⟨29480245340192872127590595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78613987573847659006908253 29480245340192872127590595)
      ·
        refine ⟨44220368010289308191385893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29480245340192872127590595 44220368010289308191385893)
        ·
          refine ⟨8291319001929245285884855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44220368010289308191385893 8291319001929245285884855)
          ·
            refine ⟨12436978502893867928827283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8291319001929245285884855 12436978502893867928827283)
            ·
              refine ⟨18655467754340801893240925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12436978502893867928827283 18655467754340801893240925)
              ·
                refine ⟨6995800407877800709965347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18655467754340801893240925 6995800407877800709965347)
                ·
                  refine ⟨10493700611816701064948021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6995800407877800709965347 10493700611816701064948021)
                  ·
                    refine ⟨983784432357815724838877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10493700611816701064948021 983784432357815724838877)
                    ·
                      rfl

theorem cell23_5747740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_5747740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747740 prefixEnd_5747740 := by exact prefixLift 5747740
  have htrace : WordTrace (prefixWord ++ tailWord_5747740) baseStart_5747740 baseEnd_5747740 := by
    simpa [prefixWord, tailWord_5747740, baseEnd_5747740] using wordTrace_append hprefix tailTrace_5747740
  have hstable : (prefixWord ++ tailWord_5747740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747740).length < 2 ^ (prefixWord ++ tailWord_5747740).sum := by decide
  have hdescent : baseEnd_5747740 < baseStart_5747740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747756 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_5747756 : Nat := 118140960795 + 5747756 * 2 ^ 59
def prefixEnd_5747756 : Nat := 4983230072969 + 3 ^ 40 * 5747756 * 2
def baseEnd_5747756 : Nat := 2951361512763919111916557

theorem tailTrace_5747756 : CollatzResearch.WordTrace tailWord_5747756 prefixEnd_5747756 2951361512763919111916557 := by
  unfold tailWord_5747756
  simp only [CollatzResearch.WordTrace]
  refine ⟨104818941882434562708835561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139758589176579416945114081 104818941882434562708835561)
  ·
    refine ⟨78614206411825922031626671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104818941882434562708835561 78614206411825922031626671)
    ·
      refine ⟨117921309617738883047440007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78614206411825922031626671 117921309617738883047440007)
      ·
        refine ⟨176881964426608324571160011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117921309617738883047440007 176881964426608324571160011)
        ·
          refine ⟨265322946639912486856740017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176881964426608324571160011 265322946639912486856740017)
          ·
            refine ⟨198992209979934365142555013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265322946639912486856740017 198992209979934365142555013)
            ·
              refine ⟨37311039371237693464229065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198992209979934365142555013 37311039371237693464229065)
              ·
                refine ⟨27983279528428270098171799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37311039371237693464229065 27983279528428270098171799)
                ·
                  refine ⟨41974919292642405147257699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27983279528428270098171799 41974919292642405147257699)
                  ·
                    refine ⟨62962378938963607720886549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41974919292642405147257699 62962378938963607720886549)
                    ·
                      refine ⟨2951361512763919111916557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62962378938963607720886549 2951361512763919111916557)
                      ·
                        rfl

theorem cell23_5747756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_5747756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747756 prefixEnd_5747756 := by exact prefixLift 5747756
  have htrace : WordTrace (prefixWord ++ tailWord_5747756) baseStart_5747756 baseEnd_5747756 := by
    simpa [prefixWord, tailWord_5747756, baseEnd_5747756] using wordTrace_append hprefix tailTrace_5747756
  have hstable : (prefixWord ++ tailWord_5747756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747756).length < 2 ^ (prefixWord ++ tailWord_5747756).sum := by decide
  have hdescent : baseEnd_5747756 < baseStart_5747756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747773 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5747773 : Nat := 118140960795 + 5747773 * 2 ^ 59
def prefixEnd_5747773 : Nat := 4983230072969 + 3 ^ 40 * 5747773 * 2
def baseEnd_5747773 : Nat := 2951370241935045545403979

theorem tailTrace_5747773 : CollatzResearch.WordTrace tailWord_5747773 prefixEnd_5747773 2951370241935045545403979 := by
  unfold tailWord_5747773
  simp only [CollatzResearch.WordTrace]
  refine ⟨209638503805807537321039973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139759002537205024880693315 209638503805807537321039973)
  ·
    refine ⟨39307219463588913247694995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209638503805807537321039973 39307219463588913247694995)
    ·
      refine ⟨58960829195383369871542493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39307219463588913247694995 58960829195383369871542493)
      ·
        refine ⟨22110310948268763701828435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58960829195383369871542493 22110310948268763701828435)
        ·
          refine ⟨33165466422403145552742653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22110310948268763701828435 33165466422403145552742653)
          ·
            refine ⟨12437049908401179582278495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33165466422403145552742653 12437049908401179582278495)
            ·
              refine ⟨18655574862601769373417743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12437049908401179582278495 18655574862601769373417743)
              ·
                refine ⟨27983362293902654060126615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18655574862601769373417743 27983362293902654060126615)
                ·
                  refine ⟨41975043440853981090189923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27983362293902654060126615 41975043440853981090189923)
                  ·
                    refine ⟨62962565161280971635284885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41975043440853981090189923 62962565161280971635284885)
                    ·
                      refine ⟨2951370241935045545403979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62962565161280971635284885 2951370241935045545403979)
                      ·
                        rfl

theorem cell23_5747773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5747773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747773 prefixEnd_5747773 := by exact prefixLift 5747773
  have htrace : WordTrace (prefixWord ++ tailWord_5747773) baseStart_5747773 baseEnd_5747773 := by
    simpa [prefixWord, tailWord_5747773, baseEnd_5747773] using wordTrace_append hprefix tailTrace_5747773
  have hstable : (prefixWord ++ tailWord_5747773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747773).length < 2 ^ (prefixWord ++ tailWord_5747773).sum := by decide
  have hdescent : baseEnd_5747773 < baseStart_5747773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747777 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5747777 : Nat := 118140960795 + 5747777 * 2 ^ 59
def prefixEnd_5747777 : Nat := 4983230072969 + 3 ^ 40 * 5747777 * 2
def baseEnd_5747777 : Nat := 2951372295857663529753961

theorem tailTrace_5747777 : CollatzResearch.WordTrace tailWord_5747777 prefixEnd_5747777 2951372295857663529753961 := by
  unfold tailWord_5747777
  simp only [CollatzResearch.WordTrace]
  refine ⟨209638649697793046004185585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139759099798528697336123723 209638649697793046004185585)
  ·
    refine ⟨157228987273344784503139189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209638649697793046004185585 157228987273344784503139189)
    ·
      refine ⟨14740217556876073547169299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157228987273344784503139189 14740217556876073547169299)
      ·
        refine ⟨22110326335314110320753949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14740217556876073547169299 22110326335314110320753949)
        ·
          refine ⟨8291372375742791370282731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22110326335314110320753949 8291372375742791370282731)
          ·
            refine ⟨12437058563614187055424097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8291372375742791370282731 12437058563614187055424097)
            ·
              refine ⟨9327793922710640291568073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12437058563614187055424097 9327793922710640291568073)
              ·
                refine ⟨6995845442032980218676055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9327793922710640291568073 6995845442032980218676055)
                ·
                  refine ⟨10493768163049470328014083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6995845442032980218676055 10493768163049470328014083)
                  ·
                    refine ⟨15740652244574205492021125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10493768163049470328014083 15740652244574205492021125)
                    ·
                      refine ⟨2951372295857663529753961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15740652244574205492021125 2951372295857663529753961)
                      ·
                        rfl

theorem cell23_5747777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5747777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747777 prefixEnd_5747777 := by exact prefixLift 5747777
  have htrace : WordTrace (prefixWord ++ tailWord_5747777) baseStart_5747777 baseEnd_5747777 := by
    simpa [prefixWord, tailWord_5747777, baseEnd_5747777] using wordTrace_append hprefix tailTrace_5747777
  have hstable : (prefixWord ++ tailWord_5747777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747777).length < 2 ^ (prefixWord ++ tailWord_5747777).sum := by decide
  have hdescent : baseEnd_5747777 < baseStart_5747777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
