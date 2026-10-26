import V185TrunkScan23Chunk1251

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7415285 : List Nat := [1, 3, 5, 1, 1, 2, 1, 9]
def baseStart_7415285 : Nat := 118140960795 + 7415285 * 2 ^ 59
def prefixEnd_7415285 : Nat := 4983230072969 + 3 ^ 40 * 7415285 * 2
def baseEnd_7415285 : Nat := 141022422039819459149453

theorem tailTrace_7415285 : CollatzResearch.WordTrace tailWord_7415285 prefixEnd_7415285 141022422039819459149453 := by
  unfold tailWord_7415285
  simp only [CollatzResearch.WordTrace]
  refine ⟨270457662940696349697479309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180305108627130899798319539 270457662940696349697479309)
  ·
    refine ⟨101421623602761131136554741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270457662940696349697479309 101421623602761131136554741)
    ·
      refine ⟨9508277212758856044052007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101421623602761131136554741 9508277212758856044052007)
      ·
        refine ⟨14262415819138284066078011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9508277212758856044052007 14262415819138284066078011)
        ·
          refine ⟨21393623728707426099117017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262415819138284066078011 21393623728707426099117017)
          ·
            refine ⟨16045217796530569574337763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21393623728707426099117017 16045217796530569574337763)
            ·
              refine ⟨24067826694795854361506645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16045217796530569574337763 24067826694795854361506645)
              ·
                refine ⟨141022422039819459149453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24067826694795854361506645 141022422039819459149453)
                ·
                  rfl

theorem cell23_7415285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 9].length) (baseStart_7415285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415285 prefixEnd_7415285 := by exact prefixLift 7415285
  have htrace : WordTrace (prefixWord ++ tailWord_7415285) baseStart_7415285 baseEnd_7415285 := by
    simpa [prefixWord, tailWord_7415285, baseEnd_7415285] using wordTrace_append hprefix tailTrace_7415285
  have hstable : (prefixWord ++ tailWord_7415285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415285).length < 2 ^ (prefixWord ++ tailWord_7415285).sum := by decide
  have hdescent : baseEnd_7415285 < baseStart_7415285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415329 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_7415329 : Nat := 118140960795 + 7415329 * 2 ^ 59
def prefixEnd_7415329 : Nat := 4983230072969 + 3 ^ 40 * 7415329 * 2
def baseEnd_7415329 : Nat := 3807627988223923224885029

theorem tailTrace_7415329 : CollatzResearch.WordTrace tailWord_7415329 prefixEnd_7415329 3807627988223923224885029 := by
  unfold tailWord_7415329
  simp only [CollatzResearch.WordTrace]
  refine ⟨270459267752536945212081041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180306178501691296808054027 270459267752536945212081041)
  ·
    refine ⟨202844450814402708909060781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270459267752536945212081041 202844450814402708909060781)
    ·
      refine ⟨76066669055401015840897793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202844450814402708909060781 76066669055401015840897793)
      ·
        refine ⟨57050001791550761880673345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76066669055401015840897793 57050001791550761880673345)
        ·
          refine ⟨42787501343663071410505009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57050001791550761880673345 42787501343663071410505009)
          ·
            refine ⟨32090626007747303557878757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42787501343663071410505009 32090626007747303557878757)
            ·
              refine ⟨6016992376452619417102267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32090626007747303557878757 6016992376452619417102267)
              ·
                refine ⟨9025488564678929125653401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016992376452619417102267 9025488564678929125653401)
                ·
                  refine ⟨6769116423509196844240051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9025488564678929125653401 6769116423509196844240051)
                  ·
                    refine ⟨10153674635263795266360077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6769116423509196844240051 10153674635263795266360077)
                    ·
                      refine ⟨3807627988223923224885029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10153674635263795266360077 3807627988223923224885029)
                      ·
                        rfl

theorem cell23_7415329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_7415329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415329 prefixEnd_7415329 := by exact prefixLift 7415329
  have htrace : WordTrace (prefixWord ++ tailWord_7415329) baseStart_7415329 baseEnd_7415329 := by
    simpa [prefixWord, tailWord_7415329, baseEnd_7415329] using wordTrace_append hprefix tailTrace_7415329
  have hstable : (prefixWord ++ tailWord_7415329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415329).length < 2 ^ (prefixWord ++ tailWord_7415329).sum := by decide
  have hdescent : baseEnd_7415329 < baseStart_7415329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415352 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 1, 4, 2]
def baseStart_7415352 : Nat := 118140960795 + 7415352 * 2 ^ 59
def prefixEnd_7415352 : Nat := 4983230072969 + 3 ^ 40 * 7415352 * 2
def baseEnd_7415352 : Nat := 3807639798278976634897423

theorem tailTrace_7415352 : CollatzResearch.WordTrace tailWord_7415352 prefixEnd_7415352 3807639798278976634897423 := by
  unfold tailWord_7415352
  simp only [CollatzResearch.WordTrace]
  refine ⟨135230053315726810070084155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180306737754302413426778873 135230053315726810070084155)
  ·
    refine ⟨202845079973590215105126233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135230053315726810070084155 202845079973590215105126233)
    ·
      refine ⟨152133809980192661328844675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202845079973590215105126233 152133809980192661328844675)
      ·
        refine ⟨228200714970288991993267013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152133809980192661328844675 228200714970288991993267013)
        ·
          refine ⟨42787634056929185998737565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228200714970288991993267013 42787634056929185998737565)
          ·
            refine ⟨16045362771348444749526587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42787634056929185998737565 16045362771348444749526587)
            ·
              refine ⟨24068044157022667124289881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16045362771348444749526587 24068044157022667124289881)
              ·
                refine ⟨18051033117767000343217411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24068044157022667124289881 18051033117767000343217411)
                ·
                  refine ⟨27076549676650500514826117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18051033117767000343217411 27076549676650500514826117)
                  ·
                    refine ⟨5076853064371968846529897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27076549676650500514826117 5076853064371968846529897)
                    ·
                      refine ⟨3807639798278976634897423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076853064371968846529897 3807639798278976634897423)
                      ·
                        rfl

theorem cell23_7415352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_7415352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415352 prefixEnd_7415352 := by exact prefixLift 7415352
  have htrace : WordTrace (prefixWord ++ tailWord_7415352) baseStart_7415352 baseEnd_7415352 := by
    simpa [prefixWord, tailWord_7415352, baseEnd_7415352] using wordTrace_append hprefix tailTrace_7415352
  have hstable : (prefixWord ++ tailWord_7415352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415352).length < 2 ^ (prefixWord ++ tailWord_7415352).sum := by decide
  have hdescent : baseEnd_7415352 < baseStart_7415352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415356 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_7415356 : Nat := 118140960795 + 7415356 * 2 ^ 59
def prefixEnd_7415356 : Nat := 4983230072969 + 3 ^ 40 * 7415356 * 2
def baseEnd_7415356 : Nat := 3807641852201594619247405

theorem tailTrace_7415356 : CollatzResearch.WordTrace tailWord_7415356 prefixEnd_7415356 3807641852201594619247405 := by
  unfold tailWord_7415356
  simp only [CollatzResearch.WordTrace]
  refine ⟨135230126261719564411656961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180306835015626085882209281 135230126261719564411656961)
  ·
    refine ⟨101422594696289673308742721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135230126261719564411656961 101422594696289673308742721)
    ·
      refine ⟨76066946022217254981557041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101422594696289673308742721 76066946022217254981557041)
      ·
        refine ⟨57050209516662941236167781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76066946022217254981557041 57050209516662941236167781)
        ·
          refine ⟨10696914284374301481781459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57050209516662941236167781 10696914284374301481781459)
          ·
            refine ⟨16045371426561452222672189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696914284374301481781459 16045371426561452222672189)
            ·
              refine ⟨6017014284960544583502071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16045371426561452222672189 6017014284960544583502071)
              ·
                refine ⟨9025521427440816875253107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017014284960544583502071 9025521427440816875253107)
                ·
                  refine ⟨13538282141161225312879661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025521427440816875253107 13538282141161225312879661)
                  ·
                    refine ⟨5076855802935459492329873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13538282141161225312879661 5076855802935459492329873)
                    ·
                      refine ⟨3807641852201594619247405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076855802935459492329873 3807641852201594619247405)
                      ·
                        rfl

theorem cell23_7415356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_7415356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415356 prefixEnd_7415356 := by exact prefixLift 7415356
  have htrace : WordTrace (prefixWord ++ tailWord_7415356) baseStart_7415356 baseEnd_7415356 := by
    simpa [prefixWord, tailWord_7415356, baseEnd_7415356] using wordTrace_append hprefix tailTrace_7415356
  have hstable : (prefixWord ++ tailWord_7415356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415356).length < 2 ^ (prefixWord ++ tailWord_7415356).sum := by decide
  have hdescent : baseEnd_7415356 < baseStart_7415356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415495 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 3, 5]
def baseStart_7415495 : Nat := 118140960795 + 7415495 * 2 ^ 59
def prefixEnd_7415495 : Nat := 4983230072969 + 3 ^ 40 * 7415495 * 2
def baseEnd_7415495 : Nat := 1269237742004189858469755

theorem tailTrace_7415495 : CollatzResearch.WordTrace tailWord_7415495 prefixEnd_7415495 1269237742004189858469755 := by
  unfold tailWord_7415495
  simp only [CollatzResearch.WordTrace]
  refine ⟨270465322269935555562623939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180310214846623703708415959 270465322269935555562623939)
  ·
    refine ⟨405697983404903333343935909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270465322269935555562623939 405697983404903333343935909)
    ·
      refine ⟨76068371888419375001987983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405697983404903333343935909 76068371888419375001987983)
      ·
        refine ⟨114102557832629062502981975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76068371888419375001987983 114102557832629062502981975)
        ·
          refine ⟨171153836748943593754472963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114102557832629062502981975 171153836748943593754472963)
          ·
            refine ⟨256730755123415390631709445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171153836748943593754472963 256730755123415390631709445)
            ·
              refine ⟨48137016585640385743445521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256730755123415390631709445 48137016585640385743445521)
              ·
                refine ⟨36102762439230289307584141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48137016585640385743445521 36102762439230289307584141)
                ·
                  refine ⟨13538535914711358490344053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36102762439230289307584141 13538535914711358490344053)
                  ·
                    refine ⟨1269237742004189858469755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13538535914711358490344053 1269237742004189858469755)
                    ·
                      rfl

theorem cell23_7415495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_7415495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415495 prefixEnd_7415495 := by exact prefixLift 7415495
  have htrace : WordTrace (prefixWord ++ tailWord_7415495) baseStart_7415495 baseEnd_7415495 := by
    simpa [prefixWord, tailWord_7415495, baseEnd_7415495] using wordTrace_append hprefix tailTrace_7415495
  have hstable : (prefixWord ++ tailWord_7415495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415495).length < 2 ^ (prefixWord ++ tailWord_7415495).sum := by decide
  have hdescent : baseEnd_7415495 < baseStart_7415495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415519 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 2, 3, 2]
def baseStart_7415519 : Nat := 118140960795 + 7415519 * 2 ^ 59
def prefixEnd_7415519 : Nat := 4983230072969 + 3 ^ 40 * 7415519 * 2
def baseEnd_7415519 : Nat := 3807725549548277481509155

theorem tailTrace_7415519 : CollatzResearch.WordTrace tailWord_7415519 prefixEnd_7415519 3807725549548277481509155 := by
  unfold tailWord_7415519
  simp only [CollatzResearch.WordTrace]
  refine ⟨270466197621848607661497611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180310798414565738440998407 270466197621848607661497611)
  ·
    refine ⟨405699296432772911492246417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270466197621848607661497611 405699296432772911492246417)
    ·
      refine ⟨304274472324579683619184813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405699296432772911492246417 304274472324579683619184813)
      ·
        refine ⟨114102927121717381357194305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304274472324579683619184813 114102927121717381357194305)
        ·
          refine ⟨85577195341288036017895729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114102927121717381357194305 85577195341288036017895729)
          ·
            refine ⟨64182896505966027013421797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85577195341288036017895729 64182896505966027013421797)
            ·
              refine ⟨12034293094868630065016587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64182896505966027013421797 12034293094868630065016587)
              ·
                refine ⟨18051439642302945097524881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12034293094868630065016587 18051439642302945097524881)
                ·
                  refine ⟨13538579731727208823143661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18051439642302945097524881 13538579731727208823143661)
                  ·
                    refine ⟨5076967399397703308678873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13538579731727208823143661 5076967399397703308678873)
                    ·
                      refine ⟨3807725549548277481509155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076967399397703308678873 3807725549548277481509155)
                      ·
                        rfl

theorem cell23_7415519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_7415519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415519 prefixEnd_7415519 := by exact prefixLift 7415519
  have htrace : WordTrace (prefixWord ++ tailWord_7415519) baseStart_7415519 baseEnd_7415519 := by
    simpa [prefixWord, tailWord_7415519, baseEnd_7415519] using wordTrace_append hprefix tailTrace_7415519
  have hstable : (prefixWord ++ tailWord_7415519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415519).length < 2 ^ (prefixWord ++ tailWord_7415519).sum := by decide
  have hdescent : baseEnd_7415519 < baseStart_7415519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415532 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_7415532 : Nat := 118140960795 + 7415532 * 2 ^ 59
def prefixEnd_7415532 : Nat := 4983230072969 + 3 ^ 40 * 7415532 * 2
def baseEnd_7415532 : Nat := 3807732224796785930646595

theorem tailTrace_7415532 : CollatzResearch.WordTrace tailWord_7415532 prefixEnd_7415532 3807732224796785930646595 := by
  unfold tailWord_7415532
  simp only [CollatzResearch.WordTrace]
  refine ⟨135233335885400755440860425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180311114513867673921147233 135233335885400755440860425)
  ·
    refine ⟨101425001914050566580645319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135233335885400755440860425 101425001914050566580645319)
    ·
      refine ⟨152137502871075849870967979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101425001914050566580645319 152137502871075849870967979)
      ·
        refine ⟨228206254306613774806451969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152137502871075849870967979 228206254306613774806451969)
        ·
          refine ⟨171154690729960331104838977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228206254306613774806451969 171154690729960331104838977)
          ·
            refine ⟨128366018047470248328629233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171154690729960331104838977 128366018047470248328629233)
            ·
              refine ⟨96274513535602686246471925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128366018047470248328629233 96274513535602686246471925)
              ·
                refine ⟨9025735643962751835606743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96274513535602686246471925 9025735643962751835606743)
                ·
                  refine ⟨13538603465944127753410115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025735643962751835606743 13538603465944127753410115)
                  ·
                    refine ⟨20307905198916191630115173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13538603465944127753410115 20307905198916191630115173)
                    ·
                      refine ⟨3807732224796785930646595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20307905198916191630115173 3807732224796785930646595)
                      ·
                        rfl

theorem cell23_7415532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_7415532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415532 prefixEnd_7415532 := by exact prefixLift 7415532
  have htrace : WordTrace (prefixWord ++ tailWord_7415532) baseStart_7415532 baseEnd_7415532 := by
    simpa [prefixWord, tailWord_7415532, baseEnd_7415532] using wordTrace_append hprefix tailTrace_7415532
  have hstable : (prefixWord ++ tailWord_7415532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415532).length < 2 ^ (prefixWord ++ tailWord_7415532).sum := by decide
  have hdescent : baseEnd_7415532 < baseStart_7415532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415555 : List Nat := [1, 1, 1, 3, 2, 2, 5, 8]
def baseStart_7415555 : Nat := 118140960795 + 7415555 * 2 ^ 59
def prefixEnd_7415555 : Nat := 4983230072969 + 3 ^ 40 * 7415555 * 2
def baseEnd_7415555 : Nat := 141027556846364420024407

theorem tailTrace_7415555 : CollatzResearch.WordTrace tailWord_7415555 prefixEnd_7415555 141027556846364420024407 := by
  unfold tailWord_7415555
  simp only [CollatzResearch.WordTrace]
  refine ⟨270467510649718185809808119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180311673766478790539872079 270467510649718185809808119)
  ·
    refine ⟨405701265974577278714712179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270467510649718185809808119 405701265974577278714712179)
    ·
      refine ⟨608551898961865918072068269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405701265974577278714712179 608551898961865918072068269)
      ·
        refine ⟨228206962110699719277025601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608551898961865918072068269 228206962110699719277025601)
        ·
          refine ⟨171155221583024789457769201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228206962110699719277025601 171155221583024789457769201)
          ·
            refine ⟨128366416187268592093326901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171155221583024789457769201 128366416187268592093326901)
            ·
              refine ⟨12034351517556430508749397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128366416187268592093326901 12034351517556430508749397)
              ·
                refine ⟨141027556846364420024407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12034351517556430508749397 141027556846364420024407)
                ·
                  rfl

theorem cell23_7415555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 8].length) (baseStart_7415555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415555 prefixEnd_7415555 := by exact prefixLift 7415555
  have htrace : WordTrace (prefixWord ++ tailWord_7415555) baseStart_7415555 baseEnd_7415555 := by
    simpa [prefixWord, tailWord_7415555, baseEnd_7415555] using wordTrace_append hprefix tailTrace_7415555
  have hstable : (prefixWord ++ tailWord_7415555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415555).length < 2 ^ (prefixWord ++ tailWord_7415555).sum := by decide
  have hdescent : baseEnd_7415555 < baseStart_7415555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415559 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 1, 6]
def baseStart_7415559 : Nat := 118140960795 + 7415559 * 2 ^ 59
def prefixEnd_7415559 : Nat := 4983230072969 + 3 ^ 40 * 7415559 * 2
def baseEnd_7415559 : Nat := 1269248696258152441669657

theorem tailTrace_7415559 : CollatzResearch.WordTrace tailWord_7415559 prefixEnd_7415559 1269248696258152441669657 := by
  unfold tailWord_7415559
  simp only [CollatzResearch.WordTrace]
  refine ⟨270467656541703694492953731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180311771027802462995302487 270467656541703694492953731)
  ·
    refine ⟨405701484812555541739430597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270467656541703694492953731 405701484812555541739430597)
    ·
      refine ⟨76069028402354164076143237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405701484812555541739430597 76069028402354164076143237)
      ·
        refine ⟨14262942825441405764276857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76069028402354164076143237 14262942825441405764276857)
        ·
          refine ⟨10697207119081054323207643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14262942825441405764276857 10697207119081054323207643)
          ·
            refine ⟨16045810678621581484811465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10697207119081054323207643 16045810678621581484811465)
            ·
              refine ⟨12034358008966186113608599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16045810678621581484811465 12034358008966186113608599)
              ·
                refine ⟨18051537013449279170412899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12034358008966186113608599 18051537013449279170412899)
                ·
                  refine ⟨27077305520173918755619349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18051537013449279170412899 27077305520173918755619349)
                  ·
                    refine ⟨1269248696258152441669657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27077305520173918755619349 1269248696258152441669657)
                    ·
                      rfl

theorem cell23_7415559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_7415559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415559 prefixEnd_7415559 := by exact prefixLift 7415559
  have htrace : WordTrace (prefixWord ++ tailWord_7415559) baseStart_7415559 baseEnd_7415559 := by
    simpa [prefixWord, tailWord_7415559, baseEnd_7415559] using wordTrace_append hprefix tailTrace_7415559
  have hstable : (prefixWord ++ tailWord_7415559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415559).length < 2 ^ (prefixWord ++ tailWord_7415559).sum := by decide
  have hdescent : baseEnd_7415559 < baseStart_7415559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415562 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_7415562 : Nat := 118140960795 + 7415562 * 2 ^ 59
def prefixEnd_7415562 : Nat := 4983230072969 + 3 ^ 40 * 7415562 * 2
def baseEnd_7415562 : Nat := 3807747629216420813271457

theorem tailTrace_7415562 : CollatzResearch.WordTrace tailWord_7415562 prefixEnd_7415562 3807747629216420813271457 := by
  unfold tailWord_7415562
  simp only [CollatzResearch.WordTrace]
  refine ⟨67616941490173206501328235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180311843973795217336875293 67616941490173206501328235)
  ·
    refine ⟨101425412235259809751992353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67616941490173206501328235 101425412235259809751992353)
    ·
      refine ⟨76069059176444857313994265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101425412235259809751992353 76069059176444857313994265)
      ·
        refine ⟨57051794382333642985495699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76069059176444857313994265 57051794382333642985495699)
        ·
          refine ⟨85577691573500464478243549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57051794382333642985495699 85577691573500464478243549)
          ·
            refine ⟨32091634340062674179341331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85577691573500464478243549 32091634340062674179341331)
            ·
              refine ⟨48137451510094011269011997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32091634340062674179341331 48137451510094011269011997)
              ·
                refine ⟨18051544316285254225879499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48137451510094011269011997 18051544316285254225879499)
                ·
                  refine ⟨27077316474427881338819249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18051544316285254225879499 27077316474427881338819249)
                  ·
                    refine ⟨20307987355820911004114437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27077316474427881338819249 20307987355820911004114437)
                    ·
                      refine ⟨3807747629216420813271457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20307987355820911004114437 3807747629216420813271457)
                      ·
                        rfl

theorem cell23_7415562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_7415562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415562 prefixEnd_7415562 := by exact prefixLift 7415562
  have htrace : WordTrace (prefixWord ++ tailWord_7415562) baseStart_7415562 baseEnd_7415562 := by
    simpa [prefixWord, tailWord_7415562, baseEnd_7415562] using wordTrace_append hprefix tailTrace_7415562
  have hstable : (prefixWord ++ tailWord_7415562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415562).length < 2 ^ (prefixWord ++ tailWord_7415562).sum := by decide
  have hdescent : baseEnd_7415562 < baseStart_7415562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415583 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 1, 2, 2]
def baseStart_7415583 : Nat := 118140960795 + 7415583 * 2 ^ 59
def prefixEnd_7415583 : Nat := 4983230072969 + 3 ^ 40 * 7415583 * 2
def baseEnd_7415583 : Nat := 3807758412310165231108861

theorem tailTrace_7415583 : CollatzResearch.WordTrace tailWord_7415583 prefixEnd_7415583 3807758412310165231108861 := by
  unfold tailWord_7415583
  simp only [CollatzResearch.WordTrace]
  refine ⟨270468531893616746591827403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180312354595744497727884935 270468531893616746591827403)
  ·
    refine ⟨405702797840425119887741105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270468531893616746591827403 405702797840425119887741105)
    ·
      refine ⟨304277098380318839915805829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405702797840425119887741105 304277098380318839915805829)
      ·
        refine ⟨57051955946309782484213593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304277098380318839915805829 57051955946309782484213593)
        ·
          refine ⟨42788966959732336863160195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57051955946309782484213593 42788966959732336863160195)
          ·
            refine ⟨64183450439598505294740293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42788966959732336863160195 64183450439598505294740293)
            ·
              refine ⟨12034396957424719742763805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64183450439598505294740293 12034396957424719742763805)
              ·
                refine ⟨4512898859034269903536427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12034396957424719742763805 4512898859034269903536427)
                ·
                  refine ⟨6769348288551404855304641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512898859034269903536427 6769348288551404855304641)
                  ·
                    refine ⟨5077011216413553641478481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6769348288551404855304641 5077011216413553641478481)
                    ·
                      refine ⟨3807758412310165231108861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077011216413553641478481 3807758412310165231108861)
                      ·
                        rfl

theorem cell23_7415583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_7415583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415583 prefixEnd_7415583 := by exact prefixLift 7415583
  have htrace : WordTrace (prefixWord ++ tailWord_7415583) baseStart_7415583 baseEnd_7415583 := by
    simpa [prefixWord, tailWord_7415583, baseEnd_7415583] using wordTrace_append hprefix tailTrace_7415583
  have hstable : (prefixWord ++ tailWord_7415583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415583).length < 2 ^ (prefixWord ++ tailWord_7415583).sum := by decide
  have hdescent : baseEnd_7415583 < baseStart_7415583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415626 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_7415626 : Nat := 118140960795 + 7415626 * 2 ^ 59
def prefixEnd_7415626 : Nat := 4983230072969 + 3 ^ 40 * 7415626 * 2
def baseEnd_7415626 : Nat := 3807780491978308562871163

theorem tailTrace_7415626 : CollatzResearch.WordTrace tailWord_7415626 prefixEnd_7415626 3807780491978308562871163 := by
  unfold tailWord_7415626
  simp only [CollatzResearch.WordTrace]
  refine ⟨67617525058115241233910683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180313400154973976623761821 67617525058115241233910683)
  ·
    refine ⟨101426287587172861850866025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67617525058115241233910683 101426287587172861850866025)
    ·
      refine ⟨76069715690379646388149519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101426287587172861850866025 76069715690379646388149519)
      ·
        refine ⟨114104573535569469582224279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76069715690379646388149519 114104573535569469582224279)
        ·
          refine ⟨171156860303354204373336419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114104573535569469582224279 171156860303354204373336419)
          ·
            refine ⟨256735290455031306560004629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171156860303354204373336419 256735290455031306560004629)
            ·
              refine ⟨12034466740079592495000217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256735290455031306560004629 12034466740079592495000217)
              ·
                refine ⟨9025850055059694371250163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12034466740079592495000217 9025850055059694371250163)
                ·
                  refine ⟨13538775082589541556875245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025850055059694371250163 13538775082589541556875245)
                  ·
                    refine ⟨5077040655971078083828217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13538775082589541556875245 5077040655971078083828217)
                    ·
                      refine ⟨3807780491978308562871163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077040655971078083828217 3807780491978308562871163)
                      ·
                        rfl

theorem cell23_7415626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_7415626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415626 prefixEnd_7415626 := by exact prefixLift 7415626
  have htrace : WordTrace (prefixWord ++ tailWord_7415626) baseStart_7415626 baseEnd_7415626 := by
    simpa [prefixWord, tailWord_7415626, baseEnd_7415626] using wordTrace_append hprefix tailTrace_7415626
  have hstable : (prefixWord ++ tailWord_7415626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415626).length < 2 ^ (prefixWord ++ tailWord_7415626).sum := by decide
  have hdescent : baseEnd_7415626 < baseStart_7415626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415629 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7415629 : Nat := 118140960795 + 7415629 * 2 ^ 59
def prefixEnd_7415629 : Nat := 4983230072969 + 3 ^ 40 * 7415629 * 2
def baseEnd_7415629 : Nat := 3807782032420272051133649

theorem tailTrace_7415629 : CollatzResearch.WordTrace tailWord_7415629 prefixEnd_7415629 3807782032420272051133649 := by
  unfold tailWord_7415629
  simp only [CollatzResearch.WordTrace]
  refine ⟨270470209651450096448001941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180313473100966730965334627 270470209651450096448001941)
  ·
    refine ⟨12678291077411723271000091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270470209651450096448001941 12678291077411723271000091)
    ·
      refine ⟨19017436616117584906500137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12678291077411723271000091 19017436616117584906500137)
      ·
        refine ⟨14263077462088188679875103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19017436616117584906500137 14263077462088188679875103)
        ·
          refine ⟨21394616193132283019812655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14263077462088188679875103 21394616193132283019812655)
          ·
            refine ⟨32091924289698424529718983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21394616193132283019812655 32091924289698424529718983)
            ·
              refine ⟨48137886434547636794578475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32091924289698424529718983 48137886434547636794578475)
              ·
                refine ⟨72206829651821455191867713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48137886434547636794578475 72206829651821455191867713)
                ·
                  refine ⟨54155122238866091393900785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72206829651821455191867713 54155122238866091393900785)
                  ·
                    refine ⟨40616341679149568545425589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54155122238866091393900785 40616341679149568545425589)
                    ·
                      refine ⟨3807782032420272051133649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40616341679149568545425589 3807782032420272051133649)
                      ·
                        rfl

theorem cell23_7415629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7415629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415629 prefixEnd_7415629 := by exact prefixLift 7415629
  have htrace : WordTrace (prefixWord ++ tailWord_7415629) baseStart_7415629 baseEnd_7415629 := by
    simpa [prefixWord, tailWord_7415629, baseEnd_7415629] using wordTrace_append hprefix tailTrace_7415629
  have hstable : (prefixWord ++ tailWord_7415629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415629).length < 2 ^ (prefixWord ++ tailWord_7415629).sum := by decide
  have hdescent : baseEnd_7415629 < baseStart_7415629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415642 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_7415642 : Nat := 118140960795 + 7415642 * 2 ^ 59
def prefixEnd_7415642 : Nat := 4983230072969 + 3 ^ 40 * 7415642 * 2
def baseEnd_7415642 : Nat := 3807788707668780500271089

theorem tailTrace_7415642 : CollatzResearch.WordTrace tailWord_7415642 prefixEnd_7415642 3807788707668780500271089 := by
  unfold tailWord_7415642
  simp only [CollatzResearch.WordTrace]
  refine ⟨67617670950100749917056295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180313789200268666445483453 67617670950100749917056295)
  ·
    refine ⟨101426506425151124875584443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67617670950100749917056295 101426506425151124875584443)
    ·
      refine ⟨152139759637726687313376665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101426506425151124875584443 152139759637726687313376665)
      ·
        refine ⟨114104819728295015485032499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152139759637726687313376665 114104819728295015485032499)
        ·
          refine ⟨171157229592442523227548749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114104819728295015485032499 171157229592442523227548749)
          ·
            refine ⟨64183961097165946210330781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171157229592442523227548749 64183961097165946210330781)
            ·
              refine ⟨24068985411437229828874043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64183961097165946210330781 24068985411437229828874043)
              ·
                refine ⟨36103478117155844743311065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24068985411437229828874043 36103478117155844743311065)
                ·
                  refine ⟨27077608587866883557483299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36103478117155844743311065 27077608587866883557483299)
                  ·
                    refine ⟨40616412881800325336224949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27077608587866883557483299 40616412881800325336224949)
                    ·
                      refine ⟨3807788707668780500271089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40616412881800325336224949 3807788707668780500271089)
                      ·
                        rfl

theorem cell23_7415642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_7415642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415642 prefixEnd_7415642 := by exact prefixLift 7415642
  have htrace : WordTrace (prefixWord ++ tailWord_7415642) baseStart_7415642 baseEnd_7415642 := by
    simpa [prefixWord, tailWord_7415642, baseEnd_7415642] using wordTrace_append hprefix tailTrace_7415642
  have hstable : (prefixWord ++ tailWord_7415642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415642).length < 2 ^ (prefixWord ++ tailWord_7415642).sum := by decide
  have hdescent : baseEnd_7415642 < baseStart_7415642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415656 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_7415656 : Nat := 118140960795 + 7415656 * 2 ^ 59
def prefixEnd_7415656 : Nat := 4983230072969 + 3 ^ 40 * 7415656 * 2
def baseEnd_7415656 : Nat := 3807795896397943445496025

theorem tailTrace_7415656 : CollatzResearch.WordTrace tailWord_7415656 prefixEnd_7415656 3807795896397943445496025 := by
  unfold tailWord_7415656
  simp only [CollatzResearch.WordTrace]
  refine ⟨135235597211176140029617411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180314129614901520039489881 135235597211176140029617411)
  ·
    refine ⟨202853395816764210044426117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135235597211176140029617411 202853395816764210044426117)
    ·
      refine ⟨38035011715643289383329897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202853395816764210044426117 38035011715643289383329897)
      ·
        refine ⟨28526258786732467037497423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38035011715643289383329897 28526258786732467037497423)
        ·
          refine ⟨42789388180098700556246135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28526258786732467037497423 42789388180098700556246135)
          ·
            refine ⟨64184082270148050834369203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42789388180098700556246135 64184082270148050834369203)
            ·
              refine ⟨96276123405222076251553805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64184082270148050834369203 96276123405222076251553805)
              ·
                refine ⟨36103546276958278594332677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96276123405222076251553805 36103546276958278594332677)
                ·
                  refine ⟨6769414926929677236437377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36103546276958278594332677 6769414926929677236437377)
                  ·
                    refine ⟨5077061195197257927328033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6769414926929677236437377 5077061195197257927328033)
                    ·
                      refine ⟨3807795896397943445496025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077061195197257927328033 3807795896397943445496025)
                      ·
                        rfl

theorem cell23_7415656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_7415656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415656 prefixEnd_7415656 := by exact prefixLift 7415656
  have htrace : WordTrace (prefixWord ++ tailWord_7415656) baseStart_7415656 baseEnd_7415656 := by
    simpa [prefixWord, tailWord_7415656, baseEnd_7415656] using wordTrace_append hprefix tailTrace_7415656
  have hstable : (prefixWord ++ tailWord_7415656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415656).length < 2 ^ (prefixWord ++ tailWord_7415656).sum := by decide
  have hdescent : baseEnd_7415656 < baseStart_7415656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415672 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_7415672 : Nat := 118140960795 + 7415672 * 2 ^ 59
def prefixEnd_7415672 : Nat := 4983230072969 + 3 ^ 40 * 7415672 * 2
def baseEnd_7415672 : Nat := 3807804112088415382895951

theorem tailTrace_7415672 : CollatzResearch.WordTrace tailWord_7415672 prefixEnd_7415672 3807804112088415382895951 := by
  unfold tailWord_7415672
  simp only [CollatzResearch.WordTrace]
  refine ⟨135235888995147157395908635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180314518660196209861211513 135235888995147157395908635)
  ·
    refine ⟨202853833492720736093862953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135235888995147157395908635 202853833492720736093862953)
    ·
      refine ⟨152140375119540552070397215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202853833492720736093862953 152140375119540552070397215)
      ·
        refine ⟨228210562679310828105595823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152140375119540552070397215 228210562679310828105595823)
        ·
          refine ⟨342315844018966242158393735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228210562679310828105595823 342315844018966242158393735)
          ·
            refine ⟨513473766028449363237590603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342315844018966242158393735 513473766028449363237590603)
            ·
              refine ⟨770210649042674044856385905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513473766028449363237590603 770210649042674044856385905)
              ·
                refine ⟨577657986782005533642289429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770210649042674044856385905 577657986782005533642289429)
                ·
                  refine ⟨27077718130406509389482317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 577657986782005533642289429 27077718130406509389482317)
                  ·
                    refine ⟨10154144298902441021055869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27077718130406509389482317 10154144298902441021055869)
                    ·
                      refine ⟨3807804112088415382895951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10154144298902441021055869 3807804112088415382895951)
                      ·
                        rfl

theorem cell23_7415672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_7415672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415672 prefixEnd_7415672 := by exact prefixLift 7415672
  have htrace : WordTrace (prefixWord ++ tailWord_7415672) baseStart_7415672 baseEnd_7415672 := by
    simpa [prefixWord, tailWord_7415672, baseEnd_7415672] using wordTrace_append hprefix tailTrace_7415672
  have hstable : (prefixWord ++ tailWord_7415672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415672).length < 2 ^ (prefixWord ++ tailWord_7415672).sum := by decide
  have hdescent : baseEnd_7415672 < baseStart_7415672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415709 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_7415709 : Nat := 118140960795 + 7415709 * 2 ^ 59
def prefixEnd_7415709 : Nat := 4983230072969 + 3 ^ 40 * 7415709 * 2
def baseEnd_7415709 : Nat := 1269274370290877246044427

theorem tailTrace_7415709 : CollatzResearch.WordTrace tailWord_7415709 prefixEnd_7415709 1269274370290877246044427 := by
  unfold tailWord_7415709
  simp only [CollatzResearch.WordTrace]
  refine ⟨270473127491160270110914181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180315418327440180073942787 270473127491160270110914181)
  ·
    refine ⟨50713711404592550645796409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270473127491160270110914181 50713711404592550645796409)
    ·
      refine ⟨38035283553444412984347307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50713711404592550645796409 38035283553444412984347307)
      ·
        refine ⟨57052925330166619476520961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38035283553444412984347307 57052925330166619476520961)
        ·
          refine ⟨42789693997624964607390721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57052925330166619476520961 42789693997624964607390721)
          ·
            refine ⟨32092270498218723455543041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42789693997624964607390721 32092270498218723455543041)
            ·
              refine ⟨24069202873664042591657281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32092270498218723455543041 24069202873664042591657281)
              ·
                refine ⟨18051902155248031943742961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24069202873664042591657281 18051902155248031943742961)
                ·
                  refine ⟨13538926616436023957807221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18051902155248031943742961 13538926616436023957807221)
                  ·
                    refine ⟨1269274370290877246044427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13538926616436023957807221 1269274370290877246044427)
                    ·
                      rfl

theorem cell23_7415709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_7415709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415709 prefixEnd_7415709 := by exact prefixLift 7415709
  have htrace : WordTrace (prefixWord ++ tailWord_7415709) baseStart_7415709 baseEnd_7415709 := by
    simpa [prefixWord, tailWord_7415709, baseEnd_7415709] using wordTrace_append hprefix tailTrace_7415709
  have hstable : (prefixWord ++ tailWord_7415709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415709).length < 2 ^ (prefixWord ++ tailWord_7415709).sum := by decide
  have hdescent : baseEnd_7415709 < baseStart_7415709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415712 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_7415712 : Nat := 118140960795 + 7415712 * 2 ^ 59
def prefixEnd_7415712 : Nat := 4983230072969 + 3 ^ 40 * 7415712 * 2
def baseEnd_7415712 : Nat := 3807824651314595226395767

theorem tailTrace_7415712 : CollatzResearch.WordTrace tailWord_7415712 prefixEnd_7415712 3807824651314595226395767 := by
  unfold tailWord_7415712
  simp only [CollatzResearch.WordTrace]
  refine ⟨135236618455074700811636695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180315491273432934415515593 135236618455074700811636695)
  ·
    refine ⟨202854927682612051217455043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135236618455074700811636695 202854927682612051217455043)
    ·
      refine ⟨304282391523918076826182565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202854927682612051217455043 304282391523918076826182565)
      ·
        refine ⟨57052948410734639404909231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304282391523918076826182565 57052948410734639404909231)
        ·
          refine ⟨85579422616101959107363847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57052948410734639404909231 85579422616101959107363847)
          ·
            refine ⟨128369133924152938661045771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85579422616101959107363847 128369133924152938661045771)
            ·
              refine ⟨192553700886229407991568657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128369133924152938661045771 192553700886229407991568657)
              ·
                refine ⟨144415275664672055993676493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192553700886229407991568657 144415275664672055993676493)
                ·
                  refine ⟨54155728374252020997628685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144415275664672055993676493 54155728374252020997628685)
                  ·
                    refine ⟨20308398140344507874110757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54155728374252020997628685 20308398140344507874110757)
                    ·
                      refine ⟨3807824651314595226395767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20308398140344507874110757 3807824651314595226395767)
                      ·
                        rfl

theorem cell23_7415712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_7415712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415712 prefixEnd_7415712 := by exact prefixLift 7415712
  have htrace : WordTrace (prefixWord ++ tailWord_7415712) baseStart_7415712 baseEnd_7415712 := by
    simpa [prefixWord, tailWord_7415712, baseEnd_7415712] using wordTrace_append hprefix tailTrace_7415712
  have hstable : (prefixWord ++ tailWord_7415712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415712).length < 2 ^ (prefixWord ++ tailWord_7415712).sum := by decide
  have hdescent : baseEnd_7415712 < baseStart_7415712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415719 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7415719 : Nat := 118140960795 + 7415719 * 2 ^ 59
def prefixEnd_7415719 : Nat := 4983230072969 + 3 ^ 40 * 7415719 * 2
def baseEnd_7415719 : Nat := 3807828245679176699008235

theorem tailTrace_7415719 : CollatzResearch.WordTrace tailWord_7415719 prefixEnd_7415719 3807828245679176699008235 := by
  unfold tailWord_7415719
  simp only [CollatzResearch.WordTrace]
  refine ⟨270473492221124041818778211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180315661480749361212518807 270473492221124041818778211)
  ·
    refine ⟨405710238331686062728167317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270473492221124041818778211 405710238331686062728167317)
    ·
      refine ⟨19017667421797784190382843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405710238331686062728167317 19017667421797784190382843)
      ·
        refine ⟨28526501132696676285574265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19017667421797784190382843 28526501132696676285574265)
        ·
          refine ⟨21394875849522507214180699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28526501132696676285574265 21394875849522507214180699)
          ·
            refine ⟨32092313774283760821271049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21394875849522507214180699 32092313774283760821271049)
            ·
              refine ⟨24069235330712820615953287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32092313774283760821271049 24069235330712820615953287)
              ·
                refine ⟨36103852996069230923929931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24069235330712820615953287 36103852996069230923929931)
                ·
                  refine ⟨54155779494103846385894897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36103852996069230923929931 54155779494103846385894897)
                  ·
                    refine ⟨40616834620577884789421173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54155779494103846385894897 40616834620577884789421173)
                    ·
                      refine ⟨3807828245679176699008235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40616834620577884789421173 3807828245679176699008235)
                      ·
                        rfl

theorem cell23_7415719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7415719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415719 prefixEnd_7415719 := by exact prefixLift 7415719
  have htrace : WordTrace (prefixWord ++ tailWord_7415719) baseStart_7415719 baseEnd_7415719 := by
    simpa [prefixWord, tailWord_7415719, baseEnd_7415719] using wordTrace_append hprefix tailTrace_7415719
  have hstable : (prefixWord ++ tailWord_7415719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415719).length < 2 ^ (prefixWord ++ tailWord_7415719).sum := by decide
  have hdescent : baseEnd_7415719 < baseStart_7415719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415749 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_7415749 : Nat := 118140960795 + 7415749 * 2 ^ 59
def prefixEnd_7415749 : Nat := 4983230072969 + 3 ^ 40 * 7415749 * 2
def baseEnd_7415749 : Nat := 3807843650098811581633097

theorem tailTrace_7415749 : CollatzResearch.WordTrace tailWord_7415749 prefixEnd_7415749 3807843650098811581633097 := by
  unfold tailWord_7415749
  simp only [CollatzResearch.WordTrace]
  refine ⟨270474586411015356942370301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180316390940676904628246867 270474586411015356942370301)
  ·
    refine ⟨101427969904130758853388863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270474586411015356942370301 101427969904130758853388863)
    ·
      refine ⟨152141954856196138280083295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101427969904130758853388863 152141954856196138280083295)
      ·
        refine ⟨228212932284294207420124943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152141954856196138280083295 228212932284294207420124943)
        ·
          refine ⟨342319398426441311130187415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228212932284294207420124943 342319398426441311130187415)
          ·
            refine ⟨513479097639661966695281123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342319398426441311130187415 513479097639661966695281123)
            ·
              refine ⟨770218646459492950042921685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513479097639661966695281123 770218646459492950042921685)
              ·
                refine ⟨18051999526394366016630977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 770218646459492950042921685 18051999526394366016630977)
                ·
                  refine ⟨13538999644795774512473233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18051999526394366016630977 13538999644795774512473233)
                  ·
                    refine ⟨10154249733596830884354925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13538999644795774512473233 10154249733596830884354925)
                    ·
                      refine ⟨3807843650098811581633097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10154249733596830884354925 3807843650098811581633097)
                      ·
                        rfl

theorem cell23_7415749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_7415749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415749 prefixEnd_7415749 := by exact prefixLift 7415749
  have htrace : WordTrace (prefixWord ++ tailWord_7415749) baseStart_7415749 baseEnd_7415749 := by
    simpa [prefixWord, tailWord_7415749, baseEnd_7415749] using wordTrace_append hprefix tailTrace_7415749
  have hstable : (prefixWord ++ tailWord_7415749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415749).length < 2 ^ (prefixWord ++ tailWord_7415749).sum := by decide
  have hdescent : baseEnd_7415749 < baseStart_7415749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415769 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 8]
def baseStart_7415769 : Nat := 118140960795 + 7415769 * 2 ^ 59
def prefixEnd_7415769 : Nat := 4983230072969 + 3 ^ 40 * 7415769 * 2
def baseEnd_7415769 : Nat := 423094879967989055931445

theorem tailTrace_7415769 : CollatzResearch.WordTrace tailWord_7415769 prefixEnd_7415769 423094879967989055931445 := by
  unfold tailWord_7415769
  simp only [CollatzResearch.WordTrace]
  refine ⟨270475315870942900358098361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180316877247295266905398907 270475315870942900358098361)
  ·
    refine ⟨202856486903207175268573771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270475315870942900358098361 202856486903207175268573771)
    ·
      refine ⟨304284730354810762902860657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202856486903207175268573771 304284730354810762902860657)
      ·
        refine ⟨228213547766108072177145493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304284730354810762902860657 228213547766108072177145493)
        ·
          refine ⟨10697510051536315883303695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228213547766108072177145493 10697510051536315883303695)
          ·
            refine ⟨16046265077304473824955543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10697510051536315883303695 16046265077304473824955543)
            ·
              refine ⟨24069397615956710737433315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16046265077304473824955543 24069397615956710737433315)
              ·
                refine ⟨36104096423935066106149973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24069397615956710737433315 36104096423935066106149973)
                ·
                  refine ⟨423094879967989055931445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36104096423935066106149973 423094879967989055931445)
                  ·
                    rfl

theorem cell23_7415769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_7415769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415769 prefixEnd_7415769 := by exact prefixLift 7415769
  have htrace : WordTrace (prefixWord ++ tailWord_7415769) baseStart_7415769 baseEnd_7415769 := by
    simpa [prefixWord, tailWord_7415769, baseEnd_7415769] using wordTrace_append hprefix tailTrace_7415769
  have hstable : (prefixWord ++ tailWord_7415769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415769).length < 2 ^ (prefixWord ++ tailWord_7415769).sum := by decide
  have hdescent : baseEnd_7415769 < baseStart_7415769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415773 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_7415773 : Nat := 118140960795 + 7415773 * 2 ^ 59
def prefixEnd_7415773 : Nat := 4983230072969 + 3 ^ 40 * 7415773 * 2
def baseEnd_7415773 : Nat := 1269285324544839829244329

theorem tailTrace_7415773 : CollatzResearch.WordTrace tailWord_7415773 prefixEnd_7415773 1269285324544839829244329 := by
  unfold tailWord_7415773
  simp only [CollatzResearch.WordTrace]
  refine ⟨270475461762928409041243973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180316974508618939360829315 270475461762928409041243973)
  ·
    refine ⟨50714149080549076695233245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270475461762928409041243973 50714149080549076695233245)
    ·
      refine ⟨19017805905205903760712467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50714149080549076695233245 19017805905205903760712467)
      ·
        refine ⟨28526708857808855641068701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19017805905205903760712467 28526708857808855641068701)
        ·
          refine ⟨10697515821678320865400763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28526708857808855641068701 10697515821678320865400763)
          ·
            refine ⟨16046273732517481298101145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10697515821678320865400763 16046273732517481298101145)
            ·
              refine ⟨12034705299388110973575859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16046273732517481298101145 12034705299388110973575859)
              ·
                refine ⟨18052057949082166460363789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12034705299388110973575859 18052057949082166460363789)
                ·
                  refine ⟨6769521730905812422636421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18052057949082166460363789 6769521730905812422636421)
                  ·
                    refine ⟨1269285324544839829244329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6769521730905812422636421 1269285324544839829244329)
                    ·
                      rfl

theorem cell23_7415773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_7415773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415773 prefixEnd_7415773 := by exact prefixLift 7415773
  have htrace : WordTrace (prefixWord ++ tailWord_7415773) baseStart_7415773 baseEnd_7415773 := by
    simpa [prefixWord, tailWord_7415773, baseEnd_7415773] using wordTrace_append hprefix tailTrace_7415773
  have hstable : (prefixWord ++ tailWord_7415773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415773).length < 2 ^ (prefixWord ++ tailWord_7415773).sum := by decide
  have hdescent : baseEnd_7415773 < baseStart_7415773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415786 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_7415786 : Nat := 118140960795 + 7415786 * 2 ^ 59
def prefixEnd_7415786 : Nat := 4983230072969 + 3 ^ 40 * 7415786 * 2
def baseEnd_7415786 : Nat := 423095849875891992985603

theorem tailTrace_7415786 : CollatzResearch.WordTrace tailWord_7415786 prefixEnd_7415786 423095849875891992985603 := by
  unfold tailWord_7415786
  simp only [CollatzResearch.WordTrace]
  refine ⟨67618983977970328065366803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180317290607920874840978141 67618983977970328065366803)
  ·
    refine ⟨101428475966955492098050205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67618983977970328065366803 101428475966955492098050205)
    ·
      refine ⟨38035678487608309536768827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101428475966955492098050205 38035678487608309536768827)
      ·
        refine ⟨57053517731412464305153241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38035678487608309536768827 57053517731412464305153241)
        ·
          refine ⟨42790138298559348228864931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57053517731412464305153241 42790138298559348228864931)
          ·
            refine ⟨64185207447839022343297397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42790138298559348228864931 64185207447839022343297397)
            ·
              refine ⟨6017363198234908344684131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64185207447839022343297397 6017363198234908344684131)
              ·
                refine ⟨9026044797352362517026197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017363198234908344684131 9026044797352362517026197)
                ·
                  refine ⟨423095849875891992985603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9026044797352362517026197 423095849875891992985603)
                  ·
                    rfl

theorem cell23_7415786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_7415786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415786 prefixEnd_7415786 := by exact prefixLift 7415786
  have htrace : WordTrace (prefixWord ++ tailWord_7415786) baseStart_7415786 baseEnd_7415786 := by
    simpa [prefixWord, tailWord_7415786, baseEnd_7415786] using wordTrace_append hprefix tailTrace_7415786
  have hstable : (prefixWord ++ tailWord_7415786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415786).length < 2 ^ (prefixWord ++ tailWord_7415786).sum := by decide
  have hdescent : baseEnd_7415786 < baseStart_7415786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415792 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_7415792 : Nat := 118140960795 + 7415792 * 2 ^ 59
def prefixEnd_7415792 : Nat := 4983230072969 + 3 ^ 40 * 7415792 * 2
def baseEnd_7415792 : Nat := 3807865729766954913395399

theorem tailTrace_7415792 : CollatzResearch.WordTrace tailWord_7415792 prefixEnd_7415792 3807865729766954913395399 := by
  unfold tailWord_7415792
  simp only [CollatzResearch.WordTrace]
  refine ⟨135238077374929787643092815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180317436499906383524123753 135238077374929787643092815)
  ·
    refine ⟨202857116062394681464639223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135238077374929787643092815 202857116062394681464639223)
    ·
      refine ⟨304285674093592022196958835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202857116062394681464639223 304285674093592022196958835)
      ·
        refine ⟨456428511140388033295438253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304285674093592022196958835 456428511140388033295438253)
        ·
          refine ⟨171160691677645512485789345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456428511140388033295438253 171160691677645512485789345)
          ·
            refine ⟨128370518758234134364342009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171160691677645512485789345 128370518758234134364342009)
            ·
              refine ⟨96277889068675600773256507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128370518758234134364342009 96277889068675600773256507)
              ·
                refine ⟨144416833603013401159884761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96277889068675600773256507 144416833603013401159884761)
                ·
                  refine ⟨108312625202260050869913571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144416833603013401159884761 108312625202260050869913571)
                  ·
                    refine ⟨162468937803390076304870357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108312625202260050869913571 162468937803390076304870357)
                    ·
                      refine ⟨3807865729766954913395399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162468937803390076304870357 3807865729766954913395399)
                      ·
                        rfl

theorem cell23_7415792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_7415792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415792 prefixEnd_7415792 := by exact prefixLift 7415792
  have htrace : WordTrace (prefixWord ++ tailWord_7415792) baseStart_7415792 baseEnd_7415792 := by
    simpa [prefixWord, tailWord_7415792, baseEnd_7415792] using wordTrace_append hprefix tailTrace_7415792
  have hstable : (prefixWord ++ tailWord_7415792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415792).length < 2 ^ (prefixWord ++ tailWord_7415792).sum := by decide
  have hdescent : baseEnd_7415792 < baseStart_7415792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415839 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_7415839 : Nat := 118140960795 + 7415839 * 2 ^ 59
def prefixEnd_7415839 : Nat := 4983230072969 + 3 ^ 40 * 7415839 * 2
def baseEnd_7415839 : Nat := 3807889863357716229507683

theorem tailTrace_7415839 : CollatzResearch.WordTrace tailWord_7415839 prefixEnd_7415839 3807889863357716229507683 := by
  unfold tailWord_7415839
  simp only [CollatzResearch.WordTrace]
  refine ⟨270477868980689302313146571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180318579320459534875431047 270477868980689302313146571)
  ·
    refine ⟨405716803471033953469719857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270477868980689302313146571 405716803471033953469719857)
    ·
      refine ⟨304287602603275465102289893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405716803471033953469719857 304287602603275465102289893)
      ·
        refine ⟨57053925488114149706679355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304287602603275465102289893 57053925488114149706679355)
        ·
          refine ⟨85580888232171224560019033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57053925488114149706679355 85580888232171224560019033)
          ·
            refine ⟨64185666174128418420014275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85580888232171224560019033 64185666174128418420014275)
            ·
              refine ⟨96278499261192627630021413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64185666174128418420014275 96278499261192627630021413)
              ·
                refine ⟨18052218611473617680629015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96278499261192627630021413 18052218611473617680629015)
                ·
                  refine ⟨27078327917210426520943523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18052218611473617680629015 27078327917210426520943523)
                  ·
                    refine ⟨40617491875815639781415285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27078327917210426520943523 40617491875815639781415285)
                    ·
                      refine ⟨3807889863357716229507683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40617491875815639781415285 3807889863357716229507683)
                      ·
                        rfl

theorem cell23_7415839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_7415839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415839 prefixEnd_7415839 := by exact prefixLift 7415839
  have htrace : WordTrace (prefixWord ++ tailWord_7415839) baseStart_7415839 baseEnd_7415839 := by
    simpa [prefixWord, tailWord_7415839, baseEnd_7415839] using wordTrace_append hprefix tailTrace_7415839
  have hstable : (prefixWord ++ tailWord_7415839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415839).length < 2 ^ (prefixWord ++ tailWord_7415839).sum := by decide
  have hdescent : baseEnd_7415839 < baseStart_7415839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415856 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_7415856 : Nat := 118140960795 + 7415856 * 2 ^ 59
def prefixEnd_7415856 : Nat := 4983230072969 + 3 ^ 40 * 7415856 * 2
def baseEnd_7415856 : Nat := 3807898592528842662995105

theorem tailTrace_7415856 : CollatzResearch.WordTrace tailWord_7415856 prefixEnd_7415856 3807898592528842662995105 := by
  unfold tailWord_7415856
  simp only [CollatzResearch.WordTrace]
  refine ⟨135239244510813857108257711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180318992681085142811010281 135239244510813857108257711)
  ·
    refine ⟨202858866766220785662386567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135239244510813857108257711 202858866766220785662386567)
    ·
      refine ⟨304288300149331178493579851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202858866766220785662386567 304288300149331178493579851)
      ·
        refine ⟨456432450223996767740369777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304288300149331178493579851 456432450223996767740369777)
        ·
          refine ⟨342324337667997575805277333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456432450223996767740369777 342324337667997575805277333)
          ·
            refine ⟨16046453328187386365872375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 342324337667997575805277333 16046453328187386365872375)
            ·
              refine ⟨24069679992281079548808563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16046453328187386365872375 24069679992281079548808563)
              ·
                refine ⟨36104519988421619323212845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24069679992281079548808563 36104519988421619323212845)
                ·
                  refine ⟨13539194995658107246204817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36104519988421619323212845 13539194995658107246204817)
                  ·
                    refine ⟨10154396246743580434653613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13539194995658107246204817 10154396246743580434653613)
                    ·
                      refine ⟨3807898592528842662995105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10154396246743580434653613 3807898592528842662995105)
                      ·
                        rfl

theorem cell23_7415856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_7415856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415856 prefixEnd_7415856 := by exact prefixLift 7415856
  have htrace : WordTrace (prefixWord ++ tailWord_7415856) baseStart_7415856 baseEnd_7415856 := by
    simpa [prefixWord, tailWord_7415856, baseEnd_7415856] using wordTrace_append hprefix tailTrace_7415856
  have hstable : (prefixWord ++ tailWord_7415856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415856).length < 2 ^ (prefixWord ++ tailWord_7415856).sum := by decide
  have hdescent : baseEnd_7415856 < baseStart_7415856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415873 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7415873 : Nat := 118140960795 + 7415873 * 2 ^ 59
def prefixEnd_7415873 : Nat := 4983230072969 + 3 ^ 40 * 7415873 * 2
def baseEnd_7415873 : Nat := 3807907321699969096482527

theorem tailTrace_7415873 : CollatzResearch.WordTrace tailWord_7415873 prefixEnd_7415873 3807907321699969096482527 := by
  unfold tailWord_7415873
  simp only [CollatzResearch.WordTrace]
  refine ⟨270479109062566126119884273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180319406041710750746589515 270479109062566126119884273)
  ·
    refine ⟨202859331796924594589913205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270479109062566126119884273 202859331796924594589913205)
    ·
      refine ⟨19018062355961680742804363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202859331796924594589913205 19018062355961680742804363)
      ·
        refine ⟨28527093533942521114206545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19018062355961680742804363 28527093533942521114206545)
        ·
          refine ⟨21395320150456890835654909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28527093533942521114206545 21395320150456890835654909)
          ·
            refine ⟨8023245056421334063370591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21395320150456890835654909 8023245056421334063370591)
            ·
              refine ⟨12034867584632001095055887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023245056421334063370591 12034867584632001095055887)
              ·
                refine ⟨18052301376948001642583831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12034867584632001095055887 18052301376948001642583831)
                ·
                  refine ⟨27078452065422002463875747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18052301376948001642583831 27078452065422002463875747)
                  ·
                    refine ⟨40617678098133003695813621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27078452065422002463875747 40617678098133003695813621)
                    ·
                      refine ⟨3807907321699969096482527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40617678098133003695813621 3807907321699969096482527)
                      ·
                        rfl

theorem cell23_7415873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7415873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415873 prefixEnd_7415873 := by exact prefixLift 7415873
  have htrace : WordTrace (prefixWord ++ tailWord_7415873) baseStart_7415873 baseEnd_7415873 := by
    simpa [prefixWord, tailWord_7415873, baseEnd_7415873] using wordTrace_append hprefix tailTrace_7415873
  have hstable : (prefixWord ++ tailWord_7415873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415873).length < 2 ^ (prefixWord ++ tailWord_7415873).sum := by decide
  have hdescent : baseEnd_7415873 < baseStart_7415873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415913 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 1, 3, 2]
def baseStart_7415913 : Nat := 118140960795 + 7415913 * 2 ^ 59
def prefixEnd_7415913 : Nat := 4983230072969 + 3 ^ 40 * 7415913 * 2
def baseEnd_7415913 : Nat := 3807927860926148939982343

theorem tailTrace_7415913 : CollatzResearch.WordTrace tailWord_7415913 prefixEnd_7415913 3807927860926148939982343 := by
  unfold tailWord_7415913
  simp only [CollatzResearch.WordTrace]
  refine ⟨270480567982421212951340393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180320378654947475300893595 270480567982421212951340393)
  ·
    refine ⟨202860425986815909713505295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270480567982421212951340393 202860425986815909713505295)
    ·
      refine ⟨304290638980223864570257943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202860425986815909713505295 304290638980223864570257943)
      ·
        refine ⟨456435958470335796855386915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304290638980223864570257943 456435958470335796855386915)
        ·
          refine ⟨684653937705503695283080373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456435958470335796855386915 684653937705503695283080373)
          ·
            refine ⟨64186306659890971432788785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 684653937705503695283080373 64186306659890971432788785)
            ·
              refine ⟨48139729994918228574591589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64186306659890971432788785 48139729994918228574591589)
              ·
                refine ⟨9026199374047167857735923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48139729994918228574591589 9026199374047167857735923)
                ·
                  refine ⟨13539299061070751786603885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026199374047167857735923 13539299061070751786603885)
                  ·
                    refine ⟨5077237147901531919976457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13539299061070751786603885 5077237147901531919976457)
                    ·
                      refine ⟨3807927860926148939982343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077237147901531919976457 3807927860926148939982343)
                      ·
                        rfl

theorem cell23_7415913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 3, 2].length) (baseStart_7415913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415913 prefixEnd_7415913 := by exact prefixLift 7415913
  have htrace : WordTrace (prefixWord ++ tailWord_7415913) baseStart_7415913 baseEnd_7415913 := by
    simpa [prefixWord, tailWord_7415913, baseEnd_7415913] using wordTrace_append hprefix tailTrace_7415913
  have hstable : (prefixWord ++ tailWord_7415913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415913).length < 2 ^ (prefixWord ++ tailWord_7415913).sum := by decide
  have hdescent : baseEnd_7415913 < baseStart_7415913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415937 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_7415937 : Nat := 118140960795 + 7415937 * 2 ^ 59
def prefixEnd_7415937 : Nat := 4983230072969 + 3 ^ 40 * 7415937 * 2
def baseEnd_7415937 : Nat := 3807940184461856846082233

theorem tailTrace_7415937 : CollatzResearch.WordTrace tailWord_7415937 prefixEnd_7415937 3807940184461856846082233 := by
  unfold tailWord_7415937
  simp only [CollatzResearch.WordTrace]
  refine ⟨270481443334334265050214065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180320962222889510033476043 270481443334334265050214065)
  ·
    refine ⟨202861082500750698787660549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270481443334334265050214065 202861082500750698787660549)
    ·
      refine ⟨38036452968890756022686353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202861082500750698787660549 38036452968890756022686353)
      ·
        refine ⟨28527339726668067017014765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38036452968890756022686353 28527339726668067017014765)
        ·
          refine ⟨10697752397500525131380537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28527339726668067017014765 10697752397500525131380537)
          ·
            refine ⟨8023314298125393848535403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10697752397500525131380537 8023314298125393848535403)
            ·
              refine ⟨12034971447188090772803105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023314298125393848535403 12034971447188090772803105)
              ·
                refine ⟨9026228585391068079602329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12034971447188090772803105 9026228585391068079602329)
                ·
                  refine ⟨6769671439043301059701747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9026228585391068079602329 6769671439043301059701747)
                  ·
                    refine ⟨10154507158564951589552621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6769671439043301059701747 10154507158564951589552621)
                    ·
                      refine ⟨3807940184461856846082233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10154507158564951589552621 3807940184461856846082233)
                      ·
                        rfl

theorem cell23_7415937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_7415937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415937 prefixEnd_7415937 := by exact prefixLift 7415937
  have htrace : WordTrace (prefixWord ++ tailWord_7415937) baseStart_7415937 baseEnd_7415937 := by
    simpa [prefixWord, tailWord_7415937, baseEnd_7415937] using wordTrace_append hprefix tailTrace_7415937
  have hstable : (prefixWord ++ tailWord_7415937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415937).length < 2 ^ (prefixWord ++ tailWord_7415937).sum := by decide
  have hdescent : baseEnd_7415937 < baseStart_7415937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416000 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 5]
def baseStart_7416000 : Nat := 118140960795 + 7416000 * 2 ^ 59
def prefixEnd_7416000 : Nat := 4983230072969 + 3 ^ 40 * 7416000 * 2
def baseEnd_7416000 : Nat := 423108059304787788843827

theorem tailTrace_7416000 : CollatzResearch.WordTrace tailWord_7416000 prefixEnd_7416000 423108059304787788843827 := by
  unfold tailWord_7416000
  simp only [CollatzResearch.WordTrace]
  refine ⟨135241870566553013404878727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180322494088737351206504969 135241870566553013404878727)
  ·
    refine ⟨202862805849829520107318091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135241870566553013404878727 202862805849829520107318091)
    ·
      refine ⟨304294208774744280160977137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202862805849829520107318091 304294208774744280160977137)
      ·
        refine ⟨228220656581058210120732853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304294208774744280160977137 228220656581058210120732853)
        ·
          refine ⟨21395686554474207198818705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228220656581058210120732853 21395686554474207198818705)
          ·
            refine ⟨16046764915855655399114029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21395686554474207198818705 16046764915855655399114029)
            ·
              refine ⟨6017536843445870774667761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16046764915855655399114029 6017536843445870774667761)
              ·
                refine ⟨4513152632584403081000821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6017536843445870774667761 4513152632584403081000821)
                ·
                  refine ⟨423108059304787788843827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4513152632584403081000821 423108059304787788843827)
                  ·
                    rfl

theorem cell23_7416000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 5].length) (baseStart_7416000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416000 prefixEnd_7416000 := by exact prefixLift 7416000
  have htrace : WordTrace (prefixWord ++ tailWord_7416000) baseStart_7416000 baseEnd_7416000 := by
    simpa [prefixWord, tailWord_7416000, baseEnd_7416000] using wordTrace_append hprefix tailTrace_7416000
  have hstable : (prefixWord ++ tailWord_7416000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416000).length < 2 ^ (prefixWord ++ tailWord_7416000).sum := by decide
  have hdescent : baseEnd_7416000 < baseStart_7416000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416009 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_7416009 : Nat := 118140960795 + 7416009 * 2 ^ 59
def prefixEnd_7416009 : Nat := 4983230072969 + 3 ^ 40 * 7416009 * 2
def baseEnd_7416009 : Nat := 1269325718356326854793967

theorem tailTrace_7416009 : CollatzResearch.WordTrace tailWord_7416009 prefixEnd_7416009 1269325718356326854793967 := by
  unfold tailWord_7416009
  simp only [CollatzResearch.WordTrace]
  refine ⟨270484069390073421346835081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180322712926715614231223387 270484069390073421346835081)
  ·
    refine ⟨202863052042555066010126311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270484069390073421346835081 202863052042555066010126311)
    ·
      refine ⟨304294578063832599015189467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202863052042555066010126311 304294578063832599015189467)
      ·
        refine ⟨456441867095748898522784201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304294578063832599015189467 456441867095748898522784201)
        ·
          refine ⟨342331400321811673892088151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456441867095748898522784201 342331400321811673892088151)
          ·
            refine ⟨513497100482717510838132227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342331400321811673892088151 513497100482717510838132227)
            ·
              refine ⟨770245650724076266257198341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513497100482717510838132227 770245650724076266257198341)
              ·
                refine ⟨144421059510764299923224689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770245650724076266257198341 144421059510764299923224689)
                ·
                  refine ⟨108315794633073224942418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144421059510764299923224689 108315794633073224942418517)
                  ·
                    refine ⟨1269325718356326854793967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108315794633073224942418517 1269325718356326854793967)
                    ·
                      rfl

theorem cell23_7416009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_7416009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416009 prefixEnd_7416009 := by exact prefixLift 7416009
  have htrace : WordTrace (prefixWord ++ tailWord_7416009) baseStart_7416009 baseEnd_7416009 := by
    simpa [prefixWord, tailWord_7416009, baseEnd_7416009] using wordTrace_append hprefix tailTrace_7416009
  have hstable : (prefixWord ++ tailWord_7416009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416009).length < 2 ^ (prefixWord ++ tailWord_7416009).sum := by decide
  have hdescent : baseEnd_7416009 < baseStart_7416009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416033 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_7416033 : Nat := 118140960795 + 7416033 * 2 ^ 59
def prefixEnd_7416033 : Nat := 4983230072969 + 3 ^ 40 * 7416033 * 2
def baseEnd_7416033 : Nat := 3807989478604688470481791

theorem tailTrace_7416033 : CollatzResearch.WordTrace tailWord_7416033 prefixEnd_7416033 3807989478604688470481791 := by
  unfold tailWord_7416033
  simp only [CollatzResearch.WordTrace]
  refine ⟨270484944741986473445708753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180323296494657648963805835 270484944741986473445708753)
  ·
    refine ⟨202863708556489855084281565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270484944741986473445708753 202863708556489855084281565)
    ·
      refine ⟨76073890708683695656605587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202863708556489855084281565 76073890708683695656605587)
      ·
        refine ⟨114110836063025543484908381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76073890708683695656605587 114110836063025543484908381)
        ·
          refine ⟨42791563523634578806840643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114110836063025543484908381 42791563523634578806840643)
          ·
            refine ⟨64187345285451868210260965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42791563523634578806840643 64187345285451868210260965)
            ·
              refine ⟨12035127241022225289423931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64187345285451868210260965 12035127241022225289423931)
              ·
                refine ⟨18052690861533337934135897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12035127241022225289423931 18052690861533337934135897)
                ·
                  refine ⟨13539518146150003450601923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18052690861533337934135897 13539518146150003450601923)
                  ·
                    refine ⟨20309277219225005175902885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13539518146150003450601923 20309277219225005175902885)
                    ·
                      refine ⟨3807989478604688470481791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20309277219225005175902885 3807989478604688470481791)
                      ·
                        rfl

theorem cell23_7416033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_7416033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416033 prefixEnd_7416033 := by exact prefixLift 7416033
  have htrace : WordTrace (prefixWord ++ tailWord_7416033) baseStart_7416033 baseEnd_7416033 := by
    simpa [prefixWord, tailWord_7416033, baseEnd_7416033] using wordTrace_append hprefix tailTrace_7416033
  have hstable : (prefixWord ++ tailWord_7416033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416033).length < 2 ^ (prefixWord ++ tailWord_7416033).sum := by decide
  have hdescent : baseEnd_7416033 < baseStart_7416033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416046 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7416046 : Nat := 118140960795 + 7416046 * 2 ^ 59
def prefixEnd_7416046 : Nat := 4983230072969 + 3 ^ 40 * 7416046 * 2
def baseEnd_7416046 : Nat := 3807996153853196919619231

theorem tailTrace_7416046 : CollatzResearch.WordTrace tailWord_7416046 prefixEnd_7416046 3807996153853196919619231 := by
  unfold tailWord_7416046
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810677361367422083241499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180323612593959584443954661 33810677361367422083241499)
  ·
    refine ⟨50716016042051133124862249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33810677361367422083241499 50716016042051133124862249)
    ·
      refine ⟨38037012031538349843646687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50716016042051133124862249 38037012031538349843646687)
      ·
        refine ⟨57055518047307524765470031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38037012031538349843646687 57055518047307524765470031)
        ·
          refine ⟨85583277070961287148205047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57055518047307524765470031 85583277070961287148205047)
          ·
            refine ⟨128374915606441930722307571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85583277070961287148205047 128374915606441930722307571)
            ·
              refine ⟨192562373409662896083461357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128374915606441930722307571 192562373409662896083461357)
              ·
                refine ⟨72210890028623586031298009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192562373409662896083461357 72210890028623586031298009)
                ·
                  refine ⟨54158167521467689523473507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72210890028623586031298009 54158167521467689523473507)
                  ·
                    refine ⟨81237251282201534285210261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54158167521467689523473507 81237251282201534285210261)
                    ·
                      refine ⟨3807996153853196919619231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81237251282201534285210261 3807996153853196919619231)
                      ·
                        rfl

theorem cell23_7416046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7416046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416046 prefixEnd_7416046 := by exact prefixLift 7416046
  have htrace : WordTrace (prefixWord ++ tailWord_7416046) baseStart_7416046 baseEnd_7416046 := by
    simpa [prefixWord, tailWord_7416046, baseEnd_7416046] using wordTrace_append hprefix tailTrace_7416046
  have hstable : (prefixWord ++ tailWord_7416046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416046).length < 2 ^ (prefixWord ++ tailWord_7416046).sum := by decide
  have hdescent : baseEnd_7416046 < baseStart_7416046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416094 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7416094 : Nat := 118140960795 + 7416094 * 2 ^ 59
def prefixEnd_7416094 : Nat := 4983230072969 + 3 ^ 40 * 7416094 * 2
def baseEnd_7416094 : Nat := 1269340266974870910606337

theorem tailTrace_7416094 : CollatzResearch.WordTrace tailWord_7416094 prefixEnd_7416094 1269340266974870910606337 := by
  unfold tailWord_7416094
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810896199345685107959917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180324779729843653909119557 33810896199345685107959917)
  ·
    refine ⟨12679086074754631915484969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33810896199345685107959917 12679086074754631915484969)
    ·
      refine ⟨9509314556065973936613727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12679086074754631915484969 9509314556065973936613727)
      ·
        refine ⟨14263971834098960904920591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509314556065973936613727 14263971834098960904920591)
        ·
          refine ⟨21395957751148441357380887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14263971834098960904920591 21395957751148441357380887)
          ·
            refine ⟨32093936626722662036071331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21395957751148441357380887 32093936626722662036071331)
            ·
              refine ⟨48140904940083993054106997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32093936626722662036071331 48140904940083993054106997)
              ·
                refine ⟨4513209838132874348822531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48140904940083993054106997 4513209838132874348822531)
                ·
                  refine ⟨6769814757199311523233797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513209838132874348822531 6769814757199311523233797)
                  ·
                    refine ⟨1269340266974870910606337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6769814757199311523233797 1269340266974870910606337)
                    ·
                      rfl

theorem cell23_7416094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7416094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416094 prefixEnd_7416094 := by exact prefixLift 7416094
  have htrace : WordTrace (prefixWord ++ tailWord_7416094) baseStart_7416094 baseEnd_7416094 := by
    simpa [prefixWord, tailWord_7416094, baseEnd_7416094] using wordTrace_append hprefix tailTrace_7416094
  have hstable : (prefixWord ++ tailWord_7416094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416094).length < 2 ^ (prefixWord ++ tailWord_7416094).sum := by decide
  have hdescent : baseEnd_7416094 < baseStart_7416094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416117 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_7416117 : Nat := 118140960795 + 7416117 * 2 ^ 59
def prefixEnd_7416117 : Nat := 4983230072969 + 3 ^ 40 * 7416117 * 2
def baseEnd_7416117 : Nat := 3808032610979666141831405

theorem tailTrace_7416117 : CollatzResearch.WordTrace tailWord_7416117 prefixEnd_7416117 3808032610979666141831405 := by
  unfold tailWord_7416117
  simp only [CollatzResearch.WordTrace]
  refine ⟨270488008473682155791766605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180325338982454770527844403 270488008473682155791766605)
  ·
    refine ⟨101433003177630808421912477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270488008473682155791766605 101433003177630808421912477)
    ·
      refine ⟨38037376191611553158217179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101433003177630808421912477 38037376191611553158217179)
      ·
        refine ⟨57056064287417329737325769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38037376191611553158217179 57056064287417329737325769)
        ·
          refine ⟨42792048215562997302994327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57056064287417329737325769 42792048215562997302994327)
          ·
            refine ⟨64188072323344495954491491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42792048215562997302994327 64188072323344495954491491)
            ·
              refine ⟨96282108485016743931737237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64188072323344495954491491 96282108485016743931737237)
              ·
                refine ⟨4513223835235159871800183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96282108485016743931737237 4513223835235159871800183)
                ·
                  refine ⟨6769835752852739807700275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513223835235159871800183 6769835752852739807700275)
                  ·
                    refine ⟨10154753629279109711550413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6769835752852739807700275 10154753629279109711550413)
                    ·
                      refine ⟨3808032610979666141831405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10154753629279109711550413 3808032610979666141831405)
                      ·
                        rfl

theorem cell23_7416117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_7416117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416117 prefixEnd_7416117 := by exact prefixLift 7416117
  have htrace : WordTrace (prefixWord ++ tailWord_7416117) baseStart_7416117 baseEnd_7416117 := by
    simpa [prefixWord, tailWord_7416117, baseEnd_7416117] using wordTrace_append hprefix tailTrace_7416117
  have hstable : (prefixWord ++ tailWord_7416117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416117).length < 2 ^ (prefixWord ++ tailWord_7416117).sum := by decide
  have hdescent : baseEnd_7416117 < baseStart_7416117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416140 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_7416140 : Nat := 118140960795 + 7416140 * 2 ^ 59
def prefixEnd_7416140 : Nat := 4983230072969 + 3 ^ 40 * 7416140 * 2
def baseEnd_7416140 : Nat := 3808044421034719551843799

theorem tailTrace_7416140 : CollatzResearch.WordTrace tailWord_7416140 prefixEnd_7416140 3808044421034719551843799 := by
  unfold tailWord_7416140
  simp only [CollatzResearch.WordTrace]
  refine ⟨135244423676299415359926937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180325898235065887146569249 135244423676299415359926937)
  ·
    refine ⟨101433317757224561519945203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135244423676299415359926937 101433317757224561519945203)
    ·
      refine ⟨152149976635836842279917805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101433317757224561519945203 152149976635836842279917805)
      ·
        refine ⟨57056241238438815854969177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152149976635836842279917805 57056241238438815854969177)
        ·
          refine ⟨42792180928829111891226883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57056241238438815854969177 42792180928829111891226883)
          ·
            refine ⟨64188271393243667836840325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42792180928829111891226883 64188271393243667836840325)
            ·
              refine ⟨12035300886233187719407561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64188271393243667836840325 12035300886233187719407561)
              ·
                refine ⟨9026475664674890789555671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12035300886233187719407561 9026475664674890789555671)
                ·
                  refine ⟨13539713497012336184333507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026475664674890789555671 13539713497012336184333507)
                  ·
                    refine ⟨20309570245518504276500261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13539713497012336184333507 20309570245518504276500261)
                    ·
                      refine ⟨3808044421034719551843799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20309570245518504276500261 3808044421034719551843799)
                      ·
                        rfl

theorem cell23_7416140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_7416140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416140 prefixEnd_7416140 := by exact prefixLift 7416140
  have htrace : WordTrace (prefixWord ++ tailWord_7416140) baseStart_7416140 baseEnd_7416140 := by
    simpa [prefixWord, tailWord_7416140, baseEnd_7416140] using wordTrace_append hprefix tailTrace_7416140
  have hstable : (prefixWord ++ tailWord_7416140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416140).length < 2 ^ (prefixWord ++ tailWord_7416140).sum := by decide
  have hdescent : baseEnd_7416140 < baseStart_7416140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416160 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_7416160 : Nat := 118140960795 + 7416160 * 2 ^ 59
def prefixEnd_7416160 : Nat := 4983230072969 + 3 ^ 40 * 7416160 * 2
def baseEnd_7416160 : Nat := 3808054690647809473593707

theorem tailTrace_7416160 : CollatzResearch.WordTrace tailWord_7416160 prefixEnd_7416160 3808054690647809473593707 := by
  unfold tailWord_7416160
  simp only [CollatzResearch.WordTrace]
  refine ⟨135244788406263187067790967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180326384541684249423721289 135244788406263187067790967)
  ·
    refine ⟨202867182609394780601686451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135244788406263187067790967 202867182609394780601686451)
    ·
      refine ⟨304300773914092170902529677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202867182609394780601686451 304300773914092170902529677)
      ·
        refine ⟨114112790217784564088448629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304300773914092170902529677 114112790217784564088448629)
        ·
          refine ⟨10698074082917302883292059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114112790217784564088448629 10698074082917302883292059)
          ·
            refine ⟨16047111124375954324938089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10698074082917302883292059 16047111124375954324938089)
            ·
              refine ⟨12035333343281965743703567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16047111124375954324938089 12035333343281965743703567)
              ·
                refine ⟨18053000014922948615555351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12035333343281965743703567 18053000014922948615555351)
                ·
                  refine ⟨27079500022384422923333027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18053000014922948615555351 27079500022384422923333027)
                  ·
                    refine ⟨40619250033576634384999541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27079500022384422923333027 40619250033576634384999541)
                    ·
                      refine ⟨3808054690647809473593707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40619250033576634384999541 3808054690647809473593707)
                      ·
                        rfl

theorem cell23_7416160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_7416160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416160 prefixEnd_7416160 := by exact prefixLift 7416160
  have htrace : WordTrace (prefixWord ++ tailWord_7416160) baseStart_7416160 baseEnd_7416160 := by
    simpa [prefixWord, tailWord_7416160, baseEnd_7416160] using wordTrace_append hprefix tailTrace_7416160
  have hstable : (prefixWord ++ tailWord_7416160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416160).length < 2 ^ (prefixWord ++ tailWord_7416160).sum := by decide
  have hdescent : baseEnd_7416160 < baseStart_7416160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416194 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_7416194 : Nat := 118140960795 + 7416194 * 2 ^ 59
def prefixEnd_7416194 : Nat := 4983230072969 + 3 ^ 40 * 7416194 * 2
def baseEnd_7416194 : Nat := 3808072148990062340568551

theorem tailTrace_7416194 : CollatzResearch.WordTrace tailWord_7416194 prefixEnd_7416194 3808072148990062340568551 := by
  unfold tailWord_7416194
  simp only [CollatzResearch.WordTrace]
  refine ⟨67622704223600799485579909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180327211262935465294879757 67622704223600799485579909)
  ·
    refine ⟨12679257041925149903546233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67622704223600799485579909 12679257041925149903546233)
    ·
      refine ⟨9509442781443862427659675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12679257041925149903546233 9509442781443862427659675)
      ·
        refine ⟨14264164172165793641489513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509442781443862427659675 14264164172165793641489513)
        ·
          refine ⟨10698123129124345231117135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14264164172165793641489513 10698123129124345231117135)
          ·
            refine ⟨16047184693686517846675703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10698123129124345231117135 16047184693686517846675703)
            ·
              refine ⟨24070777040529776770013555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16047184693686517846675703 24070777040529776770013555)
              ·
                refine ⟨36106165560794665155020333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24070777040529776770013555 36106165560794665155020333)
                ·
                  refine ⟨13539812085297999433132625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36106165560794665155020333 13539812085297999433132625)
                  ·
                    refine ⟨10154859063973499574849469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13539812085297999433132625 10154859063973499574849469)
                    ·
                      refine ⟨3808072148990062340568551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10154859063973499574849469 3808072148990062340568551)
                      ·
                        rfl

theorem cell23_7416194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_7416194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416194 prefixEnd_7416194 := by exact prefixLift 7416194
  have htrace : WordTrace (prefixWord ++ tailWord_7416194) baseStart_7416194 baseEnd_7416194 := by
    simpa [prefixWord, tailWord_7416194, baseEnd_7416194] using wordTrace_append hprefix tailTrace_7416194
  have hstable : (prefixWord ++ tailWord_7416194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416194).length < 2 ^ (prefixWord ++ tailWord_7416194).sum := by decide
  have hdescent : baseEnd_7416194 < baseStart_7416194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416214 : List Nat := [5, 3, 1, 2, 2, 10]
def baseStart_7416214 : Nat := 118140960795 + 7416214 * 2 ^ 59
def prefixEnd_7416214 : Nat := 4983230072969 + 3 ^ 40 * 7416214 * 2
def baseEnd_7416214 : Nat := 15671121064210503137113

theorem tailTrace_7416214 : CollatzResearch.WordTrace tailWord_7416214 prefixEnd_7416214 15671121064210503137113 := by
  unfold tailWord_7416214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16905721647145671334877981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180327697569553827572031797 16905721647145671334877981)
  ·
    refine ⟨6339645617679626750579243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16905721647145671334877981 6339645617679626750579243)
    ·
      refine ⟨9509468426519440125868865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6339645617679626750579243 9509468426519440125868865)
      ·
        refine ⟨7132101319889580094401649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9509468426519440125868865 7132101319889580094401649)
        ·
          refine ⟨5349075989917185070801237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7132101319889580094401649 5349075989917185070801237)
          ·
            refine ⟨15671121064210503137113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5349075989917185070801237 15671121064210503137113)
            ·
              rfl

theorem cell23_7416214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 10].length) (baseStart_7416214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416214 prefixEnd_7416214 := by exact prefixLift 7416214
  have htrace : WordTrace (prefixWord ++ tailWord_7416214) baseStart_7416214 baseEnd_7416214 := by
    simpa [prefixWord, tailWord_7416214, baseEnd_7416214] using wordTrace_append hprefix tailTrace_7416214
  have hstable : (prefixWord ++ tailWord_7416214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416214).length < 2 ^ (prefixWord ++ tailWord_7416214).sum := by decide
  have hdescent : baseEnd_7416214 < baseStart_7416214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416223 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 2, 6]
def baseStart_7416223 : Nat := 118140960795 + 7416223 * 2 ^ 59
def prefixEnd_7416223 : Nat := 4983230072969 + 3 ^ 40 * 7416223 * 2
def baseEnd_7416223 : Nat := 1269362346643014242368639

theorem tailTrace_7416223 : CollatzResearch.WordTrace tailWord_7416223 prefixEnd_7416223 1269362346643014242368639 := by
  unfold tailWord_7416223
  simp only [CollatzResearch.WordTrace]
  refine ⟨270491874611298135895125323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180327916407532090596750215 270491874611298135895125323)
  ·
    refine ⟨405737811916947203842687985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270491874611298135895125323 405737811916947203842687985)
    ·
      refine ⟨304303358937710402882015989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405737811916947203842687985 304303358937710402882015989)
      ·
        refine ⟨28528439900410350270188999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304303358937710402882015989 28528439900410350270188999)
        ·
          refine ⟨42792659850615525405283499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28528439900410350270188999 42792659850615525405283499)
          ·
            refine ⟨64188989775923288107925249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42792659850615525405283499 64188989775923288107925249)
            ·
              refine ⟨48141742331942466080943937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64188989775923288107925249 48141742331942466080943937)
              ·
                refine ⟨36106306748956849560707953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48141742331942466080943937 36106306748956849560707953)
                ·
                  refine ⟨27079730061717637170530965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36106306748956849560707953 27079730061717637170530965)
                  ·
                    refine ⟨1269362346643014242368639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27079730061717637170530965 1269362346643014242368639)
                    ·
                      rfl

theorem cell23_7416223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_7416223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416223 prefixEnd_7416223 := by exact prefixLift 7416223
  have htrace : WordTrace (prefixWord ++ tailWord_7416223) baseStart_7416223 baseEnd_7416223 := by
    simpa [prefixWord, tailWord_7416223, baseEnd_7416223] using wordTrace_append hprefix tailTrace_7416223
  have hstable : (prefixWord ++ tailWord_7416223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416223).length < 2 ^ (prefixWord ++ tailWord_7416223).sum := by decide
  have hdescent : baseEnd_7416223 < baseStart_7416223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416225 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7416225 : Nat := 118140960795 + 7416225 * 2 ^ 59
def prefixEnd_7416225 : Nat := 4983230072969 + 3 ^ 40 * 7416225 * 2
def baseEnd_7416225 : Nat := 3808088066890351719280909

theorem tailTrace_7416225 : CollatzResearch.WordTrace tailWord_7416225 prefixEnd_7416225 3808088066890351719280909 := by
  unfold tailWord_7416225
  simp only [CollatzResearch.WordTrace]
  refine ⟨270491947557290890236698129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180327965038193926824465419 270491947557290890236698129)
  ·
    refine ⟨202868960667968167677523597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270491947557290890236698129 202868960667968167677523597)
    ·
      refine ⟨76075860250488062879071349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202868960667968167677523597 76075860250488062879071349)
      ·
        refine ⟨7132111898483255894912939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76075860250488062879071349 7132111898483255894912939)
        ·
          refine ⟨10698167847724883842369409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7132111898483255894912939 10698167847724883842369409)
          ·
            refine ⟨8023625885793662881777057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10698167847724883842369409 8023625885793662881777057)
            ·
              refine ⟨6017719414345247161332793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8023625885793662881777057 6017719414345247161332793)
              ·
                refine ⟨4513289560758935370999595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6017719414345247161332793 4513289560758935370999595)
                ·
                  refine ⟨6769934341138403056499393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513289560758935370999595 6769934341138403056499393)
                  ·
                    refine ⟨5077450755853802292374545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6769934341138403056499393 5077450755853802292374545)
                    ·
                      refine ⟨3808088066890351719280909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077450755853802292374545 3808088066890351719280909)
                      ·
                        rfl

theorem cell23_7416225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7416225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416225 prefixEnd_7416225 := by exact prefixLift 7416225
  have htrace : WordTrace (prefixWord ++ tailWord_7416225) baseStart_7416225 baseEnd_7416225 := by
    simpa [prefixWord, tailWord_7416225, baseEnd_7416225] using wordTrace_append hprefix tailTrace_7416225
  have hstable : (prefixWord ++ tailWord_7416225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416225).length < 2 ^ (prefixWord ++ tailWord_7416225).sum := by decide
  have hdescent : baseEnd_7416225 < baseStart_7416225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416247 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 1, 4, 2]
def baseStart_7416247 : Nat := 118140960795 + 7416247 * 2 ^ 59
def prefixEnd_7416247 : Nat := 4983230072969 + 3 ^ 40 * 7416247 * 2
def baseEnd_7416247 : Nat := 3808099363464750633205807

theorem tailTrace_7416247 : CollatzResearch.WordTrace tailWord_7416247 prefixEnd_7416247 3808099363464750633205807 := by
  unfold tailWord_7416247
  simp only [CollatzResearch.WordTrace]
  refine ⟨270492749963211187993998995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180328499975474125329332663 270492749963211187993998995)
  ·
    refine ⟨405739124944816781990998493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270492749963211187993998995 405739124944816781990998493)
    ·
      refine ⟨152152171854306293246624435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405739124944816781990998493 152152171854306293246624435)
      ·
        refine ⟨228228257781459439869936653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152152171854306293246624435 228228257781459439869936653)
        ·
          refine ⟨85585596668047289951226245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228228257781459439869936653 85585596668047289951226245)
          ·
            refine ⟨16047299375258866865854921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85585596668047289951226245 16047299375258866865854921)
            ·
              refine ⟨12035474531444150149391191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16047299375258866865854921 12035474531444150149391191)
              ·
                refine ⟨18053211797166225224086787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12035474531444150149391191 18053211797166225224086787)
                ·
                  refine ⟨27079817695749337836130181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18053211797166225224086787 27079817695749337836130181)
                  ·
                    refine ⟨5077465817953000844274409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27079817695749337836130181 5077465817953000844274409)
                    ·
                      refine ⟨3808099363464750633205807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077465817953000844274409 3808099363464750633205807)
                      ·
                        rfl

theorem cell23_7416247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_7416247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416247 prefixEnd_7416247 := by exact prefixLift 7416247
  have htrace : WordTrace (prefixWord ++ tailWord_7416247) baseStart_7416247 baseEnd_7416247 := by
    simpa [prefixWord, tailWord_7416247, baseEnd_7416247] using wordTrace_append hprefix tailTrace_7416247
  have hstable : (prefixWord ++ tailWord_7416247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416247).length < 2 ^ (prefixWord ++ tailWord_7416247).sum := by decide
  have hdescent : baseEnd_7416247 < baseStart_7416247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416253 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 9]
def baseStart_7416253 : Nat := 118140960795 + 7416253 * 2 ^ 59
def prefixEnd_7416253 : Nat := 4983230072969 + 3 ^ 40 * 7416253 * 2
def baseEnd_7416253 : Nat := 423122493816519734414531

theorem tailTrace_7416253 : CollatzResearch.WordTrace tailWord_7416253 prefixEnd_7416253 423122493816519734414531 := by
  unfold tailWord_7416253
  simp only [CollatzResearch.WordTrace]
  refine ⟨270492968801189451018717413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180328645867459634012478275 270492968801189451018717413)
  ·
    refine ⟨50717431650223022066009515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270492968801189451018717413 50717431650223022066009515)
    ·
      refine ⟨76076147475334533099014273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50717431650223022066009515 76076147475334533099014273)
      ·
        refine ⟨57057110606500899824260705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76076147475334533099014273 57057110606500899824260705)
        ·
          refine ⟨42792832954875674868195529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57057110606500899824260705 42792832954875674868195529)
          ·
            refine ⟨32094624716156756151146647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42792832954875674868195529 32094624716156756151146647)
            ·
              refine ⟨48141937074235134226719971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32094624716156756151146647 48141937074235134226719971)
              ·
                refine ⟨72212905611352701340079957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48141937074235134226719971 72212905611352701340079957)
                ·
                  refine ⟨423122493816519734414531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72212905611352701340079957 423122493816519734414531)
                  ·
                    rfl

theorem cell23_7416253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_7416253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416253 prefixEnd_7416253 := by exact prefixLift 7416253
  have htrace : WordTrace (prefixWord ++ tailWord_7416253) baseStart_7416253 baseEnd_7416253 := by
    simpa [prefixWord, tailWord_7416253, baseEnd_7416253] using wordTrace_append hprefix tailTrace_7416253
  have hstable : (prefixWord ++ tailWord_7416253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416253).length < 2 ^ (prefixWord ++ tailWord_7416253).sum := by decide
  have hdescent : baseEnd_7416253 < baseStart_7416253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416268 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7416268 : Nat := 118140960795 + 7416268 * 2 ^ 59
def prefixEnd_7416268 : Nat := 4983230072969 + 3 ^ 40 * 7416268 * 2
def baseEnd_7416268 : Nat := 3808110146558495051043211

theorem tailTrace_7416268 : CollatzResearch.WordTrace tailWord_7416268 prefixEnd_7416268 3808110146558495051043211 := by
  unfold tailWord_7416268
  simp only [CollatzResearch.WordTrace]
  refine ⟨135246757948067554290256729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180329010597423405720342305 135246757948067554290256729)
  ·
    refine ⟨101435068461050665717692547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135246757948067554290256729 101435068461050665717692547)
    ·
      refine ⟨152152602691575998576538821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101435068461050665717692547 152152602691575998576538821)
      ·
        refine ⟨28528613004670499733101029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152152602691575998576538821 28528613004670499733101029)
        ·
          refine ⟨5349114938375718699956443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28528613004670499733101029 5349114938375718699956443)
          ·
            refine ⟨8023672407563578049934665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5349114938375718699956443 8023672407563578049934665)
            ·
              refine ⟨6017754305672683537450999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8023672407563578049934665 6017754305672683537450999)
              ·
                refine ⟨9026631458509025306176499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017754305672683537450999 9026631458509025306176499)
                ·
                  refine ⟨13539947187763537959264749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026631458509025306176499 13539947187763537959264749)
                  ·
                    refine ⟨5077480195411326734724281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13539947187763537959264749 5077480195411326734724281)
                    ·
                      refine ⟨3808110146558495051043211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077480195411326734724281 3808110146558495051043211)
                      ·
                        rfl

theorem cell23_7416268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7416268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416268 prefixEnd_7416268 := by exact prefixLift 7416268
  have htrace : WordTrace (prefixWord ++ tailWord_7416268) baseStart_7416268 baseEnd_7416268 := by
    simpa [prefixWord, tailWord_7416268, baseEnd_7416268] using wordTrace_append hprefix tailTrace_7416268
  have hstable : (prefixWord ++ tailWord_7416268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416268).length < 2 ^ (prefixWord ++ tailWord_7416268).sum := by decide
  have hdescent : baseEnd_7416268 < baseStart_7416268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416363 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_7416363 : Nat := 118140960795 + 7416363 * 2 ^ 59
def prefixEnd_7416363 : Nat := 4983230072969 + 3 ^ 40 * 7416363 * 2
def baseEnd_7416363 : Nat := 3808158927220672179355273

theorem tailTrace_7416363 : CollatzResearch.WordTrace tailWord_7416363 prefixEnd_7416363 3808158927220672179355273 := by
  unfold tailWord_7416363
  simp only [CollatzResearch.WordTrace]
  refine ⟨270496980830790939805221743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180331320553860626536814495 270496980830790939805221743)
  ·
    refine ⟨405745471246186409707832615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270496980830790939805221743 405745471246186409707832615)
    ·
      refine ⟨608618206869279614561748923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405745471246186409707832615 608618206869279614561748923)
      ·
        refine ⟨912927310303919421842623385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608618206869279614561748923 912927310303919421842623385)
        ·
          refine ⟨684695482727939566381967539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912927310303919421842623385 684695482727939566381967539)
          ·
            refine ⟨1027043224091909349572951309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684695482727939566381967539 1027043224091909349572951309)
            ·
              refine ⟨385141209034466006089856741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1027043224091909349572951309 385141209034466006089856741)
              ·
                refine ⟨72213976693962376141848139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385141209034466006089856741 72213976693962376141848139)
                ·
                  refine ⟨108320965040943564212772209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72213976693962376141848139 108320965040943564212772209)
                  ·
                    refine ⟨81240723780707673159579157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108320965040943564212772209 81240723780707673159579157)
                    ·
                      refine ⟨3808158927220672179355273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81240723780707673159579157 3808158927220672179355273)
                      ·
                        rfl

theorem cell23_7416363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_7416363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416363 prefixEnd_7416363 := by exact prefixLift 7416363
  have htrace : WordTrace (prefixWord ++ tailWord_7416363) baseStart_7416363 baseEnd_7416363 := by
    simpa [prefixWord, tailWord_7416363, baseEnd_7416363] using wordTrace_append hprefix tailTrace_7416363
  have hstable : (prefixWord ++ tailWord_7416363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416363).length < 2 ^ (prefixWord ++ tailWord_7416363).sum := by decide
  have hdescent : baseEnd_7416363 < baseStart_7416363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416370 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_7416370 : Nat := 118140960795 + 7416370 * 2 ^ 59
def prefixEnd_7416370 : Nat := 4983230072969 + 3 ^ 40 * 7416370 * 2
def baseEnd_7416370 : Nat := 3808162521585253651967741

theorem tailTrace_7416370 : CollatzResearch.WordTrace tailWord_7416370 prefixEnd_7416370 3808162521585253651967741 := by
  unfold tailWord_7416370
  simp only [CollatzResearch.WordTrace]
  refine ⟨67624309035441395000181641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180331490761177053333817709 67624309035441395000181641)
  ·
    refine ⟨50718231776581046250136231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67624309035441395000181641 50718231776581046250136231)
    ·
      refine ⟨76077347664871569375204347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50718231776581046250136231 76077347664871569375204347)
      ·
        refine ⟨114116021497307354062806521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76077347664871569375204347 114116021497307354062806521)
        ·
          refine ⟨85587016122980515547104891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114116021497307354062806521 85587016122980515547104891)
          ·
            refine ⟨128380524184470773320657337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85587016122980515547104891 128380524184470773320657337)
            ·
              refine ⟨96285393138353079990493003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128380524184470773320657337 96285393138353079990493003)
              ·
                refine ⟨144428089707529619985739505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96285393138353079990493003 144428089707529619985739505)
                ·
                  refine ⟨108321067280647214989304629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144428089707529619985739505 108321067280647214989304629)
                  ·
                    refine ⟨10155100057560676405247309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108321067280647214989304629 10155100057560676405247309)
                    ·
                      refine ⟨3808162521585253651967741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155100057560676405247309 3808162521585253651967741)
                      ·
                        rfl

theorem cell23_7416370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_7416370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416370 prefixEnd_7416370 := by exact prefixLift 7416370
  have htrace : WordTrace (prefixWord ++ tailWord_7416370) baseStart_7416370 baseEnd_7416370 := by
    simpa [prefixWord, tailWord_7416370, baseEnd_7416370] using wordTrace_append hprefix tailTrace_7416370
  have hstable : (prefixWord ++ tailWord_7416370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416370).length < 2 ^ (prefixWord ++ tailWord_7416370).sum := by decide
  have hdescent : baseEnd_7416370 < baseStart_7416370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416374 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7416374 : Nat := 118140960795 + 7416374 * 2 ^ 59
def prefixEnd_7416374 : Nat := 4983230072969 + 3 ^ 40 * 7416374 * 2
def baseEnd_7416374 : Nat := 3808164575507871636317723

theorem tailTrace_7416374 : CollatzResearch.WordTrace tailWord_7416374 prefixEnd_7416374 3808164575507871636317723 := by
  unfold tailWord_7416374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16906086377109443042742011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180331588022500725789248117 16906086377109443042742011)
  ·
    refine ⟨25359129565664164564113017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16906086377109443042742011 25359129565664164564113017)
    ·
      refine ⟨19019347174248123423084763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25359129565664164564113017 19019347174248123423084763)
      ·
        refine ⟨28529020761372185134627145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19019347174248123423084763 28529020761372185134627145)
        ·
          refine ⟨21396765571029138850970359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28529020761372185134627145 21396765571029138850970359)
          ·
            refine ⟨32095148356543708276455539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21396765571029138850970359 32095148356543708276455539)
            ·
              refine ⟨48142722534815562414683309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32095148356543708276455539 48142722534815562414683309)
              ·
                refine ⟨18053520950555835905506241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48142722534815562414683309 18053520950555835905506241)
                ·
                  refine ⟨13540140712916876929129681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18053520950555835905506241 13540140712916876929129681)
                  ·
                    refine ⟨10155105534687657696847261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13540140712916876929129681 10155105534687657696847261)
                    ·
                      refine ⟨3808164575507871636317723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155105534687657696847261 3808164575507871636317723)
                      ·
                        rfl

theorem cell23_7416374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7416374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416374 prefixEnd_7416374 := by exact prefixLift 7416374
  have htrace : WordTrace (prefixWord ++ tailWord_7416374) baseStart_7416374 baseEnd_7416374 := by
    simpa [prefixWord, tailWord_7416374, baseEnd_7416374] using wordTrace_append hprefix tailTrace_7416374
  have hstable : (prefixWord ++ tailWord_7416374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416374).length < 2 ^ (prefixWord ++ tailWord_7416374).sum := by decide
  have hdescent : baseEnd_7416374 < baseStart_7416374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416403 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 12]
def baseStart_7416403 : Nat := 118140960795 + 7416403 * 2 ^ 59
def prefixEnd_7416403 : Nat := 4983230072969 + 3 ^ 40 * 7416403 * 2
def baseEnd_7416403 : Nat := 1269393155482284007618363

theorem tailTrace_7416403 : CollatzResearch.WordTrace tailWord_7416403 prefixEnd_7416403 1269393155482284007618363 := by
  unfold tailWord_7416403
  simp only [CollatzResearch.WordTrace]
  refine ⟨270498439750646026636677863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180332293167097351091118575 270498439750646026636677863)
  ·
    refine ⟨405747659625969039955016795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270498439750646026636677863 405747659625969039955016795)
    ·
      refine ⟨608621489438953559932525193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405747659625969039955016795 608621489438953559932525193)
      ·
        refine ⟨456466117079215169949393895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608621489438953559932525193 456466117079215169949393895)
        ·
          refine ⟨684699175618822754924090843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456466117079215169949393895 684699175618822754924090843)
          ·
            refine ⟨1027048763428234132386136265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684699175618822754924090843 1027048763428234132386136265)
            ·
              refine ⟨770286572571175599289602199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027048763428234132386136265 770286572571175599289602199)
              ·
                refine ⟨1155429858856763398934403299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770286572571175599289602199 1155429858856763398934403299)
                ·
                  refine ⟨1733144788285145098401604949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155429858856763398934403299 1733144788285145098401604949)
                  ·
                    refine ⟨1269393155482284007618363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1733144788285145098401604949 1269393155482284007618363)
                    ·
                      rfl

theorem cell23_7416403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_7416403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416403 prefixEnd_7416403 := by exact prefixLift 7416403
  have htrace : WordTrace (prefixWord ++ tailWord_7416403) baseStart_7416403 baseEnd_7416403 := by
    simpa [prefixWord, tailWord_7416403, baseEnd_7416403] using wordTrace_append hprefix tailTrace_7416403
  have hstable : (prefixWord ++ tailWord_7416403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416403).length < 2 ^ (prefixWord ++ tailWord_7416403).sum := by decide
  have hdescent : baseEnd_7416403 < baseStart_7416403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416444 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_7416444 : Nat := 118140960795 + 7416444 * 2 ^ 59
def prefixEnd_7416444 : Nat := 4983230072969 + 3 ^ 40 * 7416444 * 2
def baseEnd_7416444 : Nat := 3808200519153686362442401

theorem tailTrace_7416444 : CollatzResearch.WordTrace tailWord_7416444 prefixEnd_7416444 3808200519153686362442401 := by
  unfold tailWord_7416444
  simp only [CollatzResearch.WordTrace]
  refine ⟨135249967571748745319460193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180333290095664993759280257 135249967571748745319460193)
  ·
    refine ⟨101437475678811558989595145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135249967571748745319460193 101437475678811558989595145)
    ·
      refine ⟨76078106759108669242196359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101437475678811558989595145 76078106759108669242196359)
      ·
        refine ⟨114117160138663003863294539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76078106759108669242196359 114117160138663003863294539)
        ·
          refine ⟨171175740207994505794941809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114117160138663003863294539 171175740207994505794941809)
          ·
            refine ⟨128381805155995879346206357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171175740207994505794941809 128381805155995879346206357)
            ·
              refine ⟨6017897116687306844353423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128381805155995879346206357 6017897116687306844353423)
              ·
                refine ⟨9026845675030960266530135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017897116687306844353423 9026845675030960266530135)
                ·
                  refine ⟨13540268512546440399795203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026845675030960266530135 13540268512546440399795203)
                  ·
                    refine ⟨20310402768819660599692805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13540268512546440399795203 20310402768819660599692805)
                    ·
                      refine ⟨3808200519153686362442401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20310402768819660599692805 3808200519153686362442401)
                      ·
                        rfl

theorem cell23_7416444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_7416444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416444 prefixEnd_7416444 := by exact prefixLift 7416444
  have htrace : WordTrace (prefixWord ++ tailWord_7416444) baseStart_7416444 baseEnd_7416444 := by
    simpa [prefixWord, tailWord_7416444, baseEnd_7416444] using wordTrace_append hprefix tailTrace_7416444
  have hstable : (prefixWord ++ tailWord_7416444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416444).length < 2 ^ (prefixWord ++ tailWord_7416444).sum := by decide
  have hdescent : baseEnd_7416444 < baseStart_7416444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416474 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7416474 : Nat := 118140960795 + 7416474 * 2 ^ 59
def prefixEnd_7416474 : Nat := 4983230072969 + 3 ^ 40 * 7416474 * 2
def baseEnd_7416474 : Nat := 3808215923573321245067263

theorem tailTrace_7416474 : CollatzResearch.WordTrace tailWord_7416474 prefixEnd_7416474 3808215923573321245067263 := by
  unfold tailWord_7416474
  simp only [CollatzResearch.WordTrace]
  refine ⟨67625257333347201440628119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180334019555592537175008317 67625257333347201440628119)
  ·
    refine ⟨101437886000020802160942179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67625257333347201440628119 101437886000020802160942179)
    ·
      refine ⟨152156829000031203241413269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101437886000020802160942179 152156829000031203241413269)
      ·
        refine ⟨7132351359376462651941247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152156829000031203241413269 7132351359376462651941247)
        ·
          refine ⟨10698527039064693977911871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7132351359376462651941247 10698527039064693977911871)
          ·
            refine ⟨16047790558597040966867807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10698527039064693977911871 16047790558597040966867807)
            ·
              refine ⟨24071685837895561450301711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16047790558597040966867807 24071685837895561450301711)
              ·
                refine ⟨36107528756843342175452567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24071685837895561450301711 36107528756843342175452567)
                ·
                  refine ⟨54161293135265013263178851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36107528756843342175452567 54161293135265013263178851)
                  ·
                    refine ⟨81241939702897519894768277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54161293135265013263178851 81241939702897519894768277)
                    ·
                      refine ⟨3808215923573321245067263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81241939702897519894768277 3808215923573321245067263)
                      ·
                        rfl

theorem cell23_7416474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7416474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416474 prefixEnd_7416474 := by exact prefixLift 7416474
  have htrace : WordTrace (prefixWord ++ tailWord_7416474) baseStart_7416474 baseEnd_7416474 := by
    simpa [prefixWord, tailWord_7416474, baseEnd_7416474] using wordTrace_append hprefix tailTrace_7416474
  have hstable : (prefixWord ++ tailWord_7416474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416474).length < 2 ^ (prefixWord ++ tailWord_7416474).sum := by decide
  have hdescent : baseEnd_7416474 < baseStart_7416474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416481 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_7416481 : Nat := 118140960795 + 7416481 * 2 ^ 59
def prefixEnd_7416481 : Nat := 4983230072969 + 3 ^ 40 * 7416481 * 2
def baseEnd_7416481 : Nat := 3808219517937902717679731

theorem tailTrace_7416481 : CollatzResearch.WordTrace tailWord_7416481 prefixEnd_7416481 3808219517937902717679731 := by
  unfold tailWord_7416481
  simp only [CollatzResearch.WordTrace]
  refine ⟨270501284644363445958017297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180334189762908963972011531 270501284644363445958017297)
  ·
    refine ⟨202875963483272584468512973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270501284644363445958017297 202875963483272584468512973)
    ·
      refine ⟨76078486306227219175692365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202875963483272584468512973 76078486306227219175692365)
      ·
        refine ⟨28529432364835207190884637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76078486306227219175692365 28529432364835207190884637)
        ·
          refine ⟨10698537136813202696581739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28529432364835207190884637 10698537136813202696581739)
          ·
            refine ⟨16047805705219804044872609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10698537136813202696581739 16047805705219804044872609)
            ·
              refine ⟨12035854278914853033654457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16047805705219804044872609 12035854278914853033654457)
              ·
                refine ⟨9026890709186139775240843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12035854278914853033654457 9026890709186139775240843)
                ·
                  refine ⟨13540336063779209662861265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026890709186139775240843 13540336063779209662861265)
                  ·
                    refine ⟨10155252047834407247145949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13540336063779209662861265 10155252047834407247145949)
                    ·
                      refine ⟨3808219517937902717679731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155252047834407247145949 3808219517937902717679731)
                      ·
                        rfl

theorem cell23_7416481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_7416481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416481 prefixEnd_7416481 := by exact prefixLift 7416481
  have htrace : WordTrace (prefixWord ++ tailWord_7416481) baseStart_7416481 baseEnd_7416481 := by
    simpa [prefixWord, tailWord_7416481, baseEnd_7416481] using wordTrace_append hprefix tailTrace_7416481
  have hstable : (prefixWord ++ tailWord_7416481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416481).length < 2 ^ (prefixWord ++ tailWord_7416481).sum := by decide
  have hdescent : baseEnd_7416481 < baseStart_7416481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416517 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 8, 2]
def baseStart_7416517 : Nat := 118140960795 + 7416517 * 2 ^ 59
def prefixEnd_7416517 : Nat := 4983230072969 + 3 ^ 40 * 7416517 * 2
def baseEnd_7416517 : Nat := 3808238003241464576829565

theorem tailTrace_7416517 : CollatzResearch.WordTrace tailWord_7416517 prefixEnd_7416517 3808238003241464576829565 := by
  unfold tailWord_7416517
  simp only [CollatzResearch.WordTrace]
  refine ⟨270502597672233024106327805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180335065114822016070885203 270502597672233024106327805)
  ·
    refine ⟨101438474127087384039872927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270502597672233024106327805 101438474127087384039872927)
    ·
      refine ⟨152157711190631076059809391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101438474127087384039872927 152157711190631076059809391)
      ·
        refine ⟨228236566785946614089714087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152157711190631076059809391 228236566785946614089714087)
        ·
          refine ⟨342354850178919921134571131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228236566785946614089714087 342354850178919921134571131)
          ·
            refine ⟨513532275268379881701856697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342354850178919921134571131 513532275268379881701856697)
            ·
              refine ⟨385149206451284911276392523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513532275268379881701856697 385149206451284911276392523)
              ·
                refine ⟨577723809676927366914588785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385149206451284911276392523 577723809676927366914588785)
                ·
                  refine ⟨433292857257695525185941589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577723809676927366914588785 433292857257695525185941589)
                  ·
                    refine ⟨5077650670988619435772753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 433292857257695525185941589 5077650670988619435772753)
                    ·
                      refine ⟨3808238003241464576829565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077650670988619435772753 3808238003241464576829565)
                      ·
                        rfl

theorem cell23_7416517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_7416517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416517 prefixEnd_7416517 := by exact prefixLift 7416517
  have htrace : WordTrace (prefixWord ++ tailWord_7416517) baseStart_7416517 baseEnd_7416517 := by
    simpa [prefixWord, tailWord_7416517, baseEnd_7416517] using wordTrace_append hprefix tailTrace_7416517
  have hstable : (prefixWord ++ tailWord_7416517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416517).length < 2 ^ (prefixWord ++ tailWord_7416517).sum := by decide
  have hdescent : baseEnd_7416517 < baseStart_7416517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416567 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_7416567 : Nat := 118140960795 + 7416567 * 2 ^ 59
def prefixEnd_7416567 : Nat := 4983230072969 + 3 ^ 40 * 7416567 * 2
def baseEnd_7416567 : Nat := 3808263677274189381204335

theorem tailTrace_7416567 : CollatzResearch.WordTrace tailWord_7416567 prefixEnd_7416567 3808263677274189381204335 := by
  unfold tailWord_7416567
  simp only [CollatzResearch.WordTrace]
  refine ⟨270504421322051882645647955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180336280881367921763765303 270504421322051882645647955)
  ·
    refine ⟨405756631983077823968471933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270504421322051882645647955 405756631983077823968471933)
    ·
      refine ⟨152158736993654183988176975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405756631983077823968471933 152158736993654183988176975)
      ·
        refine ⟨228238105490481275982265463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152158736993654183988176975 228238105490481275982265463)
        ·
          refine ⟨342357158235721913973398195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228238105490481275982265463 342357158235721913973398195)
          ·
            refine ⟨513535737353582870960097293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342357158235721913973398195 513535737353582870960097293)
            ·
              refine ⟨192575901507593576610036485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513535737353582870960097293 192575901507593576610036485)
              ·
                refine ⟨36107981532673795614381841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192575901507593576610036485 36107981532673795614381841)
                ·
                  refine ⟨27080986149505346710786381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36107981532673795614381841 27080986149505346710786381)
                  ·
                    refine ⟨10155369806064505016544893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27080986149505346710786381 10155369806064505016544893)
                    ·
                      refine ⟨3808263677274189381204335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155369806064505016544893 3808263677274189381204335)
                      ·
                        rfl

theorem cell23_7416567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_7416567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416567 prefixEnd_7416567 := by exact prefixLift 7416567
  have htrace : WordTrace (prefixWord ++ tailWord_7416567) baseStart_7416567 baseEnd_7416567 := by
    simpa [prefixWord, tailWord_7416567, baseEnd_7416567] using wordTrace_append hprefix tailTrace_7416567
  have hstable : (prefixWord ++ tailWord_7416567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416567).length < 2 ^ (prefixWord ++ tailWord_7416567).sum := by decide
  have hdescent : baseEnd_7416567 < baseStart_7416567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416584 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_7416584 : Nat := 118140960795 + 7416584 * 2 ^ 59
def prefixEnd_7416584 : Nat := 4983230072969 + 3 ^ 40 * 7416584 * 2
def baseEnd_7416584 : Nat := 3808272406445315814691757

theorem tailTrace_7416584 : CollatzResearch.WordTrace tailWord_7416584 prefixEnd_7416584 3808272406445315814691757 := by
  unfold tailWord_7416584
  simp only [CollatzResearch.WordTrace]
  refine ⟨135252520681495147274508403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180336694241993529699344537 135252520681495147274508403)
  ·
    refine ⟨202878781022242720911762605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135252520681495147274508403 202878781022242720911762605)
    ·
      refine ⟨76079542883341020341910977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202878781022242720911762605 76079542883341020341910977)
      ·
        refine ⟨57059657162505765256433233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76079542883341020341910977 57059657162505765256433233)
        ·
          refine ⟨42794742871879323942324925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57059657162505765256433233 42794742871879323942324925)
          ·
            refine ⟨16048028576954746478371847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42794742871879323942324925 16048028576954746478371847)
            ·
              refine ⟨24072042865432119717557771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16048028576954746478371847 24072042865432119717557771)
              ·
                refine ⟨36108064298148179576336657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24072042865432119717557771 36108064298148179576336657)
                ·
                  refine ⟨27081048223611134682252493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36108064298148179576336657 27081048223611134682252493)
                  ·
                    refine ⟨10155393083854175505844685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27081048223611134682252493 10155393083854175505844685)
                    ·
                      refine ⟨3808272406445315814691757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155393083854175505844685 3808272406445315814691757)
                      ·
                        rfl

theorem cell23_7416584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_7416584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416584 prefixEnd_7416584 := by exact prefixLift 7416584
  have htrace : WordTrace (prefixWord ++ tailWord_7416584) baseStart_7416584 baseEnd_7416584 := by
    simpa [prefixWord, tailWord_7416584, baseEnd_7416584] using wordTrace_append hprefix tailTrace_7416584
  have hstable : (prefixWord ++ tailWord_7416584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416584).length < 2 ^ (prefixWord ++ tailWord_7416584).sum := by decide
  have hdescent : baseEnd_7416584 < baseStart_7416584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416604 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_7416604 : Nat := 118140960795 + 7416604 * 2 ^ 59
def prefixEnd_7416604 : Nat := 4983230072969 + 3 ^ 40 * 7416604 * 2
def baseEnd_7416604 : Nat := 1269427558686135245480555

theorem tailTrace_7416604 : CollatzResearch.WordTrace tailWord_7416604 prefixEnd_7416604 1269427558686135245480555 := by
  unfold tailWord_7416604
  simp only [CollatzResearch.WordTrace]
  refine ⟨135252885411458918982372433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180337180548611891976496577 135252885411458918982372433)
  ·
    refine ⟨101439664058594189236779325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135252885411458918982372433 101439664058594189236779325)
    ·
      refine ⟨38039874021972820963792247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101439664058594189236779325 38039874021972820963792247)
      ·
        refine ⟨57059811032959231445688371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38039874021972820963792247 57059811032959231445688371)
        ·
          refine ⟨85589716549438847168532557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57059811032959231445688371 85589716549438847168532557)
          ·
            refine ⟨32096143706039567688199709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85589716549438847168532557 32096143706039567688199709)
            ·
              refine ⟨12036053889764837883074891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32096143706039567688199709 12036053889764837883074891)
              ·
                refine ⟨18054080834647256824612337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12036053889764837883074891 18054080834647256824612337)
                ·
                  refine ⟨13540560625985442618459253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18054080834647256824612337 13540560625985442618459253)
                  ·
                    refine ⟨1269427558686135245480555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13540560625985442618459253 1269427558686135245480555)
                    ·
                      rfl

theorem cell23_7416604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_7416604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416604 prefixEnd_7416604 := by exact prefixLift 7416604
  have htrace : WordTrace (prefixWord ++ tailWord_7416604) baseStart_7416604 baseEnd_7416604 := by
    simpa [prefixWord, tailWord_7416604, baseEnd_7416604] using wordTrace_append hprefix tailTrace_7416604
  have hstable : (prefixWord ++ tailWord_7416604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416604).length < 2 ^ (prefixWord ++ tailWord_7416604).sum := by decide
  have hdescent : baseEnd_7416604 < baseStart_7416604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416691 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 3]
def baseStart_7416691 : Nat := 118140960795 + 7416691 * 2 ^ 59
def prefixEnd_7416691 : Nat := 4983230072969 + 3 ^ 40 * 7416691 * 2
def baseEnd_7416691 : Nat := 3808327348875346896053765

theorem tailTrace_7416691 : CollatzResearch.WordTrace tailWord_7416691 prefixEnd_7416691 3808327348875346896053765 := by
  unfold tailWord_7416691
  simp only [CollatzResearch.WordTrace]
  refine ⟨270508943973602651823161927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180339295982401767882107951 270508943973602651823161927)
  ·
    refine ⟨405763415960403977734742891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270508943973602651823161927 405763415960403977734742891)
    ·
      refine ⟨608645123940605966602114337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405763415960403977734742891 608645123940605966602114337)
      ·
        refine ⟨456483842955454474951585753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608645123940605966602114337 456483842955454474951585753)
        ·
          refine ⟨342362882216590856213689315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456483842955454474951585753 342362882216590856213689315)
          ·
            refine ⟨513544323324886284320533973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342362882216590856213689315 513544323324886284320533973)
            ·
              refine ⟨12036195077927022288762515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 513544323324886284320533973 12036195077927022288762515)
              ·
                refine ⟨18054292616890533433143773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12036195077927022288762515 18054292616890533433143773)
                ·
                  refine ⟨6770359731333950037428915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18054292616890533433143773 6770359731333950037428915)
                  ·
                    refine ⟨10155539597000925056143373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6770359731333950037428915 10155539597000925056143373)
                    ·
                      refine ⟨3808327348875346896053765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155539597000925056143373 3808327348875346896053765)
                      ·
                        rfl

theorem cell23_7416691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_7416691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416691 prefixEnd_7416691 := by exact prefixLift 7416691
  have htrace : WordTrace (prefixWord ++ tailWord_7416691) baseStart_7416691 baseEnd_7416691 := by
    simpa [prefixWord, tailWord_7416691, baseEnd_7416691] using wordTrace_append hprefix tailTrace_7416691
  have hstable : (prefixWord ++ tailWord_7416691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416691).length < 2 ^ (prefixWord ++ tailWord_7416691).sum := by decide
  have hdescent : baseEnd_7416691 < baseStart_7416691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416711 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 1, 5]
def baseStart_7416711 : Nat := 118140960795 + 7416711 * 2 ^ 59
def prefixEnd_7416711 : Nat := 4983230072969 + 3 ^ 40 * 7416711 * 2
def baseEnd_7416711 : Nat := 1269445872829478939267891

theorem tailTrace_7416711 : CollatzResearch.WordTrace tailWord_7416711 prefixEnd_7416711 1269445872829478939267891 := by
  unfold tailWord_7416711
  simp only [CollatzResearch.WordTrace]
  refine ⟨270509673433530195238889987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180339782289020130159259991 270509673433530195238889987)
  ·
    refine ⟨405764510150295292858334981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270509673433530195238889987 405764510150295292858334981)
    ·
      refine ⟨76080845653180367410937809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405764510150295292858334981 76080845653180367410937809)
      ·
        refine ⟨57060634239885275558203357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76080845653180367410937809 57060634239885275558203357)
        ·
          refine ⟨21397737839956978334326259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57060634239885275558203357 21397737839956978334326259)
          ·
            refine ⟨32096606759935467501489389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21397737839956978334326259 32096606759935467501489389)
            ·
              refine ⟨12036227534975800313058521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32096606759935467501489389 12036227534975800313058521)
              ·
                refine ⟨9027170651231850234793891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12036227534975800313058521 9027170651231850234793891)
                ·
                  refine ⟨13540755976847775352190837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9027170651231850234793891 13540755976847775352190837)
                  ·
                    refine ⟨1269445872829478939267891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13540755976847775352190837 1269445872829478939267891)
                    ·
                      rfl

theorem cell23_7416711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_7416711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416711 prefixEnd_7416711 := by exact prefixLift 7416711
  have htrace : WordTrace (prefixWord ++ tailWord_7416711) baseStart_7416711 baseEnd_7416711 := by
    simpa [prefixWord, tailWord_7416711, baseEnd_7416711] using wordTrace_append hprefix tailTrace_7416711
  have hstable : (prefixWord ++ tailWord_7416711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416711).length < 2 ^ (prefixWord ++ tailWord_7416711).sum := by decide
  have hdescent : baseEnd_7416711 < baseStart_7416711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416761 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7416761 : Nat := 118140960795 + 7416761 * 2 ^ 59
def prefixEnd_7416761 : Nat := 4983230072969 + 3 ^ 40 * 7416761 * 2
def baseEnd_7416761 : Nat := 3808363292521161622178443

theorem tailTrace_7416761 : CollatzResearch.WordTrace tailWord_7416761 prefixEnd_7416761 3808363292521161622178443 := by
  unfold tailWord_7416761
  simp only [CollatzResearch.WordTrace]
  refine ⟨270511497083349053778210137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180340998055566035852140091 270511497083349053778210137)
  ·
    refine ⟨202883622812511790333657603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270511497083349053778210137 202883622812511790333657603)
    ·
      refine ⟨304325434218767685500486405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202883622812511790333657603 304325434218767685500486405)
      ·
        refine ⟨57061018916018941031341201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304325434218767685500486405 57061018916018941031341201)
        ·
          refine ⟨42795764187014205773505901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57061018916018941031341201 42795764187014205773505901)
          ·
            refine ⟨16048411570130327165064713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42795764187014205773505901 16048411570130327165064713)
            ·
              refine ⟨12036308677597745373798535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16048411570130327165064713 12036308677597745373798535)
              ·
                refine ⟨18054463016396618060697803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12036308677597745373798535 18054463016396618060697803)
                ·
                  refine ⟨27081694524594927091046705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18054463016396618060697803 27081694524594927091046705)
                  ·
                    refine ⟨20311270893446195318285029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27081694524594927091046705 20311270893446195318285029)
                    ·
                      refine ⟨3808363292521161622178443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20311270893446195318285029 3808363292521161622178443)
                      ·
                        rfl

theorem cell23_7416761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7416761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416761 prefixEnd_7416761 := by exact prefixLift 7416761
  have htrace : WordTrace (prefixWord ++ tailWord_7416761) baseStart_7416761 baseEnd_7416761 := by
    simpa [prefixWord, tailWord_7416761, baseEnd_7416761] using wordTrace_append hprefix tailTrace_7416761
  have hstable : (prefixWord ++ tailWord_7416761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416761).length < 2 ^ (prefixWord ++ tailWord_7416761).sum := by decide
  have hdescent : baseEnd_7416761 < baseStart_7416761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416765 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_7416765 : Nat := 118140960795 + 7416765 * 2 ^ 59
def prefixEnd_7416765 : Nat := 4983230072969 + 3 ^ 40 * 7416765 * 2
def baseEnd_7416765 : Nat := 3808365346443779606528425

theorem tailTrace_7416765 : CollatzResearch.WordTrace tailWord_7416765 prefixEnd_7416765 3808365346443779606528425 := by
  unfold tailWord_7416765
  simp only [CollatzResearch.WordTrace]
  refine ⟨270511642975334562461355749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180341095316889708307570499 270511642975334562461355749)
  ·
    refine ⟨50720933057875230461504203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270511642975334562461355749 50720933057875230461504203)
    ·
      refine ⟨76081399586812845692256305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50720933057875230461504203 76081399586812845692256305)
      ·
        refine ⟨57061049690109634269192229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76081399586812845692256305 57061049690109634269192229)
        ·
          refine ⟨10698946816895556425473543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57061049690109634269192229 10698946816895556425473543)
          ·
            refine ⟨16048420225343334638210315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10698946816895556425473543 16048420225343334638210315)
            ·
              refine ⟨24072630338015001957315473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16048420225343334638210315 24072630338015001957315473)
              ·
                refine ⟨18054472753511251467986605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24072630338015001957315473 18054472753511251467986605)
                ·
                  refine ⟨6770427282566719300494977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18054472753511251467986605 6770427282566719300494977)
                  ·
                    refine ⟨5077820461925039475371233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6770427282566719300494977 5077820461925039475371233)
                    ·
                      refine ⟨3808365346443779606528425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077820461925039475371233 3808365346443779606528425)
                      ·
                        rfl

theorem cell23_7416765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_7416765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416765 prefixEnd_7416765 := by exact prefixLift 7416765
  have htrace : WordTrace (prefixWord ++ tailWord_7416765) baseStart_7416765 baseEnd_7416765 := by
    simpa [prefixWord, tailWord_7416765, baseEnd_7416765] using wordTrace_append hprefix tailTrace_7416765
  have hstable : (prefixWord ++ tailWord_7416765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416765).length < 2 ^ (prefixWord ++ tailWord_7416765).sum := by decide
  have hdescent : baseEnd_7416765 < baseStart_7416765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416782 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_7416782 : Nat := 118140960795 + 7416782 * 2 ^ 59
def prefixEnd_7416782 : Nat := 4983230072969 + 3 ^ 40 * 7416782 * 2
def baseEnd_7416782 : Nat := 3808374075614906040015847

theorem tailTrace_7416782 : CollatzResearch.WordTrace tailWord_7416782 prefixEnd_7416782 3808374075614906040015847 := by
  unfold tailWord_7416782
  simp only [CollatzResearch.WordTrace]
  refine ⟨33814032877034121795590575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180341508677515316243149733 33814032877034121795590575)
  ·
    refine ⟨50721049315551182693385863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33814032877034121795590575 50721049315551182693385863)
    ·
      refine ⟨76081573973326774040078795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50721049315551182693385863 76081573973326774040078795)
      ·
        refine ⟨114122360959990161060118193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76081573973326774040078795 114122360959990161060118193)
        ·
          refine ⟨85591770719992620795088645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114122360959990161060118193 85591770719992620795088645)
          ·
            refine ⟨16048457009998616399079121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85591770719992620795088645 16048457009998616399079121)
            ·
              refine ⟨12036342757498962299309341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16048457009998616399079121 12036342757498962299309341)
              ·
                refine ⟨4513628534062110862241003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12036342757498962299309341 4513628534062110862241003)
                ·
                  refine ⟨6770442801093166293361505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513628534062110862241003 6770442801093166293361505)
                  ·
                    refine ⟨5077832100819874720021129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6770442801093166293361505 5077832100819874720021129)
                    ·
                      refine ⟨3808374075614906040015847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077832100819874720021129 3808374075614906040015847)
                      ·
                        rfl

theorem cell23_7416782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_7416782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416782 prefixEnd_7416782 := by exact prefixLift 7416782
  have htrace : WordTrace (prefixWord ++ tailWord_7416782) baseStart_7416782 baseEnd_7416782 := by
    simpa [prefixWord, tailWord_7416782, baseEnd_7416782] using wordTrace_append hprefix tailTrace_7416782
  have hstable : (prefixWord ++ tailWord_7416782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416782).length < 2 ^ (prefixWord ++ tailWord_7416782).sum := by decide
  have hdescent : baseEnd_7416782 < baseStart_7416782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416791 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 5, 3, 2]
def baseStart_7416791 : Nat := 118140960795 + 7416791 * 2 ^ 59
def prefixEnd_7416791 : Nat := 4983230072969 + 3 ^ 40 * 7416791 * 2
def baseEnd_7416791 : Nat := 3808378696940796504803305

theorem tailTrace_7416791 : CollatzResearch.WordTrace tailWord_7416791 prefixEnd_7416791 3808378696940796504803305 := by
  unfold tailWord_7416791
  simp only [CollatzResearch.WordTrace]
  refine ⟨270512591273240368901802227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180341727515493579267868151 270512591273240368901802227)
  ·
    refine ⟨405768886909860553352703341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270512591273240368901802227 405768886909860553352703341)
    ·
      refine ⟨152163332591197707507263753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405768886909860553352703341 152163332591197707507263753)
      ·
        refine ⟨114122499443398280630447815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152163332591197707507263753 114122499443398280630447815)
        ·
          refine ⟨171183749165097420945671723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114122499443398280630447815 171183749165097420945671723)
          ·
            refine ⟨256775623747646131418507585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171183749165097420945671723 256775623747646131418507585)
            ·
              refine ⟨192581717810734598563880689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256775623747646131418507585 192581717810734598563880689)
              ·
                refine ⟨144436288358050948922910517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192581717810734598563880689 144436288358050948922910517)
                ·
                  refine ⟨13540902033567276461522861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144436288358050948922910517 13540902033567276461522861)
                  ·
                    refine ⟨5077838262587728673071073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13540902033567276461522861 5077838262587728673071073)
                    ·
                      refine ⟨3808378696940796504803305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077838262587728673071073 3808378696940796504803305)
                      ·
                        rfl

theorem cell23_7416791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_7416791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416791 prefixEnd_7416791 := by exact prefixLift 7416791
  have htrace : WordTrace (prefixWord ++ tailWord_7416791) baseStart_7416791 baseEnd_7416791 := by
    simpa [prefixWord, tailWord_7416791, baseEnd_7416791] using wordTrace_append hprefix tailTrace_7416791
  have hstable : (prefixWord ++ tailWord_7416791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416791).length < 2 ^ (prefixWord ++ tailWord_7416791).sum := by decide
  have hdescent : baseEnd_7416791 < baseStart_7416791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416804 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_7416804 : Nat := 118140960795 + 7416804 * 2 ^ 59
def prefixEnd_7416804 : Nat := 4983230072969 + 3 ^ 40 * 7416804 * 2
def baseEnd_7416804 : Nat := 3808385372189304953940745

theorem tailTrace_7416804 : CollatzResearch.WordTrace tailWord_7416804 prefixEnd_7416804 3808385372189304953940745 := by
  unfold tailWord_7416804
  simp only [CollatzResearch.WordTrace]
  refine ⟨135256532711096636061012733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180342043614795514748016977 135256532711096636061012733)
  ·
    refine ⟨50721199766661238522879775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135256532711096636061012733 50721199766661238522879775)
    ·
      refine ⟨76081799649991857784319663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50721199766661238522879775 76081799649991857784319663)
      ·
        refine ⟨114122699474987786676479495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76081799649991857784319663 114122699474987786676479495)
        ·
          refine ⟨171184049212481680014719243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114122699474987786676479495 171184049212481680014719243)
          ·
            refine ⟨256776073818722520022078865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171184049212481680014719243 256776073818722520022078865)
            ·
              refine ⟨192582055364041890016559149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256776073818722520022078865 192582055364041890016559149)
              ·
                refine ⟨72218270761515708756209681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192582055364041890016559149 72218270761515708756209681)
                ·
                  refine ⟨54163703071136781567157261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72218270761515708756209681 54163703071136781567157261)
                  ·
                    refine ⟨20311388651676293087683973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54163703071136781567157261 20311388651676293087683973)
                    ·
                      refine ⟨3808385372189304953940745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20311388651676293087683973 3808385372189304953940745)
                      ·
                        rfl

theorem cell23_7416804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_7416804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416804 prefixEnd_7416804 := by exact prefixLift 7416804
  have htrace : WordTrace (prefixWord ++ tailWord_7416804) baseStart_7416804 baseEnd_7416804 := by
    simpa [prefixWord, tailWord_7416804, baseEnd_7416804] using wordTrace_append hprefix tailTrace_7416804
  have hstable : (prefixWord ++ tailWord_7416804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416804).length < 2 ^ (prefixWord ++ tailWord_7416804).sum := by decide
  have hdescent : baseEnd_7416804 < baseStart_7416804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416815 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 2, 1, 3]
def baseStart_7416815 : Nat := 118140960795 + 7416815 * 2 ^ 59
def prefixEnd_7416815 : Nat := 4983230072969 + 3 ^ 40 * 7416815 * 2
def baseEnd_7416815 : Nat := 3808391020476504410903195

theorem tailTrace_7416815 : CollatzResearch.WordTrace tailWord_7416815 prefixEnd_7416815 3808391020476504410903195 := by
  unfold tailWord_7416815
  simp only [CollatzResearch.WordTrace]
  refine ⟨270513466625153421000675899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180342311083435614000450599 270513466625153421000675899)
  ·
    refine ⟨405770199937730131501013849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270513466625153421000675899 405770199937730131501013849)
    ·
      refine ⟨304327649953297598625760387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405770199937730131501013849 304327649953297598625760387)
      ·
        refine ⟨456491474929946397938640581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304327649953297598625760387 456491474929946397938640581)
        ·
          refine ⟨85592151549364949613495109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456491474929946397938640581 85592151549364949613495109)
          ·
            refine ⟨16048528415505928052530333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85592151549364949613495109 16048528415505928052530333)
            ·
              refine ⟨6018198155814723019698875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16048528415505928052530333 6018198155814723019698875)
              ·
                refine ⟨9027297233722084529548313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018198155814723019698875 9027297233722084529548313)
                ·
                  refine ⟨6770472925291563397161235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027297233722084529548313 6770472925291563397161235)
                  ·
                    refine ⟨10155709387937345095741853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6770472925291563397161235 10155709387937345095741853)
                    ·
                      refine ⟨3808391020476504410903195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155709387937345095741853 3808391020476504410903195)
                      ·
                        rfl

theorem cell23_7416815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 1, 3].length) (baseStart_7416815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416815 prefixEnd_7416815 := by exact prefixLift 7416815
  have htrace : WordTrace (prefixWord ++ tailWord_7416815) baseStart_7416815 baseEnd_7416815 := by
    simpa [prefixWord, tailWord_7416815, baseEnd_7416815] using wordTrace_append hprefix tailTrace_7416815
  have hstable : (prefixWord ++ tailWord_7416815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416815).length < 2 ^ (prefixWord ++ tailWord_7416815).sum := by decide
  have hdescent : baseEnd_7416815 < baseStart_7416815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416824 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_7416824 : Nat := 118140960795 + 7416824 * 2 ^ 59
def prefixEnd_7416824 : Nat := 4983230072969 + 3 ^ 40 * 7416824 * 2
def baseEnd_7416824 : Nat := 3808395641802394875690653

theorem tailTrace_7416824 : CollatzResearch.WordTrace tailWord_7416824 prefixEnd_7416824 3808395641802394875690653 := by
  unfold tailWord_7416824
  simp only [CollatzResearch.WordTrace]
  refine ⟨135256897441060407768876763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180342529921413877025169017 135256897441060407768876763)
  ·
    refine ⟨202885346161590611653315145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135256897441060407768876763 202885346161590611653315145)
    ·
      refine ⟨152164009621192958739986359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202885346161590611653315145 152164009621192958739986359)
      ·
        refine ⟨228246014431789438109979539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152164009621192958739986359 228246014431789438109979539)
        ·
          refine ⟨342369021647684157164969309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228246014431789438109979539 342369021647684157164969309)
          ·
            refine ⟨128388383117881558936863491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342369021647684157164969309 128388383117881558936863491)
            ·
              refine ⟨192582574676822338405295237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128388383117881558936863491 192582574676822338405295237)
              ·
                refine ⟨36109232751904188450992857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192582574676822338405295237 36109232751904188450992857)
                ·
                  refine ⟨27081924563928141338244643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36109232751904188450992857 27081924563928141338244643)
                  ·
                    refine ⟨40622886845892212007366965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27081924563928141338244643 40622886845892212007366965)
                    ·
                      refine ⟨3808395641802394875690653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40622886845892212007366965 3808395641802394875690653)
                      ·
                        rfl

theorem cell23_7416824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_7416824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416824 prefixEnd_7416824 := by exact prefixLift 7416824
  have htrace : WordTrace (prefixWord ++ tailWord_7416824) baseStart_7416824 baseEnd_7416824 := by
    simpa [prefixWord, tailWord_7416824, baseEnd_7416824] using wordTrace_append hprefix tailTrace_7416824
  have hstable : (prefixWord ++ tailWord_7416824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416824).length < 2 ^ (prefixWord ++ tailWord_7416824).sum := by decide
  have hdescent : baseEnd_7416824 < baseStart_7416824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416855 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7416855 : Nat := 118140960795 + 7416855 * 2 ^ 59
def prefixEnd_7416855 : Nat := 4983230072969 + 3 ^ 40 * 7416855 * 2
def baseEnd_7416855 : Nat := 3808411559702684254403011

theorem tailTrace_7416855 : CollatzResearch.WordTrace tailWord_7416855 prefixEnd_7416855 3808411559702684254403011 := by
  unfold tailWord_7416855
  simp only [CollatzResearch.WordTrace]
  refine ⟨270514925545008507832132019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180343283696672338554754679 270514925545008507832132019)
  ·
    refine ⟨405772388317512761748198029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270514925545008507832132019 405772388317512761748198029)
    ·
      refine ⟨152164645619067285655574261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405772388317512761748198029 152164645619067285655574261)
      ·
        refine ⟨14265435526787558030210087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152164645619067285655574261 14265435526787558030210087)
        ·
          refine ⟨21398153290181337045315131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14265435526787558030210087 21398153290181337045315131)
          ·
            refine ⟨32097229935272005567972697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21398153290181337045315131 32097229935272005567972697)
            ·
              refine ⟨24072922451454004175979523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32097229935272005567972697 24072922451454004175979523)
              ·
                refine ⟨36109383677181006263969285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24072922451454004175979523 36109383677181006263969285)
                ·
                  refine ⟨6770509439471438674494241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36109383677181006263969285 6770509439471438674494241)
                  ·
                    refine ⟨5077882079603579005870681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6770509439471438674494241 5077882079603579005870681)
                    ·
                      refine ⟨3808411559702684254403011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077882079603579005870681 3808411559702684254403011)
                      ·
                        rfl

theorem cell23_7416855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7416855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416855 prefixEnd_7416855 := by exact prefixLift 7416855
  have htrace : WordTrace (prefixWord ++ tailWord_7416855) baseStart_7416855 baseEnd_7416855 := by
    simpa [prefixWord, tailWord_7416855, baseEnd_7416855] using wordTrace_append hprefix tailTrace_7416855
  have hstable : (prefixWord ++ tailWord_7416855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416855).length < 2 ^ (prefixWord ++ tailWord_7416855).sum := by decide
  have hdescent : baseEnd_7416855 < baseStart_7416855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416928 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 2, 4, 2]
def baseStart_7416928 : Nat := 118140960795 + 7416928 * 2 ^ 59
def prefixEnd_7416928 : Nat := 4983230072969 + 3 ^ 40 * 7416928 * 2
def baseEnd_7416928 : Nat := 3808449043790462468790175

theorem tailTrace_7416928 : CollatzResearch.WordTrace tailWord_7416928 prefixEnd_7416928 3808449043790462468790175 := by
  unfold tailWord_7416928
  simp only [CollatzResearch.WordTrace]
  refine ⟨135258794036872020649769719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180345058715829360866359625 135258794036872020649769719)
  ·
    refine ⟨202888191055308030974654579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135258794036872020649769719 202888191055308030974654579)
    ·
      refine ⟨304332286582962046461981869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202888191055308030974654579 304332286582962046461981869)
      ·
        refine ⟨114124607468610767423243201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304332286582962046461981869 114124607468610767423243201)
        ·
          refine ⟨85593455601458075567432401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114124607468610767423243201 85593455601458075567432401)
          ·
            refine ⟨64195091701093556675574301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85593455601458075567432401 64195091701093556675574301)
            ·
              refine ⟨24073159387910083753340363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64195091701093556675574301 24073159387910083753340363)
              ·
                refine ⟨36109739081865125630010545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24073159387910083753340363 36109739081865125630010545)
                ·
                  refine ⟨27082304311398844222507909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36109739081865125630010545 27082304311398844222507909)
                  ·
                    refine ⟨5077932058387283291720233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27082304311398844222507909 5077932058387283291720233)
                    ·
                      refine ⟨3808449043790462468790175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077932058387283291720233 3808449043790462468790175)
                      ·
                        rfl

theorem cell23_7416928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_7416928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416928 prefixEnd_7416928 := by exact prefixLift 7416928
  have htrace : WordTrace (prefixWord ++ tailWord_7416928) baseStart_7416928 baseEnd_7416928 := by
    simpa [prefixWord, tailWord_7416928, baseEnd_7416928] using wordTrace_append hprefix tailTrace_7416928
  have hstable : (prefixWord ++ tailWord_7416928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416928).length < 2 ^ (prefixWord ++ tailWord_7416928).sum := by decide
  have hdescent : baseEnd_7416928 < baseStart_7416928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416931 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 3]
def baseStart_7416931 : Nat := 118140960795 + 7416931 * 2 ^ 59
def prefixEnd_7416931 : Nat := 4983230072969 + 3 ^ 40 * 7416931 * 2
def baseEnd_7416931 : Nat := 3808450584232425957052661

theorem tailTrace_7416931 : CollatzResearch.WordTrace tailWord_7416931 prefixEnd_7416931 3808450584232425957052661 := by
  unfold tailWord_7416931
  simp only [CollatzResearch.WordTrace]
  refine ⟨270517697492733172811898647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180345131661822115207932431 270517697492733172811898647)
  ·
    refine ⟨405776546239099759217847971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270517697492733172811898647 405776546239099759217847971)
    ·
      refine ⟨608664819358649638826771957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405776546239099759217847971 608664819358649638826771957)
      ·
        refine ⟨57062326814873403640009871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 608664819358649638826771957 57062326814873403640009871)
        ·
          refine ⟨85593490222310105460014807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57062326814873403640009871 85593490222310105460014807)
          ·
            refine ⟨128390235333465158190022211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85593490222310105460014807 128390235333465158190022211)
            ·
              refine ⟨192585353000197737285033317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128390235333465158190022211 192585353000197737285033317)
              ·
                refine ⟨36109753687537075740943747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192585353000197737285033317 36109753687537075740943747)
                ·
                  refine ⟨54164630531305613611415621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36109753687537075740943747 54164630531305613611415621)
                  ·
                    refine ⟨10155868224619802552140429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54164630531305613611415621 10155868224619802552140429)
                    ·
                      refine ⟨3808450584232425957052661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10155868224619802552140429 3808450584232425957052661)
                      ·
                        rfl

theorem cell23_7416931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_7416931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416931 prefixEnd_7416931 := by exact prefixLift 7416931
  have htrace : WordTrace (prefixWord ++ tailWord_7416931) baseStart_7416931 baseEnd_7416931 := by
    simpa [prefixWord, tailWord_7416931, baseEnd_7416931] using wordTrace_append hprefix tailTrace_7416931
  have hstable : (prefixWord ++ tailWord_7416931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416931).length < 2 ^ (prefixWord ++ tailWord_7416931).sum := by decide
  have hdescent : baseEnd_7416931 < baseStart_7416931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416938 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_7416938 : Nat := 118140960795 + 7416938 * 2 ^ 59
def prefixEnd_7416938 : Nat := 4983230072969 + 3 ^ 40 * 7416938 * 2
def baseEnd_7416938 : Nat := 1269484726199002476555043

theorem tailTrace_7416938 : CollatzResearch.WordTrace tailWord_7416938 prefixEnd_7416938 1269484726199002476555043 := by
  unfold tailWord_7416938
  simp only [CollatzResearch.WordTrace]
  refine ⟨67629488200926953251850867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180345301869138542004935645 67629488200926953251850867)
  ·
    refine ⟨101444232301390429877776301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67629488200926953251850867 101444232301390429877776301)
    ·
      refine ⟨38041587113021411204166113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101444232301390429877776301 38041587113021411204166113)
      ·
        refine ⟨28531190334766058403124585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38041587113021411204166113 28531190334766058403124585)
        ·
          refine ⟨21398392751074543802343439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28531190334766058403124585 21398392751074543802343439)
          ·
            refine ⟨32097589126611815703515159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21398392751074543802343439 32097589126611815703515159)
            ·
              refine ⟨48146383689917723555272739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32097589126611815703515159 48146383689917723555272739)
              ·
                refine ⟨72219575534876585332909109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48146383689917723555272739 72219575534876585332909109)
                ·
                  refine ⟨6770585206394679874960229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72219575534876585332909109 6770585206394679874960229)
                  ·
                    refine ⟨1269484726199002476555043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6770585206394679874960229 1269484726199002476555043)
                    ·
                      rfl

theorem cell23_7416938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_7416938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416938 prefixEnd_7416938 := by exact prefixLift 7416938
  have htrace : WordTrace (prefixWord ++ tailWord_7416938) baseStart_7416938 baseEnd_7416938 := by
    simpa [prefixWord, tailWord_7416938, baseEnd_7416938] using wordTrace_append hprefix tailTrace_7416938
  have hstable : (prefixWord ++ tailWord_7416938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416938).length < 2 ^ (prefixWord ++ tailWord_7416938).sum := by decide
  have hdescent : baseEnd_7416938 < baseStart_7416938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416968 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 8]
def baseStart_7416968 : Nat := 118140960795 + 7416968 * 2 ^ 59
def prefixEnd_7416968 : Nat := 4983230072969 + 3 ^ 40 * 7416968 * 2
def baseEnd_7416968 : Nat := 423163287001849145809999

theorem tailTrace_7416968 : CollatzResearch.WordTrace tailWord_7416968 prefixEnd_7416968 423163287001849145809999 := by
  unfold tailWord_7416968
  simp only [CollatzResearch.WordTrace]
  refine ⟨135259523496799564065497779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180346031329066085420663705 135259523496799564065497779)
  ·
    refine ⟨202889285245199346098246669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135259523496799564065497779 202889285245199346098246669)
    ·
      refine ⟨76083481966949754786842501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202889285245199346098246669 76083481966949754786842501)
      ·
        refine ⟨14265652868803079022532969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76083481966949754786842501 14265652868803079022532969)
        ·
          refine ⟨10699239651602309266899727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14265652868803079022532969 10699239651602309266899727)
          ·
            refine ⟨16048859477403463900349591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10699239651602309266899727 16048859477403463900349591)
            ·
              refine ⟨24073289216105195850524387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16048859477403463900349591 24073289216105195850524387)
              ·
                refine ⟨36109933824157793775786581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24073289216105195850524387 36109933824157793775786581)
                ·
                  refine ⟨423163287001849145809999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36109933824157793775786581 423163287001849145809999)
                  ·
                    rfl

theorem cell23_7416968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 8].length) (baseStart_7416968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416968 prefixEnd_7416968 := by exact prefixLift 7416968
  have htrace : WordTrace (prefixWord ++ tailWord_7416968) baseStart_7416968 baseEnd_7416968 := by
    simpa [prefixWord, tailWord_7416968, baseEnd_7416968] using wordTrace_append hprefix tailTrace_7416968
  have hstable : (prefixWord ++ tailWord_7416968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416968).length < 2 ^ (prefixWord ++ tailWord_7416968).sum := by decide
  have hdescent : baseEnd_7416968 < baseStart_7416968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7416981 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_7416981 : Nat := 118140960795 + 7416981 * 2 ^ 59
def prefixEnd_7416981 : Nat := 4983230072969 + 3 ^ 40 * 7416981 * 2
def baseEnd_7416981 : Nat := 1269492086088383587142477

theorem tailTrace_7416981 : CollatzResearch.WordTrace tailWord_7416981 prefixEnd_7416981 1269492086088383587142477 := by
  unfold tailWord_7416981
  simp only [CollatzResearch.WordTrace]
  refine ⟨270519521142552031351218797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180346347428368020900812531 270519521142552031351218797)
  ·
    refine ⟨101444820428457011756707049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270519521142552031351218797 101444820428457011756707049)
    ·
      refine ⟨76083615321342758817530287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101444820428457011756707049 76083615321342758817530287)
      ·
        refine ⟨114125422982014138226295431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76083615321342758817530287 114125422982014138226295431)
        ·
          refine ⟨171188134473021207339443147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114125422982014138226295431 171188134473021207339443147)
          ·
            refine ⟨256782201709531811009164721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171188134473021207339443147 256782201709531811009164721)
            ·
              refine ⟨192586651282148858256873541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256782201709531811009164721 192586651282148858256873541)
              ·
                refine ⟨36109997115402910923163789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192586651282148858256873541 36109997115402910923163789)
                ·
                  refine ⟨13541248918276091596186421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36109997115402910923163789 13541248918276091596186421)
                  ·
                    refine ⟨1269492086088383587142477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13541248918276091596186421 1269492086088383587142477)
                    ·
                      rfl

theorem cell23_7416981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_7416981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7416981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7416981 prefixEnd_7416981 := by exact prefixLift 7416981
  have htrace : WordTrace (prefixWord ++ tailWord_7416981) baseStart_7416981 baseEnd_7416981 := by
    simpa [prefixWord, tailWord_7416981, baseEnd_7416981] using wordTrace_append hprefix tailTrace_7416981
  have hstable : (prefixWord ++ tailWord_7416981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7416981).length < 2 ^ (prefixWord ++ tailWord_7416981).sum := by decide
  have hdescent : baseEnd_7416981 < baseStart_7416981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7416981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417011 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 1, 6]
def baseStart_7417011 : Nat := 118140960795 + 7417011 * 2 ^ 59
def prefixEnd_7417011 : Nat := 4983230072969 + 3 ^ 40 * 7417011 * 2
def baseEnd_7417011 : Nat := 1269497220894928548017431

theorem tailTrace_7417011 : CollatzResearch.WordTrace tailWord_7417011 prefixEnd_7417011 1269497220894928548017431 := by
  unfold tailWord_7417011
  simp only [CollatzResearch.WordTrace]
  refine ⟨270520615332443346474810887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180347076888295564316540591 270520615332443346474810887)
  ·
    refine ⟨405780922998665019712216331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270520615332443346474810887 405780922998665019712216331)
    ·
      refine ⟨608671384497997529568324497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405780922998665019712216331 608671384497997529568324497)
      ·
        refine ⟨456503538373498147176243373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608671384497997529568324497 456503538373498147176243373)
        ·
          refine ⟨171188826890061805191091265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456503538373498147176243373 171188826890061805191091265)
          ·
            refine ⟨128391620167546353893318449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171188826890061805191091265 128391620167546353893318449)
            ·
              refine ⟨96293715125659765419988837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128391620167546353893318449 96293715125659765419988837)
              ·
                refine ⟨18055071586061206016247907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96293715125659765419988837 18055071586061206016247907)
                ·
                  refine ⟨27082607379091809024371861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18055071586061206016247907 27082607379091809024371861)
                  ·
                    refine ⟨1269497220894928548017431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27082607379091809024371861 1269497220894928548017431)
                    ·
                      rfl

theorem cell23_7417011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 6].length) (baseStart_7417011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417011 prefixEnd_7417011 := by exact prefixLift 7417011
  have htrace : WordTrace (prefixWord ++ tailWord_7417011) baseStart_7417011 baseEnd_7417011 := by
    simpa [prefixWord, tailWord_7417011, baseEnd_7417011] using wordTrace_append hprefix tailTrace_7417011
  have hstable : (prefixWord ++ tailWord_7417011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417011).length < 2 ^ (prefixWord ++ tailWord_7417011).sum := by decide
  have hdescent : baseEnd_7417011 < baseStart_7417011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417022 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_7417022 : Nat := 118140960795 + 7417022 * 2 ^ 59
def prefixEnd_7417022 : Nat := 4983230072969 + 3 ^ 40 * 7417022 * 2
def baseEnd_7417022 : Nat := 3808497310971985101014743

theorem tailTrace_7417022 : CollatzResearch.WordTrace tailWord_7417022 prefixEnd_7417022 3808497310971985101014743 := by
  unfold tailWord_7417022
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815127066925436919182665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180347344356935663568974213 33815127066925436919182665)
  ·
    refine ⟨25361345300194077689386999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33815127066925436919182665 25361345300194077689386999)
    ·
      refine ⟨38042017950291116534080499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25361345300194077689386999 38042017950291116534080499)
      ·
        refine ⟨57063026925436674801120749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38042017950291116534080499 57063026925436674801120749)
        ·
          refine ⟨21398635097038753050420281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57063026925436674801120749 21398635097038753050420281)
          ·
            refine ⟨16048976322779064787815211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21398635097038753050420281 16048976322779064787815211)
            ·
              refine ⟨24073464484168597181722817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16048976322779064787815211 24073464484168597181722817)
              ·
                refine ⟨18055098363126447886292113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24073464484168597181722817 18055098363126447886292113)
                ·
                  refine ⟨13541323772344835914719085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18055098363126447886292113 13541323772344835914719085)
                  ·
                    refine ⟨5077996414629313468019657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13541323772344835914719085 5077996414629313468019657)
                    ·
                      refine ⟨3808497310971985101014743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5077996414629313468019657 3808497310971985101014743)
                      ·
                        rfl

theorem cell23_7417022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_7417022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417022 prefixEnd_7417022 := by exact prefixLift 7417022
  have htrace : WordTrace (prefixWord ++ tailWord_7417022) baseStart_7417022 baseEnd_7417022 := by
    simpa [prefixWord, tailWord_7417022, baseEnd_7417022] using wordTrace_append hprefix tailTrace_7417022
  have hstable : (prefixWord ++ tailWord_7417022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417022).length < 2 ^ (prefixWord ++ tailWord_7417022).sum := by decide
  have hdescent : baseEnd_7417022 < baseStart_7417022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417035 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 3, 2, 2]
def baseStart_7417035 : Nat := 118140960795 + 7417035 * 2 ^ 59
def prefixEnd_7417035 : Nat := 4983230072969 + 3 ^ 40 * 7417035 * 2
def baseEnd_7417035 : Nat := 3808503986220493550152183

theorem tailTrace_7417035 : CollatzResearch.WordTrace tailWord_7417035 prefixEnd_7417035 3808503986220493550152183 := by
  unfold tailWord_7417035
  simp only [CollatzResearch.WordTrace]
  refine ⟨270521490684356398573684559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180347660456237599049123039 270521490684356398573684559)
  ·
    refine ⟨405782236026534597860526839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270521490684356398573684559 405782236026534597860526839)
    ·
      refine ⟨608673354039801896790790259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405782236026534597860526839 608673354039801896790790259)
      ·
        refine ⟨913010031059702845186185389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608673354039801896790790259 913010031059702845186185389)
        ·
          refine ⟨342378761647388566944819521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 913010031059702845186185389 342378761647388566944819521)
          ·
            refine ⟨256784071235541425208614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342378761647388566944819521 256784071235541425208614641)
            ·
              refine ⟨192588053426656068906460981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256784071235541425208614641 192588053426656068906460981)
              ·
                refine ⟨18055130008749006459980717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192588053426656068906460981 18055130008749006459980717)
                ·
                  refine ⟨6770673753280877422492769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18055130008749006459980717 6770673753280877422492769)
                  ·
                    refine ⟨5078005314960658066869577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6770673753280877422492769 5078005314960658066869577)
                    ·
                      refine ⟨3808503986220493550152183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078005314960658066869577 3808503986220493550152183)
                      ·
                        rfl

theorem cell23_7417035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 2, 2].length) (baseStart_7417035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417035 prefixEnd_7417035 := by exact prefixLift 7417035
  have htrace : WordTrace (prefixWord ++ tailWord_7417035) baseStart_7417035 baseEnd_7417035 := by
    simpa [prefixWord, tailWord_7417035, baseEnd_7417035] using wordTrace_append hprefix tailTrace_7417035
  have hstable : (prefixWord ++ tailWord_7417035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417035).length < 2 ^ (prefixWord ++ tailWord_7417035).sum := by decide
  have hdescent : baseEnd_7417035 < baseStart_7417035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417055 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 3]
def baseStart_7417055 : Nat := 118140960795 + 7417055 * 2 ^ 59
def prefixEnd_7417055 : Nat := 4983230072969 + 3 ^ 40 * 7417055 * 2
def baseEnd_7417055 : Nat := 3808514255833583471902091

theorem tailTrace_7417055 : CollatzResearch.WordTrace tailWord_7417055 prefixEnd_7417055 3808514255833583471902091 := by
  unfold tailWord_7417055
  simp only [CollatzResearch.WordTrace]
  refine ⟨270522220144283941989412619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180348146762855961326275079 270522220144283941989412619)
  ·
    refine ⟨405783330216425912984118929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270522220144283941989412619 405783330216425912984118929)
    ·
      refine ⟨304337497662319434738089197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405783330216425912984118929 304337497662319434738089197)
      ·
        refine ⟨114126561623369788026783449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304337497662319434738089197 114126561623369788026783449)
        ·
          refine ⟨85594921217527341020087587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114126561623369788026783449 85594921217527341020087587)
          ·
            refine ⟨128392381826291011530131381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85594921217527341020087587 128392381826291011530131381)
            ·
              refine ⟨12036785796214782330949817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128392381826291011530131381 12036785796214782330949817)
              ·
                refine ⟨9027589347161086748212363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12036785796214782330949817 9027589347161086748212363)
                ·
                  refine ⟨13541384020741630122318545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9027589347161086748212363 13541384020741630122318545)
                  ·
                    refine ⟨10156038015556222591738909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13541384020741630122318545 10156038015556222591738909)
                    ·
                      refine ⟨3808514255833583471902091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10156038015556222591738909 3808514255833583471902091)
                      ·
                        rfl

theorem cell23_7417055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_7417055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417055 prefixEnd_7417055 := by exact prefixLift 7417055
  have htrace : WordTrace (prefixWord ++ tailWord_7417055) baseStart_7417055 baseEnd_7417055 := by
    simpa [prefixWord, tailWord_7417055, baseEnd_7417055] using wordTrace_append hprefix tailTrace_7417055
  have hstable : (prefixWord ++ tailWord_7417055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417055).length < 2 ^ (prefixWord ++ tailWord_7417055).sum := by decide
  have hdescent : baseEnd_7417055 < baseStart_7417055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417068 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_7417068 : Nat := 118140960795 + 7417068 * 2 ^ 59
def prefixEnd_7417068 : Nat := 4983230072969 + 3 ^ 40 * 7417068 * 2
def baseEnd_7417068 : Nat := 3808520931082091921039531

theorem tailTrace_7417068 : CollatzResearch.WordTrace tailWord_7417068 prefixEnd_7417068 3808520931082091921039531 := by
  unfold tailWord_7417068
  simp only [CollatzResearch.WordTrace]
  refine ⟨135261347146618422604817929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180348462862157896806423905 135261347146618422604817929)
  ·
    refine ⟨101446010359963816953613447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135261347146618422604817929 101446010359963816953613447)
    ·
      refine ⟨152169015539945725430420171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101446010359963816953613447 152169015539945725430420171)
      ·
        refine ⟨228253523309918588145630257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152169015539945725430420171 228253523309918588145630257)
        ·
          refine ⟨171190142482438941109222693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228253523309918588145630257 171190142482438941109222693)
          ·
            refine ⟨32098151715457301457979255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171190142482438941109222693 32098151715457301457979255)
            ·
              refine ⟨48147227573185952186968883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32098151715457301457979255 48147227573185952186968883)
              ·
                refine ⟨72220841359778928280453325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48147227573185952186968883 72220841359778928280453325)
                ·
                  refine ⟨27082815509917098105169997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72220841359778928280453325 27082815509917098105169997)
                  ·
                    refine ⟨10156055816218911789438749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27082815509917098105169997 10156055816218911789438749)
                    ·
                      refine ⟨3808520931082091921039531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10156055816218911789438749 3808520931082091921039531)
                      ·
                        rfl

theorem cell23_7417068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_7417068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417068 prefixEnd_7417068 := by exact prefixLift 7417068
  have htrace : WordTrace (prefixWord ++ tailWord_7417068) baseStart_7417068 baseEnd_7417068 := by
    simpa [prefixWord, tailWord_7417068, baseEnd_7417068] using wordTrace_append hprefix tailTrace_7417068
  have hstable : (prefixWord ++ tailWord_7417068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417068).length < 2 ^ (prefixWord ++ tailWord_7417068).sum := by decide
  have hdescent : baseEnd_7417068 < baseStart_7417068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417086 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_7417086 : Nat := 118140960795 + 7417086 * 2 ^ 59
def prefixEnd_7417086 : Nat := 4983230072969 + 3 ^ 40 * 7417086 * 2
def baseEnd_7417086 : Nat := 3808530173733872850614449

theorem tailTrace_7417086 : CollatzResearch.WordTrace tailWord_7417086 prefixEnd_7417086 3808530173733872850614449 := by
  unfold tailWord_7417086
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815418850896454285473889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180348900538114422855860741 33815418850896454285473889)
  ·
    refine ⟨25361564138172340714105417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33815418850896454285473889 25361564138172340714105417)
    ·
      refine ⟨19021173103629255535579063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25361564138172340714105417 19021173103629255535579063)
      ·
        refine ⟨28531759655443883303368595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19021173103629255535579063 28531759655443883303368595)
        ·
          refine ⟨42797639483165824955052893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28531759655443883303368595 42797639483165824955052893)
          ·
            refine ⟨16049114806187184358144835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42797639483165824955052893 16049114806187184358144835)
            ·
              refine ⟨24073672209280776537217253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16049114806187184358144835 24073672209280776537217253)
              ·
                refine ⟨4513813539240145600728235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24073672209280776537217253 4513813539240145600728235)
                ·
                  refine ⟨6770720308860218401092353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513813539240145600728235 6770720308860218401092353)
                  ·
                    refine ⟨5078040231645163800819265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6770720308860218401092353 5078040231645163800819265)
                    ·
                      refine ⟨3808530173733872850614449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078040231645163800819265 3808530173733872850614449)
                      ·
                        rfl

theorem cell23_7417086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_7417086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417086 prefixEnd_7417086 := by exact prefixLift 7417086
  have htrace : WordTrace (prefixWord ++ tailWord_7417086) baseStart_7417086 baseEnd_7417086 := by
    simpa [prefixWord, tailWord_7417086, baseEnd_7417086] using wordTrace_append hprefix tailTrace_7417086
  have hstable : (prefixWord ++ tailWord_7417086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417086).length < 2 ^ (prefixWord ++ tailWord_7417086).sum := by decide
  have hdescent : baseEnd_7417086 < baseStart_7417086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417102 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7417102 : Nat := 118140960795 + 7417102 * 2 ^ 59
def prefixEnd_7417102 : Nat := 4983230072969 + 3 ^ 40 * 7417102 * 2
def baseEnd_7417102 : Nat := 3808538389424344788014375

theorem tailTrace_7417102 : CollatzResearch.WordTrace tailWord_7417102 prefixEnd_7417102 3808538389424344788014375 := by
  unfold tailWord_7417102
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815491796889208627046695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180349289583409112677582373 33815491796889208627046695)
  ·
    refine ⟨50723237695333812940570043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33815491796889208627046695 50723237695333812940570043)
    ·
      refine ⟨76084856543000719410855065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50723237695333812940570043 76084856543000719410855065)
      ·
        refine ⟨57063642407250539558141299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76084856543000719410855065 57063642407250539558141299)
        ·
          refine ⟨85595463610875809337211949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57063642407250539558141299 85595463610875809337211949)
          ·
            refine ⟨32098298854078428501454481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85595463610875809337211949 32098298854078428501454481)
            ·
              refine ⟨24073724140558821376090861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32098298854078428501454481 24073724140558821376090861)
              ·
                refine ⟨9027646552709558016034073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24073724140558821376090861 9027646552709558016034073)
                ·
                  refine ⟨6770734914532168512025555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9027646552709558016034073 6770734914532168512025555)
                  ·
                    refine ⟨10156102371798252768038333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6770734914532168512025555 10156102371798252768038333)
                    ·
                      refine ⟨3808538389424344788014375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10156102371798252768038333 3808538389424344788014375)
                      ·
                        rfl

theorem cell23_7417102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7417102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417102 prefixEnd_7417102 := by exact prefixLift 7417102
  have htrace : WordTrace (prefixWord ++ tailWord_7417102) baseStart_7417102 baseEnd_7417102 := by
    simpa [prefixWord, tailWord_7417102, baseEnd_7417102] using wordTrace_append hprefix tailTrace_7417102
  have hstable : (prefixWord ++ tailWord_7417102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417102).length < 2 ^ (prefixWord ++ tailWord_7417102).sum := by decide
  have hdescent : baseEnd_7417102 < baseStart_7417102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417148 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 7]
def baseStart_7417148 : Nat := 118140960795 + 7417148 * 2 ^ 59
def prefixEnd_7417148 : Nat := 4983230072969 + 3 ^ 40 * 7417148 * 2
def baseEnd_7417148 : Nat := 423173556614939067559907

theorem tailTrace_7417148 : CollatzResearch.WordTrace tailWord_7417148 prefixEnd_7417148 423173556614939067559907 := by
  unfold tailWord_7417148
  simp only [CollatzResearch.WordTrace]
  refine ⟨135262806066473509436274049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180350408088631345915032065 135262806066473509436274049)
  ·
    refine ⟨101447104549855132077205537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135262806066473509436274049 101447104549855132077205537)
    ·
      refine ⟨76085328412391349057904153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101447104549855132077205537 76085328412391349057904153)
      ·
        refine ⟨57063996309293511793428115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76085328412391349057904153 57063996309293511793428115)
        ·
          refine ⟨85595994463940267690142173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57063996309293511793428115 85595994463940267690142173)
          ·
            refine ⟨32098497923977600383803315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85595994463940267690142173 32098497923977600383803315)
            ·
              refine ⟨48147746885966400575704973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32098497923977600383803315 48147746885966400575704973)
              ·
                refine ⟨18055405082237400215889365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48147746885966400575704973 18055405082237400215889365)
                ·
                  refine ⟨423173556614939067559907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18055405082237400215889365 423173556614939067559907)
                  ·
                    rfl

theorem cell23_7417148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_7417148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417148 prefixEnd_7417148 := by exact prefixLift 7417148
  have htrace : WordTrace (prefixWord ++ tailWord_7417148) baseStart_7417148 baseEnd_7417148 := by
    simpa [prefixWord, tailWord_7417148, baseEnd_7417148] using wordTrace_append hprefix tailTrace_7417148
  have hstable : (prefixWord ++ tailWord_7417148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417148).length < 2 ^ (prefixWord ++ tailWord_7417148).sum := by decide
  have hdescent : baseEnd_7417148 < baseStart_7417148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417178 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_7417178 : Nat := 118140960795 + 7417178 * 2 ^ 59
def prefixEnd_7417178 : Nat := 4983230072969 + 3 ^ 40 * 7417178 * 2
def baseEnd_7417178 : Nat := 1269525804651362163554675

theorem tailTrace_7417178 : CollatzResearch.WordTrace tailWord_7417178 prefixEnd_7417178 1269525804651362163554675 := by
  unfold tailWord_7417178
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631676580709583499035047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180351137548558889330760125 67631676580709583499035047)
  ·
    refine ⟨101447514871064375248552571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67631676580709583499035047 101447514871064375248552571)
    ·
      refine ⟨152171272306596562872828857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101447514871064375248552571 152171272306596562872828857)
      ·
        refine ⟨114128454229947422154621643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152171272306596562872828857 114128454229947422154621643)
        ·
          refine ⟨171192681344921133231932465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114128454229947422154621643 171192681344921133231932465)
          ·
            refine ⟨128394511008690849923949349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171192681344921133231932465 128394511008690849923949349)
            ·
              refine ⟨24073970814129534360740503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128394511008690849923949349 24073970814129534360740503)
              ·
                refine ⟨36110956221194301541110755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24073970814129534360740503 36110956221194301541110755)
                ·
                  refine ⟨54166434331791452311666133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36110956221194301541110755 54166434331791452311666133)
                  ·
                    refine ⟨1269525804651362163554675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54166434331791452311666133 1269525804651362163554675)
                    ·
                      rfl

theorem cell23_7417178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_7417178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417178 prefixEnd_7417178 := by exact prefixLift 7417178
  have htrace : WordTrace (prefixWord ++ tailWord_7417178) baseStart_7417178 baseEnd_7417178 := by
    simpa [prefixWord, tailWord_7417178, baseEnd_7417178] using wordTrace_append hprefix tailTrace_7417178
  have hstable : (prefixWord ++ tailWord_7417178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417178).length < 2 ^ (prefixWord ++ tailWord_7417178).sum := by decide
  have hdescent : baseEnd_7417178 < baseStart_7417178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417335 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_7417335 : Nat := 118140960795 + 7417335 * 2 ^ 59
def prefixEnd_7417335 : Nat := 4983230072969 + 3 ^ 40 * 7417335 * 2
def baseEnd_7417335 : Nat := 3808658030416842376400803

theorem tailTrace_7417335 : CollatzResearch.WordTrace tailWord_7417335 prefixEnd_7417335 3808658030416842376400803 := by
  unfold tailWord_7417335
  simp only [CollatzResearch.WordTrace]
  refine ⟨270532432583269549809605459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180354955055513033206403639 270532432583269549809605459)
  ·
    refine ⟨405798648874904324714408189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270532432583269549809605459 405798648874904324714408189)
    ·
      refine ⟨152174493328089121767903071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405798648874904324714408189 152174493328089121767903071)
      ·
        refine ⟨228261739992133682651854607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152174493328089121767903071 228261739992133682651854607)
        ·
          refine ⟨342392609988200523977781911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228261739992133682651854607 342392609988200523977781911)
          ·
            refine ⟨513588914982300785966672867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342392609988200523977781911 513588914982300785966672867)
            ·
              refine ⟨770383372473451178950009301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513588914982300785966672867 770383372473451178950009301)
              ·
                refine ⟨18055860292346512006640843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 770383372473451178950009301 18055860292346512006640843)
                ·
                  refine ⟨27083790438519768009961265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18055860292346512006640843 27083790438519768009961265)
                  ·
                    refine ⟨20312842828889826007470949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27083790438519768009961265 20312842828889826007470949)
                    ·
                      refine ⟨3808658030416842376400803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20312842828889826007470949 3808658030416842376400803)
                      ·
                        rfl

theorem cell23_7417335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_7417335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417335 prefixEnd_7417335 := by exact prefixLift 7417335
  have htrace : WordTrace (prefixWord ++ tailWord_7417335) baseStart_7417335 baseEnd_7417335 := by
    simpa [prefixWord, tailWord_7417335, baseEnd_7417335] using wordTrace_append hprefix tailTrace_7417335
  have hstable : (prefixWord ++ tailWord_7417335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417335).length < 2 ^ (prefixWord ++ tailWord_7417335).sum := by decide
  have hdescent : baseEnd_7417335 < baseStart_7417335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417399 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 3, 3, 2]
def baseStart_7417399 : Nat := 118140960795 + 7417399 * 2 ^ 59
def prefixEnd_7417399 : Nat := 4983230072969 + 3 ^ 40 * 7417399 * 2
def baseEnd_7417399 : Nat := 3808690893178730126000509

theorem tailTrace_7417399 : CollatzResearch.WordTrace tailWord_7417399 prefixEnd_7417399 3808690893178730126000509 := by
  unfold tailWord_7417399
  simp only [CollatzResearch.WordTrace]
  refine ⟨270534766855037688739935251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180356511236691792493290167 270534766855037688739935251)
  ·
    refine ⟨405802150282556533109902877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270534766855037688739935251 405802150282556533109902877)
    ·
      refine ⟨152175806355958699916213579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405802150282556533109902877 152175806355958699916213579)
      ·
        refine ⟨228263709533938049874320369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152175806355958699916213579 228263709533938049874320369)
        ·
          refine ⟨171197782150453537405740277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228263709533938049874320369 171197782150453537405740277)
          ·
            refine ⟨16049792076605019131788151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171197782150453537405740277 16049792076605019131788151)
            ·
              refine ⟨24074688114907528697682227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16049792076605019131788151 24074688114907528697682227)
              ·
                refine ⟨36112032172361293046523341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24074688114907528697682227 36112032172361293046523341)
                ·
                  refine ⟨13542012064635484892446253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36112032172361293046523341 13542012064635484892446253)
                  ·
                    refine ⟨5078254524238306834667345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13542012064635484892446253 5078254524238306834667345)
                    ·
                      refine ⟨3808690893178730126000509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078254524238306834667345 3808690893178730126000509)
                      ·
                        rfl

theorem cell23_7417399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_7417399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417399 prefixEnd_7417399 := by exact prefixLift 7417399
  have htrace : WordTrace (prefixWord ++ tailWord_7417399) baseStart_7417399 baseEnd_7417399 := by
    simpa [prefixWord, tailWord_7417399, baseEnd_7417399] using wordTrace_append hprefix tailTrace_7417399
  have hstable : (prefixWord ++ tailWord_7417399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417399).length < 2 ^ (prefixWord ++ tailWord_7417399).sum := by decide
  have hdescent : baseEnd_7417399 < baseStart_7417399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417469 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 5]
def baseStart_7417469 : Nat := 118140960795 + 7417469 * 2 ^ 59
def prefixEnd_7417469 : Nat := 4983230072969 + 3 ^ 40 * 7417469 * 2
def baseEnd_7417469 : Nat := 423191870758282761347243

theorem tailTrace_7417469 : CollatzResearch.WordTrace tailWord_7417469 prefixEnd_7417469 423191870758282761347243 := by
  unfold tailWord_7417469
  simp only [CollatzResearch.WordTrace]
  refine ⟨270537319964784090694983461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180358213309856060463322307 270537319964784090694983461)
  ·
    refine ⟨50725747493397017005309399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270537319964784090694983461 50725747493397017005309399)
    ·
      refine ⟨76088621240095525507964099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50725747493397017005309399 76088621240095525507964099)
      ·
        refine ⟨114132931860143288261946149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76088621240095525507964099 114132931860143288261946149)
        ·
          refine ⟨21399924723776866549114903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114132931860143288261946149 21399924723776866549114903)
          ·
            refine ⟨32099887085665299823672355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21399924723776866549114903 32099887085665299823672355)
            ·
              refine ⟨48149830628497949735508533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32099887085665299823672355 48149830628497949735508533)
              ·
                refine ⟨4514046621421682787703925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48149830628497949735508533 4514046621421682787703925)
                ·
                  refine ⟨423191870758282761347243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4514046621421682787703925 423191870758282761347243)
                  ·
                    rfl

theorem cell23_7417469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_7417469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417469 prefixEnd_7417469 := by exact prefixLift 7417469
  have htrace : WordTrace (prefixWord ++ tailWord_7417469) baseStart_7417469 baseEnd_7417469 := by
    simpa [prefixWord, tailWord_7417469, baseEnd_7417469] using wordTrace_append hprefix tailTrace_7417469
  have hstable : (prefixWord ++ tailWord_7417469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417469).length < 2 ^ (prefixWord ++ tailWord_7417469).sum := by decide
  have hdescent : baseEnd_7417469 < baseStart_7417469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417552 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_7417552 : Nat := 118140960795 + 7417552 * 2 ^ 59
def prefixEnd_7417552 : Nat := 4983230072969 + 3 ^ 40 * 7417552 * 2
def baseEnd_7417552 : Nat := 3808769455718868027387305

theorem tailTrace_7417552 : CollatzResearch.WordTrace tailWord_7417552 prefixEnd_7417552 3808769455718868027387305 := by
  unfold tailWord_7417552
  simp only [CollatzResearch.WordTrace]
  refine ⟨135270173611741697935127455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180360231482322263913503273 135270173611741697935127455)
  ·
    refine ⟨202905260417612546902691183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135270173611741697935127455 202905260417612546902691183)
    ·
      refine ⟨304357890626418820354036775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202905260417612546902691183 304357890626418820354036775)
      ·
        refine ⟨456536835939628230531055163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304357890626418820354036775 456536835939628230531055163)
        ·
          refine ⟨684805253909442345796582745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456536835939628230531055163 684805253909442345796582745)
          ·
            refine ⟨513603940432081759347437059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684805253909442345796582745 513603940432081759347437059)
            ·
              refine ⟨770405910648122639021155589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513603940432081759347437059 770405910648122639021155589)
              ·
                refine ⟨144451108246522994816466673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770405910648122639021155589 144451108246522994816466673)
                ·
                  refine ⟨108338331184892246112350005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144451108246522994816466673 108338331184892246112350005)
                  ·
                    refine ⟨10156718548583648073032813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108338331184892246112350005 10156718548583648073032813)
                    ·
                      refine ⟨3808769455718868027387305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10156718548583648073032813 3808769455718868027387305)
                      ·
                        rfl

theorem cell23_7417552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_7417552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417552 prefixEnd_7417552 := by exact prefixLift 7417552
  have htrace : WordTrace (prefixWord ++ tailWord_7417552) baseStart_7417552 baseEnd_7417552 := by
    simpa [prefixWord, tailWord_7417552, baseEnd_7417552] using wordTrace_append hprefix tailTrace_7417552
  have hstable : (prefixWord ++ tailWord_7417552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417552).length < 2 ^ (prefixWord ++ tailWord_7417552).sum := by decide
  have hdescent : baseEnd_7417552 < baseStart_7417552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417579 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 1, 5, 2]
def baseStart_7417579 : Nat := 118140960795 + 7417579 * 2 ^ 59
def prefixEnd_7417579 : Nat := 4983230072969 + 3 ^ 40 * 7417579 * 2
def baseEnd_7417579 : Nat := 3808783319696539421749681

theorem tailTrace_7417579 : CollatzResearch.WordTrace tailWord_7417579 prefixEnd_7417579 3808783319696539421749681 := by
  unfold tailWord_7417579
  simp only [CollatzResearch.WordTrace]
  refine ⟨270541331994385579481487791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180360887996257052987658527 270541331994385579481487791)
  ·
    refine ⟨405811997991578369222231687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270541331994385579481487791 405811997991578369222231687)
    ·
      refine ⟨608717996987367553833347531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405811997991578369222231687 608717996987367553833347531)
      ·
        refine ⟨913076995481051330750021297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608717996987367553833347531 913076995481051330750021297)
        ·
          refine ⟨684807746610788498062515973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913076995481051330750021297 684807746610788498062515973)
          ·
            refine ⟨128401452489522843386721745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 684807746610788498062515973 128401452489522843386721745)
            ·
              refine ⟨96301089367142132540041309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128401452489522843386721745 96301089367142132540041309)
              ·
                refine ⟨36112908512678299702515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96301089367142132540041309 36112908512678299702515491)
                ·
                  refine ⟨54169362769017449553773237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36112908512678299702515491 54169362769017449553773237)
                  ·
                    refine ⟨5078377759595385895666241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54169362769017449553773237 5078377759595385895666241)
                    ·
                      refine ⟨3808783319696539421749681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078377759595385895666241 3808783319696539421749681)
                      ·
                        rfl

theorem cell23_7417579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5, 2].length) (baseStart_7417579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417579 prefixEnd_7417579 := by exact prefixLift 7417579
  have htrace : WordTrace (prefixWord ++ tailWord_7417579) baseStart_7417579 baseEnd_7417579 := by
    simpa [prefixWord, tailWord_7417579, baseEnd_7417579] using wordTrace_append hprefix tailTrace_7417579
  have hstable : (prefixWord ++ tailWord_7417579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417579).length < 2 ^ (prefixWord ++ tailWord_7417579).sum := by decide
  have hdescent : baseEnd_7417579 < baseStart_7417579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417596 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_7417596 : Nat := 118140960795 + 7417596 * 2 ^ 59
def prefixEnd_7417596 : Nat := 4983230072969 + 3 ^ 40 * 7417596 * 2
def baseEnd_7417596 : Nat := 3808792048867665855237103

theorem tailTrace_7417596 : CollatzResearch.WordTrace tailWord_7417596 prefixEnd_7417596 3808792048867665855237103 := by
  unfold tailWord_7417596
  simp only [CollatzResearch.WordTrace]
  refine ⟨135270976017661995692428321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180361301356882660923237761 135270976017661995692428321)
  ·
    refine ⟨101453232013246496769321241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135270976017661995692428321 101453232013246496769321241)
    ·
      refine ⟨76089924009934872576990931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101453232013246496769321241 76089924009934872576990931)
      ·
        refine ⟨114134886014902308865486397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76089924009934872576990931 114134886014902308865486397)
        ·
          refine ⟨42800582255588365824557399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114134886014902308865486397 42800582255588365824557399)
          ·
            refine ⟨64200873383382548736836099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42800582255588365824557399 64200873383382548736836099)
            ·
              refine ⟨96301310075073823105254149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64200873383382548736836099 96301310075073823105254149)
              ·
                refine ⟨18056495639076341832235153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96301310075073823105254149 18056495639076341832235153)
                ·
                  refine ⟨13542371729307256374176365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18056495639076341832235153 13542371729307256374176365)
                  ·
                    refine ⟨5078389398490221140316137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13542371729307256374176365 5078389398490221140316137)
                    ·
                      refine ⟨3808792048867665855237103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078389398490221140316137 3808792048867665855237103)
                      ·
                        rfl

theorem cell23_7417596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_7417596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417596 prefixEnd_7417596 := by exact prefixLift 7417596
  have htrace : WordTrace (prefixWord ++ tailWord_7417596) baseStart_7417596 baseEnd_7417596 := by
    simpa [prefixWord, tailWord_7417596, baseEnd_7417596] using wordTrace_append hprefix tailTrace_7417596
  have hstable : (prefixWord ++ tailWord_7417596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417596).length < 2 ^ (prefixWord ++ tailWord_7417596).sum := by decide
  have hdescent : baseEnd_7417596 < baseStart_7417596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417609 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 6, 2]
def baseStart_7417609 : Nat := 118140960795 + 7417609 * 2 ^ 59
def prefixEnd_7417609 : Nat := 4983230072969 + 3 ^ 40 * 7417609 * 2
def baseEnd_7417609 : Nat := 3808798724116174304374543

theorem tailTrace_7417609 : CollatzResearch.WordTrace tailWord_7417609 prefixEnd_7417609 3808798724116174304374543 := by
  unfold tailWord_7417609
  simp only [CollatzResearch.WordTrace]
  refine ⟨270542426184276894605079881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180361617456184596403386587 270542426184276894605079881)
  ·
    refine ⟨202906819638207670953809911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270542426184276894605079881 202906819638207670953809911)
    ·
      refine ⟨304360229457311506430714867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202906819638207670953809911 304360229457311506430714867)
      ·
        refine ⟨456540344185967259646072301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304360229457311506430714867 456540344185967259646072301)
        ·
          refine ⟨171202629069737722367277113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456540344185967259646072301 171202629069737722367277113)
          ·
            refine ⟨128401971802303291775457835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171202629069737722367277113 128401971802303291775457835)
            ·
              refine ⟨192602957703454937663186753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128401971802303291775457835 192602957703454937663186753)
              ·
                refine ⟨144452218277591203247390065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192602957703454937663186753 144452218277591203247390065)
                ·
                  refine ⟨108339163708193402435542549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144452218277591203247390065 108339163708193402435542549)
                  ·
                    refine ⟨5078398298821565739166057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108339163708193402435542549 5078398298821565739166057)
                    ·
                      refine ⟨3808798724116174304374543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078398298821565739166057 3808798724116174304374543)
                      ·
                        rfl

theorem cell23_7417609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 6, 2].length) (baseStart_7417609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417609 prefixEnd_7417609 := by exact prefixLift 7417609
  have htrace : WordTrace (prefixWord ++ tailWord_7417609) baseStart_7417609 baseEnd_7417609 := by
    simpa [prefixWord, tailWord_7417609, baseEnd_7417609] using wordTrace_append hprefix tailTrace_7417609
  have hstable : (prefixWord ++ tailWord_7417609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417609).length < 2 ^ (prefixWord ++ tailWord_7417609).sum := by decide
  have hdescent : baseEnd_7417609 < baseStart_7417609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417660 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_7417660 : Nat := 118140960795 + 7417660 * 2 ^ 59
def prefixEnd_7417660 : Nat := 4983230072969 + 3 ^ 40 * 7417660 * 2
def baseEnd_7417660 : Nat := 3808824911629553604836809

theorem tailTrace_7417660 : CollatzResearch.WordTrace tailWord_7417660 prefixEnd_7417660 3808824911629553604836809 := by
  unfold tailWord_7417660
  simp only [CollatzResearch.WordTrace]
  refine ⟨135272143153546065157593217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180362857538061420210124289 135272143153546065157593217)
  ·
    refine ⟨101454107365159548868194913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135272143153546065157593217 101454107365159548868194913)
    ·
      refine ⟨76090580523869661651146185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101454107365159548868194913 76090580523869661651146185)
      ·
        refine ⟨57067935392902246238359639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76090580523869661651146185 57067935392902246238359639)
        ·
          refine ⟨85601903089353369357539459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57067935392902246238359639 85601903089353369357539459)
          ·
            refine ⟨128402854634030054036309189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85601903089353369357539459 128402854634030054036309189)
            ·
              refine ⟨24075535243880635131807973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128402854634030054036309189 24075535243880635131807973)
              ·
                refine ⟨4514162858227619087213995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24075535243880635131807973 4514162858227619087213995)
                ·
                  refine ⟨6771244287341428630820993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514162858227619087213995 6771244287341428630820993)
                  ·
                    refine ⟨5078433215506071473115745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6771244287341428630820993 5078433215506071473115745)
                    ·
                      refine ⟨3808824911629553604836809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078433215506071473115745 3808824911629553604836809)
                      ·
                        rfl

theorem cell23_7417660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_7417660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417660 prefixEnd_7417660 := by exact prefixLift 7417660
  have htrace : WordTrace (prefixWord ++ tailWord_7417660) baseStart_7417660 baseEnd_7417660 := by
    simpa [prefixWord, tailWord_7417660, baseEnd_7417660] using wordTrace_append hprefix tailTrace_7417660
  have hstable : (prefixWord ++ tailWord_7417660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417660).length < 2 ^ (prefixWord ++ tailWord_7417660).sum := by decide
  have hdescent : baseEnd_7417660 < baseStart_7417660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417670 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_7417670 : Nat := 118140960795 + 7417670 * 2 ^ 59
def prefixEnd_7417670 : Nat := 4983230072969 + 3 ^ 40 * 7417670 * 2
def baseEnd_7417670 : Nat := 1269610015478699521903921

theorem tailTrace_7417670 : CollatzResearch.WordTrace tailWord_7417670 prefixEnd_7417670 1269610015478699521903921 := by
  unfold tailWord_7417670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454520344907996938220327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180363100691370601348700309 8454520344907996938220327)
  ·
    refine ⟨12681780517361995407330491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8454520344907996938220327 12681780517361995407330491)
    ·
      refine ⟨19022670776042993110995737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681780517361995407330491 19022670776042993110995737)
      ·
        refine ⟨14267003082032244833246803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19022670776042993110995737 14267003082032244833246803)
        ·
          refine ⟨21400504623048367249870205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14267003082032244833246803 21400504623048367249870205)
          ·
            refine ⟨8025189233643137718701327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21400504623048367249870205 8025189233643137718701327)
            ·
              refine ⟨12037783850464706578051991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8025189233643137718701327 12037783850464706578051991)
              ·
                refine ⟨18056675775697059867077987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12037783850464706578051991 18056675775697059867077987)
                ·
                  refine ⟨27085013663545589800616981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18056675775697059867077987 27085013663545589800616981)
                  ·
                    refine ⟨1269610015478699521903921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27085013663545589800616981 1269610015478699521903921)
                    ·
                      rfl

theorem cell23_7417670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_7417670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417670 prefixEnd_7417670 := by exact prefixLift 7417670
  have htrace : WordTrace (prefixWord ++ tailWord_7417670) baseStart_7417670 baseEnd_7417670 := by
    simpa [prefixWord, tailWord_7417670, baseEnd_7417670] using wordTrace_append hprefix tailTrace_7417670
  have hstable : (prefixWord ++ tailWord_7417670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417670).length < 2 ^ (prefixWord ++ tailWord_7417670).sum := by decide
  have hdescent : baseEnd_7417670 < baseStart_7417670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417703 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_7417703 : Nat := 118140960795 + 7417703 * 2 ^ 59
def prefixEnd_7417703 : Nat := 4983230072969 + 3 ^ 40 * 7417703 * 2
def baseEnd_7417703 : Nat := 3808846991297696936599111

theorem tailTrace_7417703 : CollatzResearch.WordTrace tailWord_7417703 prefixEnd_7417703 3808846991297696936599111 := by
  unfold tailWord_7417703
  simp only [CollatzResearch.WordTrace]
  refine ⟨270545854645936348659001763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180363903097290899106001175 270545854645936348659001763)
  ·
    refine ⟨405818781968904522988502645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270545854645936348659001763 405818781968904522988502645)
    ·
      refine ⟨38045510809584799030172123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 405818781968904522988502645 38045510809584799030172123)
      ·
        refine ⟨57068266214377198545258185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38045510809584799030172123 57068266214377198545258185)
        ·
          refine ⟨42801199660782898908943639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57068266214377198545258185 42801199660782898908943639)
          ·
            refine ⟨64201799491174348363415459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42801199660782898908943639 64201799491174348363415459)
            ·
              refine ⟨96302699236761522545123189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64201799491174348363415459 96302699236761522545123189)
              ·
                refine ⟨9028378053446392738605299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96302699236761522545123189 9028378053446392738605299)
                ·
                  refine ⟨13542567080169589107907949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9028378053446392738605299 13542567080169589107907949)
                  ·
                    refine ⟨5078462655063595915465481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13542567080169589107907949 5078462655063595915465481)
                    ·
                      refine ⟨3808846991297696936599111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078462655063595915465481 3808846991297696936599111)
                      ·
                        rfl

theorem cell23_7417703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_7417703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417703 prefixEnd_7417703 := by exact prefixLift 7417703
  have htrace : WordTrace (prefixWord ++ tailWord_7417703) baseStart_7417703 baseEnd_7417703 := by
    simpa [prefixWord, tailWord_7417703, baseEnd_7417703] using wordTrace_append hprefix tailTrace_7417703
  have hstable : (prefixWord ++ tailWord_7417703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417703).length < 2 ^ (prefixWord ++ tailWord_7417703).sum := by decide
  have hdescent : baseEnd_7417703 < baseStart_7417703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417709 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_7417709 : Nat := 118140960795 + 7417709 * 2 ^ 59
def prefixEnd_7417709 : Nat := 4983230072969 + 3 ^ 40 * 7417709 * 2
def baseEnd_7417709 : Nat := 1269616690727207971041361

theorem tailTrace_7417709 : CollatzResearch.WordTrace tailWord_7417709 prefixEnd_7417709 1269616690727207971041361 := by
  unfold tailWord_7417709
  simp only [CollatzResearch.WordTrace]
  refine ⟨270546073483914611683720181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180364048989276407789146787 270546073483914611683720181)
  ·
    refine ⟨25363694389116994845348767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270546073483914611683720181 25363694389116994845348767)
    ·
      refine ⟨38045541583675492268023151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25363694389116994845348767 38045541583675492268023151)
      ·
        refine ⟨57068312375513238402034727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38045541583675492268023151 57068312375513238402034727)
        ·
          refine ⟨85602468563269857603052091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57068312375513238402034727 85602468563269857603052091)
          ·
            refine ⟨128403702844904786404578137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85602468563269857603052091 128403702844904786404578137)
            ·
              refine ⟨96302777133678589803433603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128403702844904786404578137 96302777133678589803433603)
              ·
                refine ⟨144454165700517884705150405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96302777133678589803433603 144454165700517884705150405)
                ·
                  refine ⟨27085156068847103382215701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144454165700517884705150405 27085156068847103382215701)
                  ·
                    refine ⟨1269616690727207971041361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27085156068847103382215701 1269616690727207971041361)
                    ·
                      rfl

theorem cell23_7417709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_7417709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417709 prefixEnd_7417709 := by exact prefixLift 7417709
  have htrace : WordTrace (prefixWord ++ tailWord_7417709) baseStart_7417709 baseEnd_7417709 := by
    simpa [prefixWord, tailWord_7417709, baseEnd_7417709] using wordTrace_append hprefix tailTrace_7417709
  have hstable : (prefixWord ++ tailWord_7417709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417709).length < 2 ^ (prefixWord ++ tailWord_7417709).sum := by decide
  have hdescent : baseEnd_7417709 < baseStart_7417709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417767 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_7417767 : Nat := 118140960795 + 7417767 * 2 ^ 59
def prefixEnd_7417767 : Nat := 4983230072969 + 3 ^ 40 * 7417767 * 2
def baseEnd_7417767 : Nat := 3808879854059584686198817

theorem tailTrace_7417767 : CollatzResearch.WordTrace tailWord_7417767 prefixEnd_7417767 3808879854059584686198817 := by
  unfold tailWord_7417767
  simp only [CollatzResearch.WordTrace]
  refine ⟨270548188917704487589331555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180365459278469658392887703 270548188917704487589331555)
  ·
    refine ⟨405822283376556731383997333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270548188917704487589331555 405822283376556731383997333)
    ·
      refine ⟨19022919533276096783624875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405822283376556731383997333 19022919533276096783624875)
      ·
        refine ⟨28534379299914145175437313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19022919533276096783624875 28534379299914145175437313)
        ·
          refine ⟨21400784474935608881577985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28534379299914145175437313 21400784474935608881577985)
          ·
            refine ⟨16050588356201706661183489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21400784474935608881577985 16050588356201706661183489)
            ·
              refine ⟨12037941267151279995887617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16050588356201706661183489 12037941267151279995887617)
              ·
                refine ⟨9028455950363459996915713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12037941267151279995887617 9028455950363459996915713)
                ·
                  refine ⟨6771341962772594997686785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9028455950363459996915713 6771341962772594997686785)
                  ·
                    refine ⟨5078506472079446248265089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6771341962772594997686785 5078506472079446248265089)
                    ·
                      refine ⟨3808879854059584686198817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078506472079446248265089 3808879854059584686198817)
                      ·
                        rfl

theorem cell23_7417767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_7417767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417767 prefixEnd_7417767 := by exact prefixLift 7417767
  have htrace : WordTrace (prefixWord ++ tailWord_7417767) baseStart_7417767 baseEnd_7417767 := by
    simpa [prefixWord, tailWord_7417767, baseEnd_7417767] using wordTrace_append hprefix tailTrace_7417767
  have hstable : (prefixWord ++ tailWord_7417767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417767).length < 2 ^ (prefixWord ++ tailWord_7417767).sum := by decide
  have hdescent : baseEnd_7417767 < baseStart_7417767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417769 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_7417769 : Nat := 118140960795 + 7417769 * 2 ^ 59
def prefixEnd_7417769 : Nat := 4983230072969 + 3 ^ 40 * 7417769 * 2
def baseEnd_7417769 : Nat := 1269626960340297892791269

theorem tailTrace_7417769 : CollatzResearch.WordTrace tailWord_7417769 prefixEnd_7417769 1269626960340297892791269 := by
  unfold tailWord_7417769
  simp only [CollatzResearch.WordTrace]
  refine ⟨270548261863697241930904361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180365507909131494620602907 270548261863697241930904361)
  ·
    refine ⟨202911196397772931448178271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270548261863697241930904361 202911196397772931448178271)
    ·
      refine ⟨304366794596659397172267407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202911196397772931448178271 304366794596659397172267407)
      ·
        refine ⟨456550191894989095758401111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304366794596659397172267407 456550191894989095758401111)
        ·
          refine ⟨684825287842483643637601667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456550191894989095758401111 684825287842483643637601667)
          ·
            refine ⟨1027237931763725465456402501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684825287842483643637601667 1027237931763725465456402501)
            ·
              refine ⟨192607112205698524773075469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1027237931763725465456402501 192607112205698524773075469)
              ·
                refine ⟨72227667077136946789903301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192607112205698524773075469 72227667077136946789903301)
                ·
                  refine ⟨13542687576963177523106869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72227667077136946789903301 13542687576963177523106869)
                  ·
                    refine ⟨1269626960340297892791269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13542687576963177523106869 1269626960340297892791269)
                    ·
                      rfl

theorem cell23_7417769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_7417769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417769 prefixEnd_7417769 := by exact prefixLift 7417769
  have htrace : WordTrace (prefixWord ++ tailWord_7417769) baseStart_7417769 baseEnd_7417769 := by
    simpa [prefixWord, tailWord_7417769, baseEnd_7417769] using wordTrace_append hprefix tailTrace_7417769
  have hstable : (prefixWord ++ tailWord_7417769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417769).length < 2 ^ (prefixWord ++ tailWord_7417769).sum := by decide
  have hdescent : baseEnd_7417769 < baseStart_7417769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417779 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5]
def baseStart_7417779 : Nat := 118140960795 + 7417779 * 2 ^ 59
def prefixEnd_7417779 : Nat := 4983230072969 + 3 ^ 40 * 7417779 * 2
def baseEnd_7417779 : Nat := 3808886015827438639248761

theorem tailTrace_7417779 : CollatzResearch.WordTrace tailWord_7417779 prefixEnd_7417779 3808886015827438639248761 := by
  unfold tailWord_7417779
  simp only [CollatzResearch.WordTrace]
  refine ⟨270548626593661013638768391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180365751062440675759178927 270548626593661013638768391)
  ·
    refine ⟨405822939890491520458152587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270548626593661013638768391 405822939890491520458152587)
    ·
      refine ⟨608734409835737280687228881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405822939890491520458152587 608734409835737280687228881)
      ·
        refine ⟨456550807376802960515421661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608734409835737280687228881 456550807376802960515421661)
        ·
          refine ⟨171206552766301110193283123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456550807376802960515421661 171206552766301110193283123)
          ·
            refine ⟨256809829149451665289924685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171206552766301110193283123 256809829149451665289924685)
            ·
              refine ⟨96303685931044374483721757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256809829149451665289924685 96303685931044374483721757)
              ·
                refine ⟨36113882224141640431395659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96303685931044374483721757 36113882224141640431395659)
                ·
                  refine ⟨54170823336212460647093489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36113882224141640431395659 54170823336212460647093489)
                  ·
                    refine ⟨40628117502159345485320117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54170823336212460647093489 40628117502159345485320117)
                    ·
                      refine ⟨3808886015827438639248761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40628117502159345485320117 3808886015827438639248761)
                      ·
                        rfl

theorem cell23_7417779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_7417779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417779 prefixEnd_7417779 := by exact prefixLift 7417779
  have htrace : WordTrace (prefixWord ++ tailWord_7417779) baseStart_7417779 baseEnd_7417779 := by
    simpa [prefixWord, tailWord_7417779, baseEnd_7417779] using wordTrace_append hprefix tailTrace_7417779
  have hstable : (prefixWord ++ tailWord_7417779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417779).length < 2 ^ (prefixWord ++ tailWord_7417779).sum := by decide
  have hdescent : baseEnd_7417779 < baseStart_7417779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417780 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7417780 : Nat := 118140960795 + 7417780 * 2 ^ 59
def prefixEnd_7417780 : Nat := 4983230072969 + 3 ^ 40 * 7417780 * 2
def baseEnd_7417780 : Nat := 3808886529308093135336257

theorem tailTrace_7417780 : CollatzResearch.WordTrace tailWord_7417780 prefixEnd_7417780 3808886529308093135336257 := by
  unfold tailWord_7417780
  simp only [CollatzResearch.WordTrace]
  refine ⟨135274331533328695404777397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180365775377771593873036529 135274331533328695404777397)
  ·
    refine ⟨12681968581249565194197881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135274331533328695404777397 12681968581249565194197881)
    ·
      refine ⟨9511476435937173895648411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12681968581249565194197881 9511476435937173895648411)
      ·
        refine ⟨14267214653905760843472617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9511476435937173895648411 14267214653905760843472617)
        ·
          refine ⟨10700410990429320632604463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14267214653905760843472617 10700410990429320632604463)
          ·
            refine ⟨16050616485643980948906695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10700410990429320632604463 16050616485643980948906695)
            ·
              refine ⟨24075924728465971423360043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16050616485643980948906695 24075924728465971423360043)
              ·
                refine ⟨36113887092698957135040065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24075924728465971423360043 36113887092698957135040065)
                ·
                  refine ⟨27085415319524217851280049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36113887092698957135040065 27085415319524217851280049)
                  ·
                    refine ⟨20314061489643163388460037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27085415319524217851280049 20314061489643163388460037)
                    ·
                      refine ⟨3808886529308093135336257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20314061489643163388460037 3808886529308093135336257)
                      ·
                        rfl

theorem cell23_7417780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7417780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417780 prefixEnd_7417780 := by exact prefixLift 7417780
  have htrace : WordTrace (prefixWord ++ tailWord_7417780) baseStart_7417780 baseEnd_7417780 := by
    simpa [prefixWord, tailWord_7417780, baseEnd_7417780] using wordTrace_append hprefix tailTrace_7417780
  have hstable : (prefixWord ++ tailWord_7417780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417780).length < 2 ^ (prefixWord ++ tailWord_7417780).sum := by decide
  have hdescent : baseEnd_7417780 < baseStart_7417780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417806 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7417806 : Nat := 118140960795 + 7417806 * 2 ^ 59
def prefixEnd_7417806 : Nat := 4983230072969 + 3 ^ 40 * 7417806 * 2
def baseEnd_7417806 : Nat := 3808899879805110033611137

theorem tailTrace_7417806 : CollatzResearch.WordTrace tailWord_7417806 prefixEnd_7417806 3808899879805110033611137 := by
  unfold tailWord_7417806
  simp only [CollatzResearch.WordTrace]
  refine ⟨33818701420570399656250159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180366407576375464833334181 33818701420570399656250159)
  ·
    refine ⟨50728052130855599484375239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33818701420570399656250159 50728052130855599484375239)
    ·
      refine ⟨76092078196283399226562859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50728052130855599484375239 76092078196283399226562859)
      ·
        refine ⟨114138117294425098839844289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76092078196283399226562859 114138117294425098839844289)
        ·
          refine ⟨85603587970818824129883217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114138117294425098839844289 85603587970818824129883217)
          ·
            refine ⟨64202690978114118097412413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85603587970818824129883217 64202690978114118097412413)
            ·
              refine ⟨24076009116792794286529655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64202690978114118097412413 24076009116792794286529655)
              ·
                refine ⟨36114013675189191429794483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24076009116792794286529655 36114013675189191429794483)
                ·
                  refine ⟨54171020512783787144691725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36114013675189191429794483 54171020512783787144691725)
                  ·
                    refine ⟨20314132692293920179259397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54171020512783787144691725 20314132692293920179259397)
                    ·
                      refine ⟨3808899879805110033611137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20314132692293920179259397 3808899879805110033611137)
                      ·
                        rfl

theorem cell23_7417806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7417806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417806 prefixEnd_7417806 := by exact prefixLift 7417806
  have htrace : WordTrace (prefixWord ++ tailWord_7417806) baseStart_7417806 baseEnd_7417806 := by
    simpa [prefixWord, tailWord_7417806, baseEnd_7417806] using wordTrace_append hprefix tailTrace_7417806
  have hstable : (prefixWord ++ tailWord_7417806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417806).length < 2 ^ (prefixWord ++ tailWord_7417806).sum := by decide
  have hdescent : baseEnd_7417806 < baseStart_7417806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417809 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_7417809 : Nat := 118140960795 + 7417809 * 2 ^ 59
def prefixEnd_7417809 : Nat := 4983230072969 + 3 ^ 40 * 7417809 * 2
def baseEnd_7417809 : Nat := 3808901420247073521873623

theorem tailTrace_7417809 : CollatzResearch.WordTrace tailWord_7417809 prefixEnd_7417809 3808901420247073521873623 := by
  unfold tailWord_7417809
  simp only [CollatzResearch.WordTrace]
  refine ⟨270549720783552328762360481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180366480522368219174906987 270549720783552328762360481)
  ·
    refine ⟨202912290587664246571770361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270549720783552328762360481 202912290587664246571770361)
    ·
      refine ⟨152184217940748184928827771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202912290587664246571770361 152184217940748184928827771)
      ·
        refine ⟨228276326911122277393241657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152184217940748184928827771 228276326911122277393241657)
        ·
          refine ⟨171207245183341708044931243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228276326911122277393241657 171207245183341708044931243)
          ·
            refine ⟨256810867775012562067396865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171207245183341708044931243 256810867775012562067396865)
            ·
              refine ⟨192608150831259421550547649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256810867775012562067396865 192608150831259421550547649)
              ·
                refine ⟨144456113123444566162910737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192608150831259421550547649 144456113123444566162910737)
                ·
                  refine ⟨108342084842583424622183053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144456113123444566162910737 108342084842583424622183053)
                  ·
                    refine ⟨40628281815968784233318645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108342084842583424622183053 40628281815968784233318645)
                    ·
                      refine ⟨3808901420247073521873623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40628281815968784233318645 3808901420247073521873623)
                      ·
                        rfl

theorem cell23_7417809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_7417809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417809 prefixEnd_7417809 := by exact prefixLift 7417809
  have htrace : WordTrace (prefixWord ++ tailWord_7417809) baseStart_7417809 baseEnd_7417809 := by
    simpa [prefixWord, tailWord_7417809, baseEnd_7417809] using wordTrace_append hprefix tailTrace_7417809
  have hstable : (prefixWord ++ tailWord_7417809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417809).length < 2 ^ (prefixWord ++ tailWord_7417809).sum := by decide
  have hdescent : baseEnd_7417809 < baseStart_7417809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417816 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 5, 4]
def baseStart_7417816 : Nat := 118140960795 + 7417816 * 2 ^ 59
def prefixEnd_7417816 : Nat := 4983230072969 + 3 ^ 40 * 7417816 * 2
def baseEnd_7417816 : Nat := 1269635004870551664828697

theorem tailTrace_7417816 : CollatzResearch.WordTrace tailWord_7417816 prefixEnd_7417816 1269635004870551664828697 := by
  unfold tailWord_7417816
  simp only [CollatzResearch.WordTrace]
  refine ⟨135274988047263484478932651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180366650729684645971910201 135274988047263484478932651)
  ·
    refine ⟨202912482070895226718398977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135274988047263484478932651 202912482070895226718398977)
    ·
      refine ⟨152184361553171420038799233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202912482070895226718398977 152184361553171420038799233)
      ·
        refine ⟨114138271164878565029099425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152184361553171420038799233 114138271164878565029099425)
        ·
          refine ⟨85603703373658923771824569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114138271164878565029099425 85603703373658923771824569)
          ·
            refine ⟨64202777530244192828868427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85603703373658923771824569 64202777530244192828868427)
            ·
              refine ⟨96304166295366289243302641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64202777530244192828868427 96304166295366289243302641)
              ·
                refine ⟨72228124721524716932476981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96304166295366289243302641 72228124721524716932476981)
                ·
                  refine ⟨6771386692642942212419717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72228124721524716932476981 6771386692642942212419717)
                  ·
                    refine ⟨1269635004870551664828697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6771386692642942212419717 1269635004870551664828697)
                    ·
                      rfl

theorem cell23_7417816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_7417816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417816 prefixEnd_7417816 := by exact prefixLift 7417816
  have htrace : WordTrace (prefixWord ++ tailWord_7417816) baseStart_7417816 baseEnd_7417816 := by
    simpa [prefixWord, tailWord_7417816, baseEnd_7417816] using wordTrace_append hprefix tailTrace_7417816
  have hstable : (prefixWord ++ tailWord_7417816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417816).length < 2 ^ (prefixWord ++ tailWord_7417816).sum := by decide
  have hdescent : baseEnd_7417816 < baseStart_7417816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417823 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 2, 4, 2]
def baseStart_7417823 : Nat := 118140960795 + 7417823 * 2 ^ 59
def prefixEnd_7417823 : Nat := 4983230072969 + 3 ^ 40 * 7417823 * 2
def baseEnd_7417823 : Nat := 3808908608976236467098559

theorem tailTrace_7417823 : CollatzResearch.WordTrace tailWord_7417823 prefixEnd_7417823 3808908608976236467098559 := by
  unfold tailWord_7417823
  simp only [CollatzResearch.WordTrace]
  refine ⟨270550231405501609153370123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180366820937001072768913415 270550231405501609153370123)
  ·
    refine ⟨405825347108252413730055185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270550231405501609153370123 405825347108252413730055185)
    ·
      refine ⟨304369010331189310297541389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405825347108252413730055185 304369010331189310297541389)
      ·
        refine ⟨114138378874195991361578021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304369010331189310297541389 114138378874195991361578021)
        ·
          refine ⟨21400946038911748380295879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114138378874195991361578021 21400946038911748380295879)
          ·
            refine ⟨32101419058367622570443819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21400946038911748380295879 32101419058367622570443819)
            ·
              refine ⟨48152128587551433855665729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32101419058367622570443819 48152128587551433855665729)
              ·
                refine ⟨36114096440663575391749297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48152128587551433855665729 36114096440663575391749297)
                ·
                  refine ⟨27085572330497681543811973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36114096440663575391749297 27085572330497681543811973)
                  ·
                    refine ⟨5078544811968315289464745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27085572330497681543811973 5078544811968315289464745)
                    ·
                      refine ⟨3808908608976236467098559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078544811968315289464745 3808908608976236467098559)
                      ·
                        rfl

theorem cell23_7417823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_7417823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417823 prefixEnd_7417823 := by exact prefixLift 7417823
  have htrace : WordTrace (prefixWord ++ tailWord_7417823) baseStart_7417823 baseEnd_7417823 := by
    simpa [prefixWord, tailWord_7417823, baseEnd_7417823] using wordTrace_append hprefix tailTrace_7417823
  have hstable : (prefixWord ++ tailWord_7417823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417823).length < 2 ^ (prefixWord ++ tailWord_7417823).sum := by decide
  have hdescent : baseEnd_7417823 < baseStart_7417823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417859 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 9]
def baseStart_7417859 : Nat := 118140960795 + 7417859 * 2 ^ 59
def prefixEnd_7417859 : Nat := 4983230072969 + 3 ^ 40 * 7417859 * 2
def baseEnd_7417859 : Nat := 1269642364759932775416131

theorem tailTrace_7417859 : CollatzResearch.WordTrace tailWord_7417859 prefixEnd_7417859 1269642364759932775416131 := by
  unfold tailWord_7417859
  simp only [CollatzResearch.WordTrace]
  refine ⟨270551544433371187301680631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180367696288914124867787087 270551544433371187301680631)
  ·
    refine ⟨405827316650056780952520947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270551544433371187301680631 405827316650056780952520947)
    ·
      refine ⟨608740974975085171428781421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405827316650056780952520947 608740974975085171428781421)
      ·
        refine ⟨228277865615656939285793033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608740974975085171428781421 228277865615656939285793033)
        ·
          refine ⟨171208399211742704464344775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228277865615656939285793033 171208399211742704464344775)
          ·
            refine ⟨256812598817614056696517163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171208399211742704464344775 256812598817614056696517163)
            ·
              refine ⟨385218898226421085044775745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256812598817614056696517163 385218898226421085044775745)
              ·
                refine ⟨288914173669815813783581809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385218898226421085044775745 288914173669815813783581809)
                ·
                  refine ⟨216685630252361860337686357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288914173669815813783581809 216685630252361860337686357)
                  ·
                    refine ⟨1269642364759932775416131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 216685630252361860337686357 1269642364759932775416131)
                    ·
                      rfl

theorem cell23_7417859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_7417859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417859 prefixEnd_7417859 := by exact prefixLift 7417859
  have htrace : WordTrace (prefixWord ++ tailWord_7417859) baseStart_7417859 baseEnd_7417859 := by
    simpa [prefixWord, tailWord_7417859, baseEnd_7417859] using wordTrace_append hprefix tailTrace_7417859
  have hstable : (prefixWord ++ tailWord_7417859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417859).length < 2 ^ (prefixWord ++ tailWord_7417859).sum := by decide
  have hdescent : baseEnd_7417859 < baseStart_7417859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417956 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_7417956 : Nat := 118140960795 + 7417956 * 2 ^ 59
def prefixEnd_7417956 : Nat := 4983230072969 + 3 ^ 40 * 7417956 * 2
def baseEnd_7417956 : Nat := 3808976901903284446735447

theorem tailTrace_7417956 : CollatzResearch.WordTrace tailWord_7417956 prefixEnd_7417956 3808976901903284446735447 := by
  unfold tailWord_7417956
  simp only [CollatzResearch.WordTrace]
  refine ⟨135277541157009886433980861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180370054876013181911974481 135277541157009886433980861)
  ·
    refine ⟨50729077933878707412742823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135277541157009886433980861 50729077933878707412742823)
    ·
      refine ⟨76093616900818061119114235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50729077933878707412742823 76093616900818061119114235)
      ·
        refine ⟨114140425351227091678671353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76093616900818061119114235 114140425351227091678671353)
        ·
          refine ⟨85605319013420318759003515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114140425351227091678671353 85605319013420318759003515)
          ·
            refine ⟨128407978520130478138505273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85605319013420318759003515 128407978520130478138505273)
            ·
              refine ⟨96305983890097858603878955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128407978520130478138505273 96305983890097858603878955)
              ·
                refine ⟨144458975835146787905818433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96305983890097858603878955 144458975835146787905818433)
                ·
                  refine ⟨108344231876360090929363825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144458975835146787905818433 108344231876360090929363825)
                  ·
                    refine ⟨81258173907270068197022869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108344231876360090929363825 81258173907270068197022869)
                    ·
                      refine ⟨3808976901903284446735447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81258173907270068197022869 3808976901903284446735447)
                      ·
                        rfl

theorem cell23_7417956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_7417956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417956 prefixEnd_7417956 := by exact prefixLift 7417956
  have htrace : WordTrace (prefixWord ++ tailWord_7417956) baseStart_7417956 baseEnd_7417956 := by
    simpa [prefixWord, tailWord_7417956, baseEnd_7417956] using wordTrace_append hprefix tailTrace_7417956
  have hstable : (prefixWord ++ tailWord_7417956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417956).length < 2 ^ (prefixWord ++ tailWord_7417956).sum := by decide
  have hdescent : baseEnd_7417956 < baseStart_7417956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7417976 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_7417976 : Nat := 118140960795 + 7417976 * 2 ^ 59
def prefixEnd_7417976 : Nat := 4983230072969 + 3 ^ 40 * 7417976 * 2
def baseEnd_7417976 : Nat := 3808987171516374368485355

theorem tailTrace_7417976 : CollatzResearch.WordTrace tailWord_7417976 prefixEnd_7417976 3808987171516374368485355 := by
  unfold tailWord_7417976
  simp only [CollatzResearch.WordTrace]
  refine ⟨135277905886973658141844891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180370541182631544189126521 135277905886973658141844891)
  ·
    refine ⟨202916858830460487212767337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135277905886973658141844891 202916858830460487212767337)
    ·
      refine ⟨152187644122845365409575503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202916858830460487212767337 152187644122845365409575503)
      ·
        refine ⟨228281466184268048114363255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152187644122845365409575503 228281466184268048114363255)
        ·
          refine ⟨342422199276402072171544883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228281466184268048114363255 342422199276402072171544883)
          ·
            refine ⟨513633298914603108257317325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342422199276402072171544883 513633298914603108257317325)
            ·
              refine ⟨192612487092976165596493997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513633298914603108257317325 192612487092976165596493997)
              ·
                refine ⟨72229682659866062098685249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192612487092976165596493997 72229682659866062098685249)
                ·
                  refine ⟨54172261994899546574013937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72229682659866062098685249 54172261994899546574013937)
                  ·
                    refine ⟨40629196496174659930510453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54172261994899546574013937 40629196496174659930510453)
                    ·
                      refine ⟨3808987171516374368485355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40629196496174659930510453 3808987171516374368485355)
                      ·
                        rfl

theorem cell23_7417976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_7417976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7417976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7417976 prefixEnd_7417976 := by exact prefixLift 7417976
  have htrace : WordTrace (prefixWord ++ tailWord_7417976) baseStart_7417976 baseEnd_7417976 := by
    simpa [prefixWord, tailWord_7417976, baseEnd_7417976] using wordTrace_append hprefix tailTrace_7417976
  have hstable : (prefixWord ++ tailWord_7417976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7417976).length < 2 ^ (prefixWord ++ tailWord_7417976).sum := by decide
  have hdescent : baseEnd_7417976 < baseStart_7417976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7417976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418013 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_7418013 : Nat := 118140960795 + 7418013 * 2 ^ 59
def prefixEnd_7418013 : Nat := 4983230072969 + 3 ^ 40 * 7418013 * 2
def baseEnd_7418013 : Nat := 1269668723433530241240895

theorem tailTrace_7418013 : CollatzResearch.WordTrace tailWord_7418013 prefixEnd_7418013 1269668723433530241240895 := by
  unfold tailWord_7418013
  simp only [CollatzResearch.WordTrace]
  refine ⟨270557161274813271602786693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180371440849875514401857795 270557161274813271602786693)
  ·
    refine ⟨50729467739027488425522505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270557161274813271602786693 50729467739027488425522505)
    ·
      refine ⟨38047100804270616319141879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50729467739027488425522505 38047100804270616319141879)
      ·
        refine ⟨57070651206405924478712819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38047100804270616319141879 57070651206405924478712819)
        ·
          refine ⟨85605976809608886718069229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57070651206405924478712819 85605976809608886718069229)
          ·
            refine ⟨32102241303603332519275961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85605976809608886718069229 32102241303603332519275961)
            ·
              refine ⟨24076680977702499389456971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32102241303603332519275961 24076680977702499389456971)
              ·
                refine ⟨36115021466553749084185457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24076680977702499389456971 36115021466553749084185457)
                ·
                  refine ⟨27086266099915311813139093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36115021466553749084185457 27086266099915311813139093)
                  ·
                    refine ⟨1269668723433530241240895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27086266099915311813139093 1269668723433530241240895)
                    ·
                      rfl

theorem cell23_7418013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_7418013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418013 prefixEnd_7418013 := by exact prefixLift 7418013
  have htrace : WordTrace (prefixWord ++ tailWord_7418013) baseStart_7418013 baseEnd_7418013 := by
    simpa [prefixWord, tailWord_7418013, baseEnd_7418013] using wordTrace_append hprefix tailTrace_7418013
  have hstable : (prefixWord ++ tailWord_7418013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418013).length < 2 ^ (prefixWord ++ tailWord_7418013).sum := by decide
  have hdescent : baseEnd_7418013 < baseStart_7418013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418014 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_7418014 : Nat := 118140960795 + 7418014 * 2 ^ 59
def prefixEnd_7418014 : Nat := 4983230072969 + 3 ^ 40 * 7418014 * 2
def baseEnd_7418014 : Nat := 3809006683781245219810181

theorem tailTrace_7418014 : CollatzResearch.WordTrace tailWord_7418014 prefixEnd_7418014 3809006683781245219810181 := by
  unfold tailWord_7418014
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819649718476206096696637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180371465165206432515715397 33819649718476206096696637)
  ·
    refine ⟨12682368644428577286261239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33819649718476206096696637 12682368644428577286261239)
    ·
      refine ⟨19023552966642865929391859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12682368644428577286261239 19023552966642865929391859)
      ·
        refine ⟨28535329449964298894087789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19023552966642865929391859 28535329449964298894087789)
        ·
          refine ⟨10700748543736612085282921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28535329449964298894087789 10700748543736612085282921)
          ·
            refine ⟨8025561407802459063962191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10700748543736612085282921 8025561407802459063962191)
            ·
              refine ⟨12038342111703688595943287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8025561407802459063962191 12038342111703688595943287)
              ·
                refine ⟨18057513167555532893914931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12038342111703688595943287 18057513167555532893914931)
                ·
                  refine ⟨27086269751333299340872397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18057513167555532893914931 27086269751333299340872397)
                  ·
                    refine ⟨10157351156749987252827149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27086269751333299340872397 10157351156749987252827149)
                    ·
                      refine ⟨3809006683781245219810181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10157351156749987252827149 3809006683781245219810181)
                      ·
                        rfl

theorem cell23_7418014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_7418014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418014 prefixEnd_7418014 := by exact prefixLift 7418014
  have htrace : WordTrace (prefixWord ++ tailWord_7418014) baseStart_7418014 baseEnd_7418014 := by
    simpa [prefixWord, tailWord_7418014, baseEnd_7418014] using wordTrace_append hprefix tailTrace_7418014
  have hstable : (prefixWord ++ tailWord_7418014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418014).length < 2 ^ (prefixWord ++ tailWord_7418014).sum := by decide
  have hdescent : baseEnd_7418014 < baseStart_7418014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418053 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_7418053 : Nat := 118140960795 + 7418053 * 2 ^ 59
def prefixEnd_7418053 : Nat := 4983230072969 + 3 ^ 40 * 7418053 * 2
def baseEnd_7418053 : Nat := 3809026709526770567222501

theorem tailTrace_7418053 : CollatzResearch.WordTrace tailWord_7418053 prefixEnd_7418053 3809026709526770567222501 := by
  unfold tailWord_7418053
  simp only [CollatzResearch.WordTrace]
  refine ⟨270558620194668358434242813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180372413463112238956161875 270558620194668358434242813)
  ·
    refine ⟨101459482573000634412841055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270558620194668358434242813 101459482573000634412841055)
    ·
      refine ⟨152189223859500951619261583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101459482573000634412841055 152189223859500951619261583)
      ·
        refine ⟨228283835789251427428892375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152189223859500951619261583 228283835789251427428892375)
        ·
          refine ⟨342425753683877141143338563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228283835789251427428892375 342425753683877141143338563)
          ·
            refine ⟨513638630525815711715007845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342425753683877141143338563 513638630525815711715007845)
            ·
              refine ⟨96307243223590445946563971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513638630525815711715007845 96307243223590445946563971)
              ·
                refine ⟨144460864835385668919845957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96307243223590445946563971 144460864835385668919845957)
                ·
                  refine ⟨27086412156634812922471117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144460864835385668919845957 27086412156634812922471117)
                  ·
                    refine ⟨10157404558738054845926669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27086412156634812922471117 10157404558738054845926669)
                    ·
                      refine ⟨3809026709526770567222501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10157404558738054845926669 3809026709526770567222501)
                      ·
                        rfl

theorem cell23_7418053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_7418053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418053 prefixEnd_7418053 := by exact prefixLift 7418053
  have htrace : WordTrace (prefixWord ++ tailWord_7418053) baseStart_7418053 baseEnd_7418053 := by
    simpa [prefixWord, tailWord_7418053, baseEnd_7418053] using wordTrace_append hprefix tailTrace_7418053
  have hstable : (prefixWord ++ tailWord_7418053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418053).length < 2 ^ (prefixWord ++ tailWord_7418053).sum := by decide
  have hdescent : baseEnd_7418053 < baseStart_7418053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418090 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_7418090 : Nat := 118140960795 + 7418090 * 2 ^ 59
def prefixEnd_7418090 : Nat := 4983230072969 + 3 ^ 40 * 7418090 * 2
def baseEnd_7418090 : Nat := 1269681902770328974153277

theorem tailTrace_7418090 : CollatzResearch.WordTrace tailWord_7418090 prefixEnd_7418090 1269681902770328974153277 := by
  unfold tailWord_7418090
  simp only [CollatzResearch.WordTrace]
  refine ⟨67639992423883578438334931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180373313130356209168893149 67639992423883578438334931)
  ·
    refine ⟨101459988635825367657502397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67639992423883578438334931 101459988635825367657502397)
    ·
      refine ⟨38047495738434512871563399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101459988635825367657502397 38047495738434512871563399)
      ·
        refine ⟨57071243607651769307345099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38047495738434512871563399 57071243607651769307345099)
        ·
          refine ⟨85606865411477653961017649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57071243607651769307345099 85606865411477653961017649)
          ·
            refine ⟨64205149058608240470763237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85606865411477653961017649 64205149058608240470763237)
            ·
              refine ⟨12038465448489045088268107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64205149058608240470763237 12038465448489045088268107)
              ·
                refine ⟨18057698172733567632402161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12038465448489045088268107 18057698172733567632402161)
                ·
                  refine ⟨13543273629550175724301621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18057698172733567632402161 13543273629550175724301621)
                  ·
                    refine ⟨1269681902770328974153277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13543273629550175724301621 1269681902770328974153277)
                    ·
                      rfl

theorem cell23_7418090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_7418090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418090 prefixEnd_7418090 := by exact prefixLift 7418090
  have htrace : WordTrace (prefixWord ++ tailWord_7418090) baseStart_7418090 baseEnd_7418090 := by
    simpa [prefixWord, tailWord_7418090, baseEnd_7418090] using wordTrace_append hprefix tailTrace_7418090
  have hstable : (prefixWord ++ tailWord_7418090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418090).length < 2 ^ (prefixWord ++ tailWord_7418090).sum := by decide
  have hdescent : baseEnd_7418090 < baseStart_7418090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418113 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7418113 : Nat := 118140960795 + 7418113 * 2 ^ 59
def prefixEnd_7418113 : Nat := 4983230072969 + 3 ^ 40 * 7418113 * 2
def baseEnd_7418113 : Nat := 3809057518366040332472225

theorem tailTrace_7418113 : CollatzResearch.WordTrace tailWord_7418113 prefixEnd_7418113 3809057518366040332472225 := by
  unfold tailWord_7418113
  simp only [CollatzResearch.WordTrace]
  refine ⟨270560808574450988681426993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180373872382967325787617995 270560808574450988681426993)
  ·
    refine ⟨202920606430838241511070245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270560808574450988681426993 202920606430838241511070245)
    ·
      refine ⟨38047613705782170283325671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202920606430838241511070245 38047613705782170283325671)
      ·
        refine ⟨57071420558673255424988507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38047613705782170283325671 57071420558673255424988507)
        ·
          refine ⟨85607130838009883137482761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57071420558673255424988507 85607130838009883137482761)
          ·
            refine ⟨64205348128507412353112071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85607130838009883137482761 64205348128507412353112071)
            ·
              refine ⟨96308022192761118529668107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64205348128507412353112071 96308022192761118529668107)
              ·
                refine ⟨144462033289141677794502161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96308022192761118529668107 144462033289141677794502161)
                ·
                  refine ⟨108346524966856258345876621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144462033289141677794502161 108346524966856258345876621)
                  ·
                    refine ⟨40629946862571096879703733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108346524966856258345876621 40629946862571096879703733)
                    ·
                      refine ⟨3809057518366040332472225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40629946862571096879703733 3809057518366040332472225)
                      ·
                        rfl

theorem cell23_7418113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7418113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418113 prefixEnd_7418113 := by exact prefixLift 7418113
  have htrace : WordTrace (prefixWord ++ tailWord_7418113) baseStart_7418113 baseEnd_7418113 := by
    simpa [prefixWord, tailWord_7418113, baseEnd_7418113] using wordTrace_append hprefix tailTrace_7418113
  have hstable : (prefixWord ++ tailWord_7418113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418113).length < 2 ^ (prefixWord ++ tailWord_7418113).sum := by decide
  have hdescent : baseEnd_7418113 < baseStart_7418113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418254 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7418254 : Nat := 118140960795 + 7418254 * 2 ^ 59
def prefixEnd_7418254 : Nat := 4983230072969 + 3 ^ 40 * 7418254 * 2
def baseEnd_7418254 : Nat := 3809129919138324280809077

theorem tailTrace_7418254 : CollatzResearch.WordTrace tailWord_7418254 prefixEnd_7418254 3809129919138324280809077 := by
  unfold tailWord_7418254
  simp only [CollatzResearch.WordTrace]
  refine ⟨33820743908367521220288727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180377300844626779841539877 33820743908367521220288727)
  ·
    refine ⟨50731115862551281830433091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33820743908367521220288727 50731115862551281830433091)
    ·
      refine ⟨76096673793826922745649637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50731115862551281830433091 76096673793826922745649637)
      ·
        refine ⟨14268126336342548014809307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76096673793826922745649637 14268126336342548014809307)
        ·
          refine ⟨21402189504513822022213961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14268126336342548014809307 21402189504513822022213961)
          ·
            refine ⟨16051642128385366516660471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21402189504513822022213961 16051642128385366516660471)
            ·
              refine ⟨24077463192578049774990707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16051642128385366516660471 24077463192578049774990707)
              ·
                refine ⟨36116194788867074662486061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24077463192578049774990707 36116194788867074662486061)
                ·
                  refine ⟨13543573045825152998432273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36116194788867074662486061 13543573045825152998432273)
                  ·
                    refine ⟨10157679784368864748824205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13543573045825152998432273 10157679784368864748824205)
                    ·
                      refine ⟨3809129919138324280809077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10157679784368864748824205 3809129919138324280809077)
                      ·
                        rfl

theorem cell23_7418254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7418254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418254 prefixEnd_7418254 := by exact prefixLift 7418254
  have htrace : WordTrace (prefixWord ++ tailWord_7418254) baseStart_7418254 baseEnd_7418254 := by
    simpa [prefixWord, tailWord_7418254, baseEnd_7418254] using wordTrace_append hprefix tailTrace_7418254
  have hstable : (prefixWord ++ tailWord_7418254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418254).length < 2 ^ (prefixWord ++ tailWord_7418254).sum := by decide
  have hdescent : baseEnd_7418254 < baseStart_7418254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418285 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7418285 : Nat := 118140960795 + 7418285 * 2 ^ 59
def prefixEnd_7418285 : Nat := 4983230072969 + 3 ^ 40 * 7418285 * 2
def baseEnd_7418285 : Nat := 3809145837038613659521435

theorem tailTrace_7418285 : CollatzResearch.WordTrace tailWord_7418285 prefixEnd_7418285 3809145837038613659521435 := by
  unfold tailWord_7418285
  simp only [CollatzResearch.WordTrace]
  refine ⟨270567081929827862056688309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180378054619885241371125539 270567081929827862056688309)
  ·
    refine ⟨25365663930921362067814529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270567081929827862056688309 25365663930921362067814529)
    ·
      refine ⟨19024247948191021550860897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25365663930921362067814529 19024247948191021550860897)
      ·
        refine ⟨14268185961143266163145673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19024247948191021550860897 14268185961143266163145673)
        ·
          refine ⟨10701139470857449622359255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14268185961143266163145673 10701139470857449622359255)
          ·
            refine ⟨16051709206286174433538883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701139470857449622359255 16051709206286174433538883)
            ·
              refine ⟨24077563809429261650308325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16051709206286174433538883 24077563809429261650308325)
              ·
                refine ⟨4514543214267986559432811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24077563809429261650308325 4514543214267986559432811)
                ·
                  refine ⟨6771814821401979839149217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514543214267986559432811 6771814821401979839149217)
                  ·
                    refine ⟨5078861116051484879361913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6771814821401979839149217 5078861116051484879361913)
                    ·
                      refine ⟨3809145837038613659521435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5078861116051484879361913 3809145837038613659521435)
                      ·
                        rfl

theorem cell23_7418285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7418285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418285 prefixEnd_7418285 := by exact prefixLift 7418285
  have htrace : WordTrace (prefixWord ++ tailWord_7418285) baseStart_7418285 baseEnd_7418285 := by
    simpa [prefixWord, tailWord_7418285, baseEnd_7418285] using wordTrace_append hprefix tailTrace_7418285
  have hstable : (prefixWord ++ tailWord_7418285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418285).length < 2 ^ (prefixWord ++ tailWord_7418285).sum := by decide
  have hdescent : baseEnd_7418285 < baseStart_7418285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418290 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_7418290 : Nat := 118140960795 + 7418290 * 2 ^ 59
def prefixEnd_7418290 : Nat := 4983230072969 + 3 ^ 40 * 7418290 * 2
def baseEnd_7418290 : Nat := 3809148404441886139958911

theorem tailTrace_7418290 : CollatzResearch.WordTrace tailWord_7418290 prefixEnd_7418290 3809148404441886139958911 := by
  unfold tailWord_7418290
  simp only [CollatzResearch.WordTrace]
  refine ⟨67641816073702436977655081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180378176196539831940413549 67641816073702436977655081)
  ·
    refine ⟨50731362055276827733241311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67641816073702436977655081 50731362055276827733241311)
    ·
      refine ⟨76097043082915241599861967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50731362055276827733241311 76097043082915241599861967)
      ·
        refine ⟨114145564624372862399792951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76097043082915241599861967 114145564624372862399792951)
        ·
          refine ⟨171218346936559293599689427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114145564624372862399792951 171218346936559293599689427)
          ·
            refine ⟨256827520404838940399534141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171218346936559293599689427 256827520404838940399534141)
            ·
              refine ⟨96310320151814602649825303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256827520404838940399534141 96310320151814602649825303)
              ·
                refine ⟨144465480227721903974737955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96310320151814602649825303 144465480227721903974737955)
                ·
                  refine ⟨216698220341582855962106933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144465480227721903974737955 216698220341582855962106933)
                  ·
                    refine ⟨20315458157023392746447525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216698220341582855962106933 20315458157023392746447525)
                    ·
                      refine ⟨3809148404441886139958911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20315458157023392746447525 3809148404441886139958911)
                      ·
                        rfl

theorem cell23_7418290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_7418290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418290 prefixEnd_7418290 := by exact prefixLift 7418290
  have htrace : WordTrace (prefixWord ++ tailWord_7418290) baseStart_7418290 baseEnd_7418290 := by
    simpa [prefixWord, tailWord_7418290, baseEnd_7418290] using wordTrace_append hprefix tailTrace_7418290
  have hstable : (prefixWord ++ tailWord_7418290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418290).length < 2 ^ (prefixWord ++ tailWord_7418290).sum := by decide
  have hdescent : baseEnd_7418290 < baseStart_7418290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418320 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_7418320 : Nat := 118140960795 + 7418320 * 2 ^ 59
def prefixEnd_7418320 : Nat := 4983230072969 + 3 ^ 40 * 7418320 * 2
def baseEnd_7418320 : Nat := 3809163808861521022583773

theorem tailTrace_7418320 : CollatzResearch.WordTrace tailWord_7418320 prefixEnd_7418320 3809163808861521022583773 := by
  unfold tailWord_7418320
  simp only [CollatzResearch.WordTrace]
  refine ⟨135284179242350531517106207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180378905656467375356141609 135284179242350531517106207)
  ·
    refine ⟨202926268863525797275659311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135284179242350531517106207 202926268863525797275659311)
    ·
      refine ⟨304389403295288695913488967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202926268863525797275659311 304389403295288695913488967)
      ·
        refine ⟨456584104942933043870233451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304389403295288695913488967 456584104942933043870233451)
        ·
          refine ⟨684876157414399565805350177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456584104942933043870233451 684876157414399565805350177)
          ·
            refine ⟨513657118060799674354012633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684876157414399565805350177 513657118060799674354012633)
            ·
              refine ⟨385242838545599755765509475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513657118060799674354012633 385242838545599755765509475)
              ·
                refine ⟨577864257818399633648264213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385242838545599755765509475 577864257818399633648264213)
                ·
                  refine ⟨27087387085237482827262385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 577864257818399633648264213 27087387085237482827262385)
                  ·
                    refine ⟨20315540313928112120446789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27087387085237482827262385 20315540313928112120446789)
                    ·
                      refine ⟨3809163808861521022583773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20315540313928112120446789 3809163808861521022583773)
                      ·
                        rfl

theorem cell23_7418320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_7418320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418320 prefixEnd_7418320 := by exact prefixLift 7418320
  have htrace : WordTrace (prefixWord ++ tailWord_7418320) baseStart_7418320 baseEnd_7418320 := by
    simpa [prefixWord, tailWord_7418320, baseEnd_7418320] using wordTrace_append hprefix tailTrace_7418320
  have hstable : (prefixWord ++ tailWord_7418320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418320).length < 2 ^ (prefixWord ++ tailWord_7418320).sum := by decide
  have hdescent : baseEnd_7418320 < baseStart_7418320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418330 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_7418330 : Nat := 118140960795 + 7418330 * 2 ^ 59
def prefixEnd_7418330 : Nat := 4983230072969 + 3 ^ 40 * 7418330 * 2
def baseEnd_7418330 : Nat := 423240993740896220384303

theorem tailTrace_7418330 : CollatzResearch.WordTrace tailWord_7418330 prefixEnd_7418330 423240993740896220384303 := by
  unfold tailWord_7418330
  simp only [CollatzResearch.WordTrace]
  refine ⟨67642180803666208685519111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180379148809776556494717629 67642180803666208685519111)
  ·
    refine ⟨101463271205499313028278667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67642180803666208685519111 101463271205499313028278667)
    ·
      refine ⟨152194906808248969542418001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101463271205499313028278667 152194906808248969542418001)
      ·
        refine ⟨114146180106186727156813501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152194906808248969542418001 114146180106186727156813501)
        ·
          refine ⟨42804817539820022683805063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114146180106186727156813501 42804817539820022683805063)
          ·
            refine ⟨64207226309730034025707595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42804817539820022683805063 64207226309730034025707595)
            ·
              refine ⟨96310839464595051038561393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64207226309730034025707595 96310839464595051038561393)
              ·
                refine ⟨72233129598446288278921045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96310839464595051038561393 72233129598446288278921045)
                ·
                  refine ⟨423240993740896220384303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72233129598446288278921045 423240993740896220384303)
                  ·
                    rfl

theorem cell23_7418330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_7418330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418330 prefixEnd_7418330 := by exact prefixLift 7418330
  have htrace : WordTrace (prefixWord ++ tailWord_7418330) baseStart_7418330 baseEnd_7418330 := by
    simpa [prefixWord, tailWord_7418330, baseEnd_7418330] using wordTrace_append hprefix tailTrace_7418330
  have hstable : (prefixWord ++ tailWord_7418330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418330).length < 2 ^ (prefixWord ++ tailWord_7418330).sum := by decide
  have hdescent : baseEnd_7418330 < baseStart_7418330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418347 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 5]
def baseStart_7418347 : Nat := 118140960795 + 7418347 * 2 ^ 59
def prefixEnd_7418347 : Nat := 4983230072969 + 3 ^ 40 * 7418347 * 2
def baseEnd_7418347 : Nat := 423241963648799157438461

theorem tailTrace_7418347 : CollatzResearch.WordTrace tailWord_7418347 prefixEnd_7418347 423241963648799157438461 := by
  unfold tailWord_7418347
  simp only [CollatzResearch.WordTrace]
  refine ⟨270569343255603246645445295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180379562170402164430296863 270569343255603246645445295)
  ·
    refine ⟨405854014883404869968167943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270569343255603246645445295 405854014883404869968167943)
    ·
      refine ⟨608781022325107304952251915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405854014883404869968167943 608781022325107304952251915)
      ·
        refine ⟨913171533487660957428377873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608781022325107304952251915 913171533487660957428377873)
        ·
          refine ⟨684878650115745718071283405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913171533487660957428377873 684878650115745718071283405)
          ·
            refine ⟨256829493793404644276731277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 684878650115745718071283405 256829493793404644276731277)
            ·
              refine ⟨96311060172526741603774229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256829493793404644276731277 96311060172526741603774229)
              ·
                refine ⟨4514580945587191012676917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96311060172526741603774229 4514580945587191012676917)
                ·
                  refine ⟨423241963648799157438461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4514580945587191012676917 423241963648799157438461)
                  ·
                    rfl

theorem cell23_7418347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 5].length) (baseStart_7418347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418347 prefixEnd_7418347 := by exact prefixLift 7418347
  have htrace : WordTrace (prefixWord ++ tailWord_7418347) baseStart_7418347 baseEnd_7418347 := by
    simpa [prefixWord, tailWord_7418347, baseEnd_7418347] using wordTrace_append hprefix tailTrace_7418347
  have hstable : (prefixWord ++ tailWord_7418347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418347).length < 2 ^ (prefixWord ++ tailWord_7418347).sum := by decide
  have hdescent : baseEnd_7418347 < baseStart_7418347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418360 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_7418360 : Nat := 118140960795 + 7418360 * 2 ^ 59
def prefixEnd_7418360 : Nat := 4983230072969 + 3 ^ 40 * 7418360 * 2
def baseEnd_7418360 : Nat := 1269728116029233622027863

theorem tailTrace_7418360 : CollatzResearch.WordTrace tailWord_7418360 prefixEnd_7418360 1269728116029233622027863 := by
  unfold tailWord_7418360
  simp only [CollatzResearch.WordTrace]
  refine ⟨135284908702278074932834267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180379878269704099910445689 135284908702278074932834267)
  ·
    refine ⟨202927363053417112399251401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135284908702278074932834267 202927363053417112399251401)
    ·
      refine ⟨152195522290062834299438551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202927363053417112399251401 152195522290062834299438551)
      ·
        refine ⟨228293283435094251449157827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152195522290062834299438551 228293283435094251449157827)
        ·
          refine ⟨342439925152641377173736741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228293283435094251449157827 342439925152641377173736741)
          ·
            refine ⟨64207485966120258220075639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342439925152641377173736741 64207485966120258220075639)
            ·
              refine ⟨96311228949180387330113459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64207485966120258220075639 96311228949180387330113459)
              ·
                refine ⟨144466843423770580995170189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96311228949180387330113459 144466843423770580995170189)
                ·
                  refine ⟨54175066283913967873188821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144466843423770580995170189 54175066283913967873188821)
                  ·
                    refine ⟨1269728116029233622027863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54175066283913967873188821 1269728116029233622027863)
                    ·
                      rfl

theorem cell23_7418360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_7418360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418360 prefixEnd_7418360 := by exact prefixLift 7418360
  have htrace : WordTrace (prefixWord ++ tailWord_7418360) baseStart_7418360 baseEnd_7418360 := by
    simpa [prefixWord, tailWord_7418360, baseEnd_7418360] using wordTrace_append hprefix tailTrace_7418360
  have hstable : (prefixWord ++ tailWord_7418360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418360).length < 2 ^ (prefixWord ++ tailWord_7418360).sum := by decide
  have hdescent : baseEnd_7418360 < baseStart_7418360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418417 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_7418417 : Nat := 118140960795 + 7418417 * 2 ^ 59
def prefixEnd_7418417 : Nat := 4983230072969 + 3 ^ 40 * 7418417 * 2
def baseEnd_7418417 : Nat := 3809213616485007143070827

theorem tailTrace_7418417 : CollatzResearch.WordTrace tailWord_7418417 prefixEnd_7418417 3809213616485007143070827 := by
  unfold tailWord_7418417
  simp only [CollatzResearch.WordTrace]
  refine ⟨270571896365349648600493505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180381264243566432400329003 270571896365349648600493505)
  ·
    refine ⟨202928922274012236450370129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270571896365349648600493505 202928922274012236450370129)
    ·
      refine ⟨152196691705509177337777597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202928922274012236450370129 152196691705509177337777597)
      ·
        refine ⟨57073759389565941501666599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152196691705509177337777597 57073759389565941501666599)
        ·
          refine ⟨85610639084348912252499899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57073759389565941501666599 85610639084348912252499899)
          ·
            refine ⟨128415958626523368378749849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85610639084348912252499899 128415958626523368378749849)
            ·
              refine ⟨96311968969892526284062387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128415958626523368378749849 96311968969892526284062387)
              ·
                refine ⟨144467953454838789426093581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96311968969892526284062387 144467953454838789426093581)
                ·
                  refine ⟨54175482545564546034785093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144467953454838789426093581 54175482545564546034785093)
                  ·
                    refine ⟨10157902977293352381522205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54175482545564546034785093 10157902977293352381522205)
                    ·
                      refine ⟨3809213616485007143070827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10157902977293352381522205 3809213616485007143070827)
                      ·
                        rfl

theorem cell23_7418417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_7418417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418417 prefixEnd_7418417 := by exact prefixLift 7418417
  have htrace : WordTrace (prefixWord ++ tailWord_7418417) baseStart_7418417 baseEnd_7418417 := by
    simpa [prefixWord, tailWord_7418417, baseEnd_7418417] using wordTrace_append hprefix tailTrace_7418417
  have hstable : (prefixWord ++ tailWord_7418417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418417).length < 2 ^ (prefixWord ++ tailWord_7418417).sum := by decide
  have hdescent : baseEnd_7418417 < baseStart_7418417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418467 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 5, 5]
def baseStart_7418467 : Nat := 118140960795 + 7418467 * 2 ^ 59
def prefixEnd_7418467 : Nat := 4983230072969 + 3 ^ 40 * 7418467 * 2
def baseEnd_7418467 : Nat := 1269746430172577315815199

theorem tailTrace_7418467 : CollatzResearch.WordTrace tailWord_7418467 prefixEnd_7418467 1269746430172577315815199 := by
  unfold tailWord_7418467
  simp only [CollatzResearch.WordTrace]
  refine ⟨270573720015168507139813655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180382480010112338093209103 270573720015168507139813655)
  ·
    refine ⟨405860580022752760709720483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270573720015168507139813655 405860580022752760709720483)
    ·
      refine ⟨608790870034129141064580725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405860580022752760709720483 608790870034129141064580725)
      ·
        refine ⟨57074144065699606974804443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 608790870034129141064580725 57074144065699606974804443)
        ·
          refine ⟨85611216098549410462206665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57074144065699606974804443 85611216098549410462206665)
          ·
            refine ⟨64208412073912057846654999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85611216098549410462206665 64208412073912057846654999)
            ·
              refine ⟨96312618110868086769982499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64208412073912057846654999 96312618110868086769982499)
              ·
                refine ⟨144468927166302130154973749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96312618110868086769982499 144468927166302130154973749)
                ·
                  refine ⟨13543961921840824702028789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144468927166302130154973749 13543961921840824702028789)
                  ·
                    refine ⟨1269746430172577315815199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13543961921840824702028789 1269746430172577315815199)
                    ·
                      rfl

theorem cell23_7418467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 5].length) (baseStart_7418467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418467 prefixEnd_7418467 := by exact prefixLift 7418467
  have htrace : WordTrace (prefixWord ++ tailWord_7418467) baseStart_7418467 baseEnd_7418467 := by
    simpa [prefixWord, tailWord_7418467, baseEnd_7418467] using wordTrace_append hprefix tailTrace_7418467
  have hstable : (prefixWord ++ tailWord_7418467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418467).length < 2 ^ (prefixWord ++ tailWord_7418467).sum := by decide
  have hdescent : baseEnd_7418467 < baseStart_7418467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418485 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7418485 : Nat := 118140960795 + 7418485 * 2 ^ 59
def prefixEnd_7418485 : Nat := 4983230072969 + 3 ^ 40 * 7418485 * 2
def baseEnd_7418485 : Nat := 3809248533169512877020515

theorem tailTrace_7418485 : CollatzResearch.WordTrace tailWord_7418485 prefixEnd_7418485 3809248533169512877020515 := by
  unfold tailWord_7418485
  simp only [CollatzResearch.WordTrace]
  refine ⟨270574376529103296213968909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180382917686068864142645939 270574376529103296213968909)
  ·
    refine ⟨101465391198413736080238341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270574376529103296213968909 101465391198413736080238341)
    ·
      refine ⟨19024760849702575515044689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101465391198413736080238341 19024760849702575515044689)
      ·
        refine ⟨14268570637276931636283517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19024760849702575515044689 14268570637276931636283517)
        ·
          refine ⟨5350713988978849363606319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14268570637276931636283517 5350713988978849363606319)
          ·
            refine ⟨8026070983468274045409479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350713988978849363606319 8026070983468274045409479)
            ·
              refine ⟨12039106475202411068114219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026070983468274045409479 12039106475202411068114219)
              ·
                refine ⟨18058659712803616602171329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12039106475202411068114219 18058659712803616602171329)
                ·
                  refine ⟨13543994784602712451628497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18058659712803616602171329 13543994784602712451628497)
                  ·
                    refine ⟨10157996088452034338721373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13543994784602712451628497 10157996088452034338721373)
                    ·
                      refine ⟨3809248533169512877020515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10157996088452034338721373 3809248533169512877020515)
                      ·
                        rfl

theorem cell23_7418485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7418485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418485 prefixEnd_7418485 := by exact prefixLift 7418485
  have htrace : WordTrace (prefixWord ++ tailWord_7418485) baseStart_7418485 baseEnd_7418485 := by
    simpa [prefixWord, tailWord_7418485, baseEnd_7418485] using wordTrace_append hprefix tailTrace_7418485
  have hstable : (prefixWord ++ tailWord_7418485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418485).length < 2 ^ (prefixWord ++ tailWord_7418485).sum := by decide
  have hdescent : baseEnd_7418485 < baseStart_7418485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418501 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_7418501 : Nat := 118140960795 + 7418501 * 2 ^ 59
def prefixEnd_7418501 : Nat := 4983230072969 + 3 ^ 40 * 7418501 * 2
def baseEnd_7418501 : Nat := 1269752249619994938140147

theorem tailTrace_7418501 : CollatzResearch.WordTrace tailWord_7418501 prefixEnd_7418501 1269752249619994938140147 := by
  unfold tailWord_7418501
  simp only [CollatzResearch.WordTrace]
  refine ⟨270574960097045330946551357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180383306731363553964367571 270574960097045330946551357)
  ·
    refine ⟨101465610036391999104956759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270574960097045330946551357 101465610036391999104956759)
    ·
      refine ⟨152198415054587998657435139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101465610036391999104956759 152198415054587998657435139)
      ·
        refine ⟨228297622581881997986152709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152198415054587998657435139 228297622581881997986152709)
        ·
          refine ⟨42805804234102874622403633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228297622581881997986152709 42805804234102874622403633)
          ·
            refine ⟨32104353175577155966802725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42805804234102874622403633 32104353175577155966802725)
            ·
              refine ⟨6019566220420716743775511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32104353175577155966802725 6019566220420716743775511)
              ·
                refine ⟨9029349330631075115663267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019566220420716743775511 9029349330631075115663267)
                ·
                  refine ⟨13544023995946612673494901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029349330631075115663267 13544023995946612673494901)
                  ·
                    refine ⟨1269752249619994938140147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13544023995946612673494901 1269752249619994938140147)
                    ·
                      rfl

theorem cell23_7418501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_7418501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418501 prefixEnd_7418501 := by exact prefixLift 7418501
  have htrace : WordTrace (prefixWord ++ tailWord_7418501) baseStart_7418501 baseEnd_7418501 := by
    simpa [prefixWord, tailWord_7418501, baseEnd_7418501] using wordTrace_append hprefix tailTrace_7418501
  have hstable : (prefixWord ++ tailWord_7418501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418501).length < 2 ^ (prefixWord ++ tailWord_7418501).sum := by decide
  have hdescent : baseEnd_7418501 < baseStart_7418501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418517 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_7418517 : Nat := 118140960795 + 7418517 * 2 ^ 59
def prefixEnd_7418517 : Nat := 4983230072969 + 3 ^ 40 * 7418517 * 2
def baseEnd_7418517 : Nat := 3809264964550456751820367

theorem tailTrace_7418517 : CollatzResearch.WordTrace tailWord_7418517 prefixEnd_7418517 3809264964550456751820367 := by
  unfold tailWord_7418517
  simp only [CollatzResearch.WordTrace]
  refine ⟨270575543664987365679133805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180383695776658243786089203 270575543664987365679133805)
  ·
    refine ⟨101465828874370262129675177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270575543664987365679133805 101465828874370262129675177)
    ·
      refine ⟨76099371655777696597256383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101465828874370262129675177 76099371655777696597256383)
      ·
        refine ⟨114149057483666544895884575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76099371655777696597256383 114149057483666544895884575)
        ·
          refine ⟨171223586225499817343826863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114149057483666544895884575 171223586225499817343826863)
          ·
            refine ⟨256835379338249726015740295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171223586225499817343826863 256835379338249726015740295)
            ·
              refine ⟨385253069007374589023610443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256835379338249726015740295 385253069007374589023610443)
              ·
                refine ⟨577879603511061883535415665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385253069007374589023610443 577879603511061883535415665)
                ·
                  refine ⟨433409702633296412651561749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577879603511061883535415665 433409702633296412651561749)
                  ·
                    refine ⟨20316079810935769343041957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 433409702633296412651561749 20316079810935769343041957)
                    ·
                      refine ⟨3809264964550456751820367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20316079810935769343041957 3809264964550456751820367)
                      ·
                        rfl

theorem cell23_7418517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_7418517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418517 prefixEnd_7418517 := by exact prefixLift 7418517
  have htrace : WordTrace (prefixWord ++ tailWord_7418517) baseStart_7418517 baseEnd_7418517 := by
    simpa [prefixWord, tailWord_7418517, baseEnd_7418517] using wordTrace_append hprefix tailTrace_7418517
  have hstable : (prefixWord ++ tailWord_7418517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418517).length < 2 ^ (prefixWord ++ tailWord_7418517).sum := by decide
  have hdescent : baseEnd_7418517 < baseStart_7418517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418524 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7418524 : Nat := 118140960795 + 7418524 * 2 ^ 59
def prefixEnd_7418524 : Nat := 4983230072969 + 3 ^ 40 * 7418524 * 2
def baseEnd_7418524 : Nat := 3809268558915038224432835

theorem tailTrace_7418524 : CollatzResearch.WordTrace tailWord_7418524 prefixEnd_7418524 3809268558915038224432835 := by
  unfold tailWord_7418524
  simp only [CollatzResearch.WordTrace]
  refine ⟨135287899487981002937319313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180383865983974670583092417 135287899487981002937319313)
  ·
    refine ⟨101465924615985752202989485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135287899487981002937319313 101465924615985752202989485)
    ·
      refine ⟨38049721730994657076121057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101465924615985752202989485 38049721730994657076121057)
      ·
        refine ⟨28537291298245992807090793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38049721730994657076121057 28537291298245992807090793)
        ·
          refine ⟨21402968473684494605318095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28537291298245992807090793 21402968473684494605318095)
          ·
            refine ⟨32104452710526741907977143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21402968473684494605318095 32104452710526741907977143)
            ·
              refine ⟨48156679065790112861965715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32104452710526741907977143 48156679065790112861965715)
              ·
                refine ⟨72235018598685169292948573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48156679065790112861965715 72235018598685169292948573)
                ·
                  refine ⟨27088131974506938484855715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72235018598685169292948573 27088131974506938484855715)
                  ·
                    refine ⟨40632197961760407727283573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27088131974506938484855715 40632197961760407727283573)
                    ·
                      refine ⟨3809268558915038224432835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40632197961760407727283573 3809268558915038224432835)
                      ·
                        rfl

theorem cell23_7418524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7418524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418524 prefixEnd_7418524 := by exact prefixLift 7418524
  have htrace : WordTrace (prefixWord ++ tailWord_7418524) baseStart_7418524 baseEnd_7418524 := by
    simpa [prefixWord, tailWord_7418524, baseEnd_7418524] using wordTrace_append hprefix tailTrace_7418524
  have hstable : (prefixWord ++ tailWord_7418524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418524).length < 2 ^ (prefixWord ++ tailWord_7418524).sum := by decide
  have hdescent : baseEnd_7418524 < baseStart_7418524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418554 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_7418554 : Nat := 118140960795 + 7418554 * 2 ^ 59
def prefixEnd_7418554 : Nat := 4983230072969 + 3 ^ 40 * 7418554 * 2
def baseEnd_7418554 : Nat := 3809283963334673107057697

theorem tailTrace_7418554 : CollatzResearch.WordTrace tailWord_7418554 prefixEnd_7418554 3809283963334673107057697 := by
  unfold tailWord_7418554
  simp only [CollatzResearch.WordTrace]
  refine ⟨67644223291463330249557679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180384595443902213998820477 67644223291463330249557679)
  ·
    refine ⟨101466334937194995374336519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67644223291463330249557679 101466334937194995374336519)
    ·
      refine ⟨152199502405792493061504779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101466334937194995374336519 152199502405792493061504779)
      ·
        refine ⟨228299253608688739592257169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152199502405792493061504779 228299253608688739592257169)
        ·
          refine ⟨171224440206516554694192877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228299253608688739592257169 171224440206516554694192877)
          ·
            refine ⟨64209165077443708010322329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171224440206516554694192877 64209165077443708010322329)
            ·
              refine ⟨48156873808082781007741747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64209165077443708010322329 48156873808082781007741747)
              ·
                refine ⟨72235310712124171511612621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48156873808082781007741747 72235310712124171511612621)
                ·
                  refine ⟨27088241517046564316854733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72235310712124171511612621 27088241517046564316854733)
                  ·
                    refine ⟨10158090568892461618820525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27088241517046564316854733 10158090568892461618820525)
                    ·
                      refine ⟨3809283963334673107057697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158090568892461618820525 3809283963334673107057697)
                      ·
                        rfl

theorem cell23_7418554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_7418554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418554 prefixEnd_7418554 := by exact prefixLift 7418554
  have htrace : WordTrace (prefixWord ++ tailWord_7418554) baseStart_7418554 baseEnd_7418554 := by
    simpa [prefixWord, tailWord_7418554, baseEnd_7418554] using wordTrace_append hprefix tailTrace_7418554
  have hstable : (prefixWord ++ tailWord_7418554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418554).length < 2 ^ (prefixWord ++ tailWord_7418554).sum := by decide
  have hdescent : baseEnd_7418554 < baseStart_7418554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418566 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7418566 : Nat := 118140960795 + 7418566 * 2 ^ 59
def prefixEnd_7418566 : Nat := 4983230072969 + 3 ^ 40 * 7418566 * 2
def baseEnd_7418566 : Nat := 3809290125102527060107643

theorem tailTrace_7418566 : CollatzResearch.WordTrace tailWord_7418566 prefixEnd_7418566 3809290125102527060107643 := by
  unfold tailWord_7418566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455541588806557720239611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180384887227873231365111701 8455541588806557720239611)
  ·
    refine ⟨12683312383209836580359417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8455541588806557720239611 12683312383209836580359417)
    ·
      refine ⟨9512484287407377435269563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12683312383209836580359417 9512484287407377435269563)
      ·
        refine ⟨14268726431111066152904345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9512484287407377435269563 14268726431111066152904345)
        ·
          refine ⟨10701544823333299614678259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14268726431111066152904345 10701544823333299614678259)
          ·
            refine ⟨16052317234999949422017389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701544823333299614678259 16052317234999949422017389)
            ·
              refine ⟨6019618963124981033256521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16052317234999949422017389 6019618963124981033256521)
              ·
                refine ⟨4514714222343735774942391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6019618963124981033256521 4514714222343735774942391)
                ·
                  refine ⟨6772071333515603662413587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514714222343735774942391 6772071333515603662413587)
                  ·
                    refine ⟨10158107000273405493620381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772071333515603662413587 10158107000273405493620381)
                    ·
                      refine ⟨3809290125102527060107643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158107000273405493620381 3809290125102527060107643)
                      ·
                        rfl

theorem cell23_7418566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7418566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418566 prefixEnd_7418566 := by exact prefixLift 7418566
  have htrace : WordTrace (prefixWord ++ tailWord_7418566) baseStart_7418566 baseEnd_7418566 := by
    simpa [prefixWord, tailWord_7418566, baseEnd_7418566] using wordTrace_append hprefix tailTrace_7418566
  have hstable : (prefixWord ++ tailWord_7418566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418566).length < 2 ^ (prefixWord ++ tailWord_7418566).sum := by decide
  have hdescent : baseEnd_7418566 < baseStart_7418566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418631 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7418631 : Nat := 118140960795 + 7418631 * 2 ^ 59
def prefixEnd_7418631 : Nat := 4983230072969 + 3 ^ 40 * 7418631 * 2
def baseEnd_7418631 : Nat := 3809323501345069305794843

theorem tailTrace_7418631 : CollatzResearch.WordTrace tailWord_7418631 prefixEnd_7418631 3809323501345069305794843 := by
  unfold tailWord_7418631
  simp only [CollatzResearch.WordTrace]
  refine ⟨270579701586574363148783747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180386467724382908765855831 270579701586574363148783747)
  ·
    refine ⟨405869552379861544723175621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270579701586574363148783747 405869552379861544723175621)
    ·
      refine ⟨76100541071224039635595429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405869552379861544723175621 76100541071224039635595429)
      ·
        refine ⟨14268851450854507431674143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76100541071224039635595429 14268851450854507431674143)
        ·
          refine ⟨21403277176281761147511215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14268851450854507431674143 21403277176281761147511215)
          ·
            refine ⟨32104915764422641721266823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21403277176281761147511215 32104915764422641721266823)
            ·
              refine ⟨48157373646633962581900235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32104915764422641721266823 48157373646633962581900235)
              ·
                refine ⟨72236060469950943872850353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48157373646633962581900235 72236060469950943872850353)
                ·
                  refine ⟨54177045352463207904637765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72236060469950943872850353 54177045352463207904637765)
                  ·
                    refine ⟨10158196003586851482119581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54177045352463207904637765 10158196003586851482119581)
                    ·
                      refine ⟨3809323501345069305794843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158196003586851482119581 3809323501345069305794843)
                      ·
                        rfl

theorem cell23_7418631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7418631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418631 prefixEnd_7418631 := by exact prefixLift 7418631
  have htrace : WordTrace (prefixWord ++ tailWord_7418631) baseStart_7418631 baseEnd_7418631 := by
    simpa [prefixWord, tailWord_7418631, baseEnd_7418631] using wordTrace_append hprefix tailTrace_7418631
  have hstable : (prefixWord ++ tailWord_7418631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418631).length < 2 ^ (prefixWord ++ tailWord_7418631).sum := by decide
  have hdescent : baseEnd_7418631 < baseStart_7418631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418634 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_7418634 : Nat := 118140960795 + 7418634 * 2 ^ 59
def prefixEnd_7418634 : Nat := 4983230072969 + 3 ^ 40 * 7418634 * 2
def baseEnd_7418634 : Nat := 423258337976336977117481

theorem tailTrace_7418634 : CollatzResearch.WordTrace tailWord_7418634 prefixEnd_7418634 423258337976336977117481 := by
  unfold tailWord_7418634
  simp only [CollatzResearch.WordTrace]
  refine ⟨67644952751390873665285739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180386540670375663107428637 67644952751390873665285739)
  ·
    refine ⟨101467429127086310497928609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67644952751390873665285739 101467429127086310497928609)
    ·
      refine ⟨76100571845314732873446457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101467429127086310497928609 76100571845314732873446457)
      ·
        refine ⟨57075428883986049655084843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76100571845314732873446457 57075428883986049655084843)
        ·
          refine ⟨85613143325979074482627265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57075428883986049655084843 85613143325979074482627265)
          ·
            refine ⟨64209857494484305861970449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85613143325979074482627265 64209857494484305861970449)
            ·
              refine ⟨48157393120863229396477837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64209857494484305861970449 48157393120863229396477837)
              ·
                refine ⟨18059022420323711023679189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48157393120863229396477837 18059022420323711023679189)
                ·
                  refine ⟨423258337976336977117481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18059022420323711023679189 423258337976336977117481)
                  ·
                    rfl

theorem cell23_7418634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_7418634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418634 prefixEnd_7418634 := by exact prefixLift 7418634
  have htrace : WordTrace (prefixWord ++ tailWord_7418634) baseStart_7418634 baseEnd_7418634 := by
    simpa [prefixWord, tailWord_7418634, baseEnd_7418634] using wordTrace_append hprefix tailTrace_7418634
  have hstable : (prefixWord ++ tailWord_7418634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418634).length < 2 ^ (prefixWord ++ tailWord_7418634).sum := by decide
  have hdescent : baseEnd_7418634 < baseStart_7418634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418666 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7418666 : Nat := 118140960795 + 7418666 * 2 ^ 59
def prefixEnd_7418666 : Nat := 4983230072969 + 3 ^ 40 * 7418666 * 2
def baseEnd_7418666 : Nat := 3809341473167976668857183

theorem tailTrace_7418666 : CollatzResearch.WordTrace tailWord_7418666 prefixEnd_7418666 3809341473167976668857183 := by
  unfold tailWord_7418666
  simp only [CollatzResearch.WordTrace]
  refine ⟨67645244535361891031576963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180387318760965042750871901 67645244535361891031576963)
  ·
    refine ⟨101467866803042836547365445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67645244535361891031576963 101467866803042836547365445)
    ·
      refine ⟨19025225025570531852631021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101467866803042836547365445 19025225025570531852631021)
      ·
        refine ⟨7134459384588949444736633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19025225025570531852631021 7134459384588949444736633)
        ·
          refine ⟨5350844538441712083552475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7134459384588949444736633 5350844538441712083552475)
          ·
            refine ⟨8026266807662568125328713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350844538441712083552475 8026266807662568125328713)
            ·
              refine ⟨6019700105746926093996535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8026266807662568125328713 6019700105746926093996535)
              ·
                refine ⟨9029550158620389140994803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019700105746926093996535 9029550158620389140994803)
                ·
                  refine ⟨13544325237930583711492205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029550158620389140994803 13544325237930583711492205)
                  ·
                    refine ⟨5079121964223968891809577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13544325237930583711492205 5079121964223968891809577)
                    ·
                      refine ⟨3809341473167976668857183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079121964223968891809577 3809341473167976668857183)
                      ·
                        rfl

theorem cell23_7418666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7418666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418666 prefixEnd_7418666 := by exact prefixLift 7418666
  have htrace : WordTrace (prefixWord ++ tailWord_7418666) baseStart_7418666 baseEnd_7418666 := by
    simpa [prefixWord, tailWord_7418666, baseEnd_7418666] using wordTrace_append hprefix tailTrace_7418666
  have hstable : (prefixWord ++ tailWord_7418666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418666).length < 2 ^ (prefixWord ++ tailWord_7418666).sum := by decide
  have hdescent : baseEnd_7418666 < baseStart_7418666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418741 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 8]
def baseStart_7418741 : Nat := 118140960795 + 7418741 * 2 ^ 59
def prefixEnd_7418741 : Nat := 4983230072969 + 3 ^ 40 * 7418741 * 2
def baseEnd_7418741 : Nat := 423264442690784875046593

theorem tailTrace_7418741 : CollatzResearch.WordTrace tailWord_7418741 prefixEnd_7418741 423264442690784875046593 := by
  unfold tailWord_7418741
  simp only [CollatzResearch.WordTrace]
  refine ⟨270583713616175851935288077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180389142410783901290192051 270583713616175851935288077)
  ·
    refine ⟨101468892606065944475733029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270583713616175851935288077 101468892606065944475733029)
    ·
      refine ⟨19025417363637364589199943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101468892606065944475733029 19025417363637364589199943)
      ·
        refine ⟨28538126045456046883799915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19025417363637364589199943 28538126045456046883799915)
        ·
          refine ⟨42807189068184070325699873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28538126045456046883799915 42807189068184070325699873)
          ·
            refine ⟨32105391801138052744274905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42807189068184070325699873 32105391801138052744274905)
            ·
              refine ⟨24079043850853539558206179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32105391801138052744274905 24079043850853539558206179)
              ·
                refine ⟨36118565776280309337309269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24079043850853539558206179 36118565776280309337309269)
                ·
                  refine ⟨423264442690784875046593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36118565776280309337309269 423264442690784875046593)
                  ·
                    rfl

theorem cell23_7418741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_7418741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418741 prefixEnd_7418741 := by exact prefixLift 7418741
  have htrace : WordTrace (prefixWord ++ tailWord_7418741) baseStart_7418741 baseEnd_7418741 := by
    simpa [prefixWord, tailWord_7418741, baseEnd_7418741] using wordTrace_append hprefix tailTrace_7418741
  have hstable : (prefixWord ++ tailWord_7418741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418741).length < 2 ^ (prefixWord ++ tailWord_7418741).sum := by decide
  have hdescent : baseEnd_7418741 < baseStart_7418741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418744 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_7418744 : Nat := 118140960795 + 7418744 * 2 ^ 59
def prefixEnd_7418744 : Nat := 4983230072969 + 3 ^ 40 * 7418744 * 2
def baseEnd_7418744 : Nat := 3809381524659027363681823

theorem tailTrace_7418744 : CollatzResearch.WordTrace tailWord_7418744 prefixEnd_7418744 3809381524659027363681823 := by
  unfold tailWord_7418744
  simp only [CollatzResearch.WordTrace]
  refine ⟨135291911517582491723823643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180389215356776655631764857 135291911517582491723823643)
  ·
    refine ⟨202937867276373737585735465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135291911517582491723823643 202937867276373737585735465)
    ·
      refine ⟨152203400457280303189301599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202937867276373737585735465 152203400457280303189301599)
      ·
        refine ⟨228305100685920454783952399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152203400457280303189301599 228305100685920454783952399)
        ·
          refine ⟨342457651028880682175928599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228305100685920454783952399 342457651028880682175928599)
          ·
            refine ⟨513686476543321023263892899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342457651028880682175928599 513686476543321023263892899)
            ·
              refine ⟨770529714814981534895839349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513686476543321023263892899 770529714814981534895839349)
              ·
                refine ⟨72237160763904518896484939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 770529714814981534895839349 72237160763904518896484939)
                ·
                  refine ⟨108355741145856778344727409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72237160763904518896484939 108355741145856778344727409)
                  ·
                    refine ⟨81266805859392583758545557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108355741145856778344727409 81266805859392583758545557)
                    ·
                      refine ⟨3809381524659027363681823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81266805859392583758545557 3809381524659027363681823)
                      ·
                        rfl

theorem cell23_7418744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_7418744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418744 prefixEnd_7418744 := by exact prefixLift 7418744
  have htrace : WordTrace (prefixWord ++ tailWord_7418744) baseStart_7418744 baseEnd_7418744 := by
    simpa [prefixWord, tailWord_7418744, baseEnd_7418744] using wordTrace_append hprefix tailTrace_7418744
  have hstable : (prefixWord ++ tailWord_7418744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418744).length < 2 ^ (prefixWord ++ tailWord_7418744).sum := by decide
  have hdescent : baseEnd_7418744 < baseStart_7418744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418771 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 1, 5]
def baseStart_7418771 : Nat := 118140960795 + 7418771 * 2 ^ 59
def prefixEnd_7418771 : Nat := 4983230072969 + 3 ^ 40 * 7418771 * 2
def baseEnd_7418771 : Nat := 1269798462878899586014733

theorem tailTrace_7418771 : CollatzResearch.WordTrace tailWord_7418771 prefixEnd_7418771 1269798462878899586014733 := by
  unfold tailWord_7418771
  simp only [CollatzResearch.WordTrace]
  refine ⟨270584807806067167058880167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180389871870711444705920111 270584807806067167058880167)
  ·
    refine ⟨405877211709100750588320251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270584807806067167058880167 405877211709100750588320251)
    ·
      refine ⟨608815817563651125882480377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405877211709100750588320251 608815817563651125882480377)
      ·
        refine ⟨456611863172738344411860283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608815817563651125882480377 456611863172738344411860283)
        ·
          refine ⟨684917794759107516617790425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456611863172738344411860283 684917794759107516617790425)
          ·
            refine ⟨513688346069330637463342819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684917794759107516617790425 513688346069330637463342819)
            ·
              refine ⟨770532519103995956195014229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513688346069330637463342819 770532519103995956195014229)
              ·
                refine ⟨9029677958249952611660323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 770532519103995956195014229 9029677958249952611660323)
                ·
                  refine ⟨13544516937374928917490485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029677958249952611660323 13544516937374928917490485)
                  ·
                    refine ⟨1269798462878899586014733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13544516937374928917490485 1269798462878899586014733)
                    ·
                      rfl

theorem cell23_7418771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 5].length) (baseStart_7418771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418771 prefixEnd_7418771 := by exact prefixLift 7418771
  have htrace : WordTrace (prefixWord ++ tailWord_7418771) baseStart_7418771 baseEnd_7418771 := by
    simpa [prefixWord, tailWord_7418771, baseEnd_7418771] using wordTrace_append hprefix tailTrace_7418771
  have hstable : (prefixWord ++ tailWord_7418771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418771).length < 2 ^ (prefixWord ++ tailWord_7418771).sum := by decide
  have hdescent : baseEnd_7418771 < baseStart_7418771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418828 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7418828 : Nat := 118140960795 + 7418828 * 2 ^ 59
def prefixEnd_7418828 : Nat := 4983230072969 + 3 ^ 40 * 7418828 * 2
def baseEnd_7418828 : Nat := 3809424657034005035031437

theorem tailTrace_7418828 : CollatzResearch.WordTrace tailWord_7418828 prefixEnd_7418828 3809424657034005035031437 := by
  unfold tailWord_7418828
  simp only [CollatzResearch.WordTrace]
  refine ⟨135293443383430332896852569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180391257844573777195803425 135293443383430332896852569)
  ·
    refine ⟨101470082537572749672639427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135293443383430332896852569 101470082537572749672639427)
    ·
      refine ⟨152205123806359124508959141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101470082537572749672639427 152205123806359124508959141)
      ·
        refine ⟨28538460713692335845429839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152205123806359124508959141 28538460713692335845429839)
        ·
          refine ⟨42807691070538503768144759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28538460713692335845429839 42807691070538503768144759)
          ·
            refine ⟨64211536605807755652217139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42807691070538503768144759 64211536605807755652217139)
            ·
              refine ⟨96317304908711633478325709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64211536605807755652217139 96317304908711633478325709)
              ·
                refine ⟨36118989340766862554372141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96317304908711633478325709 36118989340766862554372141)
                ·
                  refine ⟨13544621002787573457889553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36118989340766862554372141 13544621002787573457889553)
                  ·
                    refine ⟨10158465752090680093417165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13544621002787573457889553 10158465752090680093417165)
                    ·
                      refine ⟨3809424657034005035031437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158465752090680093417165 3809424657034005035031437)
                      ·
                        rfl

theorem cell23_7418828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7418828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418828 prefixEnd_7418828 := by exact prefixLift 7418828
  have htrace : WordTrace (prefixWord ++ tailWord_7418828) baseStart_7418828 baseEnd_7418828 := by
    simpa [prefixWord, tailWord_7418828, baseEnd_7418828] using wordTrace_append hprefix tailTrace_7418828
  have hstable : (prefixWord ++ tailWord_7418828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418828).length < 2 ^ (prefixWord ++ tailWord_7418828).sum := by decide
  have hdescent : baseEnd_7418828 < baseStart_7418828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418842 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4]
def baseStart_7418842 : Nat := 118140960795 + 7418842 * 2 ^ 59
def prefixEnd_7418842 : Nat := 4983230072969 + 3 ^ 40 * 7418842 * 2
def baseEnd_7418842 : Nat := 3809431845763167980256373

theorem tailTrace_7418842 : CollatzResearch.WordTrace tailWord_7418842 prefixEnd_7418842 3809431845763167980256373 := by
  unfold tailWord_7418842
  simp only [CollatzResearch.WordTrace]
  refine ⟨67646849347202486546178695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180391598259206630789809853 67646849347202486546178695)
  ·
    refine ⟨101470274020803729819268043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67646849347202486546178695 101470274020803729819268043)
    ·
      refine ⟨152205411031205594728902065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101470274020803729819268043 152205411031205594728902065)
      ·
        refine ⟨114154058273404196046676549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152205411031205594728902065 114154058273404196046676549)
        ·
          refine ⟨21403885926263286758751853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114154058273404196046676549 21403885926263286758751853)
          ·
            refine ⟨8026457222348732534531945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21403885926263286758751853 8026457222348732534531945)
            ·
              refine ⟨6019842916761549400898959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8026457222348732534531945 6019842916761549400898959)
              ·
                refine ⟨9029764375142324101348439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019842916761549400898959 9029764375142324101348439)
                ·
                  refine ⟨13544646562713486152022659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029764375142324101348439 13544646562713486152022659)
                  ·
                    refine ⟨20316969844070229228033989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13544646562713486152022659 20316969844070229228033989)
                    ·
                      refine ⟨3809431845763167980256373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20316969844070229228033989 3809431845763167980256373)
                      ·
                        rfl

theorem cell23_7418842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_7418842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418842 prefixEnd_7418842 := by exact prefixLift 7418842
  have htrace : WordTrace (prefixWord ++ tailWord_7418842) baseStart_7418842 baseEnd_7418842 := by
    simpa [prefixWord, tailWord_7418842, baseEnd_7418842] using wordTrace_append hprefix tailTrace_7418842
  have hstable : (prefixWord ++ tailWord_7418842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418842).length < 2 ^ (prefixWord ++ tailWord_7418842).sum := by decide
  have hdescent : baseEnd_7418842 < baseStart_7418842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418869 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7418869 : Nat := 118140960795 + 7418869 * 2 ^ 59
def prefixEnd_7418869 : Nat := 4983230072969 + 3 ^ 40 * 7418869 * 2
def baseEnd_7418869 : Nat := 1269815236580279791539583

theorem tailTrace_7418869 : CollatzResearch.WordTrace tailWord_7418869 prefixEnd_7418869 1269815236580279791539583 := by
  unfold tailWord_7418869
  simp only [CollatzResearch.WordTrace]
  refine ⟨270588382159712129795947661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180392254773141419863965107 270588382159712129795947661)
  ·
    refine ⟨101470643309892048673480373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270588382159712129795947661 101470643309892048673480373)
    ·
      refine ⟨9512872810302379563138785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101470643309892048673480373 9512872810302379563138785)
      ·
        refine ⟨7134654607726784672354089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9512872810302379563138785 7134654607726784672354089)
        ·
          refine ⟨5350990955795088504265567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7134654607726784672354089 5350990955795088504265567)
          ·
            refine ⟨8026486433692632756398351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350990955795088504265567 8026486433692632756398351)
            ·
              refine ⟨12039729650538949134597527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026486433692632756398351 12039729650538949134597527)
              ·
                refine ⟨18059594475808423701896291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12039729650538949134597527 18059594475808423701896291)
                ·
                  refine ⟨27089391713712635552844437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18059594475808423701896291 27089391713712635552844437)
                  ·
                    refine ⟨1269815236580279791539583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27089391713712635552844437 1269815236580279791539583)
                    ·
                      rfl

theorem cell23_7418869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7418869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418869 prefixEnd_7418869 := by exact prefixLift 7418869
  have htrace : WordTrace (prefixWord ++ tailWord_7418869) baseStart_7418869 baseEnd_7418869 := by
    simpa [prefixWord, tailWord_7418869, baseEnd_7418869] using wordTrace_append hprefix tailTrace_7418869
  have hstable : (prefixWord ++ tailWord_7418869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418869).length < 2 ^ (prefixWord ++ tailWord_7418869).sum := by decide
  have hdescent : baseEnd_7418869 < baseStart_7418869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418968 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_7418968 : Nat := 118140960795 + 7418968 * 2 ^ 59
def prefixEnd_7418968 : Nat := 4983230072969 + 3 ^ 40 * 7418968 * 2
def baseEnd_7418968 : Nat := 1269832181441878162426931

theorem tailTrace_7418968 : CollatzResearch.WordTrace tailWord_7418968 prefixEnd_7418968 1269832181441878162426931 := by
  unfold tailWord_7418968
  simp only [CollatzResearch.WordTrace]
  refine ⟨135295996493176734851900779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180394661990902313135867705 135295996493176734851900779)
  ·
    refine ⟨202943994739765102277851169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135295996493176734851900779 202943994739765102277851169)
    ·
      refine ⟨152207996054823826708388377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202943994739765102277851169 152207996054823826708388377)
      ·
        refine ⟨114155997041117870031291283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152207996054823826708388377 114155997041117870031291283)
        ·
          refine ⟨171233995561676805046936925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114155997041117870031291283 171233995561676805046936925)
          ·
            refine ⟨64212748335628801892601347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171233995561676805046936925 64212748335628801892601347)
            ·
              refine ⟨96319122503443202838902021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64212748335628801892601347 96319122503443202838902021)
              ·
                refine ⟨18059835469395600532294129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96319122503443202838902021 18059835469395600532294129)
                ·
                  refine ⟨13544876602046700399220597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18059835469395600532294129 13544876602046700399220597)
                  ·
                    refine ⟨1269832181441878162426931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13544876602046700399220597 1269832181441878162426931)
                    ·
                      rfl

theorem cell23_7418968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_7418968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418968 prefixEnd_7418968 := by exact prefixLift 7418968
  have htrace : WordTrace (prefixWord ++ tailWord_7418968) baseStart_7418968 baseEnd_7418968 := by
    simpa [prefixWord, tailWord_7418968, baseEnd_7418968] using wordTrace_append hprefix tailTrace_7418968
  have hstable : (prefixWord ++ tailWord_7418968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418968).length < 2 ^ (prefixWord ++ tailWord_7418968).sum := by decide
  have hdescent : baseEnd_7418968 < baseStart_7418968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7418988 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_7418988 : Nat := 118140960795 + 7418988 * 2 ^ 59
def prefixEnd_7418988 : Nat := 4983230072969 + 3 ^ 40 * 7418988 * 2
def baseEnd_7418988 : Nat := 3809506813938724409030701

theorem tailTrace_7418988 : CollatzResearch.WordTrace tailWord_7418988 prefixEnd_7418988 3809506813938724409030701 := by
  unfold tailWord_7418988
  simp only [CollatzResearch.WordTrace]
  refine ⟨135296361223140506559764809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180395148297520675413019745 135296361223140506559764809)
  ·
    refine ⟨101472270917355379919823607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135296361223140506559764809 101472270917355379919823607)
    ·
      refine ⟨152208406376033069879735411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101472270917355379919823607 152208406376033069879735411)
      ·
        refine ⟨228312609564049604819603117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152208406376033069879735411 228312609564049604819603117)
        ·
          refine ⟨85617228586518601807351169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228312609564049604819603117 85617228586518601807351169)
          ·
            refine ⟨64212921439888951355513377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85617228586518601807351169 64212921439888951355513377)
            ·
              refine ⟨48159691079916713516635033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64212921439888951355513377 48159691079916713516635033)
              ·
                refine ⟨36119768309937535137476275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48159691079916713516635033 36119768309937535137476275)
                ·
                  refine ⟨54179652464906302706214413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36119768309937535137476275 54179652464906302706214413)
                  ·
                    refine ⟨20317369674339863514830405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54179652464906302706214413 20317369674339863514830405)
                    ·
                      refine ⟨3809506813938724409030701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20317369674339863514830405 3809506813938724409030701)
                      ·
                        rfl

theorem cell23_7418988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_7418988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7418988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7418988 prefixEnd_7418988 := by exact prefixLift 7418988
  have htrace : WordTrace (prefixWord ++ tailWord_7418988) baseStart_7418988 baseEnd_7418988 := by
    simpa [prefixWord, tailWord_7418988, baseEnd_7418988] using wordTrace_append hprefix tailTrace_7418988
  have hstable : (prefixWord ++ tailWord_7418988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7418988).length < 2 ^ (prefixWord ++ tailWord_7418988).sum := by decide
  have hdescent : baseEnd_7418988 < baseStart_7418988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7418988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419005 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_7419005 : Nat := 118140960795 + 7419005 * 2 ^ 59
def prefixEnd_7419005 : Nat := 4983230072969 + 3 ^ 40 * 7419005 * 2
def baseEnd_7419005 : Nat := 3809515543109850842518123

theorem tailTrace_7419005 : CollatzResearch.WordTrace tailWord_7419005 prefixEnd_7419005 3809515543109850842518123 := by
  unfold tailWord_7419005
  simp only [CollatzResearch.WordTrace]
  refine ⟨270593342487219425022898469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180395561658146283348598979 270593342487219425022898469)
  ·
    refine ⟨50736251716353642191793463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270593342487219425022898469 50736251716353642191793463)
    ·
      refine ⟨76104377574530463287690195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50736251716353642191793463 76104377574530463287690195)
      ·
        refine ⟨114156566361795694931535293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76104377574530463287690195 114156566361795694931535293)
        ·
          refine ⟨42808712385673385599325735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114156566361795694931535293 42808712385673385599325735)
          ·
            refine ⟨64213068578510078398988603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42808712385673385599325735 64213068578510078398988603)
            ·
              refine ⟨96319602867765117598482905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64213068578510078398988603 96319602867765117598482905)
              ·
                refine ⟨72239702150823838198862179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96319602867765117598482905 72239702150823838198862179)
                ·
                  refine ⟨108359553226235757298293269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72239702150823838198862179 108359553226235757298293269)
                  ·
                    refine ⟨5079354057479801123357497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108359553226235757298293269 5079354057479801123357497)
                    ·
                      refine ⟨3809515543109850842518123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079354057479801123357497 3809515543109850842518123)
                      ·
                        rfl

theorem cell23_7419005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_7419005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419005 prefixEnd_7419005 := by exact prefixLift 7419005
  have htrace : WordTrace (prefixWord ++ tailWord_7419005) baseStart_7419005 baseEnd_7419005 := by
    simpa [prefixWord, tailWord_7419005, baseEnd_7419005] using wordTrace_append hprefix tailTrace_7419005
  have hstable : (prefixWord ++ tailWord_7419005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419005).length < 2 ^ (prefixWord ++ tailWord_7419005).sum := by decide
  have hdescent : baseEnd_7419005 < baseStart_7419005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419018 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7419018 : Nat := 118140960795 + 7419018 * 2 ^ 59
def prefixEnd_7419018 : Nat := 4983230072969 + 3 ^ 40 * 7419018 * 2
def baseEnd_7419018 : Nat := 3809522218358359291655563

theorem tailTrace_7419018 : CollatzResearch.WordTrace tailWord_7419018 prefixEnd_7419018 3809522218358359291655563 := by
  unfold tailWord_7419018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67648454159043082060780427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180395877757448218828747805 67648454159043082060780427)
  ·
    refine ⟨101472681238564623091170641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67648454159043082060780427 101472681238564623091170641)
    ·
      refine ⟨76104510928923467318377981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101472681238564623091170641 76104510928923467318377981)
      ·
        refine ⟨28539191598346300244391743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76104510928923467318377981 28539191598346300244391743)
        ·
          refine ⟨42808787397519450366587615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28539191598346300244391743 42808787397519450366587615)
          ·
            refine ⟨64213181096279175549881423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42808787397519450366587615 64213181096279175549881423)
            ·
              refine ⟨96319771644418763324822135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64213181096279175549881423 96319771644418763324822135)
              ·
                refine ⟨144479657466628144987233203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96319771644418763324822135 144479657466628144987233203)
                ·
                  refine ⟨216719486199942217480849805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144479657466628144987233203 216719486199942217480849805)
                  ·
                    refine ⟨81269807324978331555318677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216719486199942217480849805 81269807324978331555318677)
                    ·
                      refine ⟨3809522218358359291655563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81269807324978331555318677 3809522218358359291655563)
                      ·
                        rfl

theorem cell23_7419018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7419018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419018 prefixEnd_7419018 := by exact prefixLift 7419018
  have htrace : WordTrace (prefixWord ++ tailWord_7419018) baseStart_7419018 baseEnd_7419018 := by
    simpa [prefixWord, tailWord_7419018, baseEnd_7419018] using wordTrace_append hprefix tailTrace_7419018
  have hstable : (prefixWord ++ tailWord_7419018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419018).length < 2 ^ (prefixWord ++ tailWord_7419018).sum := by decide
  have hdescent : baseEnd_7419018 < baseStart_7419018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419022 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7419022 : Nat := 118140960795 + 7419022 * 2 ^ 59
def prefixEnd_7419022 : Nat := 4983230072969 + 3 ^ 40 * 7419022 * 2
def baseEnd_7419022 : Nat := 3809524272280977276005545

theorem tailTrace_7419022 : CollatzResearch.WordTrace tailWord_7419022 prefixEnd_7419022 3809524272280977276005545 := by
  unfold tailWord_7419022
  simp only [CollatzResearch.WordTrace]
  refine ⟨33824245316019729615783415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180395975018771891284178213 33824245316019729615783415)
  ·
    refine ⟨50736367974029594423675123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33824245316019729615783415 50736367974029594423675123)
    ·
      refine ⟨76104551961044391635512685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50736367974029594423675123 76104551961044391635512685)
      ·
        refine ⟨28539206985391646863317257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76104551961044391635512685 28539206985391646863317257)
        ·
          refine ⟨21404405239043735147487943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28539206985391646863317257 21404405239043735147487943)
          ·
            refine ⟨32106607858565602721231915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21404405239043735147487943 32106607858565602721231915)
            ·
              refine ⟨48159911787848404081847873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32106607858565602721231915 48159911787848404081847873)
              ·
                refine ⟨36119933840886303061385905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48159911787848404081847873 36119933840886303061385905)
                ·
                  refine ⟨27089950380664727296039429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36119933840886303061385905 27089950380664727296039429)
                  ·
                    refine ⟨5079365696374636368007393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27089950380664727296039429 5079365696374636368007393)
                    ·
                      refine ⟨3809524272280977276005545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079365696374636368007393 3809524272280977276005545)
                      ·
                        rfl

theorem cell23_7419022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7419022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419022 prefixEnd_7419022 := by exact prefixLift 7419022
  have htrace : WordTrace (prefixWord ++ tailWord_7419022) baseStart_7419022 baseEnd_7419022 := by
    simpa [prefixWord, tailWord_7419022, baseEnd_7419022] using wordTrace_append hprefix tailTrace_7419022
  have hstable : (prefixWord ++ tailWord_7419022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419022).length < 2 ^ (prefixWord ++ tailWord_7419022).sum := by decide
  have hdescent : baseEnd_7419022 < baseStart_7419022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419032 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 3, 4]
def baseStart_7419032 : Nat := 118140960795 + 7419032 * 2 ^ 59
def prefixEnd_7419032 : Nat := 4983230072969 + 3 ^ 40 * 7419032 * 2
def baseEnd_7419032 : Nat := 1269843135695840745626833

theorem tailTrace_7419032 : CollatzResearch.WordTrace tailWord_7419032 prefixEnd_7419032 1269843135695840745626833 := by
  unfold tailWord_7419032
  simp only [CollatzResearch.WordTrace]
  refine ⟨135297163629060804317065675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180396218172081072422754233 135297163629060804317065675)
  ·
    refine ⟨202945745443591206475598513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135297163629060804317065675 202945745443591206475598513)
    ·
      refine ⟨152209309082693404856698885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202945745443591206475598513 152209309082693404856698885)
      ·
        refine ⟨28539245453005013410631041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152209309082693404856698885 28539245453005013410631041)
        ·
          refine ⟨21404434089753760057973281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28539245453005013410631041 21404434089753760057973281)
          ·
            refine ⟨16053325567315320043479961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21404434089753760057973281 16053325567315320043479961)
            ·
              refine ⟨12039994175486490032609971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16053325567315320043479961 12039994175486490032609971)
              ·
                refine ⟨18059991263229735048914957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12039994175486490032609971 18059991263229735048914957)
                ·
                  refine ⟨6772496723711150643343109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18059991263229735048914957 6772496723711150643343109)
                  ·
                    refine ⟨1269843135695840745626833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6772496723711150643343109 1269843135695840745626833)
                    ·
                      rfl

theorem cell23_7419032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_7419032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419032 prefixEnd_7419032 := by exact prefixLift 7419032
  have htrace : WordTrace (prefixWord ++ tailWord_7419032) baseStart_7419032 baseEnd_7419032 := by
    simpa [prefixWord, tailWord_7419032, baseEnd_7419032] using wordTrace_append hprefix tailTrace_7419032
  have hstable : (prefixWord ++ tailWord_7419032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419032).length < 2 ^ (prefixWord ++ tailWord_7419032).sum := by decide
  have hdescent : baseEnd_7419032 < baseStart_7419032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419082 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_7419082 : Nat := 118140960795 + 7419082 * 2 ^ 59
def prefixEnd_7419082 : Nat := 4983230072969 + 3 ^ 40 * 7419082 * 2
def baseEnd_7419082 : Nat := 3809555081120247041255269

theorem tailTrace_7419082 : CollatzResearch.WordTrace tailWord_7419082 prefixEnd_7419082 3809555081120247041255269 := by
  unfold tailWord_7419082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67649037726985116793362875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180397433938626978115634333 67649037726985116793362875)
  ·
    refine ⟨101473556590477675190044313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67649037726985116793362875 101473556590477675190044313)
    ·
      refine ⟨76105167442858256392533235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101473556590477675190044313 76105167442858256392533235)
      ·
        refine ⟨114157751164287384588799853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76105167442858256392533235 114157751164287384588799853)
        ·
          refine ⟨42809156686607769220799945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114157751164287384588799853 42809156686607769220799945)
          ·
            refine ⟨32106867514955826915599959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42809156686607769220799945 32106867514955826915599959)
            ·
              refine ⟨48160301272433740373399939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32106867514955826915599959 48160301272433740373399939)
              ·
                refine ⟨72240451908650610560099909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48160301272433740373399939 72240451908650610560099909)
                ·
                  refine ⟨13545084732871989480018733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72240451908650610560099909 13545084732871989480018733)
                  ·
                    refine ⟨5079406774826996055007025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13545084732871989480018733 5079406774826996055007025)
                    ·
                      refine ⟨3809555081120247041255269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079406774826996055007025 3809555081120247041255269)
                      ·
                        rfl

theorem cell23_7419082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_7419082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419082 prefixEnd_7419082 := by exact prefixLift 7419082
  have htrace : WordTrace (prefixWord ++ tailWord_7419082) baseStart_7419082 baseEnd_7419082 := by
    simpa [prefixWord, tailWord_7419082, baseEnd_7419082] using wordTrace_append hprefix tailTrace_7419082
  have hstable : (prefixWord ++ tailWord_7419082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419082).length < 2 ^ (prefixWord ++ tailWord_7419082).sum := by decide
  have hdescent : baseEnd_7419082 < baseStart_7419082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419109 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_7419109 : Nat := 118140960795 + 7419109 * 2 ^ 59
def prefixEnd_7419109 : Nat := 4983230072969 + 3 ^ 40 * 7419109 * 2
def baseEnd_7419109 : Nat := 1269856315032639478539215

theorem tailTrace_7419109 : CollatzResearch.WordTrace tailWord_7419109 prefixEnd_7419109 1269856315032639478539215 := by
  unfold tailWord_7419109
  simp only [CollatzResearch.WordTrace]
  refine ⟨270597135678842650784684381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180398090452561767189789587 270597135678842650784684381)
  ·
    refine ⟨101473925879565994044256643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270597135678842650784684381 101473925879565994044256643)
    ·
      refine ⟨152210888819348991066384965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101473925879565994044256643 152210888819348991066384965)
      ·
        refine ⟨28539541653627935824947181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152210888819348991066384965 28539541653627935824947181)
        ·
          refine ⟨10702328120110475934355193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28539541653627935824947181 10702328120110475934355193)
          ·
            refine ⟨8026746090082856950766395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10702328120110475934355193 8026746090082856950766395)
            ·
              refine ⟨12040119135124285426149593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026746090082856950766395 12040119135124285426149593)
              ·
                refine ⟨9030089351343214069612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12040119135124285426149593 9030089351343214069612195)
                ·
                  refine ⟨13545134027014821104418293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9030089351343214069612195 13545134027014821104418293)
                  ·
                    refine ⟨1269856315032639478539215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13545134027014821104418293 1269856315032639478539215)
                    ·
                      rfl

theorem cell23_7419109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_7419109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419109 prefixEnd_7419109 := by exact prefixLift 7419109
  have htrace : WordTrace (prefixWord ++ tailWord_7419109) baseStart_7419109 baseEnd_7419109 := by
    simpa [prefixWord, tailWord_7419109, baseEnd_7419109] using wordTrace_append hprefix tailTrace_7419109
  have hstable : (prefixWord ++ tailWord_7419109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419109).length < 2 ^ (prefixWord ++ tailWord_7419109).sum := by decide
  have hdescent : baseEnd_7419109 < baseStart_7419109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419122 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_7419122 : Nat := 118140960795 + 7419122 * 2 ^ 59
def prefixEnd_7419122 : Nat := 4983230072969 + 3 ^ 40 * 7419122 * 2
def baseEnd_7419122 : Nat := 1269858540115475628251695

theorem tailTrace_7419122 : CollatzResearch.WordTrace tailWord_7419122 prefixEnd_7419122 1269858540115475628251695 := by
  unfold tailWord_7419122
  simp only [CollatzResearch.WordTrace]
  refine ⟨67649402456948888501226905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180398406551863702669938413 67649402456948888501226905)
  ·
    refine ⟨50737051842711666375920179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67649402456948888501226905 50737051842711666375920179)
    ·
      refine ⟨76105577764067499563880269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50737051842711666375920179 76105577764067499563880269)
      ·
        refine ⟨28539591661525312336455101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76105577764067499563880269 28539591661525312336455101)
        ·
          refine ⟨10702346873071992126170663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28539591661525312336455101 10702346873071992126170663)
          ·
            refine ⟨16053520309607988189255995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10702346873071992126170663 16053520309607988189255995)
            ·
              refine ⟨24080280464411982283883993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16053520309607988189255995 24080280464411982283883993)
              ·
                refine ⟨18060210348308986712912995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24080280464411982283883993 18060210348308986712912995)
                ·
                  refine ⟨27090315522463480069369493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18060210348308986712912995 27090315522463480069369493)
                  ·
                    refine ⟨1269858540115475628251695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27090315522463480069369493 1269858540115475628251695)
                    ·
                      rfl

theorem cell23_7419122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_7419122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419122 prefixEnd_7419122 := by exact prefixLift 7419122
  have htrace : WordTrace (prefixWord ++ tailWord_7419122) baseStart_7419122 baseEnd_7419122 := by
    simpa [prefixWord, tailWord_7419122, baseEnd_7419122] using wordTrace_append hprefix tailTrace_7419122
  have hstable : (prefixWord ++ tailWord_7419122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419122).length < 2 ^ (prefixWord ++ tailWord_7419122).sum := by decide
  have hdescent : baseEnd_7419122 < baseStart_7419122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419145 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_7419145 : Nat := 118140960795 + 7419145 * 2 ^ 59
def prefixEnd_7419145 : Nat := 4983230072969 + 3 ^ 40 * 7419145 * 2
def baseEnd_7419145 : Nat := 3809587430401480294767479

theorem tailTrace_7419145 : CollatzResearch.WordTrace tailWord_7419145 prefixEnd_7419145 3809587430401480294767479 := by
  unfold tailWord_7419145
  simp only [CollatzResearch.WordTrace]
  refine ⟨270598448706712228932994889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180398965804474819288663259 270598448706712228932994889)
  ·
    refine ⟨202948836530034171699746167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270598448706712228932994889 202948836530034171699746167)
    ·
      refine ⟨304423254795051257549619251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202948836530034171699746167 304423254795051257549619251)
      ·
        refine ⟨456634882192576886324428877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304423254795051257549619251 456634882192576886324428877)
        ·
          refine ⟨171238080822216332371660829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456634882192576886324428877 171238080822216332371660829)
          ·
            refine ⟨64214280308331124639372811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171238080822216332371660829 64214280308331124639372811)
            ·
              refine ⟨96321420462496686959059217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64214280308331124639372811 96321420462496686959059217)
              ·
                refine ⟨72241065346872515219294413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96321420462496686959059217 72241065346872515219294413)
                ·
                  refine ⟨27090399505077193207235405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72241065346872515219294413 27090399505077193207235405)
                  ·
                    refine ⟨10158899814403947452713277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27090399505077193207235405 10158899814403947452713277)
                    ·
                      refine ⟨3809587430401480294767479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158899814403947452713277 3809587430401480294767479)
                      ·
                        rfl

theorem cell23_7419145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_7419145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419145 prefixEnd_7419145 := by exact prefixLift 7419145
  have htrace : WordTrace (prefixWord ++ tailWord_7419145) baseStart_7419145 baseEnd_7419145 := by
    simpa [prefixWord, tailWord_7419145, baseEnd_7419145] using wordTrace_append hprefix tailTrace_7419145
  have hstable : (prefixWord ++ tailWord_7419145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419145).length < 2 ^ (prefixWord ++ tailWord_7419145).sum := by decide
  have hdescent : baseEnd_7419145 < baseStart_7419145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419162 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_7419162 : Nat := 118140960795 + 7419162 * 2 ^ 59
def prefixEnd_7419162 : Nat := 4983230072969 + 3 ^ 40 * 7419162 * 2
def baseEnd_7419162 : Nat := 3809596159572606728254901

theorem tailTrace_7419162 : CollatzResearch.WordTrace tailWord_7419162 prefixEnd_7419162 3809596159572606728254901 := by
  unfold tailWord_7419162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67649767186912660209090935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180399379165100427224242493 67649767186912660209090935)
  ·
    refine ⟨101474650780368990313636403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67649767186912660209090935 101474650780368990313636403)
    ·
      refine ⟨152211976170553485470454605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101474650780368990313636403 152211976170553485470454605)
      ·
        refine ⟨57079491063957557051420477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152211976170553485470454605 57079491063957557051420477)
        ·
          refine ⟨21404809148984083894282679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57079491063957557051420477 21404809148984083894282679)
          ·
            refine ⟨32107213723476125841424019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21404809148984083894282679 32107213723476125841424019)
            ·
              refine ⟨48160820585214188762136029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32107213723476125841424019 48160820585214188762136029)
              ·
                refine ⟨18060307719455320785801011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48160820585214188762136029 18060307719455320785801011)
                ·
                  refine ⟨27090461579182981178701517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18060307719455320785801011 27090461579182981178701517)
                  ·
                    refine ⟨10158923092193617942013069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27090461579182981178701517 10158923092193617942013069)
                    ·
                      refine ⟨3809596159572606728254901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158923092193617942013069 3809596159572606728254901)
                      ·
                        rfl

theorem cell23_7419162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_7419162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419162 prefixEnd_7419162 := by exact prefixLift 7419162
  have htrace : WordTrace (prefixWord ++ tailWord_7419162) baseStart_7419162 baseEnd_7419162 := by
    simpa [prefixWord, tailWord_7419162, baseEnd_7419162] using wordTrace_append hprefix tailTrace_7419162
  have hstable : (prefixWord ++ tailWord_7419162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419162).length < 2 ^ (prefixWord ++ tailWord_7419162).sum := by decide
  have hdescent : baseEnd_7419162 < baseStart_7419162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419190 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7419190 : Nat := 118140960795 + 7419190 * 2 ^ 59
def prefixEnd_7419190 : Nat := 4983230072969 + 3 ^ 40 * 7419190 * 2
def baseEnd_7419190 : Nat := 1269870179010310872901591

theorem tailTrace_7419190 : CollatzResearch.WordTrace tailWord_7419190 prefixEnd_7419190 1269870179010310872901591 := by
  unfold tailWord_7419190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16912505624471825101148939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180400059994366134412255349 16912505624471825101148939)
  ·
    refine ⟨25368758436707737651723409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16912505624471825101148939 25368758436707737651723409)
    ·
      refine ⟨19026568827530803238792557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25368758436707737651723409 19026568827530803238792557)
      ·
        refine ⟨7134963310324051214547209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19026568827530803238792557 7134963310324051214547209)
        ·
          refine ⟨5351222482743038410910407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7134963310324051214547209 5351222482743038410910407)
          ·
            refine ⟨8026833724114557616365611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351222482743038410910407 8026833724114557616365611)
            ·
              refine ⟨12040250586171836424548417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026833724114557616365611 12040250586171836424548417)
              ·
                refine ⟨9030187939628877318411313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12040250586171836424548417 9030187939628877318411313)
                ·
                  refine ⟨6772640954721657988808485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030187939628877318411313 6772640954721657988808485)
                  ·
                    refine ⟨1269870179010310872901591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6772640954721657988808485 1269870179010310872901591)
                    ·
                      rfl

theorem cell23_7419190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7419190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419190 prefixEnd_7419190 := by exact prefixLift 7419190
  have htrace : WordTrace (prefixWord ++ tailWord_7419190) baseStart_7419190 baseEnd_7419190 := by
    simpa [prefixWord, tailWord_7419190, baseEnd_7419190] using wordTrace_append hprefix tailTrace_7419190
  have hstable : (prefixWord ++ tailWord_7419190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419190).length < 2 ^ (prefixWord ++ tailWord_7419190).sum := by decide
  have hdescent : baseEnd_7419190 < baseStart_7419190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419196 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_7419196 : Nat := 118140960795 + 7419196 * 2 ^ 59
def prefixEnd_7419196 : Nat := 4983230072969 + 3 ^ 40 * 7419196 * 2
def baseEnd_7419196 : Nat := 3809613617914859595229745

theorem tailTrace_7419196 : CollatzResearch.WordTrace tailWord_7419196 prefixEnd_7419196 3809613617914859595229745 := by
  unfold tailWord_7419196
  simp only [CollatzResearch.WordTrace]
  refine ⟨135300154414763732321550721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180400205886351643095400961 135300154414763732321550721)
  ·
    refine ⟨101475115811072799241163041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135300154414763732321550721 101475115811072799241163041)
    ·
      refine ⟨76106336858304599430872281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101475115811072799241163041 76106336858304599430872281)
      ·
        refine ⟨57079752643728449573154211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76106336858304599430872281 57079752643728449573154211)
        ·
          refine ⟨85619628965592674359731317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57079752643728449573154211 85619628965592674359731317)
          ·
            refine ⟨8026840215524313221224811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85619628965592674359731317 8026840215524313221224811)
            ·
              refine ⟨12040260323286469831837217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026840215524313221224811 12040260323286469831837217)
              ·
                refine ⟨9030195242464852373877913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12040260323286469831837217 9030195242464852373877913)
                ·
                  refine ⟨6772646431848639280408435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030195242464852373877913 6772646431848639280408435)
                  ·
                    refine ⟨10158969647772958920612653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772646431848639280408435 10158969647772958920612653)
                    ·
                      refine ⟨3809613617914859595229745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158969647772958920612653 3809613617914859595229745)
                      ·
                        rfl

theorem cell23_7419196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_7419196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419196 prefixEnd_7419196 := by exact prefixLift 7419196
  have htrace : WordTrace (prefixWord ++ tailWord_7419196) baseStart_7419196 baseEnd_7419196 := by
    simpa [prefixWord, tailWord_7419196, baseEnd_7419196] using wordTrace_append hprefix tailTrace_7419196
  have hstable : (prefixWord ++ tailWord_7419196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419196).length < 2 ^ (prefixWord ++ tailWord_7419196).sum := by decide
  have hdescent : baseEnd_7419196 < baseStart_7419196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419205 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_7419205 : Nat := 118140960795 + 7419205 * 2 ^ 59
def prefixEnd_7419205 : Nat := 4983230072969 + 3 ^ 40 * 7419205 * 2
def baseEnd_7419205 : Nat := 3809618239240750060017203

theorem tailTrace_7419205 : CollatzResearch.WordTrace tailWord_7419205 prefixEnd_7419205 3809618239240750060017203 := by
  unfold tailWord_7419205
  simp only [CollatzResearch.WordTrace]
  refine ⟨270600637086494859180179069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180400424724329906120119379 270600637086494859180179069)
  ·
    refine ⟨101475238907435572192567151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270600637086494859180179069 101475238907435572192567151)
    ·
      refine ⟨152212858361153358288850727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101475238907435572192567151 152212858361153358288850727)
      ·
        refine ⟨228319287541730037433276091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152212858361153358288850727 228319287541730037433276091)
        ·
          refine ⟨342478931312595056149914137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228319287541730037433276091 342478931312595056149914137)
          ·
            refine ⟨256859198484446292112435603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342478931312595056149914137 256859198484446292112435603)
            ·
              refine ⟨385288797726669438168653405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256859198484446292112435603 385288797726669438168653405)
              ·
                refine ⟨144483299147501039313245027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385288797726669438168653405 144483299147501039313245027)
                ·
                  refine ⟨216724948721251558969867541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144483299147501039313245027 216724948721251558969867541)
                  ·
                    refine ⟨10158981971308666826712541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216724948721251558969867541 10158981971308666826712541)
                    ·
                      refine ⟨3809618239240750060017203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158981971308666826712541 3809618239240750060017203)
                      ·
                        rfl

theorem cell23_7419205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_7419205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419205 prefixEnd_7419205 := by exact prefixLift 7419205
  have htrace : WordTrace (prefixWord ++ tailWord_7419205) baseStart_7419205 baseEnd_7419205 := by
    simpa [prefixWord, tailWord_7419205, baseEnd_7419205] using wordTrace_append hprefix tailTrace_7419205
  have hstable : (prefixWord ++ tailWord_7419205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419205).length < 2 ^ (prefixWord ++ tailWord_7419205).sum := by decide
  have hdescent : baseEnd_7419205 < baseStart_7419205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419213 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7419213 : Nat := 118140960795 + 7419213 * 2 ^ 59
def prefixEnd_7419213 : Nat := 4983230072969 + 3 ^ 40 * 7419213 * 2
def baseEnd_7419213 : Nat := 3809622347085986028717167

theorem tailTrace_7419213 : CollatzResearch.WordTrace tailWord_7419213 prefixEnd_7419213 3809622347085986028717167 := by
  unfold tailWord_7419213
  simp only [CollatzResearch.WordTrace]
  refine ⟨270600928870465876546470293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180400619246977251030980195 270600928870465876546470293)
  ·
    refine ⟨12684418540803087963115795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270600928870465876546470293 12684418540803087963115795)
    ·
      refine ⟨19026627811204631944673693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12684418540803087963115795 19026627811204631944673693)
      ·
        refine ⟨7134985429201736979252635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19026627811204631944673693 7134985429201736979252635)
        ·
          refine ⟨10702478143802605468878953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134985429201736979252635 10702478143802605468878953)
          ·
            refine ⟨8026858607851954101659215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10702478143802605468878953 8026858607851954101659215)
            ·
              refine ⟨12040287911777931152488823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026858607851954101659215 12040287911777931152488823)
              ·
                refine ⟨18060431867666896728733235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040287911777931152488823 18060431867666896728733235)
                ·
                  refine ⟨27090647801500345093099853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18060431867666896728733235 27090647801500345093099853)
                  ·
                    refine ⟨10158992925562629409912445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27090647801500345093099853 10158992925562629409912445)
                    ·
                      refine ⟨3809622347085986028717167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10158992925562629409912445 3809622347085986028717167)
                      ·
                        rfl

theorem cell23_7419213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7419213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419213 prefixEnd_7419213 := by exact prefixLift 7419213
  have htrace : WordTrace (prefixWord ++ tailWord_7419213) baseStart_7419213 baseEnd_7419213 := by
    simpa [prefixWord, tailWord_7419213, baseEnd_7419213] using wordTrace_append hprefix tailTrace_7419213
  have hstable : (prefixWord ++ tailWord_7419213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419213).length < 2 ^ (prefixWord ++ tailWord_7419213).sum := by decide
  have hdescent : baseEnd_7419213 < baseStart_7419213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419225 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 7]
def baseStart_7419225 : Nat := 118140960795 + 7419225 * 2 ^ 59
def prefixEnd_7419225 : Nat := 4983230072969 + 3 ^ 40 * 7419225 * 2
def baseEnd_7419225 : Nat := 423292056539315553529679

theorem tailTrace_7419225 : CollatzResearch.WordTrace tailWord_7419225 prefixEnd_7419225 423292056539315553529679 := by
  unfold tailWord_7419225
  simp only [CollatzResearch.WordTrace]
  refine ⟨270601366546422402595907129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180400911030948268397271419 270601366546422402595907129)
  ·
    refine ⟨202951024909816801946930347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270601366546422402595907129 202951024909816801946930347)
    ·
      refine ⟨304426537364725202920395521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202951024909816801946930347 304426537364725202920395521)
      ·
        refine ⟨228319903023543902190296641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304426537364725202920395521 228319903023543902190296641)
        ·
          refine ⟨171239927267657926642722481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228319903023543902190296641 171239927267657926642722481)
          ·
            refine ⟨128429945450743444982041861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171239927267657926642722481 128429945450743444982041861)
            ·
              refine ⟨24080614772014395934132849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128429945450743444982041861 24080614772014395934132849)
              ·
                refine ⟨18060461079010796950599637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24080614772014395934132849 18060461079010796950599637)
                ·
                  refine ⟨423292056539315553529679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18060461079010796950599637 423292056539315553529679)
                  ·
                    rfl

theorem cell23_7419225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_7419225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419225 prefixEnd_7419225 := by exact prefixLift 7419225
  have htrace : WordTrace (prefixWord ++ tailWord_7419225) baseStart_7419225 baseEnd_7419225 := by
    simpa [prefixWord, tailWord_7419225, baseEnd_7419225] using wordTrace_append hprefix tailTrace_7419225
  have hstable : (prefixWord ++ tailWord_7419225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419225).length < 2 ^ (prefixWord ++ tailWord_7419225).sum := by decide
  have hdescent : baseEnd_7419225 < baseStart_7419225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419259 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 5]
def baseStart_7419259 : Nat := 118140960795 + 7419259 * 2 ^ 59
def prefixEnd_7419259 : Nat := 4983230072969 + 3 ^ 40 * 7419259 * 2
def baseEnd_7419259 : Nat := 423293996355121427637995

theorem tailTrace_7419259 : CollatzResearch.WordTrace tailWord_7419259 prefixEnd_7419259 423293996355121427637995 := by
  unfold tailWord_7419259
  simp only [CollatzResearch.WordTrace]
  refine ⟨270602606628299226402644831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180401737752199484268429887 270602606628299226402644831)
  ·
    refine ⟨405903909942448839603967247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270602606628299226402644831 405903909942448839603967247)
    ·
      refine ⟨608855864913673259405950871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405903909942448839603967247 608855864913673259405950871)
      ·
        refine ⟨913283797370509889108926307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608855864913673259405950871 913283797370509889108926307)
        ·
          refine ⟨1369925696055764833663389461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913283797370509889108926307 1369925696055764833663389461)
          ·
            refine ⟨64215267002613976577971381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1369925696055764833663389461 64215267002613976577971381)
            ·
              refine ⟨6020181281495060304184817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64215267002613976577971381 6020181281495060304184817)
              ·
                refine ⟨4515135961121295228138613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020181281495060304184817 4515135961121295228138613)
                ·
                  refine ⟨423293996355121427637995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4515135961121295228138613 423293996355121427637995)
                  ·
                    rfl

theorem cell23_7419259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 5].length) (baseStart_7419259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419259 prefixEnd_7419259 := by exact prefixLift 7419259
  have htrace : WordTrace (prefixWord ++ tailWord_7419259) baseStart_7419259 baseEnd_7419259 := by
    simpa [prefixWord, tailWord_7419259, baseEnd_7419259] using wordTrace_append hprefix tailTrace_7419259
  have hstable : (prefixWord ++ tailWord_7419259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419259).length < 2 ^ (prefixWord ++ tailWord_7419259).sum := by decide
  have hdescent : baseEnd_7419259 < baseStart_7419259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419285 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_7419285 : Nat := 118140960795 + 7419285 * 2 ^ 59
def prefixEnd_7419285 : Nat := 4983230072969 + 3 ^ 40 * 7419285 * 2
def baseEnd_7419285 : Nat := 1269886439231036582338945

theorem tailTrace_7419285 : CollatzResearch.WordTrace tailWord_7419285 prefixEnd_7419285 1269886439231036582338945 := by
  unfold tailWord_7419285
  simp only [CollatzResearch.WordTrace]
  refine ⟨270603554926205032843091309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180402369950803355228727539 270603554926205032843091309)
  ·
    refine ⟨101476333097326887316159241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270603554926205032843091309 101476333097326887316159241)
    ·
      refine ⟨76107249822995165487119431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101476333097326887316159241 76107249822995165487119431)
      ·
        refine ⟨114160874734492748230679147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76107249822995165487119431 114160874734492748230679147)
        ·
          refine ⟨171241312101739122346018721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114160874734492748230679147 171241312101739122346018721)
          ·
            refine ⟨128430984076304341759514041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171241312101739122346018721 128430984076304341759514041)
            ·
              refine ⟨96323238057228256319635531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128430984076304341759514041 96323238057228256319635531)
              ·
                refine ⟨144484857085842384479453297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96323238057228256319635531 144484857085842384479453297)
                ·
                  refine ⟨108363642814381788359589973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144484857085842384479453297 108363642814381788359589973)
                  ·
                    refine ⟨1269886439231036582338945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108363642814381788359589973 1269886439231036582338945)
                    ·
                      rfl

theorem cell23_7419285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_7419285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419285 prefixEnd_7419285 := by exact prefixLift 7419285
  have htrace : WordTrace (prefixWord ++ tailWord_7419285) baseStart_7419285 baseEnd_7419285 := by
    simpa [prefixWord, tailWord_7419285, baseEnd_7419285] using wordTrace_append hprefix tailTrace_7419285
  have hstable : (prefixWord ++ tailWord_7419285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419285).length < 2 ^ (prefixWord ++ tailWord_7419285).sum := by decide
  have hdescent : baseEnd_7419285 < baseStart_7419285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419312 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_7419312 : Nat := 118140960795 + 7419312 * 2 ^ 59
def prefixEnd_7419312 : Nat := 4983230072969 + 3 ^ 40 * 7419312 * 2
def baseEnd_7419312 : Nat := 3809673181670781141379211

theorem tailTrace_7419312 : CollatzResearch.WordTrace tailWord_7419312 prefixEnd_7419312 3809673181670781141379211 := by
  unfold tailWord_7419312
  simp only [CollatzResearch.WordTrace]
  refine ⟨135302269848553608227162095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180403026464738144302882793 135302269848553608227162095)
  ·
    refine ⟨202953404772830412340743143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135302269848553608227162095 202953404772830412340743143)
    ·
      refine ⟨304430107159245618511114715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202953404772830412340743143 304430107159245618511114715)
      ·
        refine ⟨456645160738868427766672073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304430107159245618511114715 456645160738868427766672073)
        ·
          refine ⟨342483870554151320825004055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456645160738868427766672073 342483870554151320825004055)
          ·
            refine ⟨513725805831226981237506083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342483870554151320825004055 513725805831226981237506083)
            ·
              refine ⟨770588708746840471856259125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513725805831226981237506083 770588708746840471856259125)
              ·
                refine ⟨72242691445016294236524293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 770588708746840471856259125 72242691445016294236524293)
                ·
                  refine ⟨13545504645940555169348305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72242691445016294236524293 13545504645940555169348305)
                  ·
                    refine ⟨10159128484455416377011229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13545504645940555169348305 10159128484455416377011229)
                    ·
                      refine ⟨3809673181670781141379211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159128484455416377011229 3809673181670781141379211)
                      ·
                        rfl

theorem cell23_7419312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_7419312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419312 prefixEnd_7419312 := by exact prefixLift 7419312
  have htrace : WordTrace (prefixWord ++ tailWord_7419312) baseStart_7419312 baseEnd_7419312 := by
    simpa [prefixWord, tailWord_7419312, baseEnd_7419312] using wordTrace_append hprefix tailTrace_7419312
  have hstable : (prefixWord ++ tailWord_7419312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419312).length < 2 ^ (prefixWord ++ tailWord_7419312).sum := by decide
  have hdescent : baseEnd_7419312 < baseStart_7419312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419315 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 8]
def baseStart_7419315 : Nat := 118140960795 + 7419315 * 2 ^ 59
def prefixEnd_7419315 : Nat := 4983230072969 + 3 ^ 40 * 7419315 * 2
def baseEnd_7419315 : Nat := 423297191345860514404633

theorem tailTrace_7419315 : CollatzResearch.WordTrace tailWord_7419315 prefixEnd_7419315 423297191345860514404633 := by
  unfold tailWord_7419315
  simp only [CollatzResearch.WordTrace]
  refine ⟨270604649116096347966683399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180403099410730898644455599 270604649116096347966683399)
  ·
    refine ⟨405906973674144521950025099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270604649116096347966683399 405906973674144521950025099)
    ·
      refine ⟨608860460511216782925037649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405906973674144521950025099 608860460511216782925037649)
      ·
        refine ⟨456645345383412587193778237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608860460511216782925037649 456645345383412587193778237)
        ·
          refine ⟨171242004518779720197666839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456645345383412587193778237 171242004518779720197666839)
          ·
            refine ⟨256863006778169580296500259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171242004518779720197666839 256863006778169580296500259)
            ·
              refine ⟨385294510167254370444750389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256863006778169580296500259 385294510167254370444750389)
              ·
                refine ⟨36121360328180097229195349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 385294510167254370444750389 36121360328180097229195349)
                ·
                  refine ⟨423297191345860514404633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36121360328180097229195349 423297191345860514404633)
                  ·
                    rfl

theorem cell23_7419315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 8].length) (baseStart_7419315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419315 prefixEnd_7419315 := by exact prefixLift 7419315
  have htrace : WordTrace (prefixWord ++ tailWord_7419315) baseStart_7419315 baseEnd_7419315 := by
    simpa [prefixWord, tailWord_7419315, baseEnd_7419315] using wordTrace_append hprefix tailTrace_7419315
  have hstable : (prefixWord ++ tailWord_7419315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419315).length < 2 ^ (prefixWord ++ tailWord_7419315).sum := by decide
  have hdescent : baseEnd_7419315 < baseStart_7419315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419359 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 3]
def baseStart_7419359 : Nat := 118140960795 + 7419359 * 2 ^ 59
def prefixEnd_7419359 : Nat := 4983230072969 + 3 ^ 40 * 7419359 * 2
def baseEnd_7419359 : Nat := 3809697315261542457491495

theorem tailTrace_7419359 : CollatzResearch.WordTrace tailWord_7419359 prefixEnd_7419359 3809697315261542457491495 := by
  unfold tailWord_7419359
  simp only [CollatzResearch.WordTrace]
  refine ⟨270606253927936943481285131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180404169285291295654190087 270606253927936943481285131)
  ·
    refine ⟨405909380891905415221927697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270606253927936943481285131 405909380891905415221927697)
    ·
      refine ⟨304432035668929061416445773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405909380891905415221927697 304432035668929061416445773)
      ·
        refine ⟨114162013375848398031167165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304432035668929061416445773 114162013375848398031167165)
        ·
          refine ⟨42810755015943149261687687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114162013375848398031167165 42810755015943149261687687)
          ·
            refine ⟨64216132523914723892531531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42810755015943149261687687 64216132523914723892531531)
            ·
              refine ⟨96324198785872085838797297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64216132523914723892531531 96324198785872085838797297)
              ·
                refine ⟨72243149089404064379097973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96324198785872085838797297 72243149089404064379097973)
                ·
                  refine ⟨6772795227131631035540435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72243149089404064379097973 6772795227131631035540435)
                  ·
                    refine ⟨10159192840697446553310653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772795227131631035540435 10159192840697446553310653)
                    ·
                      refine ⟨3809697315261542457491495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159192840697446553310653 3809697315261542457491495)
                      ·
                        rfl

theorem cell23_7419359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_7419359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419359 prefixEnd_7419359 := by exact prefixLift 7419359
  have htrace : WordTrace (prefixWord ++ tailWord_7419359) baseStart_7419359 baseEnd_7419359 := by
    simpa [prefixWord, tailWord_7419359, baseEnd_7419359] using wordTrace_append hprefix tailTrace_7419359
  have hstable : (prefixWord ++ tailWord_7419359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419359).length < 2 ^ (prefixWord ++ tailWord_7419359).sum := by decide
  have hdescent : baseEnd_7419359 < baseStart_7419359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419376 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 3, 1, 3]
def baseStart_7419376 : Nat := 118140960795 + 7419376 * 2 ^ 59
def prefixEnd_7419376 : Nat := 4983230072969 + 3 ^ 40 * 7419376 * 2
def baseEnd_7419376 : Nat := 3809706044432668890978917

theorem tailTrace_7419376 : CollatzResearch.WordTrace tailWord_7419376 prefixEnd_7419376 3809706044432668890978917 := by
  unfold tailWord_7419376
  simp only [CollatzResearch.WordTrace]
  refine ⟨135303436984437677692326991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180404582645916903589769321 135303436984437677692326991)
  ·
    refine ⟨202955155476656516538490487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135303436984437677692326991 202955155476656516538490487)
    ·
      refine ⟨304432733214984774807735731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202955155476656516538490487 304432733214984774807735731)
      ·
        refine ⟨456649099822477162211603597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304432733214984774807735731 456649099822477162211603597)
        ·
          refine ⟨171243412433428935829351349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456649099822477162211603597 171243412433428935829351349)
          ·
            refine ⟨16054069915633962734001689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171243412433428935829351349 16054069915633962734001689)
            ·
              refine ⟨12040552436725472050501267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16054069915633962734001689 12040552436725472050501267)
              ·
                refine ⟨18060828655088208075751901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040552436725472050501267 18060828655088208075751901)
                ·
                  refine ⟨6772810745658078028406963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18060828655088208075751901 6772810745658078028406963)
                  ·
                    refine ⟨10159216118487117042610445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772810745658078028406963 10159216118487117042610445)
                    ·
                      refine ⟨3809706044432668890978917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159216118487117042610445 3809706044432668890978917)
                      ·
                        rfl

theorem cell23_7419376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_7419376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419376 prefixEnd_7419376 := by exact prefixLift 7419376
  have htrace : WordTrace (prefixWord ++ tailWord_7419376) baseStart_7419376 baseEnd_7419376 := by
    simpa [prefixWord, tailWord_7419376, baseEnd_7419376] using wordTrace_append hprefix tailTrace_7419376
  have hstable : (prefixWord ++ tailWord_7419376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419376).length < 2 ^ (prefixWord ++ tailWord_7419376).sum := by decide
  have hdescent : baseEnd_7419376 < baseStart_7419376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419442 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_7419442 : Nat := 118140960795 + 7419442 * 2 ^ 59
def prefixEnd_7419442 : Nat := 4983230072969 + 3 ^ 40 * 7419442 * 2
def baseEnd_7419442 : Nat := 3809739934155865632753613

theorem tailTrace_7419442 : CollatzResearch.WordTrace tailWord_7419442 prefixEnd_7419442 3809739934155865632753613 := by
  unfold tailWord_7419442
  simp only [CollatzResearch.WordTrace]
  refine ⟨67652320296659062164139145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180406187457757499104371053 67652320296659062164139145)
  ·
    refine ⟨50739240222494296623104359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67652320296659062164139145 50739240222494296623104359)
    ·
      refine ⟨76108860333741444934656539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50739240222494296623104359 76108860333741444934656539)
      ·
        refine ⟨114163290500612167401984809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76108860333741444934656539 114163290500612167401984809)
        ·
          refine ⟨85622467875459125551488607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114163290500612167401984809 85622467875459125551488607)
          ·
            refine ⟨128433701813188688327232911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85622467875459125551488607 128433701813188688327232911)
            ·
              refine ⟨192650552719783032490849367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128433701813188688327232911 192650552719783032490849367)
              ·
                refine ⟨288975829079674548736274051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192650552719783032490849367 288975829079674548736274051)
                ·
                  refine ⟨433463743619511823104411077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288975829079674548736274051 433463743619511823104411077)
                  ·
                    refine ⟨81274451928658466832077077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433463743619511823104411077 81274451928658466832077077)
                    ·
                      refine ⟨3809739934155865632753613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81274451928658466832077077 3809739934155865632753613)
                      ·
                        rfl

theorem cell23_7419442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_7419442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419442 prefixEnd_7419442 := by exact prefixLift 7419442
  have htrace : WordTrace (prefixWord ++ tailWord_7419442) baseStart_7419442 baseEnd_7419442 := by
    simpa [prefixWord, tailWord_7419442, baseEnd_7419442] using wordTrace_append hprefix tailTrace_7419442
  have hstable : (prefixWord ++ tailWord_7419442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419442).length < 2 ^ (prefixWord ++ tailWord_7419442).sum := by decide
  have hdescent : baseEnd_7419442 < baseStart_7419442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419443 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 2, 4]
def baseStart_7419443 : Nat := 118140960795 + 7419443 * 2 ^ 59
def prefixEnd_7419443 : Nat := 4983230072969 + 3 ^ 40 * 7419443 * 2
def baseEnd_7419443 : Nat := 1269913482545506709613703

theorem tailTrace_7419443 : CollatzResearch.WordTrace tailWord_7419443 prefixEnd_7419443 1269913482545506709613703 := by
  unfold tailWord_7419443
  simp only [CollatzResearch.WordTrace]
  refine ⟨270609317659632625827342983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180406211773088417218228655 270609317659632625827342983)
  ·
    refine ⟨405913976489448938741014475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270609317659632625827342983 405913976489448938741014475)
    ·
      refine ⟨608870964734173408111521713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405913976489448938741014475 608870964734173408111521713)
      ·
        refine ⟨456653223550630056083641285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608870964734173408111521713 456653223550630056083641285)
        ·
          refine ⟨85622479415743135515682741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456653223550630056083641285 85622479415743135515682741)
          ·
            refine ⟨8027107445225918954595257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85622479415743135515682741 8027107445225918954595257)
            ·
              refine ⟨6020330583919439215946443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027107445225918954595257 6020330583919439215946443)
              ·
                refine ⟨9030495875879158823919665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020330583919439215946443 9030495875879158823919665)
                ·
                  refine ⟨6772871906909369117939749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030495875879158823919665 6772871906909369117939749)
                  ·
                    refine ⟨1269913482545506709613703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6772871906909369117939749 1269913482545506709613703)
                    ·
                      rfl

theorem cell23_7419443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 4].length) (baseStart_7419443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419443 prefixEnd_7419443 := by exact prefixLift 7419443
  have htrace : WordTrace (prefixWord ++ tailWord_7419443) baseStart_7419443 baseEnd_7419443 := by
    simpa [prefixWord, tailWord_7419443, baseEnd_7419443] using wordTrace_append hprefix tailTrace_7419443
  have hstable : (prefixWord ++ tailWord_7419443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419443).length < 2 ^ (prefixWord ++ tailWord_7419443).sum := by decide
  have hdescent : baseEnd_7419443 < baseStart_7419443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419478 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7419478 : Nat := 118140960795 + 7419478 * 2 ^ 59
def prefixEnd_7419478 : Nat := 4983230072969 + 3 ^ 40 * 7419478 * 2
def baseEnd_7419478 : Nat := 3809758419459427491903449

theorem tailTrace_7419478 : CollatzResearch.WordTrace tailWord_7419478 prefixEnd_7419478 3809758419459427491903449 := by
  unfold tailWord_7419478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16913162138406614175304193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180407062809670551203244725 16913162138406614175304193)
  ·
    refine ⟨12684871603804960631478145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16913162138406614175304193 12684871603804960631478145)
    ·
      refine ⟨9513653702853720473608609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12684871603804960631478145 9513653702853720473608609)
      ·
        refine ⟨7135240277140290355206457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9513653702853720473608609 7135240277140290355206457)
        ·
          refine ⟨5351430207855217766404843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7135240277140290355206457 5351430207855217766404843)
          ·
            refine ⟨8027145311782826649607265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351430207855217766404843 8027145311782826649607265)
            ·
              refine ⟨6020358983837119987205449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027145311782826649607265 6020358983837119987205449)
              ·
                refine ⟨4515269237877839990404087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020358983837119987205449 4515269237877839990404087)
                ·
                  refine ⟨6772903856816759985606131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515269237877839990404087 6772903856816759985606131)
                  ·
                    refine ⟨10159355785225139978409197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772903856816759985606131 10159355785225139978409197)
                    ·
                      refine ⟨3809758419459427491903449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159355785225139978409197 3809758419459427491903449)
                      ·
                        rfl

theorem cell23_7419478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7419478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419478 prefixEnd_7419478 := by exact prefixLift 7419478
  have htrace : WordTrace (prefixWord ++ tailWord_7419478) baseStart_7419478 baseEnd_7419478 := by
    simpa [prefixWord, tailWord_7419478, baseEnd_7419478] using wordTrace_append hprefix tailTrace_7419478
  have hstable : (prefixWord ++ tailWord_7419478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419478).length < 2 ^ (prefixWord ++ tailWord_7419478).sum := by decide
  have hdescent : baseEnd_7419478 < baseStart_7419478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419482 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_7419482 : Nat := 118140960795 + 7419482 * 2 ^ 59
def prefixEnd_7419482 : Nat := 4983230072969 + 3 ^ 40 * 7419482 * 2
def baseEnd_7419482 : Nat := 1269920157794015158751143

theorem tailTrace_7419482 : CollatzResearch.WordTrace tailWord_7419482 prefixEnd_7419482 1269920157794015158751143 := by
  unfold tailWord_7419482
  simp only [CollatzResearch.WordTrace]
  refine ⟨67652685026622833872003175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180407160070994223658675133 67652685026622833872003175)
  ·
    refine ⟨101479027539934250808004763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67652685026622833872003175 101479027539934250808004763)
    ·
      refine ⟨152218541309901376212007145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101479027539934250808004763 152218541309901376212007145)
      ·
        refine ⟨114163905982426032159005359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152218541309901376212007145 114163905982426032159005359)
        ·
          refine ⟨171245858973639048238508039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114163905982426032159005359 171245858973639048238508039)
          ·
            refine ⟨256868788460458572357762059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171245858973639048238508039 256868788460458572357762059)
            ·
              refine ⟨385303182690687858536643089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256868788460458572357762059 385303182690687858536643089)
              ·
                refine ⟨288977387018015893902482317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385303182690687858536643089 288977387018015893902482317)
                ·
                  refine ⟨108366520131755960213430869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288977387018015893902482317 108366520131755960213430869)
                  ·
                    refine ⟨1269920157794015158751143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108366520131755960213430869 1269920157794015158751143)
                    ·
                      rfl

theorem cell23_7419482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_7419482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419482 prefixEnd_7419482 := by exact prefixLift 7419482
  have htrace : WordTrace (prefixWord ++ tailWord_7419482) baseStart_7419482 baseEnd_7419482 := by
    simpa [prefixWord, tailWord_7419482, baseEnd_7419482] using wordTrace_append hprefix tailTrace_7419482
  have hstable : (prefixWord ++ tailWord_7419482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419482).length < 2 ^ (prefixWord ++ tailWord_7419482).sum := by decide
  have hdescent : baseEnd_7419482 < baseStart_7419482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419484 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_7419484 : Nat := 118140960795 + 7419484 * 2 ^ 59
def prefixEnd_7419484 : Nat := 4983230072969 + 3 ^ 40 * 7419484 * 2
def baseEnd_7419484 : Nat := 3809761500343354468428421

theorem tailTrace_7419484 : CollatzResearch.WordTrace tailWord_7419484 prefixEnd_7419484 3809761500343354468428421 := by
  unfold tailWord_7419484
  simp only [CollatzResearch.WordTrace]
  refine ⟨135305406526242044914792753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180407208701656059886390337 135305406526242044914792753)
  ·
    refine ⟨101479054894681533686094565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135305406526242044914792753 101479054894681533686094565)
    ·
      refine ⟨19027322792752787566142731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101479054894681533686094565 19027322792752787566142731)
      ·
        refine ⟨28540984189129181349214097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19027322792752787566142731 28540984189129181349214097)
        ·
          refine ⟨21405738141846886011910573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28540984189129181349214097 21405738141846886011910573)
          ·
            refine ⟨8027151803192582254466465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21405738141846886011910573 8027151803192582254466465)
            ·
              refine ⟨6020363852394436690849849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027151803192582254466465 6020363852394436690849849)
              ·
                refine ⟨4515272889295827518137387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020363852394436690849849 4515272889295827518137387)
                ·
                  refine ⟨6772909333943741277206081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515272889295827518137387 6772909333943741277206081)
                  ·
                    refine ⟨5079682000457805957904561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6772909333943741277206081 5079682000457805957904561)
                    ·
                      refine ⟨3809761500343354468428421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079682000457805957904561 3809761500343354468428421)
                      ·
                        rfl

theorem cell23_7419484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_7419484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419484 prefixEnd_7419484 := by exact prefixLift 7419484
  have htrace : WordTrace (prefixWord ++ tailWord_7419484) baseStart_7419484 baseEnd_7419484 := by
    simpa [prefixWord, tailWord_7419484, baseEnd_7419484] using wordTrace_append hprefix tailTrace_7419484
  have hstable : (prefixWord ++ tailWord_7419484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419484).length < 2 ^ (prefixWord ++ tailWord_7419484).sum := by decide
  have hdescent : baseEnd_7419484 < baseStart_7419484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419556 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_7419556 : Nat := 118140960795 + 7419556 * 2 ^ 59
def prefixEnd_7419556 : Nat := 4983230072969 + 3 ^ 40 * 7419556 * 2
def baseEnd_7419556 : Nat := 3809798470950478186728089

theorem tailTrace_7419556 : CollatzResearch.WordTrace tailWord_7419556 prefixEnd_7419556 3809798470950478186728089 := by
  unfold tailWord_7419556
  simp only [CollatzResearch.WordTrace]
  refine ⟨135306719554111623063103261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180408959405482164084137681 135306719554111623063103261)
  ·
    refine ⟨50740019832791858648663723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135306719554111623063103261 50740019832791858648663723)
    ·
      refine ⟨76110029749187787972995585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50740019832791858648663723 76110029749187787972995585)
      ·
        refine ⟨57082522311890840979746689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76110029749187787972995585 57082522311890840979746689)
        ·
          refine ⟨42811891733918130734810017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57082522311890840979746689 42811891733918130734810017)
          ·
            refine ⟨32108918800438598051107513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42811891733918130734810017 32108918800438598051107513)
            ·
              refine ⟨24081689100328948538330635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32108918800438598051107513 24081689100328948538330635)
              ·
                refine ⟨36122533650493422807495953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24081689100328948538330635 36122533650493422807495953)
                ·
                  refine ⟨27091900237870067105621965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36122533650493422807495953 27091900237870067105621965)
                  ·
                    refine ⟨10159462589201275164608237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27091900237870067105621965 10159462589201275164608237)
                    ·
                      refine ⟨3809798470950478186728089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159462589201275164608237 3809798470950478186728089)
                      ·
                        rfl

theorem cell23_7419556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_7419556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419556 prefixEnd_7419556 := by exact prefixLift 7419556
  have htrace : WordTrace (prefixWord ++ tailWord_7419556) baseStart_7419556 baseEnd_7419556 := by
    simpa [prefixWord, tailWord_7419556, baseEnd_7419556] using wordTrace_append hprefix tailTrace_7419556
  have hstable : (prefixWord ++ tailWord_7419556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419556).length < 2 ^ (prefixWord ++ tailWord_7419556).sum := by decide
  have hdescent : baseEnd_7419556 < baseStart_7419556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419579 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 4]
def baseStart_7419579 : Nat := 118140960795 + 7419579 * 2 ^ 59
def prefixEnd_7419579 : Nat := 4983230072969 + 3 ^ 40 * 7419579 * 2
def baseEnd_7419579 : Nat := 3809810281005531596740483

theorem tailTrace_7419579 : CollatzResearch.WordTrace tailWord_7419579 prefixEnd_7419579 3809810281005531596740483 := by
  unfold tailWord_7419579
  simp only [CollatzResearch.WordTrace]
  refine ⟨270614277987139921054293791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180409518658093280702862527 270614277987139921054293791)
  ·
    refine ⟨405921416980709881581440687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270614277987139921054293791 405921416980709881581440687)
    ·
      refine ⟨608882125471064822372161031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405921416980709881581440687 608882125471064822372161031)
      ·
        refine ⟨913323188206597233558241547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608882125471064822372161031 913323188206597233558241547)
        ·
          refine ⟨1369984782309895850337362321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913323188206597233558241547 1369984782309895850337362321)
          ·
            refine ⟨1027488586732421887753021741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369984782309895850337362321 1027488586732421887753021741)
            ·
              refine ⟨385308220024658207907383153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1027488586732421887753021741 385308220024658207907383153)
              ·
                refine ⟨288981165018493655930537365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385308220024658207907383153 288981165018493655930537365)
                ·
                  refine ⟨13545992110241890121743939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288981165018493655930537365 13545992110241890121743939)
                  ·
                    refine ⟨20318988165362835182615909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13545992110241890121743939 20318988165362835182615909)
                    ·
                      refine ⟨3809810281005531596740483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20318988165362835182615909 3809810281005531596740483)
                      ·
                        rfl

theorem cell23_7419579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 4].length) (baseStart_7419579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419579 prefixEnd_7419579 := by exact prefixLift 7419579
  have htrace : WordTrace (prefixWord ++ tailWord_7419579) baseStart_7419579 baseEnd_7419579 := by
    simpa [prefixWord, tailWord_7419579, baseEnd_7419579] using wordTrace_append hprefix tailTrace_7419579
  have hstable : (prefixWord ++ tailWord_7419579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419579).length < 2 ^ (prefixWord ++ tailWord_7419579).sum := by decide
  have hdescent : baseEnd_7419579 < baseStart_7419579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419597 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 5]
def baseStart_7419597 : Nat := 118140960795 + 7419597 * 2 ^ 59
def prefixEnd_7419597 : Nat := 4983230072969 + 3 ^ 40 * 7419597 * 2
def baseEnd_7419597 : Nat := 423313280406368058479489

theorem tailTrace_7419597 : CollatzResearch.WordTrace tailWord_7419597 prefixEnd_7419597 423313280406368058479489 := by
  unfold tailWord_7419597
  simp only [CollatzResearch.WordTrace]
  refine ⟨270614934501074710128449045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180409956334049806752299363 270614934501074710128449045)
  ·
    refine ⟨12685075054737877037271049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270614934501074710128449045 12685075054737877037271049)
    ·
      refine ⟨9513806291053407777953287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12685075054737877037271049 9513806291053407777953287)
      ·
        refine ⟨14270709436580111666929931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9513806291053407777953287 14270709436580111666929931)
        ·
          refine ⟨21406064154870167500394897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14270709436580111666929931 21406064154870167500394897)
          ·
            refine ⟨16054548116152625625296173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21406064154870167500394897 16054548116152625625296173)
            ·
              refine ⟨6020455543557234609486065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16054548116152625625296173 6020455543557234609486065)
              ·
                refine ⟨4515341657667925957114549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020455543557234609486065 4515341657667925957114549)
                ·
                  refine ⟨423313280406368058479489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4515341657667925957114549 423313280406368058479489)
                  ·
                    rfl

theorem cell23_7419597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_7419597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419597 prefixEnd_7419597 := by exact prefixLift 7419597
  have htrace : WordTrace (prefixWord ++ tailWord_7419597) baseStart_7419597 baseEnd_7419597 := by
    simpa [prefixWord, tailWord_7419597, baseEnd_7419597] using wordTrace_append hprefix tailTrace_7419597
  have hstable : (prefixWord ++ tailWord_7419597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419597).length < 2 ^ (prefixWord ++ tailWord_7419597).sum := by decide
  have hdescent : baseEnd_7419597 < baseStart_7419597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419633 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_7419633 : Nat := 118140960795 + 7419633 * 2 ^ 59
def prefixEnd_7419633 : Nat := 4983230072969 + 3 ^ 40 * 7419633 * 2
def baseEnd_7419633 : Nat := 3809838008960874385465235

theorem tailTrace_7419633 : CollatzResearch.WordTrace tailWord_7419633 prefixEnd_7419633 3809838008960874385465235 := by
  unfold tailWord_7419633
  simp only [CollatzResearch.WordTrace]
  refine ⟨270616247528944288276759553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180410831685962858851173035 270616247528944288276759553)
  ·
    refine ⟨202962185646708216207569665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270616247528944288276759553 202962185646708216207569665)
    ·
      refine ⟨152221639235031162155677249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202962185646708216207569665 152221639235031162155677249)
      ·
        refine ⟨114166229426273371616757937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152221639235031162155677249 114166229426273371616757937)
        ·
          refine ⟨85624672069705028712568453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114166229426273371616757937 85624672069705028712568453)
          ·
            refine ⟨16054626013069692883606585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85624672069705028712568453 16054626013069692883606585)
            ·
              refine ⟨12040969509802269662704939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16054626013069692883606585 12040969509802269662704939)
              ·
                refine ⟨18061454264703404494057409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040969509802269662704939 18061454264703404494057409)
                ·
                  refine ⟨13546090698527553370543057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18061454264703404494057409 13546090698527553370543057)
                  ·
                    refine ⟨10159568023895665027907293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13546090698527553370543057 10159568023895665027907293)
                    ·
                      refine ⟨3809838008960874385465235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159568023895665027907293 3809838008960874385465235)
                      ·
                        rfl

theorem cell23_7419633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_7419633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419633 prefixEnd_7419633 := by exact prefixLift 7419633
  have htrace : WordTrace (prefixWord ++ tailWord_7419633) baseStart_7419633 baseEnd_7419633 := by
    simpa [prefixWord, tailWord_7419633, baseEnd_7419633] using wordTrace_append hprefix tailTrace_7419633
  have hstable : (prefixWord ++ tailWord_7419633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419633).length < 2 ^ (prefixWord ++ tailWord_7419633).sum := by decide
  have hdescent : baseEnd_7419633 < baseStart_7419633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419689 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_7419689 : Nat := 118140960795 + 7419689 * 2 ^ 59
def prefixEnd_7419689 : Nat := 4983230072969 + 3 ^ 40 * 7419689 * 2
def baseEnd_7419689 : Nat := 3809866763877526166364977

theorem tailTrace_7419689 : CollatzResearch.WordTrace tailWord_7419689 prefixEnd_7419689 3809866763877526166364977 := by
  unfold tailWord_7419689
  simp only [CollatzResearch.WordTrace]
  refine ⟨270618290016741409840798121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180412193344494273227198747 270618290016741409840798121)
  ·
    refine ⟨202963717512556057380598591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270618290016741409840798121 202963717512556057380598591)
    ·
      refine ⟨304445576268834086070897887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202963717512556057380598591 304445576268834086070897887)
      ·
        refine ⟨456668364403251129106346831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304445576268834086070897887 456668364403251129106346831)
        ·
          refine ⟨685002546604876693659520247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456668364403251129106346831 685002546604876693659520247)
          ·
            refine ⟨1027503819907315040489280371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685002546604876693659520247 1027503819907315040489280371)
            ·
              refine ⟨1541255729860972560733920557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027503819907315040489280371 1541255729860972560733920557)
              ·
                refine ⟨577970898697864710275220209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1541255729860972560733920557 577970898697864710275220209)
                ·
                  refine ⟨433478174023398532706415157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577970898697864710275220209 433478174023398532706415157)
                  ·
                    refine ⟨40638578814693612441226421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 433478174023398532706415157 40638578814693612441226421)
                    ·
                      refine ⟨3809866763877526166364977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40638578814693612441226421 3809866763877526166364977)
                      ·
                        rfl

theorem cell23_7419689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_7419689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419689 prefixEnd_7419689 := by exact prefixLift 7419689
  have htrace : WordTrace (prefixWord ++ tailWord_7419689) baseStart_7419689 baseEnd_7419689 := by
    simpa [prefixWord, tailWord_7419689, baseEnd_7419689] using wordTrace_append hprefix tailTrace_7419689
  have hstable : (prefixWord ++ tailWord_7419689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419689).length < 2 ^ (prefixWord ++ tailWord_7419689).sum := by decide
  have hdescent : baseEnd_7419689 < baseStart_7419689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419697 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 1, 1, 3]
def baseStart_7419697 : Nat := 118140960795 + 7419697 * 2 ^ 59
def prefixEnd_7419697 : Nat := 4983230072969 + 3 ^ 40 * 7419697 * 2
def baseEnd_7419697 : Nat := 3809870871722762135064941

theorem tailTrace_7419697 : CollatzResearch.WordTrace tailWord_7419697 prefixEnd_7419697 3809870871722762135064941 := by
  unfold tailWord_7419697
  simp only [CollatzResearch.WordTrace]
  refine ⟨270618581800712427207089345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180412387867141618138059563 270618581800712427207089345)
  ·
    refine ⟨202963936350534320405317009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270618581800712427207089345 202963936350534320405317009)
    ·
      refine ⟨152222952262900740303987757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202963936350534320405317009 152222952262900740303987757)
      ·
        refine ⟨57083607098587777613995409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152222952262900740303987757 57083607098587777613995409)
        ·
          refine ⟨42812705323940833210496557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57083607098587777613995409 42812705323940833210496557)
          ·
            refine ⟨16054764496477812453936209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42812705323940833210496557 16054764496477812453936209)
            ·
              refine ⟨12041073372358359340452157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16054764496477812453936209 12041073372358359340452157)
              ·
                refine ⟨4515402514634384752669559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12041073372358359340452157 4515402514634384752669559)
                ·
                  refine ⟨6773103771951577129004339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515402514634384752669559 6773103771951577129004339)
                  ·
                    refine ⟨10159655657927365693506509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773103771951577129004339 10159655657927365693506509)
                    ·
                      refine ⟨3809870871722762135064941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159655657927365693506509 3809870871722762135064941)
                      ·
                        rfl

theorem cell23_7419697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_7419697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419697 prefixEnd_7419697 := by exact prefixLift 7419697
  have htrace : WordTrace (prefixWord ++ tailWord_7419697) baseStart_7419697 baseEnd_7419697 := by
    simpa [prefixWord, tailWord_7419697, baseEnd_7419697] using wordTrace_append hprefix tailTrace_7419697
  have hstable : (prefixWord ++ tailWord_7419697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419697).length < 2 ^ (prefixWord ++ tailWord_7419697).sum := by decide
  have hdescent : baseEnd_7419697 < baseStart_7419697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419700 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_7419700 : Nat := 118140960795 + 7419700 * 2 ^ 59
def prefixEnd_7419700 : Nat := 4983230072969 + 3 ^ 40 * 7419700 * 2
def baseEnd_7419700 : Nat := 1269957470721575207775809

theorem tailTrace_7419700 : CollatzResearch.WordTrace tailWord_7419700 prefixEnd_7419700 1269957470721575207775809 := by
  unfold tailWord_7419700
  simp only [CollatzResearch.WordTrace]
  refine ⟨135309345609850779359724277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180412460813134372479632369 135309345609850779359724277)
  ·
    refine ⟨12685251150923510564974151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135309345609850779359724277 12685251150923510564974151)
    ·
      refine ⟨19027876726385265847461227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12685251150923510564974151 19027876726385265847461227)
      ·
        refine ⟨28541815089577898771191841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19027876726385265847461227 28541815089577898771191841)
        ·
          refine ⟨21406361317183424078393881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28541815089577898771191841 21406361317183424078393881)
          ·
            refine ⟨16054770987887568058795411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21406361317183424078393881 16054770987887568058795411)
            ·
              refine ⟨24082156481831352088193117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16054770987887568058795411 24082156481831352088193117)
              ·
                refine ⟨9030808680686757033072419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24082156481831352088193117 9030808680686757033072419)
                ·
                  refine ⟨13546213021030135549608629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9030808680686757033072419 13546213021030135549608629)
                  ·
                    refine ⟨1269957470721575207775809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13546213021030135549608629 1269957470721575207775809)
                    ·
                      rfl

theorem cell23_7419700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_7419700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419700 prefixEnd_7419700 := by exact prefixLift 7419700
  have htrace : WordTrace (prefixWord ++ tailWord_7419700) baseStart_7419700 baseEnd_7419700 := by
    simpa [prefixWord, tailWord_7419700, baseEnd_7419700] using wordTrace_append hprefix tailTrace_7419700
  have hstable : (prefixWord ++ tailWord_7419700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419700).length < 2 ^ (prefixWord ++ tailWord_7419700).sum := by decide
  have hdescent : baseEnd_7419700 < baseStart_7419700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419720 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_7419720 : Nat := 118140960795 + 7419720 * 2 ^ 59
def prefixEnd_7419720 : Nat := 4983230072969 + 3 ^ 40 * 7419720 * 2
def baseEnd_7419720 : Nat := 3809882681777815545077335

theorem tailTrace_7419720 : CollatzResearch.WordTrace tailWord_7419720 prefixEnd_7419720 3809882681777815545077335 := by
  unfold tailWord_7419720
  simp only [CollatzResearch.WordTrace]
  refine ⟨135309710339814551067588307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180412947119752734756784409 135309710339814551067588307)
  ·
    refine ⟨202964565509721826601382461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135309710339814551067588307 202964565509721826601382461)
    ·
      refine ⟨76111712066145684975518423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202964565509721826601382461 76111712066145684975518423)
      ·
        refine ⟨114167568099218527463277635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76111712066145684975518423 114167568099218527463277635)
        ·
          refine ⟨171251352148827791194916453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114167568099218527463277635 171251352148827791194916453)
          ·
            refine ⟨32109628527905210849046835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171251352148827791194916453 32109628527905210849046835)
            ·
              refine ⟨48164442791857816273570253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32109628527905210849046835 48164442791857816273570253)
              ·
                refine ⟨18061666046946681102588845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48164442791857816273570253 18061666046946681102588845)
                ·
                  refine ⟨6773124767605005413470817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18061666046946681102588845 6773124767605005413470817)
                  ·
                    refine ⟨5079843575703754060103113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773124767605005413470817 5079843575703754060103113)
                    ·
                      refine ⟨3809882681777815545077335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079843575703754060103113 3809882681777815545077335)
                      ·
                        rfl

theorem cell23_7419720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_7419720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419720 prefixEnd_7419720 := by exact prefixLift 7419720
  have htrace : WordTrace (prefixWord ++ tailWord_7419720) baseStart_7419720 baseEnd_7419720 := by
    simpa [prefixWord, tailWord_7419720, baseEnd_7419720] using wordTrace_append hprefix tailTrace_7419720
  have hstable : (prefixWord ++ tailWord_7419720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419720).length < 2 ^ (prefixWord ++ tailWord_7419720).sum := by decide
  have hdescent : baseEnd_7419720 < baseStart_7419720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419733 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_7419733 : Nat := 118140960795 + 7419733 * 2 ^ 59
def prefixEnd_7419733 : Nat := 4983230072969 + 3 ^ 40 * 7419733 * 2
def baseEnd_7419733 : Nat := 3809889357026323994214775

theorem tailTrace_7419733 : CollatzResearch.WordTrace tailWord_7419733 prefixEnd_7419733 3809889357026323994214775 := by
  unfold tailWord_7419733
  simp only [CollatzResearch.WordTrace]
  refine ⟨270619894828582005355399853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180413263219054670236933235 270619894828582005355399853)
  ·
    refine ⟨101482460560718252008274945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270619894828582005355399853 101482460560718252008274945)
    ·
      refine ⟨76111845420538689006206209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101482460560718252008274945 76111845420538689006206209)
      ·
        refine ⟨57083884065404016754654657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76111845420538689006206209 57083884065404016754654657)
        ·
          refine ⟨42812913049053012565990993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57083884065404016754654657 42812913049053012565990993)
          ·
            refine ⟨32109684786789759424493245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42812913049053012565990993 32109684786789759424493245)
            ·
              refine ⟨12041131795046159784184967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32109684786789759424493245 12041131795046159784184967)
              ·
                refine ⟨18061697692569239676277451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12041131795046159784184967 18061697692569239676277451)
                ·
                  refine ⟨27092546538853859514416177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18061697692569239676277451 27092546538853859514416177)
                  ·
                    refine ⟨20319409904140394635812133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27092546538853859514416177 20319409904140394635812133)
                    ·
                      refine ⟨3809889357026323994214775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20319409904140394635812133 3809889357026323994214775)
                      ·
                        rfl

theorem cell23_7419733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_7419733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419733 prefixEnd_7419733 := by exact prefixLift 7419733
  have htrace : WordTrace (prefixWord ++ tailWord_7419733) baseStart_7419733 baseEnd_7419733 := by
    simpa [prefixWord, tailWord_7419733, baseEnd_7419733] using wordTrace_append hprefix tailTrace_7419733
  have hstable : (prefixWord ++ tailWord_7419733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419733).length < 2 ^ (prefixWord ++ tailWord_7419733).sum := by decide
  have hdescent : baseEnd_7419733 < baseStart_7419733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419743 : List Nat := [1, 1, 2, 3, 1, 6, 2, 7]
def baseStart_7419743 : Nat := 118140960795 + 7419743 * 2 ^ 59
def prefixEnd_7419743 : Nat := 4983230072969 + 3 ^ 40 * 7419743 * 2
def baseEnd_7419743 : Nat := 141107203401217368707027

theorem tailTrace_7419743 : CollatzResearch.WordTrace tailWord_7419743 prefixEnd_7419743 141107203401217368707027 := by
  unfold tailWord_7419743
  simp only [CollatzResearch.WordTrace]
  refine ⟨270620259558545777063263883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180413506372363851375509255 270620259558545777063263883)
  ·
    refine ⟨405930389337818665594895825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270620259558545777063263883 405930389337818665594895825)
    ·
      refine ⟨304447792003363999196171869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405930389337818665594895825 304447792003363999196171869)
      ·
        refine ⟨114167922001261499698564451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304447792003363999196171869 114167922001261499698564451)
        ·
          refine ⟨171251883001892249547846677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114167922001261499698564451 171251883001892249547846677)
          ·
            refine ⟨8027432015713699197555313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171251883001892249547846677 8027432015713699197555313)
            ·
              refine ⟨6020574011785274398166485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027432015713699197555313 6020574011785274398166485)
              ·
                refine ⟨141107203401217368707027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6020574011785274398166485 141107203401217368707027)
                ·
                  rfl

theorem cell23_7419743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 7].length) (baseStart_7419743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419743 prefixEnd_7419743 := by exact prefixLift 7419743
  have htrace : WordTrace (prefixWord ++ tailWord_7419743) baseStart_7419743 baseEnd_7419743 := by
    simpa [prefixWord, tailWord_7419743, baseEnd_7419743] using wordTrace_append hprefix tailTrace_7419743
  have hstable : (prefixWord ++ tailWord_7419743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419743).length < 2 ^ (prefixWord ++ tailWord_7419743).sum := by decide
  have hdescent : baseEnd_7419743 < baseStart_7419743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419763 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 5, 3, 2]
def baseStart_7419763 : Nat := 118140960795 + 7419763 * 2 ^ 59
def prefixEnd_7419763 : Nat := 4983230072969 + 3 ^ 40 * 7419763 * 2
def baseEnd_7419763 : Nat := 3809904761445958876839637

theorem tailTrace_7419763 : CollatzResearch.WordTrace tailWord_7419763 prefixEnd_7419763 3809904761445958876839637 := by
  unfold tailWord_7419763
  simp only [CollatzResearch.WordTrace]
  refine ⟨270620989018473320478991943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180413992678982213652661295 270620989018473320478991943)
  ·
    refine ⟨405931483527709980718487915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270620989018473320478991943 405931483527709980718487915)
    ·
      refine ⟨608897225291564971077731873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405931483527709980718487915 608897225291564971077731873)
      ·
        refine ⟨456672918968673728308298905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608897225291564971077731873 456672918968673728308298905)
        ·
          refine ⟨342504689226505296231224179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456672918968673728308298905 342504689226505296231224179)
          ·
            refine ⟨513757033839757944346836269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342504689226505296231224179 513757033839757944346836269)
            ·
              refine ⟨192658887689909229130063601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513757033839757944346836269 192658887689909229130063601)
              ·
                refine ⟨144494165767431921847547701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192658887689909229130063601 144494165767431921847547701)
                ·
                  refine ⟨13546328040696742673207597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144494165767431921847547701 13546328040696742673207597)
                  ·
                    refine ⟨5079873015261278502452849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13546328040696742673207597 5079873015261278502452849)
                    ·
                      refine ⟨3809904761445958876839637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079873015261278502452849 3809904761445958876839637)
                      ·
                        rfl

theorem cell23_7419763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3, 2].length) (baseStart_7419763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419763 prefixEnd_7419763 := by exact prefixLift 7419763
  have htrace : WordTrace (prefixWord ++ tailWord_7419763) baseStart_7419763 baseEnd_7419763 := by
    simpa [prefixWord, tailWord_7419763, baseEnd_7419763] using wordTrace_append hprefix tailTrace_7419763
  have hstable : (prefixWord ++ tailWord_7419763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419763).length < 2 ^ (prefixWord ++ tailWord_7419763).sum := by decide
  have hdescent : baseEnd_7419763 < baseStart_7419763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419776 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_7419776 : Nat := 118140960795 + 7419776 * 2 ^ 59
def prefixEnd_7419776 : Nat := 4983230072969 + 3 ^ 40 * 7419776 * 2
def baseEnd_7419776 : Nat := 3809911436694467325977077

theorem tailTrace_7419776 : CollatzResearch.WordTrace tailWord_7419776 prefixEnd_7419776 3809911436694467325977077 := by
  unfold tailWord_7419776
  simp only [CollatzResearch.WordTrace]
  refine ⟨135310731583713111849607591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180414308778284149132810121 135310731583713111849607591)
  ·
    refine ⟨202966097375569667774411387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135310731583713111849607591 202966097375569667774411387)
    ·
      refine ⟨304449146063354501661617081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202966097375569667774411387 304449146063354501661617081)
      ·
        refine ⟨228336859547515876246212811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304449146063354501661617081 228336859547515876246212811)
        ·
          refine ⟨342505289321273814369319217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228336859547515876246212811 342505289321273814369319217)
          ·
            refine ⟨256878966990955360776989413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342505289321273814369319217 256878966990955360776989413)
            ·
              refine ⟨48164806310804130145685515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256878966990955360776989413 48164806310804130145685515)
              ·
                refine ⟨72247209466206195218528273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48164806310804130145685515 72247209466206195218528273)
                ·
                  refine ⟨54185407099654646413896205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72247209466206195218528273 54185407099654646413896205)
                  ·
                    refine ⟨20319527662370492405211077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54185407099654646413896205 20319527662370492405211077)
                    ·
                      refine ⟨3809911436694467325977077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20319527662370492405211077 3809911436694467325977077)
                      ·
                        rfl

theorem cell23_7419776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_7419776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419776 prefixEnd_7419776 := by exact prefixLift 7419776
  have htrace : WordTrace (prefixWord ++ tailWord_7419776) baseStart_7419776 baseEnd_7419776 := by
    simpa [prefixWord, tailWord_7419776, baseEnd_7419776] using wordTrace_append hprefix tailTrace_7419776
  have hstable : (prefixWord ++ tailWord_7419776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419776).length < 2 ^ (prefixWord ++ tailWord_7419776).sum := by decide
  have hdescent : baseEnd_7419776 < baseStart_7419776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419822 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7419822 : Nat := 118140960795 + 7419822 * 2 ^ 59
def prefixEnd_7419822 : Nat := 4983230072969 + 3 ^ 40 * 7419822 * 2
def baseEnd_7419822 : Nat := 3809935056804574146001867

theorem tailTrace_7419822 : CollatzResearch.WordTrace tailWord_7419822 prefixEnd_7419822 3809935056804574146001867 := by
  unfold tailWord_7419822
  simp only [CollatzResearch.WordTrace]
  refine ⟨33827892615657446694423715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180415427283506382370259813 33827892615657446694423715)
  ·
    refine ⟨50741838923486170041635573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33827892615657446694423715 50741838923486170041635573)
    ·
      refine ⟨4757047399076828441403335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50741838923486170041635573 4757047399076828441403335)
      ·
        refine ⟨7135571098615242662105003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757047399076828441403335 7135571098615242662105003)
        ·
          refine ⟨10703356647922863993157505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135571098615242662105003 10703356647922863993157505)
          ·
            refine ⟨8027517485942147994868129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10703356647922863993157505 8027517485942147994868129)
            ·
              refine ⟨6020638114456610996151097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027517485942147994868129 6020638114456610996151097)
              ·
                refine ⟨4515478585842458247113323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020638114456610996151097 4515478585842458247113323)
                ·
                  refine ⟨6773217878763687370669985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515478585842458247113323 6773217878763687370669985)
                  ·
                    refine ⟨5079913409072765528002489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773217878763687370669985 5079913409072765528002489)
                    ·
                      refine ⟨3809935056804574146001867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079913409072765528002489 3809935056804574146001867)
                      ·
                        rfl

theorem cell23_7419822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7419822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419822 prefixEnd_7419822 := by exact prefixLift 7419822
  have htrace : WordTrace (prefixWord ++ tailWord_7419822) baseStart_7419822 baseEnd_7419822 := by
    simpa [prefixWord, tailWord_7419822, baseEnd_7419822] using wordTrace_append hprefix tailTrace_7419822
  have hstable : (prefixWord ++ tailWord_7419822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419822).length < 2 ^ (prefixWord ++ tailWord_7419822).sum := by decide
  have hdescent : baseEnd_7419822 < baseStart_7419822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419826 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_7419826 : Nat := 118140960795 + 7419826 * 2 ^ 59
def prefixEnd_7419826 : Nat := 4983230072969 + 3 ^ 40 * 7419826 * 2
def baseEnd_7419826 : Nat := 3809937110727192130351847

theorem tailTrace_7419826 : CollatzResearch.WordTrace tailWord_7419826 prefixEnd_7419826 3809937110727192130351847 := by
  unfold tailWord_7419826
  simp only [CollatzResearch.WordTrace]
  refine ⟨67655821704311270559633833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180415524544830054825690221 67655821704311270559633833)
  ·
    refine ⟨50741866278233452919725375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67655821704311270559633833 50741866278233452919725375)
    ·
      refine ⟨76112799417350179379588063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50741866278233452919725375 76112799417350179379588063)
      ·
        refine ⟨114169199126025269069382095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76112799417350179379588063 114169199126025269069382095)
        ·
          refine ⟨171253798689037903604073143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114169199126025269069382095 171253798689037903604073143)
          ·
            refine ⟨256880698033556855406109715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171253798689037903604073143 256880698033556855406109715)
            ·
              refine ⟨385321047050335283109164573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256880698033556855406109715 385321047050335283109164573)
              ·
                refine ⟨144495392643875731165936715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385321047050335283109164573 144495392643875731165936715)
                ·
                  refine ⟨216743088965813596748905073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144495392643875731165936715 216743088965813596748905073)
                  ·
                    refine ⟨162557316724360197561678805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216743088965813596748905073 162557316724360197561678805)
                    ·
                      refine ⟨3809937110727192130351847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162557316724360197561678805 3809937110727192130351847)
                      ·
                        rfl

theorem cell23_7419826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_7419826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419826 prefixEnd_7419826 := by exact prefixLift 7419826
  have htrace : WordTrace (prefixWord ++ tailWord_7419826) baseStart_7419826 baseEnd_7419826 := by
    simpa [prefixWord, tailWord_7419826, baseEnd_7419826] using wordTrace_append hprefix tailTrace_7419826
  have hstable : (prefixWord ++ tailWord_7419826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419826).length < 2 ^ (prefixWord ++ tailWord_7419826).sum := by decide
  have hdescent : baseEnd_7419826 < baseStart_7419826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419827 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 2, 2, 2]
def baseStart_7419827 : Nat := 118140960795 + 7419827 * 2 ^ 59
def prefixEnd_7419827 : Nat := 4983230072969 + 3 ^ 40 * 7419827 * 2
def baseEnd_7419827 : Nat := 3809937624207846626439343

theorem tailTrace_7419827 : CollatzResearch.WordTrace tailWord_7419827 prefixEnd_7419827 3809937624207846626439343 := by
  unfold tailWord_7419827
  simp only [CollatzResearch.WordTrace]
  refine ⟨270623323290241459409321735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180415548860160972939547823 270623323290241459409321735)
  ·
    refine ⟨405934984935362189113982603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270623323290241459409321735 405934984935362189113982603)
    ·
      refine ⟨608902477403043283670973905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405934984935362189113982603 608902477403043283670973905)
      ·
        refine ⟨456676858052282462753230429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608902477403043283670973905 456676858052282462753230429)
        ·
          refine ⟨171253821769605923532461411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456676858052282462753230429 171253821769605923532461411)
          ·
            refine ⟨256880732654408885298692117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171253821769605923532461411 256880732654408885298692117)
            ·
              refine ⟨12041284343175416498376193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256880732654408885298692117 12041284343175416498376193)
              ·
                refine ⟨9030963257381562373782145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12041284343175416498376193 9030963257381562373782145)
                ·
                  refine ⟨6773222443036171780336609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9030963257381562373782145 6773222443036171780336609)
                  ·
                    refine ⟨5079916832277128835252457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773222443036171780336609 5079916832277128835252457)
                    ·
                      refine ⟨3809937624207846626439343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079916832277128835252457 3809937624207846626439343)
                      ·
                        rfl

theorem cell23_7419827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 2, 2].length) (baseStart_7419827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419827 prefixEnd_7419827 := by exact prefixLift 7419827
  have htrace : WordTrace (prefixWord ++ tailWord_7419827) baseStart_7419827 baseEnd_7419827 := by
    simpa [prefixWord, tailWord_7419827, baseEnd_7419827] using wordTrace_append hprefix tailTrace_7419827
  have hstable : (prefixWord ++ tailWord_7419827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419827).length < 2 ^ (prefixWord ++ tailWord_7419827).sum := by decide
  have hdescent : baseEnd_7419827 < baseStart_7419827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419856 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_7419856 : Nat := 118140960795 + 7419856 * 2 ^ 59
def prefixEnd_7419856 : Nat := 4983230072969 + 3 ^ 40 * 7419856 * 2
def baseEnd_7419856 : Nat := 3809952515146827012976709

theorem tailTrace_7419856 : CollatzResearch.WordTrace tailWord_7419856 prefixEnd_7419856 3809952515146827012976709 := by
  unfold tailWord_7419856
  simp only [CollatzResearch.WordTrace]
  refine ⟨135312190503568198681063711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180416254004757598241418281 135312190503568198681063711)
  ·
    refine ⟨202968285755352298021595567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135312190503568198681063711 202968285755352298021595567)
    ·
      refine ⟨304452428633028447032393351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202968285755352298021595567 304452428633028447032393351)
      ·
        refine ⟨456678642949542670548590027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304452428633028447032393351 456678642949542670548590027)
        ·
          refine ⟨685017964424314005822885041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456678642949542670548590027 685017964424314005822885041)
          ·
            refine ⟨513763473318235504367163781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685017964424314005822885041 513763473318235504367163781)
            ·
              refine ⟨96330651247169157068843209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513763473318235504367163781 96330651247169157068843209)
              ·
                refine ⟨72247988435376867801632407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96330651247169157068843209 72247988435376867801632407)
                ·
                  refine ⟨108371982653065301702448611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72247988435376867801632407 108371982653065301702448611)
                  ·
                    refine ⟨162557973979597952553672917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108371982653065301702448611 162557973979597952553672917)
                    ·
                      refine ⟨3809952515146827012976709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162557973979597952553672917 3809952515146827012976709)
                      ·
                        rfl

theorem cell23_7419856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_7419856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419856 prefixEnd_7419856 := by exact prefixLift 7419856
  have htrace : WordTrace (prefixWord ++ tailWord_7419856) baseStart_7419856 baseEnd_7419856 := by
    simpa [prefixWord, tailWord_7419856, baseEnd_7419856] using wordTrace_append hprefix tailTrace_7419856
  have hstable : (prefixWord ++ tailWord_7419856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419856).length < 2 ^ (prefixWord ++ tailWord_7419856).sum := by decide
  have hdescent : baseEnd_7419856 < baseStart_7419856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419883 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 4]
def baseStart_7419883 : Nat := 118140960795 + 7419883 * 2 ^ 59
def prefixEnd_7419883 : Nat := 4983230072969 + 3 ^ 40 * 7419883 * 2
def baseEnd_7419883 : Nat := 3809966379124498407339085

theorem tailTrace_7419883 : CollatzResearch.WordTrace tailWord_7419883 prefixEnd_7419883 3809966379124498407339085 := by
  unfold tailWord_7419883
  simp only [CollatzResearch.WordTrace]
  refine ⟨270625365778038580973360303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180416910518692387315573535 270625365778038580973360303)
  ·
    refine ⟨405938048667057871460040455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270625365778038580973360303 405938048667057871460040455)
    ·
      refine ⟨608907073000586807190060683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405938048667057871460040455 608907073000586807190060683)
      ·
        refine ⟨913360609500880210785091025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608907073000586807190060683 913360609500880210785091025)
        ·
          refine ⟨685020457125660158088818269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913360609500880210785091025 685020457125660158088818269)
          ·
            refine ⟨256882671422122559283306851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 685020457125660158088818269 256882671422122559283306851)
            ·
              refine ⟨385324007133183838924960277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256882671422122559283306851 385324007133183838924960277)
              ·
                refine ⟨18062062834367992449607513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385324007133183838924960277 18062062834367992449607513)
                ·
                  refine ⟨13546547125775994337205635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18062062834367992449607513 13546547125775994337205635)
                  ·
                    refine ⟨20319820688663991505808453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13546547125775994337205635 20319820688663991505808453)
                    ·
                      refine ⟨3809966379124498407339085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20319820688663991505808453 3809966379124498407339085)
                      ·
                        rfl

theorem cell23_7419883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 4].length) (baseStart_7419883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419883 prefixEnd_7419883 := by exact prefixLift 7419883
  have htrace : WordTrace (prefixWord ++ tailWord_7419883) baseStart_7419883 baseEnd_7419883 := by
    simpa [prefixWord, tailWord_7419883, baseEnd_7419883] using wordTrace_append hprefix tailTrace_7419883
  have hstable : (prefixWord ++ tailWord_7419883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419883).length < 2 ^ (prefixWord ++ tailWord_7419883).sum := by decide
  have hdescent : baseEnd_7419883 < baseStart_7419883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419900 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_7419900 : Nat := 118140960795 + 7419900 * 2 ^ 59
def prefixEnd_7419900 : Nat := 4983230072969 + 3 ^ 40 * 7419900 * 2
def baseEnd_7419900 : Nat := 3809975108295624840826507

theorem tailTrace_7419900 : CollatzResearch.WordTrace tailWord_7419900 prefixEnd_7419900 3809975108295624840826507 := by
  unfold tailWord_7419900
  simp only [CollatzResearch.WordTrace]
  refine ⟨135312992909488496438364577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180417323879317995251152769 135312992909488496438364577)
  ·
    refine ⟨101484744682116372328773433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135312992909488496438364577 101484744682116372328773433)
    ·
      refine ⟨76113558511587279246580075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101484744682116372328773433 76113558511587279246580075)
      ·
        refine ⟨114170337767380918869870113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76113558511587279246580075 114170337767380918869870113)
        ·
          refine ⟨85627753325535689152402585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114170337767380918869870113 85627753325535689152402585)
          ·
            refine ⟨64220814994151766864301939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85627753325535689152402585 64220814994151766864301939)
            ·
              refine ⟨96331222491227650296452909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64220814994151766864301939 96331222491227650296452909)
              ·
                refine ⟨36124208434210368861169841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96331222491227650296452909 36124208434210368861169841)
                ·
                  refine ⟨27093156325657776645877381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36124208434210368861169841 27093156325657776645877381)
                  ·
                    refine ⟨5079966811060833121102009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27093156325657776645877381 5079966811060833121102009)
                    ·
                      refine ⟨3809975108295624840826507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5079966811060833121102009 3809975108295624840826507)
                      ·
                        rfl

theorem cell23_7419900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_7419900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419900 prefixEnd_7419900 := by exact prefixLift 7419900
  have htrace : WordTrace (prefixWord ++ tailWord_7419900) baseStart_7419900 baseEnd_7419900 := by
    simpa [prefixWord, tailWord_7419900, baseEnd_7419900] using wordTrace_append hprefix tailTrace_7419900
  have hstable : (prefixWord ++ tailWord_7419900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419900).length < 2 ^ (prefixWord ++ tailWord_7419900).sum := by decide
  have hdescent : baseEnd_7419900 < baseStart_7419900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419937 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_7419937 : Nat := 118140960795 + 7419937 * 2 ^ 59
def prefixEnd_7419937 : Nat := 4983230072969 + 3 ^ 40 * 7419937 * 2
def baseEnd_7419937 : Nat := 3809994107079841196063837

theorem tailTrace_7419937 : CollatzResearch.WordTrace tailWord_7419937 prefixEnd_7419937 3809994107079841196063837 := by
  unfold tailWord_7419937
  simp only [CollatzResearch.WordTrace]
  refine ⟨270627335319842948195826065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180418223546561965463884043 270627335319842948195826065)
  ·
    refine ⟨202970501489882211146869549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270627335319842948195826065 202970501489882211146869549)
    ·
      refine ⟨76113938058705829180076081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202970501489882211146869549 76113938058705829180076081)
      ·
        refine ⟨57085453544029371885057061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76113938058705829180076081 57085453544029371885057061)
        ·
          refine ⟨10703522539505507228448199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57085453544029371885057061 10703522539505507228448199)
          ·
            refine ⟨16055283809258260842672299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10703522539505507228448199 16055283809258260842672299)
            ·
              refine ⟨24082925713887391264008449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16055283809258260842672299 24082925713887391264008449)
              ·
                refine ⟨18062194285415543448006337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24082925713887391264008449 18062194285415543448006337)
                ·
                  refine ⟨13546645714061657586004753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18062194285415543448006337 13546645714061657586004753)
                  ·
                    refine ⟨10159984285546243189503565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13546645714061657586004753 10159984285546243189503565)
                    ·
                      refine ⟨3809994107079841196063837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10159984285546243189503565 3809994107079841196063837)
                      ·
                        rfl

theorem cell23_7419937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_7419937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419937 prefixEnd_7419937 := by exact prefixLift 7419937
  have htrace : WordTrace (prefixWord ++ tailWord_7419937) baseStart_7419937 baseEnd_7419937 := by
    simpa [prefixWord, tailWord_7419937, baseEnd_7419937] using wordTrace_append hprefix tailTrace_7419937
  have hstable : (prefixWord ++ tailWord_7419937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419937).length < 2 ^ (prefixWord ++ tailWord_7419937).sum := by decide
  have hdescent : baseEnd_7419937 < baseStart_7419937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419977 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 2, 3, 2]
def baseStart_7419977 : Nat := 118140960795 + 7419977 * 2 ^ 59
def prefixEnd_7419977 : Nat := 4983230072969 + 3 ^ 40 * 7419977 * 2
def baseEnd_7419977 : Nat := 3810014646306021039563653

theorem tailTrace_7419977 : CollatzResearch.WordTrace tailWord_7419977 prefixEnd_7419977 3810014646306021039563653 := by
  unfold tailWord_7419977
  simp only [CollatzResearch.WordTrace]
  refine ⟨270628794239698035027282185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180419196159798690018188123 270628794239698035027282185)
  ·
    refine ⟨202971595679773526270461639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270628794239698035027282185 202971595679773526270461639)
    ·
      refine ⟨304457393519660289405692459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202971595679773526270461639 304457393519660289405692459)
      ·
        refine ⟨456686090279490434108538689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304457393519660289405692459 456686090279490434108538689)
        ·
          refine ⟨342514567709617825581404017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456686090279490434108538689 342514567709617825581404017)
          ·
            refine ⟨256885925782213369186053013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342514567709617825581404017 256885925782213369186053013)
            ·
              refine ⟨12041527771041251680596235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256885925782213369186053013 12041527771041251680596235)
              ·
                refine ⟨18062291656561877520894353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12041527771041251680596235 18062291656561877520894353)
                ·
                  refine ⟨13546718742421408140670765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18062291656561877520894353 13546718742421408140670765)
                  ·
                    refine ⟨5080019528408028052751537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13546718742421408140670765 5080019528408028052751537)
                    ·
                      refine ⟨3810014646306021039563653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080019528408028052751537 3810014646306021039563653)
                      ·
                        rfl

theorem cell23_7419977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 3, 2].length) (baseStart_7419977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419977 prefixEnd_7419977 := by exact prefixLift 7419977
  have htrace : WordTrace (prefixWord ++ tailWord_7419977) baseStart_7419977 baseEnd_7419977 := by
    simpa [prefixWord, tailWord_7419977, baseEnd_7419977] using wordTrace_append hprefix tailTrace_7419977
  have hstable : (prefixWord ++ tailWord_7419977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419977).length < 2 ^ (prefixWord ++ tailWord_7419977).sum := by decide
  have hdescent : baseEnd_7419977 < baseStart_7419977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7419983 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 1, 6]
def baseStart_7419983 : Nat := 118140960795 + 7419983 * 2 ^ 59
def prefixEnd_7419983 : Nat := 4983230072969 + 3 ^ 40 * 7419983 * 2
def baseEnd_7419983 : Nat := 1270005909063316005362875

theorem tailTrace_7419983 : CollatzResearch.WordTrace tailWord_7419983 prefixEnd_7419983 1270005909063316005362875 := by
  unfold tailWord_7419983
  simp only [CollatzResearch.WordTrace]
  refine ⟨270629013077676298052000603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180419342051784198701333735 270629013077676298052000603)
  ·
    refine ⟨405943519616514447078000905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270629013077676298052000603 405943519616514447078000905)
    ·
      refine ⟨304457639712385835308500679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405943519616514447078000905 304457639712385835308500679)
      ·
        refine ⟨456686459568578752962751019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304457639712385835308500679 456686459568578752962751019)
        ·
          refine ⟨685029689352868129444126529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456686459568578752962751019 685029689352868129444126529)
          ·
            refine ⟨513772267014651097083094897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685029689352868129444126529 513772267014651097083094897)
            ·
              refine ⟨385329200260988322812321173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513772267014651097083094897 385329200260988322812321173)
              ·
                refine ⟨18062306262233827631827555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385329200260988322812321173 18062306262233827631827555)
                ·
                  refine ⟨27093459393350741447741333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18062306262233827631827555 27093459393350741447741333)
                  ·
                    refine ⟨1270005909063316005362875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27093459393350741447741333 1270005909063316005362875)
                    ·
                      rfl

theorem cell23_7419983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_7419983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7419983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7419983 prefixEnd_7419983 := by exact prefixLift 7419983
  have htrace : WordTrace (prefixWord ++ tailWord_7419983) baseStart_7419983 baseEnd_7419983 := by
    simpa [prefixWord, tailWord_7419983, baseEnd_7419983] using wordTrace_append hprefix tailTrace_7419983
  have hstable : (prefixWord ++ tailWord_7419983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7419983).length < 2 ^ (prefixWord ++ tailWord_7419983).sum := by decide
  have hdescent : baseEnd_7419983 < baseStart_7419983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7419983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420003 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_7420003 : Nat := 118140960795 + 7420003 * 2 ^ 59
def prefixEnd_7420003 : Nat := 4983230072969 + 3 ^ 40 * 7420003 * 2
def baseEnd_7420003 : Nat := 3810027996803037937838533

theorem tailTrace_7420003 : CollatzResearch.WordTrace tailWord_7420003 prefixEnd_7420003 3810027996803037937838533 := by
  unfold tailWord_7420003
  simp only [CollatzResearch.WordTrace]
  refine ⟨270629742537603841467728663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180419828358402560978485775 270629742537603841467728663)
  ·
    refine ⟨405944613806405762201592995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270629742537603841467728663 405944613806405762201592995)
    ·
      refine ⟨608916920709608643302389493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405944613806405762201592995 608916920709608643302389493)
      ·
        refine ⟨57085961316525810309599015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 608916920709608643302389493 57085961316525810309599015)
        ·
          refine ⟨85628941974788715464398523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57085961316525810309599015 85628941974788715464398523)
          ·
            refine ⟨128443412962183073196597785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85628941974788715464398523 128443412962183073196597785)
            ·
              refine ⟨96332559721637304897448339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128443412962183073196597785 96332559721637304897448339)
              ·
                refine ⟨144498839582455957346172509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96332559721637304897448339 144498839582455957346172509)
                ·
                  refine ⟨54187064843420984004814691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144498839582455957346172509 54187064843420984004814691)
                  ·
                    refine ⟨81280597265131476007222037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54187064843420984004814691 81280597265131476007222037)
                    ·
                      refine ⟨3810027996803037937838533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81280597265131476007222037 3810027996803037937838533)
                      ·
                        rfl

theorem cell23_7420003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_7420003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420003 prefixEnd_7420003 := by exact prefixLift 7420003
  have htrace : WordTrace (prefixWord ++ tailWord_7420003) baseStart_7420003 baseEnd_7420003 := by
    simpa [prefixWord, tailWord_7420003, baseEnd_7420003] using wordTrace_append hprefix tailTrace_7420003
  have hstable : (prefixWord ++ tailWord_7420003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420003).length < 2 ^ (prefixWord ++ tailWord_7420003).sum := by decide
  have hdescent : baseEnd_7420003 < baseStart_7420003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420041 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 1, 2, 2]
def baseStart_7420041 : Nat := 118140960795 + 7420041 * 2 ^ 59
def prefixEnd_7420041 : Nat := 4983230072969 + 3 ^ 40 * 7420041 * 2
def baseEnd_7420041 : Nat := 3810047509067908789163359

theorem tailTrace_7420041 : CollatzResearch.WordTrace tailWord_7420041 prefixEnd_7420041 3810047509067908789163359 := by
  unfold tailWord_7420041
  simp only [CollatzResearch.WordTrace]
  refine ⟨270631128511466173957611977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180420752340977449305074651 270631128511466173957611977)
  ·
    refine ⟨202973346383599630468208983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270631128511466173957611977 202973346383599630468208983)
    ·
      refine ⟨304460019575399445702313475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202973346383599630468208983 304460019575399445702313475)
      ·
        refine ⟨456690029363099168553470213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304460019575399445702313475 456690029363099168553470213)
        ·
          refine ⟨85629380505581094103775665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456690029363099168553470213 85629380505581094103775665)
          ·
            refine ⟨64222035379185820577831749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85629380505581094103775665 64222035379185820577831749)
            ·
              refine ⟨12041631633597341358343453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64222035379185820577831749 12041631633597341358343453)
              ·
                refine ⟨4515611862599003009378795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12041631633597341358343453 4515611862599003009378795)
                ·
                  refine ⟨6773417793898504514068193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515611862599003009378795 6773417793898504514068193)
                  ·
                    refine ⟨5080063345423878385551145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773417793898504514068193 5080063345423878385551145)
                    ·
                      refine ⟨3810047509067908789163359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080063345423878385551145 3810047509067908789163359)
                      ·
                        rfl

theorem cell23_7420041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 1, 2, 2].length) (baseStart_7420041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420041 prefixEnd_7420041 := by exact prefixLift 7420041
  have htrace : WordTrace (prefixWord ++ tailWord_7420041) baseStart_7420041 baseEnd_7420041 := by
    simpa [prefixWord, tailWord_7420041, baseEnd_7420041] using wordTrace_append hprefix tailTrace_7420041
  have hstable : (prefixWord ++ tailWord_7420041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420041).length < 2 ^ (prefixWord ++ tailWord_7420041).sum := by decide
  have hdescent : baseEnd_7420041 < baseStart_7420041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420071 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7420071 : Nat := 118140960795 + 7420071 * 2 ^ 59
def prefixEnd_7420071 : Nat := 4983230072969 + 3 ^ 40 * 7420071 * 2
def baseEnd_7420071 : Nat := 3810062913487543671788221

theorem tailTrace_7420071 : CollatzResearch.WordTrace tailWord_7420071 prefixEnd_7420071 3810062913487543671788221 := by
  unfold tailWord_7420071
  simp only [CollatzResearch.WordTrace]
  refine ⟨270632222701357489081204067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180421481800904992720802711 270632222701357489081204067)
  ·
    refine ⟨405948334052036233621806101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270632222701357489081204067 405948334052036233621806101)
    ·
      refine ⟨19028828158689198451022161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405948334052036233621806101 19028828158689198451022161)
      ·
        refine ⟨14271621119016898838266621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19028828158689198451022161 14271621119016898838266621)
        ·
          refine ⟨5351857919631337064349983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14271621119016898838266621 5351857919631337064349983)
          ·
            refine ⟨8027786879447005596524975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351857919631337064349983 8027786879447005596524975)
            ·
              refine ⟨12041680319170508394787463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027786879447005596524975 12041680319170508394787463)
              ·
                refine ⟨18062520478755762592181195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12041680319170508394787463 18062520478755762592181195)
                ·
                  refine ⟨27093780718133643888271793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18062520478755762592181195 27093780718133643888271793)
                  ·
                    refine ⟨20320335538600232916203845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27093780718133643888271793 20320335538600232916203845)
                    ·
                      refine ⟨3810062913487543671788221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20320335538600232916203845 3810062913487543671788221)
                      ·
                        rfl

theorem cell23_7420071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7420071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420071 prefixEnd_7420071 := by exact prefixLift 7420071
  have htrace : WordTrace (prefixWord ++ tailWord_7420071) baseStart_7420071 baseEnd_7420071 := by
    simpa [prefixWord, tailWord_7420071, baseEnd_7420071] using wordTrace_append hprefix tailTrace_7420071
  have hstable : (prefixWord ++ tailWord_7420071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420071).length < 2 ^ (prefixWord ++ tailWord_7420071).sum := by decide
  have hdescent : baseEnd_7420071 < baseStart_7420071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420078 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7420078 : Nat := 118140960795 + 7420078 * 2 ^ 59
def prefixEnd_7420078 : Nat := 4983230072969 + 3 ^ 40 * 7420078 * 2
def baseEnd_7420078 : Nat := 3810066507852125144400689

theorem tailTrace_7420078 : CollatzResearch.WordTrace tailWord_7420078 prefixEnd_7420078 3810066507852125144400689 := by
  unfold tailWord_7420078
  simp only [CollatzResearch.WordTrace]
  refine ⟨33829059751541516159588611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180421652008221419517805925 33829059751541516159588611)
  ·
    refine ⟨50743589627312274239382917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33829059751541516159588611 50743589627312274239382917)
    ·
      refine ⟨9514423055121051419884297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50743589627312274239382917 9514423055121051419884297)
      ·
        refine ⟨7135817291340788564913223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9514423055121051419884297 7135817291340788564913223)
        ·
          refine ⟨10703725937011182847369835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135817291340788564913223 10703725937011182847369835)
          ·
            refine ⟨16055588905516774271054753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10703725937011182847369835 16055588905516774271054753)
            ·
              refine ⟨12041691679137580703291065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16055588905516774271054753 12041691679137580703291065)
              ·
                refine ⟨9031268759353185527468299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12041691679137580703291065 9031268759353185527468299)
                ·
                  refine ⟨13546903139029778291202449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9031268759353185527468299 13546903139029778291202449)
                  ·
                    refine ⟨10160177354272333718401837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13546903139029778291202449 10160177354272333718401837)
                    ·
                      refine ⟨3810066507852125144400689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10160177354272333718401837 3810066507852125144400689)
                      ·
                        rfl

theorem cell23_7420078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7420078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420078 prefixEnd_7420078 := by exact prefixLift 7420078
  have htrace : WordTrace (prefixWord ++ tailWord_7420078) baseStart_7420078 baseEnd_7420078 := by
    simpa [prefixWord, tailWord_7420078, baseEnd_7420078] using wordTrace_append hprefix tailTrace_7420078
  have hstable : (prefixWord ++ tailWord_7420078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420078).length < 2 ^ (prefixWord ++ tailWord_7420078).sum := by decide
  have hdescent : baseEnd_7420078 < baseStart_7420078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420157 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_7420157 : Nat := 118140960795 + 7420157 * 2 ^ 59
def prefixEnd_7420157 : Nat := 4983230072969 + 3 ^ 40 * 7420157 * 2
def baseEnd_7420157 : Nat := 3810107072823830335312825

theorem tailTrace_7420157 : CollatzResearch.WordTrace tailWord_7420157 prefixEnd_7420157 3810107072823830335312825 := by
  unfold tailWord_7420157
  simp only [CollatzResearch.WordTrace]
  refine ⟨270635359379045925768834725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180423572919363950512556483 270635359379045925768834725)
  ·
    refine ⟨50744129883571111081656511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270635359379045925768834725 50744129883571111081656511)
    ·
      refine ⟨76116194825356666622484767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50744129883571111081656511 76116194825356666622484767)
      ·
        refine ⟨114174292238034999933727151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76116194825356666622484767 114174292238034999933727151)
        ·
          refine ⟨171261438357052499900590727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114174292238034999933727151 171261438357052499900590727)
          ·
            refine ⟨256892157535578749850886091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171261438357052499900590727 256892157535578749850886091)
            ·
              refine ⟨385338236303368124776329137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256892157535578749850886091 385338236303368124776329137)
              ·
                refine ⟨289003677227526093582246853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385338236303368124776329137 289003677227526093582246853)
                ·
                  refine ⟨54188189480161142546671285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289003677227526093582246853 54188189480161142546671285)
                  ·
                    refine ⟨5080142763765107113750433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54188189480161142546671285 5080142763765107113750433)
                    ·
                      refine ⟨3810107072823830335312825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080142763765107113750433 3810107072823830335312825)
                      ·
                        rfl

theorem cell23_7420157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_7420157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420157 prefixEnd_7420157 := by exact prefixLift 7420157
  have htrace : WordTrace (prefixWord ++ tailWord_7420157) baseStart_7420157 baseEnd_7420157 := by
    simpa [prefixWord, tailWord_7420157, baseEnd_7420157] using wordTrace_append hprefix tailTrace_7420157
  have hstable : (prefixWord ++ tailWord_7420157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420157).length < 2 ^ (prefixWord ++ tailWord_7420157).sum := by decide
  have hdescent : baseEnd_7420157 < baseStart_7420157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420160 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_7420160 : Nat := 118140960795 + 7420160 * 2 ^ 59
def prefixEnd_7420160 : Nat := 4983230072969 + 3 ^ 40 * 7420160 * 2
def baseEnd_7420160 : Nat := 3810108613265793823575311

theorem tailTrace_7420160 : CollatzResearch.WordTrace tailWord_7420160 prefixEnd_7420160 3810108613265793823575311 := by
  unfold tailWord_7420160
  simp only [CollatzResearch.WordTrace]
  refine ⟨135317734399017528640596967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180423645865356704854129289 135317734399017528640596967)
  ·
    refine ⟨202976601598526292960895451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135317734399017528640596967 202976601598526292960895451)
    ·
      refine ⟨304464902397789439441343177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202976601598526292960895451 304464902397789439441343177)
      ·
        refine ⟨228348676798342079581007383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304464902397789439441343177 228348676798342079581007383)
        ·
          refine ⟨342523015197513119371511075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228348676798342079581007383 342523015197513119371511075)
          ·
            refine ⟨513784522796269679057266613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342523015197513119371511075 513784522796269679057266613)
            ·
              refine ⟨48167299012150282411618745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 513784522796269679057266613 48167299012150282411618745)
              ·
                refine ⟨36125474259112711808714059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48167299012150282411618745 36125474259112711808714059)
                ·
                  refine ⟨54188211388669067713071089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36125474259112711808714059 54188211388669067713071089)
                  ·
                    refine ⟨40641158541501800784803317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54188211388669067713071089 40641158541501800784803317)
                    ·
                      refine ⟨3810108613265793823575311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40641158541501800784803317 3810108613265793823575311)
                      ·
                        rfl

theorem cell23_7420160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_7420160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420160 prefixEnd_7420160 := by exact prefixLift 7420160
  have htrace : WordTrace (prefixWord ++ tailWord_7420160) baseStart_7420160 baseEnd_7420160 := by
    simpa [prefixWord, tailWord_7420160, baseEnd_7420160] using wordTrace_append hprefix tailTrace_7420160
  have hstable : (prefixWord ++ tailWord_7420160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420160).length < 2 ^ (prefixWord ++ tailWord_7420160).sum := by decide
  have hdescent : baseEnd_7420160 < baseStart_7420160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420187 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 6, 2]
def baseStart_7420187 : Nat := 118140960795 + 7420187 * 2 ^ 59
def prefixEnd_7420187 : Nat := 4983230072969 + 3 ^ 40 * 7420187 * 2
def baseEnd_7420187 : Nat := 3810122477243465217937687

theorem tailTrace_7420187 : CollatzResearch.WordTrace tailWord_7420187 prefixEnd_7420187 3810122477243465217937687 := by
  unfold tailWord_7420187
  simp only [CollatzResearch.WordTrace]
  refine ⟨270636453568937240892426815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180424302379291493928284543 270636453568937240892426815)
  ·
    refine ⟨405954680353405861338640223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270636453568937240892426815 405954680353405861338640223)
    ·
      refine ⟨608932020530108792007960335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405954680353405861338640223 608932020530108792007960335)
      ·
        refine ⟨913398030795163188011940503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608932020530108792007960335 913398030795163188011940503)
        ·
          refine ⟨1370097046192744782017910755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913398030795163188011940503 1370097046192744782017910755)
          ·
            refine ⟨2055145569289117173026866133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370097046192744782017910755 2055145569289117173026866133)
            ·
              refine ⟨48167474280213683742817175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2055145569289117173026866133 48167474280213683742817175)
              ·
                refine ⟨72251211420320525614225763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48167474280213683742817175 72251211420320525614225763)
                ·
                  refine ⟨108376817130480788421338645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72251211420320525614225763 108376817130480788421338645)
                  ·
                    refine ⟨5080163302991286957250249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108376817130480788421338645 5080163302991286957250249)
                    ·
                      refine ⟨3810122477243465217937687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080163302991286957250249 3810122477243465217937687)
                      ·
                        rfl

theorem cell23_7420187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6, 2].length) (baseStart_7420187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420187 prefixEnd_7420187 := by exact prefixLift 7420187
  have htrace : WordTrace (prefixWord ++ tailWord_7420187) baseStart_7420187 baseEnd_7420187 := by
    simpa [prefixWord, tailWord_7420187, baseEnd_7420187] using wordTrace_append hprefix tailTrace_7420187
  have hstable : (prefixWord ++ tailWord_7420187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420187).length < 2 ^ (prefixWord ++ tailWord_7420187).sum := by decide
  have hdescent : baseEnd_7420187 < baseStart_7420187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420217 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7420217 : Nat := 118140960795 + 7420217 * 2 ^ 59
def prefixEnd_7420217 : Nat := 4983230072969 + 3 ^ 40 * 7420217 * 2
def baseEnd_7420217 : Nat := 3810137881663100100562549

theorem tailTrace_7420217 : CollatzResearch.WordTrace tailWord_7420217 prefixEnd_7420217 3810137881663100100562549 := by
  unfold tailWord_7420217
  simp only [CollatzResearch.WordTrace]
  refine ⟨270637547758828556016018905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180425031839219037344012603 270637547758828556016018905)
  ·
    refine ⟨202978160819121417012014179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270637547758828556016018905 202978160819121417012014179)
    ·
      refine ⟨304467241228682125518021269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202978160819121417012014179 304467241228682125518021269)
      ·
        refine ⟨14271901932594474633657247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304467241228682125518021269 14271901932594474633657247)
        ·
          refine ⟨21407852898891711950485871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14271901932594474633657247 21407852898891711950485871)
          ·
            refine ⟨32111779348337567925728807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21407852898891711950485871 32111779348337567925728807)
            ·
              refine ⟨48167669022506351888593211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32111779348337567925728807 48167669022506351888593211)
              ·
                refine ⟨72251503533759527832889817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48167669022506351888593211 72251503533759527832889817)
                ·
                  refine ⟨54188627650319645874667363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72251503533759527832889817 54188627650319645874667363)
                  ·
                    refine ⟨81282941475479468812001045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54188627650319645874667363 81282941475479468812001045)
                    ·
                      refine ⟨3810137881663100100562549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81282941475479468812001045 3810137881663100100562549)
                      ·
                        rfl

theorem cell23_7420217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7420217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420217 prefixEnd_7420217 := by exact prefixLift 7420217
  have htrace : WordTrace (prefixWord ++ tailWord_7420217) baseStart_7420217 baseEnd_7420217 := by
    simpa [prefixWord, tailWord_7420217, baseEnd_7420217] using wordTrace_append hprefix tailTrace_7420217
  have hstable : (prefixWord ++ tailWord_7420217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420217).length < 2 ^ (prefixWord ++ tailWord_7420217).sum := by decide
  have hdescent : baseEnd_7420217 < baseStart_7420217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420227 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 6]
def baseStart_7420227 : Nat := 118140960795 + 7420227 * 2 ^ 59
def prefixEnd_7420227 : Nat := 4983230072969 + 3 ^ 40 * 7420227 * 2
def baseEnd_7420227 : Nat := 423349224052182784604167

theorem tailTrace_7420227 : CollatzResearch.WordTrace tailWord_7420227 prefixEnd_7420227 423349224052182784604167 := by
  unfold tailWord_7420227
  simp only [CollatzResearch.WordTrace]
  refine ⟨270637912488792327723882935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180425274992528218482588623 270637912488792327723882935)
  ·
    refine ⟨405956868733188491585824403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270637912488792327723882935 405956868733188491585824403)
    ·
      refine ⟨608935303099782737378736605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405956868733188491585824403 608935303099782737378736605)
      ·
        refine ⟨228350738662418526517026227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608935303099782737378736605 228350738662418526517026227)
        ·
          refine ⟨342526107993627789775539341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228350738662418526517026227 342526107993627789775539341)
          ·
            refine ⟨128447290497610421165827253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342526107993627789775539341 128447290497610421165827253)
            ·
              refine ⟨12041933484150976984296305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128447290497610421165827253 12041933484150976984296305)
              ·
                refine ⟨9031450113113232738222229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12041933484150976984296305 9031450113113232738222229)
                ·
                  refine ⟨423349224052182784604167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9031450113113232738222229 423349224052182784604167)
                  ·
                    rfl

theorem cell23_7420227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 6].length) (baseStart_7420227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420227 prefixEnd_7420227 := by exact prefixLift 7420227
  have htrace : WordTrace (prefixWord ++ tailWord_7420227) baseStart_7420227 baseEnd_7420227 := by
    simpa [prefixWord, tailWord_7420227, baseEnd_7420227] using wordTrace_append hprefix tailTrace_7420227
  have hstable : (prefixWord ++ tailWord_7420227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420227).length < 2 ^ (prefixWord ++ tailWord_7420227).sum := by decide
  have hdescent : baseEnd_7420227 < baseStart_7420227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420271 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 1, 1, 3]
def baseStart_7420271 : Nat := 118140960795 + 7420271 * 2 ^ 59
def prefixEnd_7420271 : Nat := 4983230072969 + 3 ^ 40 * 7420271 * 2
def baseEnd_7420271 : Nat := 3810165609618442889287301

theorem tailTrace_7420271 : CollatzResearch.WordTrace tailWord_7420271 prefixEnd_7420271 3810165609618442889287301 := by
  unfold tailWord_7420271
  simp only [CollatzResearch.WordTrace]
  refine ⟨270639517300632923238484667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180426344867088615492323111 270639517300632923238484667)
  ·
    refine ⟨405959275950949384857727001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270639517300632923238484667 405959275950949384857727001)
    ·
      refine ⟨304469456963212038643295251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405959275950949384857727001 304469456963212038643295251)
      ·
        refine ⟨456704185444818057964942877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304469456963212038643295251 456704185444818057964942877)
        ·
          refine ⟨171264069541806771736853579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456704185444818057964942877 171264069541806771736853579)
          ·
            refine ⟨256896104312710157605280369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171264069541806771736853579 256896104312710157605280369)
            ·
              refine ⟨192672078234532618203960277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256896104312710157605280369 192672078234532618203960277)
              ·
                refine ⟨4515751833621858239155319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192672078234532618203960277 4515751833621858239155319)
                ·
                  refine ⟨6773627750432787358732979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515751833621858239155319 6773627750432787358732979)
                  ·
                    refine ⟨10160441625649181038099469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773627750432787358732979 10160441625649181038099469)
                    ·
                      refine ⟨3810165609618442889287301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10160441625649181038099469 3810165609618442889287301)
                      ·
                        rfl

theorem cell23_7420271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 1, 3].length) (baseStart_7420271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420271 prefixEnd_7420271 := by exact prefixLift 7420271
  have htrace : WordTrace (prefixWord ++ tailWord_7420271) baseStart_7420271 baseEnd_7420271 := by
    simpa [prefixWord, tailWord_7420271, baseEnd_7420271] using wordTrace_append hprefix tailTrace_7420271
  have hstable : (prefixWord ++ tailWord_7420271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420271).length < 2 ^ (prefixWord ++ tailWord_7420271).sum := by decide
  have hdescent : baseEnd_7420271 < baseStart_7420271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420274 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_7420274 : Nat := 118140960795 + 7420274 * 2 ^ 59
def prefixEnd_7420274 : Nat := 4983230072969 + 3 ^ 40 * 7420274 * 2
def baseEnd_7420274 : Nat := 1270055716686802125849929

theorem tailTrace_7420274 : CollatzResearch.WordTrace tailWord_7420274 prefixEnd_7420274 1270055716686802125849929 := by
  unfold tailWord_7420274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67659906679905513687710969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180426417813081369833895917 67659906679905513687710969)
  ·
    refine ⟨50744930009929135265783227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67659906679905513687710969 50744930009929135265783227)
    ·
      refine ⟨76117395014893702898674841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50744930009929135265783227 76117395014893702898674841)
      ·
        refine ⟨57088046261170277174006131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76117395014893702898674841 57088046261170277174006131)
        ·
          refine ⟨85632069391755415761009197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57088046261170277174006131 85632069391755415761009197)
          ·
            refine ⟨32112026021908280910378449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85632069391755415761009197 32112026021908280910378449)
            ·
              refine ⟨24084019516431210682783837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32112026021908280910378449 24084019516431210682783837)
              ·
                refine ⟨9031507318661704006043939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24084019516431210682783837 9031507318661704006043939)
                ·
                  refine ⟨13547260977992556009065909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9031507318661704006043939 13547260977992556009065909)
                  ·
                    refine ⟨1270055716686802125849929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13547260977992556009065909 1270055716686802125849929)
                    ·
                      rfl

theorem cell23_7420274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_7420274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420274 prefixEnd_7420274 := by exact prefixLift 7420274
  have htrace : WordTrace (prefixWord ++ tailWord_7420274) baseStart_7420274 baseEnd_7420274 := by
    simpa [prefixWord, tailWord_7420274, baseEnd_7420274] using wordTrace_append hprefix tailTrace_7420274
  have hstable : (prefixWord ++ tailWord_7420274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420274).length < 2 ^ (prefixWord ++ tailWord_7420274).sum := by decide
  have hdescent : baseEnd_7420274 < baseStart_7420274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420308 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_7420308 : Nat := 118140960795 + 7420308 * 2 ^ 59
def prefixEnd_7420308 : Nat := 4983230072969 + 3 ^ 40 * 7420308 * 2
def baseEnd_7420308 : Nat := 1270061536134219748174877

theorem tailTrace_7420308 : CollatzResearch.WordTrace tailWord_7420308 prefixEnd_7420308 1270061536134219748174877 := by
  unfold tailWord_7420308
  simp only [CollatzResearch.WordTrace]
  refine ⟨135320433400749439278790789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180427244534332585705054385 135320433400749439278790789)
  ·
    refine ⟨25372581262640519864773273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135320433400749439278790789 25372581262640519864773273)
    ·
      refine ⟨19029435946980389898579955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25372581262640519864773273 19029435946980389898579955)
      ·
        refine ⟨28544153920470584847869933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19029435946980389898579955 28544153920470584847869933)
        ·
          refine ⟨10704057720176469317951225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28544153920470584847869933 10704057720176469317951225)
          ·
            refine ⟨8028043290132351988463419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10704057720176469317951225 8028043290132351988463419)
            ·
              refine ⟨12042064935198527982695129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8028043290132351988463419 12042064935198527982695129)
              ·
                refine ⟨9031548701398895987021347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12042064935198527982695129 9031548701398895987021347)
                ·
                  refine ⟨13547323052098343980532021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9031548701398895987021347 13547323052098343980532021)
                  ·
                    refine ⟨1270061536134219748174877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13547323052098343980532021 1270061536134219748174877)
                    ·
                      rfl

theorem cell23_7420308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_7420308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420308 prefixEnd_7420308 := by exact prefixLift 7420308
  have htrace : WordTrace (prefixWord ++ tailWord_7420308) baseStart_7420308 baseEnd_7420308 := by
    simpa [prefixWord, tailWord_7420308, baseEnd_7420308] using wordTrace_append hprefix tailTrace_7420308
  have hstable : (prefixWord ++ tailWord_7420308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420308).length < 2 ^ (prefixWord ++ tailWord_7420308).sum := by decide
  have hdescent : baseEnd_7420308 < baseStart_7420308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420311 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 3, 2, 2]
def baseStart_7420311 : Nat := 118140960795 + 7420311 * 2 ^ 59
def prefixEnd_7420311 : Nat := 4983230072969 + 3 ^ 40 * 7420311 * 2
def baseEnd_7420311 : Nat := 3810186148844622732787117

theorem tailTrace_7420311 : CollatzResearch.WordTrace tailWord_7420311 prefixEnd_7420311 3810186148844622732787117 := by
  unfold tailWord_7420311
  simp only [CollatzResearch.WordTrace]
  refine ⟨270640976220488010069940787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180427317480325340046627191 270640976220488010069940787)
  ·
    refine ⟨405961464330732015104911181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270640976220488010069940787 405961464330732015104911181)
    ·
      refine ⟨152235549124024505664341693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405961464330732015104911181 152235549124024505664341693)
      ·
        refine ⟨57088330921509189624128135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152235549124024505664341693 57088330921509189624128135)
        ·
          refine ⟨85632496382263784436192203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57088330921509189624128135 85632496382263784436192203)
          ·
            refine ⟨128448744573395676654288305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85632496382263784436192203 128448744573395676654288305)
            ·
              refine ⟨96336558430046757490716229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128448744573395676654288305 96336558430046757490716229)
              ·
                refine ⟨18063104705633767029509293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96336558430046757490716229 18063104705633767029509293)
                ·
                  refine ⟨6773664264612662636065985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18063104705633767029509293 6773664264612662636065985)
                  ·
                    refine ⟨5080248198459496977049489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773664264612662636065985 5080248198459496977049489)
                    ·
                      refine ⟨3810186148844622732787117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080248198459496977049489 3810186148844622732787117)
                      ·
                        rfl

theorem cell23_7420311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_7420311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420311 prefixEnd_7420311 := by exact prefixLift 7420311
  have htrace : WordTrace (prefixWord ++ tailWord_7420311) baseStart_7420311 baseEnd_7420311 := by
    simpa [prefixWord, tailWord_7420311, baseEnd_7420311] using wordTrace_append hprefix tailTrace_7420311
  have hstable : (prefixWord ++ tailWord_7420311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420311).length < 2 ^ (prefixWord ++ tailWord_7420311).sum := by decide
  have hdescent : baseEnd_7420311 < baseStart_7420311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420321 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 1, 6]
def baseStart_7420321 : Nat := 118140960795 + 7420321 * 2 ^ 59
def prefixEnd_7420321 : Nat := 4983230072969 + 3 ^ 40 * 7420321 * 2
def baseEnd_7420321 : Nat := 1270063761217055897887357

theorem tailTrace_7420321 : CollatzResearch.WordTrace tailWord_7420321 prefixEnd_7420321 1270063761217055897887357 := by
  unfold tailWord_7420321
  simp only [CollatzResearch.WordTrace]
  refine ⟨270641340950451781777804817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180427560633634521185203211 270641340950451781777804817)
  ·
    refine ⟨202981005712838836333353613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270641340950451781777804817 202981005712838836333353613)
    ·
      refine ⟨76117877142314563625007605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202981005712838836333353613 76117877142314563625007605)
      ·
        refine ⟨7136050982091990339844463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76117877142314563625007605 7136050982091990339844463)
        ·
          refine ⟨10704076473137985509766695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136050982091990339844463 10704076473137985509766695)
          ·
            refine ⟨16056114709706978264650043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10704076473137985509766695 16056114709706978264650043)
            ·
              refine ⟨24084172064560467396975065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16056114709706978264650043 24084172064560467396975065)
              ·
                refine ⟨18063129048420350547731299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24084172064560467396975065 18063129048420350547731299)
                ·
                  refine ⟨27094693572630525821596949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18063129048420350547731299 27094693572630525821596949)
                  ·
                    refine ⟨1270063761217055897887357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27094693572630525821596949 1270063761217055897887357)
                    ·
                      rfl

theorem cell23_7420321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_7420321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420321 prefixEnd_7420321 := by exact prefixLift 7420321
  have htrace : WordTrace (prefixWord ++ tailWord_7420321) baseStart_7420321 baseEnd_7420321 := by
    simpa [prefixWord, tailWord_7420321, baseEnd_7420321] using wordTrace_append hprefix tailTrace_7420321
  have hstable : (prefixWord ++ tailWord_7420321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420321).length < 2 ^ (prefixWord ++ tailWord_7420321).sum := by decide
  have hdescent : baseEnd_7420321 < baseStart_7420321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420345 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7420345 : Nat := 118140960795 + 7420345 * 2 ^ 59
def prefixEnd_7420345 : Nat := 4983230072969 + 3 ^ 40 * 7420345 * 2
def baseEnd_7420345 : Nat := 3810203607186875599761961

theorem tailTrace_7420345 : CollatzResearch.WordTrace tailWord_7420345 prefixEnd_7420345 3810203607186875599761961 := by
  unfold tailWord_7420345
  simp only [CollatzResearch.WordTrace]
  refine ⟨270642216302364833876678489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180428144201576555917785659 270642216302364833876678489)
  ·
    refine ⟨202981662226773625407508867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270642216302364833876678489 202981662226773625407508867)
    ·
      refine ⟨304472493340160438111263301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202981662226773625407508867 304472493340160438111263301)
      ·
        refine ⟨57088592501280082145861869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304472493340160438111263301 57088592501280082145861869)
        ·
          refine ⟨21408222187980030804698201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57088592501280082145861869 21408222187980030804698201)
          ·
            refine ⟨16056166640985023103523651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21408222187980030804698201 16056166640985023103523651)
            ·
              refine ⟨24084249961477534655285477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16056166640985023103523651 24084249961477534655285477)
              ·
                refine ⟨4515796867777037747866027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24084249961477534655285477 4515796867777037747866027)
                ·
                  refine ⟨6773695301665556621799041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515796867777037747866027 6773695301665556621799041)
                  ·
                    refine ⟨5080271476249167466349281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773695301665556621799041 5080271476249167466349281)
                    ·
                      refine ⟨3810203607186875599761961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080271476249167466349281 3810203607186875599761961)
                      ·
                        rfl

theorem cell23_7420345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7420345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420345 prefixEnd_7420345 := by exact prefixLift 7420345
  have htrace : WordTrace (prefixWord ++ tailWord_7420345) baseStart_7420345 baseEnd_7420345 := by
    simpa [prefixWord, tailWord_7420345, baseEnd_7420345] using wordTrace_append hprefix tailTrace_7420345
  have hstable : (prefixWord ++ tailWord_7420345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420345).length < 2 ^ (prefixWord ++ tailWord_7420345).sum := by decide
  have hdescent : baseEnd_7420345 < baseStart_7420345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420361 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 3]
def baseStart_7420361 : Nat := 118140960795 + 7420361 * 2 ^ 59
def prefixEnd_7420361 : Nat := 4983230072969 + 3 ^ 40 * 7420361 * 2
def baseEnd_7420361 : Nat := 3810211822877347537161887

theorem tailTrace_7420361 : CollatzResearch.WordTrace tailWord_7420361 prefixEnd_7420361 3810211822877347537161887 := by
  unfold tailWord_7420361
  simp only [CollatzResearch.WordTrace]
  refine ⟨270642799870306868609260937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180428533246871245739507291 270642799870306868609260937)
  ·
    refine ⟨202982099902730151456945703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270642799870306868609260937 202982099902730151456945703)
    ·
      refine ⟨304473149854095227185418555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202982099902730151456945703 304473149854095227185418555)
      ·
        refine ⟨456709724781142840778127833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304473149854095227185418555 456709724781142840778127833)
        ·
          refine ⟨342532293585857130583595875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456709724781142840778127833 342532293585857130583595875)
          ·
            refine ⟨513798440378785695875393813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342532293585857130583595875 513798440378785695875393813)
            ·
              refine ⟨24084301892755579494159085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 513798440378785695875393813 24084301892755579494159085)
              ·
                refine ⟨9031613209783342310309657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24084301892755579494159085 9031613209783342310309657)
                ·
                  refine ⟨6773709907337506732732243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9031613209783342310309657 6773709907337506732732243)
                  ·
                    refine ⟨10160564861006260099098365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773709907337506732732243 10160564861006260099098365)
                    ·
                      refine ⟨3810211822877347537161887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10160564861006260099098365 3810211822877347537161887)
                      ·
                        rfl

theorem cell23_7420361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_7420361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420361 prefixEnd_7420361 := by exact prefixLift 7420361
  have htrace : WordTrace (prefixWord ++ tailWord_7420361) baseStart_7420361 baseEnd_7420361 := by
    simpa [prefixWord, tailWord_7420361, baseEnd_7420361] using wordTrace_append hprefix tailTrace_7420361
  have hstable : (prefixWord ++ tailWord_7420361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420361).length < 2 ^ (prefixWord ++ tailWord_7420361).sum := by decide
  have hdescent : baseEnd_7420361 < baseStart_7420361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420367 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_7420367 : Nat := 118140960795 + 7420367 * 2 ^ 59
def prefixEnd_7420367 : Nat := 4983230072969 + 3 ^ 40 * 7420367 * 2
def baseEnd_7420367 : Nat := 3810214903761274513686859

theorem tailTrace_7420367 : CollatzResearch.WordTrace tailWord_7420367 prefixEnd_7420367 3810214903761274513686859 := by
  unfold tailWord_7420367
  simp only [CollatzResearch.WordTrace]
  refine ⟨270643018708285131633979355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180428679138856754422652903 270643018708285131633979355)
  ·
    refine ⟨405964528062427697450969033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270643018708285131633979355 405964528062427697450969033)
    ·
      refine ⟨304473396046820773088226775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405964528062427697450969033 304473396046820773088226775)
      ·
        refine ⟨456710094070231159632340163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304473396046820773088226775 456710094070231159632340163)
        ·
          refine ⟨685065141105346739448510245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456710094070231159632340163 685065141105346739448510245)
          ·
            refine ⟨128449713957252513646595671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 685065141105346739448510245 128449713957252513646595671)
            ·
              refine ⟨192674570935878770469893507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128449713957252513646595671 192674570935878770469893507)
              ·
                refine ⟨289011856403818155704840261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192674570935878770469893507 289011856403818155704840261)
                ·
                  refine ⟨54189723075715904194657549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289011856403818155704840261 54189723075715904194657549)
                  ·
                    refine ⟨20321146153393464072996581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54189723075715904194657549 20321146153393464072996581)
                    ·
                      refine ⟨3810214903761274513686859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20321146153393464072996581 3810214903761274513686859)
                      ·
                        rfl

theorem cell23_7420367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_7420367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420367 prefixEnd_7420367 := by exact prefixLift 7420367
  have htrace : WordTrace (prefixWord ++ tailWord_7420367) baseStart_7420367 baseEnd_7420367 := by
    simpa [prefixWord, tailWord_7420367, baseEnd_7420367] using wordTrace_append hprefix tailTrace_7420367
  have hstable : (prefixWord ++ tailWord_7420367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420367).length < 2 ^ (prefixWord ++ tailWord_7420367).sum := by decide
  have hdescent : baseEnd_7420367 < baseStart_7420367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420377 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_7420377 : Nat := 118140960795 + 7420377 * 2 ^ 59
def prefixEnd_7420377 : Nat := 4983230072969 + 3 ^ 40 * 7420377 * 2
def baseEnd_7420377 : Nat := 1270073346189273158187271

theorem tailTrace_7420377 : CollatzResearch.WordTrace tailWord_7420377 prefixEnd_7420377 1270073346189273158187271 := by
  unfold tailWord_7420377
  simp only [CollatzResearch.WordTrace]
  refine ⟨270643383438248903341843385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180428922292165935561228923 270643383438248903341843385)
  ·
    refine ⟨202982537578686677506382539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270643383438248903341843385 202982537578686677506382539)
    ·
      refine ⟨304473806368030016259573809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202982537578686677506382539 304473806368030016259573809)
      ·
        refine ⟨228355354776022512194680357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304473806368030016259573809 228355354776022512194680357)
        ·
          refine ⟨42816629020504221036502567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228355354776022512194680357 42816629020504221036502567)
          ·
            refine ⟨64224943530756331554753851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42816629020504221036502567 64224943530756331554753851)
            ·
              refine ⟨96337415296134497332130777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64224943530756331554753851 96337415296134497332130777)
              ·
                refine ⟨72253061472100872999098083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96337415296134497332130777 72253061472100872999098083)
                ·
                  refine ⟨108379592208151309498647125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72253061472100872999098083 108379592208151309498647125)
                  ·
                    refine ⟨1270073346189273158187271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108379592208151309498647125 1270073346189273158187271)
                    ·
                      rfl

theorem cell23_7420377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_7420377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420377 prefixEnd_7420377 := by exact prefixLift 7420377
  have htrace : WordTrace (prefixWord ++ tailWord_7420377) baseStart_7420377 baseEnd_7420377 := by
    simpa [prefixWord, tailWord_7420377, baseEnd_7420377] using wordTrace_append hprefix tailTrace_7420377
  have hstable : (prefixWord ++ tailWord_7420377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420377).length < 2 ^ (prefixWord ++ tailWord_7420377).sum := by decide
  have hdescent : baseEnd_7420377 < baseStart_7420377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420394 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_7420394 : Nat := 118140960795 + 7420394 * 2 ^ 59
def prefixEnd_7420394 : Nat := 4983230072969 + 3 ^ 40 * 7420394 * 2
def baseEnd_7420394 : Nat := 1270076255912981969349745

theorem tailTrace_7420394 : CollatzResearch.WordTrace tailWord_7420394 prefixEnd_7420394 1270076255912981969349745 := by
  unfold tailWord_7420394
  simp only [CollatzResearch.WordTrace]
  refine ⟨67661000869796828811303059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180429335652791543496808157 67661000869796828811303059)
  ·
    refine ⟨101491501304695243216954589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67661000869796828811303059 101491501304695243216954589)
    ·
      refine ⟨38059312989260716206357971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101491501304695243216954589 38059312989260716206357971)
      ·
        refine ⟨57088969483891074309536957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38059312989260716206357971 57088969483891074309536957)
        ·
          refine ⟨21408363556459152866076359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57088969483891074309536957 21408363556459152866076359)
          ·
            refine ⟨32112545334688729299114539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21408363556459152866076359 32112545334688729299114539)
            ·
              refine ⟨48168818002033093948671809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32112545334688729299114539 48168818002033093948671809)
              ·
                refine ⟨36126613501524820461503857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48168818002033093948671809 36126613501524820461503857)
                ·
                  refine ⟨27094960126143615346127893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36126613501524820461503857 27094960126143615346127893)
                  ·
                    refine ⟨1270076255912981969349745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27094960126143615346127893 1270076255912981969349745)
                    ·
                      rfl

theorem cell23_7420394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_7420394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420394 prefixEnd_7420394 := by exact prefixLift 7420394
  have htrace : WordTrace (prefixWord ++ tailWord_7420394) baseStart_7420394 baseEnd_7420394 := by
    simpa [prefixWord, tailWord_7420394, baseEnd_7420394] using wordTrace_append hprefix tailTrace_7420394
  have hstable : (prefixWord ++ tailWord_7420394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420394).length < 2 ^ (prefixWord ++ tailWord_7420394).sum := by decide
  have hdescent : baseEnd_7420394 < baseStart_7420394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420558 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7420558 : Nat := 118140960795 + 7420558 * 2 ^ 59
def prefixEnd_7420558 : Nat := 4983230072969 + 3 ^ 40 * 7420558 * 2
def baseEnd_7420558 : Nat := 3810312978566283266398481

theorem tailTrace_7420558 : CollatzResearch.WordTrace tailWord_7420558 prefixEnd_7420558 3810312978566283266398481 := by
  unfold tailWord_7420558
  simp only [CollatzResearch.WordTrace]
  refine ⟨33831248131324146406772791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180433323367062114169454885 33831248131324146406772791)
  ·
    refine ⟨50746872196986219610159187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33831248131324146406772791 50746872196986219610159187)
    ·
      refine ⟨76120308295479329415238781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50746872196986219610159187 76120308295479329415238781)
      ·
        refine ⟨28545115610804748530714543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76120308295479329415238781 28545115610804748530714543)
        ·
          refine ⟨42817673416207122796071815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28545115610804748530714543 42817673416207122796071815)
          ·
            refine ⟨64226510124310684194107723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42817673416207122796071815 64226510124310684194107723)
            ·
              refine ⟨96339765186466026291161585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64226510124310684194107723 96339765186466026291161585)
              ·
                refine ⟨72254823889849519718371189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96339765186466026291161585 72254823889849519718371189)
                ·
                  refine ⟨6773889739673392473597299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72254823889849519718371189 6773889739673392473597299)
                  ·
                    refine ⟨10160834609510088710395949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773889739673392473597299 10160834609510088710395949)
                    ·
                      refine ⟨3810312978566283266398481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10160834609510088710395949 3810312978566283266398481)
                      ·
                        rfl

theorem cell23_7420558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7420558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420558 prefixEnd_7420558 := by exact prefixLift 7420558
  have htrace : WordTrace (prefixWord ++ tailWord_7420558) baseStart_7420558 baseEnd_7420558 := by
    simpa [prefixWord, tailWord_7420558, baseEnd_7420558] using wordTrace_append hprefix tailTrace_7420558
  have hstable : (prefixWord ++ tailWord_7420558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420558).length < 2 ^ (prefixWord ++ tailWord_7420558).sum := by decide
  have hdescent : baseEnd_7420558 < baseStart_7420558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420568 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7420568 : Nat := 118140960795 + 7420568 * 2 ^ 59
def prefixEnd_7420568 : Nat := 4983230072969 + 3 ^ 40 * 7420568 * 2
def baseEnd_7420568 : Nat := 3810318113372828227273435

theorem tailTrace_7420568 : CollatzResearch.WordTrace tailWord_7420568 prefixEnd_7420568 3810318113372828227273435 := by
  unfold tailWord_7420568
  simp only [CollatzResearch.WordTrace]
  refine ⟨135325174890278471481023179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180433566520371295308030905 135325174890278471481023179)
  ·
    refine ⟨202987762335417707221534769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135325174890278471481023179 202987762335417707221534769)
    ·
      refine ⟨152240821751563280416151077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202987762335417707221534769 152240821751563280416151077)
      ·
        refine ⟨28545154078418115078028327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152240821751563280416151077 28545154078418115078028327)
        ·
          refine ⟨42817731117627172617042491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28545154078418115078028327 42817731117627172617042491)
          ·
            refine ⟨64226596676440758925563737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42817731117627172617042491 64226596676440758925563737)
            ·
              refine ⟨48169947507330569194172803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64226596676440758925563737 48169947507330569194172803)
              ·
                refine ⟨72254921260995853791259205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48169947507330569194172803 72254921260995853791259205)
                ·
                  refine ⟨13547797736436722585861101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72254921260995853791259205 13547797736436722585861101)
                  ·
                    refine ⟨5080424151163770969697913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13547797736436722585861101 5080424151163770969697913)
                    ·
                      refine ⟨3810318113372828227273435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080424151163770969697913 3810318113372828227273435)
                      ·
                        rfl

theorem cell23_7420568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7420568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420568 prefixEnd_7420568 := by exact prefixLift 7420568
  have htrace : WordTrace (prefixWord ++ tailWord_7420568) baseStart_7420568 baseEnd_7420568 := by
    simpa [prefixWord, tailWord_7420568, baseEnd_7420568] using wordTrace_append hprefix tailTrace_7420568
  have hstable : (prefixWord ++ tailWord_7420568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420568).length < 2 ^ (prefixWord ++ tailWord_7420568).sum := by decide
  have hdescent : baseEnd_7420568 < baseStart_7420568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420591 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 1, 6]
def baseStart_7420591 : Nat := 118140960795 + 7420591 * 2 ^ 59
def prefixEnd_7420591 : Nat := 4983230072969 + 3 ^ 40 * 7420591 * 2
def baseEnd_7420591 : Nat := 1270109974475960545761943

theorem tailTrace_7420591 : CollatzResearch.WordTrace tailWord_7420591 prefixEnd_7420591 1270109974475960545761943 := by
  unfold tailWord_7420591
  simp only [CollatzResearch.WordTrace]
  refine ⟨270651188659473617890133627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180434125772982411926755751 270651188659473617890133627)
  ·
    refine ⟨405976782989210426835200441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270651188659473617890133627 405976782989210426835200441)
    ·
      refine ⟨304482587241907820126400331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405976782989210426835200441 304482587241907820126400331)
      ·
        refine ⟨456723880862861730189600497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304482587241907820126400331 456723880862861730189600497)
        ·
          refine ⟨342542910647146297642200373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456723880862861730189600497 342542910647146297642200373)
          ·
            refine ⟨32113397873169965403956285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342542910647146297642200373 32113397873169965403956285)
            ·
              refine ⟨12042524202438737026483607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32113397873169965403956285 12042524202438737026483607)
              ·
                refine ⟨18063786303658105539725411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12042524202438737026483607 18063786303658105539725411)
                ·
                  refine ⟨27095679455487158309588117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18063786303658105539725411 27095679455487158309588117)
                  ·
                    refine ⟨1270109974475960545761943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27095679455487158309588117 1270109974475960545761943)
                    ·
                      rfl

theorem cell23_7420591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_7420591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420591 prefixEnd_7420591 := by exact prefixLift 7420591
  have htrace : WordTrace (prefixWord ++ tailWord_7420591) baseStart_7420591 baseEnd_7420591 := by
    simpa [prefixWord, tailWord_7420591, baseEnd_7420591] using wordTrace_append hprefix tailTrace_7420591
  have hstable : (prefixWord ++ tailWord_7420591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420591).length < 2 ^ (prefixWord ++ tailWord_7420591).sum := by decide
  have hdescent : baseEnd_7420591 < baseStart_7420591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420618 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_7420618 : Nat := 118140960795 + 7420618 * 2 ^ 59
def prefixEnd_7420618 : Nat := 4983230072969 + 3 ^ 40 * 7420618 * 2
def baseEnd_7420618 : Nat := 3810343787405553031648205

theorem tailTrace_7420618 : CollatzResearch.WordTrace tailWord_7420618 prefixEnd_7420618 3810343787405553031648205 := by
  unfold tailWord_7420618
  simp only [CollatzResearch.WordTrace]
  refine ⟨67663043357593950375341627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180434782286917201000911005 67663043357593950375341627)
  ·
    refine ⟨101494565036390925563012441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67663043357593950375341627 101494565036390925563012441)
    ·
      refine ⟨76120923777293194172259331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101494565036390925563012441 76120923777293194172259331)
      ·
        refine ⟨114181385665939791258388997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76120923777293194172259331 114181385665939791258388997)
        ·
          refine ⟨21409009812363710860947937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114181385665939791258388997 21409009812363710860947937)
          ·
            refine ⟨16056757359272783145710953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21409009812363710860947937 16056757359272783145710953)
            ·
              refine ⟨12042568019454587359283215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16056757359272783145710953 12042568019454587359283215)
              ·
                refine ⟨18063852029181881038924823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12042568019454587359283215 18063852029181881038924823)
                ·
                  refine ⟨27095778043772821558387235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18063852029181881038924823 27095778043772821558387235)
                  ·
                    refine ⟨40643667065659232337580853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27095778043772821558387235 40643667065659232337580853)
                    ·
                      refine ⟨3810343787405553031648205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40643667065659232337580853 3810343787405553031648205)
                      ·
                        rfl

theorem cell23_7420618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_7420618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420618 prefixEnd_7420618 := by exact prefixLift 7420618
  have htrace : WordTrace (prefixWord ++ tailWord_7420618) baseStart_7420618 baseEnd_7420618 := by
    simpa [prefixWord, tailWord_7420618, baseEnd_7420618] using wordTrace_append hprefix tailTrace_7420618
  have hstable : (prefixWord ++ tailWord_7420618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420618).length < 2 ^ (prefixWord ++ tailWord_7420618).sum := by decide
  have hdescent : baseEnd_7420618 < baseStart_7420618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420632 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 3, 2, 2]
def baseStart_7420632 : Nat := 118140960795 + 7420632 * 2 ^ 59
def prefixEnd_7420632 : Nat := 4983230072969 + 3 ^ 40 * 7420632 * 2
def baseEnd_7420632 : Nat := 3810350976134715976873141

theorem tailTrace_7420632 : CollatzResearch.WordTrace tailWord_7420632 prefixEnd_7420632 3810350976134715976873141 := by
  unfold tailWord_7420632
  simp only [CollatzResearch.WordTrace]
  refine ⟨135326342026162540946188075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180435122701550054594917433 135326342026162540946188075)
  ·
    refine ⟨202989513039243811419282113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135326342026162540946188075 202989513039243811419282113)
    ·
      refine ⟨152242134779432858564461585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202989513039243811419282113 152242134779432858564461585)
      ·
        refine ⟨114181601084574643923346189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152242134779432858564461585 114181601084574643923346189)
        ·
          refine ⟨42818100406715491471254821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114181601084574643923346189 42818100406715491471254821)
          ·
            refine ⟨8028393826259154650860279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42818100406715491471254821 8028393826259154650860279)
            ·
              refine ⟨12042590739388731976290419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8028393826259154650860279 12042590739388731976290419)
              ·
                refine ⟨18063886109083097964435629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12042590739388731976290419 18063886109083097964435629)
                ·
                  refine ⟨6773957290906161736663361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18063886109083097964435629 6773957290906161736663361)
                  ·
                    refine ⟨5080467968179621302497521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6773957290906161736663361 5080467968179621302497521)
                    ·
                      refine ⟨3810350976134715976873141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080467968179621302497521 3810350976134715976873141)
                      ·
                        rfl

theorem cell23_7420632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_7420632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420632 prefixEnd_7420632 := by exact prefixLift 7420632
  have htrace : WordTrace (prefixWord ++ tailWord_7420632) baseStart_7420632 baseEnd_7420632 := by
    simpa [prefixWord, tailWord_7420632, baseEnd_7420632] using wordTrace_append hprefix tailTrace_7420632
  have hstable : (prefixWord ++ tailWord_7420632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420632).length < 2 ^ (prefixWord ++ tailWord_7420632).sum := by decide
  have hdescent : baseEnd_7420632 < baseStart_7420632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420691 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 3]
def baseStart_7420691 : Nat := 118140960795 + 7420691 * 2 ^ 59
def prefixEnd_7420691 : Nat := 4983230072969 + 3 ^ 40 * 7420691 * 2
def baseEnd_7420691 : Nat := 3810381271493331246035369

theorem tailTrace_7420691 : CollatzResearch.WordTrace tailWord_7420691 prefixEnd_7420691 3810381271493331246035369 := by
  unfold tailWord_7420691
  simp only [CollatzResearch.WordTrace]
  refine ⟨270654835959111334968773927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180436557306074223312515951 270654835959111334968773927)
  ·
    refine ⟨405982253938667002453160891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270654835959111334968773927 405982253938667002453160891)
    ·
      refine ⟨608973380908000503679741337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405982253938667002453160891 608973380908000503679741337)
      ·
        refine ⟨456730035681000377759806003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608973380908000503679741337 456730035681000377759806003)
        ·
          refine ⟨685095053521500566639709005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456730035681000377759806003 685095053521500566639709005)
          ·
            refine ⟨256910645070562712489890877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 685095053521500566639709005 256910645070562712489890877)
            ·
              refine ⟨96341491901461017183709079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256910645070562712489890877 96341491901461017183709079)
              ·
                refine ⟨144512237852191525775563619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96341491901461017183709079 144512237852191525775563619)
                ·
                  refine ⟨216768356778287288663345429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144512237852191525775563619 216768356778287288663345429)
                  ·
                    refine ⟨10161016723982216656094317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216768356778287288663345429 10161016723982216656094317)
                    ·
                      refine ⟨3810381271493331246035369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10161016723982216656094317 3810381271493331246035369)
                      ·
                        rfl

theorem cell23_7420691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_7420691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420691 prefixEnd_7420691 := by exact prefixLift 7420691
  have htrace : WordTrace (prefixWord ++ tailWord_7420691) baseStart_7420691 baseEnd_7420691 := by
    simpa [prefixWord, tailWord_7420691, baseEnd_7420691] using wordTrace_append hprefix tailTrace_7420691
  have hstable : (prefixWord ++ tailWord_7420691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420691).length < 2 ^ (prefixWord ++ tailWord_7420691).sum := by decide
  have hdescent : baseEnd_7420691 < baseStart_7420691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420705 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_7420705 : Nat := 118140960795 + 7420705 * 2 ^ 59
def prefixEnd_7420705 : Nat := 4983230072969 + 3 ^ 40 * 7420705 * 2
def baseEnd_7420705 : Nat := 3810388460222494191260305

theorem tailTrace_7420705 : CollatzResearch.WordTrace tailWord_7420705 prefixEnd_7420705 3810388460222494191260305 := by
  unfold tailWord_7420705
  simp only [CollatzResearch.WordTrace]
  refine ⟨270655346581060615359783569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180436897720707076906522379 270655346581060615359783569)
  ·
    refine ⟨202991509935795461519837677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270655346581060615359783569 202991509935795461519837677)
    ·
      refine ⟨76121816225923298069939129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202991509935795461519837677 76121816225923298069939129)
      ·
        refine ⟨57091362169442473552454347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76121816225923298069939129 57091362169442473552454347)
        ·
          refine ⟨85637043254163710328681521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57091362169442473552454347 85637043254163710328681521)
          ·
            refine ⟨64227782440622782746511141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85637043254163710328681521 64227782440622782746511141)
            ·
              refine ⟨12042709207616771764970839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64227782440622782746511141 12042709207616771764970839)
              ·
                refine ⟨18064063811425157647456259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12042709207616771764970839 18064063811425157647456259)
                ·
                  refine ⟨27096095717137736471184389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18064063811425157647456259 27096095717137736471184389)
                  ·
                    refine ⟨5080517946963325588347073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27096095717137736471184389 5080517946963325588347073)
                    ·
                      refine ⟨3810388460222494191260305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080517946963325588347073 3810388460222494191260305)
                      ·
                        rfl

theorem cell23_7420705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_7420705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420705 prefixEnd_7420705 := by exact prefixLift 7420705
  have htrace : WordTrace (prefixWord ++ tailWord_7420705) baseStart_7420705 baseEnd_7420705 := by
    simpa [prefixWord, tailWord_7420705, baseEnd_7420705] using wordTrace_append hprefix tailTrace_7420705
  have hstable : (prefixWord ++ tailWord_7420705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420705).length < 2 ^ (prefixWord ++ tailWord_7420705).sum := by decide
  have hdescent : baseEnd_7420705 < baseStart_7420705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420756 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_7420756 : Nat := 118140960795 + 7420756 * 2 ^ 59
def prefixEnd_7420756 : Nat := 4983230072969 + 3 ^ 40 * 7420756 * 2
def baseEnd_7420756 : Nat := 3810414647735873491722571

theorem tailTrace_7420756 : CollatzResearch.WordTrace tailWord_7420756 prefixEnd_7420756 3810414647735873491722571 := by
  unfold tailWord_7420756
  simp only [CollatzResearch.WordTrace]
  refine ⟨135328603351937925534945061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180438137802583900713260081 135328603351937925534945061)
  ·
    refine ⟨25374113128488361037802199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135328603351937925534945061 25374113128488361037802199)
    ·
      refine ⟨38061169692732541556703299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25374113128488361037802199 38061169692732541556703299)
      ·
        refine ⟨57091754539098812335054949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38061169692732541556703299 57091754539098812335054949)
        ·
          refine ⟨10704703976081027312822803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57091754539098812335054949 10704703976081027312822803)
          ·
            refine ⟨16057055964121540969234205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10704703976081027312822803 16057055964121540969234205)
            ·
              refine ⟨6021395986545577863462827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16057055964121540969234205 6021395986545577863462827)
              ·
                refine ⟨9032093979818366795194241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021395986545577863462827 9032093979818366795194241)
                ·
                  refine ⟨6774070484863775096395681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9032093979818366795194241 6774070484863775096395681)
                  ·
                    refine ⟨5080552863647831322296761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6774070484863775096395681 5080552863647831322296761)
                    ·
                      refine ⟨3810414647735873491722571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080552863647831322296761 3810414647735873491722571)
                      ·
                        rfl

theorem cell23_7420756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_7420756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420756 prefixEnd_7420756 := by exact prefixLift 7420756
  have htrace : WordTrace (prefixWord ++ tailWord_7420756) baseStart_7420756 baseEnd_7420756 := by
    simpa [prefixWord, tailWord_7420756, baseEnd_7420756] using wordTrace_append hprefix tailTrace_7420756
  have hstable : (prefixWord ++ tailWord_7420756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420756).length < 2 ^ (prefixWord ++ tailWord_7420756).sum := by decide
  have hdescent : baseEnd_7420756 < baseStart_7420756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420791 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_7420791 : Nat := 118140960795 + 7420791 * 2 ^ 59
def prefixEnd_7420791 : Nat := 4983230072969 + 3 ^ 40 * 7420791 * 2
def baseEnd_7420791 : Nat := 3810432619558780854784909

theorem tailTrace_7420791 : CollatzResearch.WordTrace tailWord_7420791 prefixEnd_7420791 3810432619558780854784909 := by
  unfold tailWord_7420791
  simp only [CollatzResearch.WordTrace]
  refine ⟨270658483258749052047414227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180438988839166034698276151 270658483258749052047414227)
  ·
    refine ⟨405987724888123578071121341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270658483258749052047414227 405987724888123578071121341)
    ·
      refine ⟨152245396833046341776670503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405987724888123578071121341 152245396833046341776670503)
      ·
        refine ⟨228368095249569512665005755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152245396833046341776670503 228368095249569512665005755)
        ·
          refine ⟨342552142874354268997508633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228368095249569512665005755 342552142874354268997508633)
          ·
            refine ⟨256914107155765701748131475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342552142874354268997508633 256914107155765701748131475)
            ·
              refine ⟨385371160733648552622197213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256914107155765701748131475 385371160733648552622197213)
              ·
                refine ⟨144514185275118207233323955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385371160733648552622197213 144514185275118207233323955)
                ·
                  refine ⟨216771277912677310849985933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144514185275118207233323955 216771277912677310849985933)
                  ·
                    refine ⟨81289229217253991568744725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216771277912677310849985933 81289229217253991568744725)
                    ·
                      refine ⟨3810432619558780854784909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81289229217253991568744725 3810432619558780854784909)
                      ·
                        rfl

theorem cell23_7420791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_7420791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420791 prefixEnd_7420791 := by exact prefixLift 7420791
  have htrace : WordTrace (prefixWord ++ tailWord_7420791) baseStart_7420791 baseEnd_7420791 := by
    simpa [prefixWord, tailWord_7420791, baseEnd_7420791] using wordTrace_append hprefix tailTrace_7420791
  have hstable : (prefixWord ++ tailWord_7420791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420791).length < 2 ^ (prefixWord ++ tailWord_7420791).sum := by decide
  have hdescent : baseEnd_7420791 < baseStart_7420791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420805 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_7420805 : Nat := 118140960795 + 7420805 * 2 ^ 59
def prefixEnd_7420805 : Nat := 4983230072969 + 3 ^ 40 * 7420805 * 2
def baseEnd_7420805 : Nat := 1270146602762647933336615

theorem tailTrace_7420805 : CollatzResearch.WordTrace tailWord_7420805 prefixEnd_7420805 1270146602762647933336615 := by
  unfold tailWord_7420805
  simp only [CollatzResearch.WordTrace]
  refine ⟨270658993880698332438423869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180439329253798888292282579 270658993880698332438423869)
  ·
    refine ⟨101497122705261874664408951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270658993880698332438423869 101497122705261874664408951)
    ·
      refine ⟨152245684057892811996613427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101497122705261874664408951 152245684057892811996613427)
      ·
        refine ⟨228368526086839217994920141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152245684057892811996613427 228368526086839217994920141)
        ·
          refine ⟨85638197282564706748095053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228368526086839217994920141 85638197282564706748095053)
          ·
            refine ⟨32114323980961765030535645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85638197282564706748095053 32114323980961765030535645)
            ·
              refine ⟨12042871492860661886450867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32114323980961765030535645 12042871492860661886450867)
              ·
                refine ⟨18064307239290992829676301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12042871492860661886450867 18064307239290992829676301)
                ·
                  refine ⟨6774115214734122311128613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18064307239290992829676301 6774115214734122311128613)
                  ·
                    refine ⟨1270146602762647933336615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774115214734122311128613 1270146602762647933336615)
                    ·
                      rfl

theorem cell23_7420805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_7420805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420805 prefixEnd_7420805 := by exact prefixLift 7420805
  have htrace : WordTrace (prefixWord ++ tailWord_7420805) baseStart_7420805 baseEnd_7420805 := by
    simpa [prefixWord, tailWord_7420805, baseEnd_7420805] using wordTrace_append hprefix tailTrace_7420805
  have hstable : (prefixWord ++ tailWord_7420805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420805).length < 2 ^ (prefixWord ++ tailWord_7420805).sum := by decide
  have hdescent : baseEnd_7420805 < baseStart_7420805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420852 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 6]
def baseStart_7420852 : Nat := 118140960795 + 7420852 * 2 ^ 59
def prefixEnd_7420852 : Nat := 4983230072969 + 3 ^ 40 * 7420852 * 2
def baseEnd_7420852 : Nat := 423384882430967235124681

theorem tailTrace_7420852 : CollatzResearch.WordTrace tailWord_7420852 prefixEnd_7420852 423384882430967235124681 := by
  unfold tailWord_7420852
  simp only [CollatzResearch.WordTrace]
  refine ⟨135330354055764029732692405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180440472074352039643589873 135330354055764029732692405)
  ·
    refine ⟨12687220692727877787439913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135330354055764029732692405 12687220692727877787439913)
    ·
      refine ⟨9515415519545908340579935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12687220692727877787439913 9515415519545908340579935)
      ·
        refine ⟨14273123279318862510869903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515415519545908340579935 14273123279318862510869903)
        ·
          refine ⟨21409684918978293766304855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14273123279318862510869903 21409684918978293766304855)
          ·
            refine ⟨32114527378467440649457283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21409684918978293766304855 32114527378467440649457283)
            ·
              refine ⟨48171791067701160974185925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32114527378467440649457283 48171791067701160974185925)
              ·
                refine ⟨9032210825193967682659861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48171791067701160974185925 9032210825193967682659861)
                ·
                  refine ⟨423384882430967235124681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9032210825193967682659861 423384882430967235124681)
                  ·
                    rfl

theorem cell23_7420852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_7420852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420852 prefixEnd_7420852 := by exact prefixLift 7420852
  have htrace : WordTrace (prefixWord ++ tailWord_7420852) baseStart_7420852 baseEnd_7420852 := by
    simpa [prefixWord, tailWord_7420852, baseEnd_7420852] using wordTrace_append hprefix tailTrace_7420852
  have hstable : (prefixWord ++ tailWord_7420852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420852).length < 2 ^ (prefixWord ++ tailWord_7420852).sum := by decide
  have hdescent : baseEnd_7420852 < baseStart_7420852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420862 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_7420862 : Nat := 118140960795 + 7420862 * 2 ^ 59
def prefixEnd_7420862 : Nat := 4983230072969 + 3 ^ 40 * 7420862 * 2
def baseEnd_7420862 : Nat := 3810469076685250076997083

theorem tailTrace_7420862 : CollatzResearch.WordTrace tailWord_7420862 prefixEnd_7420862 3810469076685250076997083 := by
  unfold tailWord_7420862
  simp only [CollatzResearch.WordTrace]
  refine ⟨33832634105186478896656105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180440715227661220782165893 33832634105186478896656105)
  ·
    refine ⟨25374475578889859172492079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33832634105186478896656105 25374475578889859172492079)
    ·
      refine ⟨38061713368334788758738119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25374475578889859172492079 38061713368334788758738119)
      ·
        refine ⟨57092570052502183138107179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38061713368334788758738119 57092570052502183138107179)
        ·
          refine ⟨85638855078753274707160769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57092570052502183138107179 85638855078753274707160769)
          ·
            refine ⟨64229141309064956030370577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85638855078753274707160769 64229141309064956030370577)
            ·
              refine ⟨48171855981798717022777933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64229141309064956030370577 48171855981798717022777933)
              ·
                refine ⟨18064445993174518883541725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48171855981798717022777933 18064445993174518883541725)
                ·
                  refine ⟨6774167247440444581328147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18064445993174518883541725 6774167247440444581328147)
                  ·
                    refine ⟨10161250871160666871992221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6774167247440444581328147 10161250871160666871992221)
                    ·
                      refine ⟨3810469076685250076997083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10161250871160666871992221 3810469076685250076997083)
                      ·
                        rfl

theorem cell23_7420862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_7420862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420862 prefixEnd_7420862 := by exact prefixLift 7420862
  have htrace : WordTrace (prefixWord ++ tailWord_7420862) baseStart_7420862 baseEnd_7420862 := by
    simpa [prefixWord, tailWord_7420862, baseEnd_7420862] using wordTrace_append hprefix tailTrace_7420862
  have hstable : (prefixWord ++ tailWord_7420862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420862).length < 2 ^ (prefixWord ++ tailWord_7420862).sum := by decide
  have hdescent : baseEnd_7420862 < baseStart_7420862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420889 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 2, 3, 2]
def baseStart_7420889 : Nat := 118140960795 + 7420889 * 2 ^ 59
def prefixEnd_7420889 : Nat := 4983230072969 + 3 ^ 40 * 7420889 * 2
def baseEnd_7420889 : Nat := 3810482940662921471359459

theorem tailTrace_7420889 : CollatzResearch.WordTrace tailWord_7420889 prefixEnd_7420889 3810482940662921471359459 := by
  unfold tailWord_7420889
  simp only [CollatzResearch.WordTrace]
  refine ⟨270662057612394014784481721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180441371741596009856321147 270662057612394014784481721)
  ·
    refine ⟨202996543209295511088361291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270662057612394014784481721 202996543209295511088361291)
    ·
      refine ⟨304494814813943266632541937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202996543209295511088361291 304494814813943266632541937)
      ·
        refine ⟨228371111110457449974406453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304494814813943266632541937 228371111110457449974406453)
        ·
          refine ⟨21409791666605385935100605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228371111110457449974406453 21409791666605385935100605)
          ·
            refine ⟨8028671874977019725662727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21409791666605385935100605 8028671874977019725662727)
            ·
              refine ⟨12043007812465529588494091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8028671874977019725662727 12043007812465529588494091)
              ·
                refine ⟨18064511718698294382741137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12043007812465529588494091 18064511718698294382741137)
                ·
                  refine ⟨13548383789023720787055853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18064511718698294382741137 13548383789023720787055853)
                  ·
                    refine ⟨5080643920883895295145945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13548383789023720787055853 5080643920883895295145945)
                    ·
                      refine ⟨3810482940662921471359459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080643920883895295145945 3810482940662921471359459)
                      ·
                        rfl

theorem cell23_7420889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_7420889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420889 prefixEnd_7420889 := by exact prefixLift 7420889
  have htrace : WordTrace (prefixWord ++ tailWord_7420889) baseStart_7420889 baseEnd_7420889 := by
    simpa [prefixWord, tailWord_7420889, baseEnd_7420889] using wordTrace_append hprefix tailTrace_7420889
  have hstable : (prefixWord ++ tailWord_7420889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420889).length < 2 ^ (prefixWord ++ tailWord_7420889).sum := by decide
  have hdescent : baseEnd_7420889 < baseStart_7420889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420929 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7420929 : Nat := 118140960795 + 7420929 * 2 ^ 59
def prefixEnd_7420929 : Nat := 4983230072969 + 3 ^ 40 * 7420929 * 2
def baseEnd_7420929 : Nat := 1270167826629700438286425

theorem tailTrace_7420929 : CollatzResearch.WordTrace tailWord_7420929 prefixEnd_7420929 1270167826629700438286425 := by
  unfold tailWord_7420929
  simp only [CollatzResearch.WordTrace]
  refine ⟨270663516532249101615937841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180442344354832734410625227 270663516532249101615937841)
  ·
    refine ⟨202997637399186826211953381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270663516532249101615937841 202997637399186826211953381)
    ·
      refine ⟨38062057012347529914741259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202997637399186826211953381 38062057012347529914741259)
      ·
        refine ⟨57093085518521294872111889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38062057012347529914741259 57093085518521294872111889)
        ·
          refine ⟨42819814138890971154083917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57093085518521294872111889 42819814138890971154083917)
          ·
            refine ⟨16057430302084114182781469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42819814138890971154083917 16057430302084114182781469)
            ·
              refine ⟨6021536363281542818543051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16057430302084114182781469 6021536363281542818543051)
              ·
                refine ⟨9032304544922314227814577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021536363281542818543051 9032304544922314227814577)
                ·
                  refine ⟨6774228408691735670860933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9032304544922314227814577 6774228408691735670860933)
                  ·
                    refine ⟨1270167826629700438286425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774228408691735670860933 1270167826629700438286425)
                    ·
                      rfl

theorem cell23_7420929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7420929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420929 prefixEnd_7420929 := by exact prefixLift 7420929
  have htrace : WordTrace (prefixWord ++ tailWord_7420929) baseStart_7420929 baseEnd_7420929 := by
    simpa [prefixWord, tailWord_7420929, baseEnd_7420929] using wordTrace_append hprefix tailTrace_7420929
  have hstable : (prefixWord ++ tailWord_7420929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420929).length < 2 ^ (prefixWord ++ tailWord_7420929).sum := by decide
  have hdescent : baseEnd_7420929 < baseStart_7420929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420942 : List Nat := [4, 1, 1, 2, 2, 4, 2, 7]
def baseStart_7420942 : Nat := 118140960795 + 7420942 * 2 ^ 59
def prefixEnd_7420942 : Nat := 4983230072969 + 3 ^ 40 * 7420942 * 2
def baseEnd_7420942 : Nat := 141130005745837398666545

theorem tailTrace_7420942 : CollatzResearch.WordTrace tailWord_7420942 prefixEnd_7420942 141130005745837398666545 := by
  unfold tailWord_7420942
  simp only [CollatzResearch.WordTrace]
  refine ⟨33832998835150250604520135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180442660454134669890774053 33832998835150250604520135)
  ·
    refine ⟨50749498252725375906780203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33832998835150250604520135 50749498252725375906780203)
    ·
      refine ⟨76124247379088063860170305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50749498252725375906780203 76124247379088063860170305)
      ·
        refine ⟨57093185534316047895127729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76124247379088063860170305 57093185534316047895127729)
        ·
          refine ⟨42819889150737035921345797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57093185534316047895127729 42819889150737035921345797)
          ·
            refine ⟨8028729215763194235252337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42819889150737035921345797 8028729215763194235252337)
            ·
              refine ⟨6021546911822395676439253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8028729215763194235252337 6021546911822395676439253)
              ·
                refine ⟨141130005745837398666545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6021546911822395676439253 141130005745837398666545)
                ·
                  rfl

theorem cell23_7420942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_7420942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420942 prefixEnd_7420942 := by exact prefixLift 7420942
  have htrace : WordTrace (prefixWord ++ tailWord_7420942) baseStart_7420942 baseEnd_7420942 := by
    simpa [prefixWord, tailWord_7420942, baseEnd_7420942] using wordTrace_append hprefix tailTrace_7420942
  have hstable : (prefixWord ++ tailWord_7420942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420942).length < 2 ^ (prefixWord ++ tailWord_7420942).sum := by decide
  have hdescent : baseEnd_7420942 < baseStart_7420942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420945 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 7, 2]
def baseStart_7420945 : Nat := 118140960795 + 7420945 * 2 ^ 59
def prefixEnd_7420945 : Nat := 4983230072969 + 3 ^ 40 * 7420945 * 2
def baseEnd_7420945 : Nat := 3810511695579573252259201

theorem tailTrace_7420945 : CollatzResearch.WordTrace tailWord_7420945 prefixEnd_7420945 3810511695579573252259201 := by
  unfold tailWord_7420945
  simp only [CollatzResearch.WordTrace]
  refine ⟨270664100100191136348520289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180442733400127424232346859 270664100100191136348520289)
  ·
    refine ⟨202998075075143352261390217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270664100100191136348520289 202998075075143352261390217)
    ·
      refine ⟨152248556306357514196042663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202998075075143352261390217 152248556306357514196042663)
      ·
        refine ⟨228372834459536271294063995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152248556306357514196042663 228372834459536271294063995)
        ·
          refine ⟨342559251689304406941095993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228372834459536271294063995 342559251689304406941095993)
          ·
            refine ⟨256919438766978305205821995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342559251689304406941095993 256919438766978305205821995)
            ·
              refine ⟨385379158150467457808732993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256919438766978305205821995 385379158150467457808732993)
              ·
                refine ⟨289034368612850593356549745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385379158150467457808732993 289034368612850593356549745)
                ·
                  refine ⟨216775776459637945017412309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289034368612850593356549745 216775776459637945017412309)
                  ·
                    refine ⟨5080682260772764336345601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216775776459637945017412309 5080682260772764336345601)
                    ·
                      refine ⟨3810511695579573252259201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080682260772764336345601 3810511695579573252259201)
                      ·
                        rfl

theorem cell23_7420945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_7420945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420945 prefixEnd_7420945 := by exact prefixLift 7420945
  have htrace : WordTrace (prefixWord ++ tailWord_7420945) baseStart_7420945 baseEnd_7420945 := by
    simpa [prefixWord, tailWord_7420945, baseEnd_7420945] using wordTrace_append hprefix tailTrace_7420945
  have hstable : (prefixWord ++ tailWord_7420945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420945).length < 2 ^ (prefixWord ++ tailWord_7420945).sum := by decide
  have hdescent : baseEnd_7420945 < baseStart_7420945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420952 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_7420952 : Nat := 118140960795 + 7420952 * 2 ^ 59
def prefixEnd_7420952 : Nat := 4983230072969 + 3 ^ 40 * 7420952 * 2
def baseEnd_7420952 : Nat := 3810515289944154724871669

theorem tailTrace_7420952 : CollatzResearch.WordTrace tailWord_7420952 prefixEnd_7420952 3810515289944154724871669 := by
  unfold tailWord_7420952
  simp only [CollatzResearch.WordTrace]
  refine ⟨135332177705582888272012555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180442903607443851029350073 135332177705582888272012555)
  ·
    refine ⟨202998266558374332408018833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135332177705582888272012555 202998266558374332408018833)
    ·
      refine ⟨152248699918780749306014125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202998266558374332408018833 152248699918780749306014125)
      ·
        refine ⟨57093262469542780989755297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152248699918780749306014125 57093262469542780989755297)
        ·
          refine ⟨42819946852157085742316473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57093262469542780989755297 42819946852157085742316473)
          ·
            refine ⟨32114960139117814306737355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42819946852157085742316473 32114960139117814306737355)
            ·
              refine ⟨48172440208676721460106033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32114960139117814306737355 48172440208676721460106033)
              ·
                refine ⟨36129330156507541095079525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48172440208676721460106033 36129330156507541095079525)
                ·
                  refine ⟨6774249404345163955327411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36129330156507541095079525 6774249404345163955327411)
                  ·
                    refine ⟨10161374106517745932991117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6774249404345163955327411 10161374106517745932991117)
                    ·
                      refine ⟨3810515289944154724871669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10161374106517745932991117 3810515289944154724871669)
                      ·
                        rfl

theorem cell23_7420952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_7420952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420952 prefixEnd_7420952 := by exact prefixLift 7420952
  have htrace : WordTrace (prefixWord ++ tailWord_7420952) baseStart_7420952 baseEnd_7420952 := by
    simpa [prefixWord, tailWord_7420952, baseEnd_7420952] using wordTrace_append hprefix tailTrace_7420952
  have hstable : (prefixWord ++ tailWord_7420952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420952).length < 2 ^ (prefixWord ++ tailWord_7420952).sum := by decide
  have hdescent : baseEnd_7420952 < baseStart_7420952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420970 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7420970 : Nat := 118140960795 + 7420970 * 2 ^ 59
def prefixEnd_7420970 : Nat := 4983230072969 + 3 ^ 40 * 7420970 * 2
def baseEnd_7420970 : Nat := 3810524532595935654446587

theorem tailTrace_7420970 : CollatzResearch.WordTrace tailWord_7420970 prefixEnd_7420970 3810524532595935654446587 := by
  unfold tailWord_7420970
  simp only [CollatzResearch.WordTrace]
  refine ⟨67666252981275141404545091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180443341283400377078786909 67666252981275141404545091)
  ·
    refine ⟨101499379471912712106817637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67666252981275141404545091 101499379471912712106817637)
    ·
      refine ⟨19031133650983633520028307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101499379471912712106817637 19031133650983633520028307)
      ·
        refine ⟨28546700476475450280042461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19031133650983633520028307 28546700476475450280042461)
        ·
          refine ⟨10705012678678293855015923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28546700476475450280042461 10705012678678293855015923)
          ·
            refine ⟨16057519018017440782523885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10705012678678293855015923 16057519018017440782523885)
            ·
              refine ⟨6021569631756540293446457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16057519018017440782523885 6021569631756540293446457)
              ·
                refine ⟨4516177223817405220084843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6021569631756540293446457 4516177223817405220084843)
                ·
                  refine ⟨6774265835726107830127265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516177223817405220084843 6774265835726107830127265)
                  ·
                    refine ⟨5080699376794580872595449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6774265835726107830127265 5080699376794580872595449)
                    ·
                      refine ⟨3810524532595935654446587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080699376794580872595449 3810524532595935654446587)
                      ·
                        rfl

theorem cell23_7420970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7420970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420970 prefixEnd_7420970 := by exact prefixLift 7420970
  have htrace : WordTrace (prefixWord ++ tailWord_7420970) baseStart_7420970 baseEnd_7420970 := by
    simpa [prefixWord, tailWord_7420970, baseEnd_7420970] using wordTrace_append hprefix tailTrace_7420970
  have hstable : (prefixWord ++ tailWord_7420970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420970).length < 2 ^ (prefixWord ++ tailWord_7420970).sum := by decide
  have hdescent : baseEnd_7420970 < baseStart_7420970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7420992 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 1, 4, 2]
def baseStart_7420992 : Nat := 118140960795 + 7420992 * 2 ^ 59
def prefixEnd_7420992 : Nat := 4983230072969 + 3 ^ 40 * 7420992 * 2
def baseEnd_7420992 : Nat := 3810535829170334568371485

theorem tailTrace_7420992 : CollatzResearch.WordTrace tailWord_7420992 prefixEnd_7420992 3810535829170334568371485 := by
  unfold tailWord_7420992
  simp only [CollatzResearch.WordTrace]
  refine ⟨135332907165510431687740615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180443876220680575583654153 135332907165510431687740615)
  ·
    refine ⟨202999360748265647531610923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135332907165510431687740615 202999360748265647531610923)
    ·
      refine ⟨304499041122398471297416385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202999360748265647531610923 304499041122398471297416385)
      ·
        refine ⟨228374280841798853473062289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304499041122398471297416385 228374280841798853473062289)
        ·
          refine ⟨171280710631349140104796717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228374280841798853473062289 171280710631349140104796717)
          ·
            refine ⟨64230266486755927539298769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171280710631349140104796717 64230266486755927539298769)
            ·
              refine ⟨48172699865066945654474077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64230266486755927539298769 48172699865066945654474077)
              ·
                refine ⟨18064762449400104620427779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48172699865066945654474077 18064762449400104620427779)
                ·
                  refine ⟨27097143674100156930641669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18064762449400104620427779 27097143674100156930641669)
                  ·
                    refine ⟨5080714438893779424495313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27097143674100156930641669 5080714438893779424495313)
                    ·
                      refine ⟨3810535829170334568371485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080714438893779424495313 3810535829170334568371485)
                      ·
                        rfl

theorem cell23_7420992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_7420992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7420992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7420992 prefixEnd_7420992 := by exact prefixLift 7420992
  have htrace : WordTrace (prefixWord ++ tailWord_7420992) baseStart_7420992 baseEnd_7420992 := by
    simpa [prefixWord, tailWord_7420992, baseEnd_7420992] using wordTrace_append hprefix tailTrace_7420992
  have hstable : (prefixWord ++ tailWord_7420992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7420992).length < 2 ^ (prefixWord ++ tailWord_7420992).sum := by decide
  have hdescent : baseEnd_7420992 < baseStart_7420992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7420992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421042 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_7421042 : Nat := 118140960795 + 7421042 * 2 ^ 59
def prefixEnd_7421042 : Nat := 4983230072969 + 3 ^ 40 * 7421042 * 2
def baseEnd_7421042 : Nat := 3810561503203059372746255

theorem tailTrace_7421042 : CollatzResearch.WordTrace tailWord_7421042 prefixEnd_7421042 3810561503203059372746255 := by
  unfold tailWord_7421042
  simp only [CollatzResearch.WordTrace]
  refine ⟨67666909495209930478700345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180445091987226481276534253 67666909495209930478700345)
  ·
    refine ⟨50750182121407447859025259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67666909495209930478700345 50750182121407447859025259)
    ·
      refine ⟨76125273182111171788537889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50750182121407447859025259 76125273182111171788537889)
      ·
        refine ⟨57093954886583378841403417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76125273182111171788537889 57093954886583378841403417)
        ·
          refine ⟨42820466164937534131052563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57093954886583378841403417 42820466164937534131052563)
          ·
            refine ⟨64230699247406301196578845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42820466164937534131052563 64230699247406301196578845)
            ·
              refine ⟨24086512217777362948717067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64230699247406301196578845 24086512217777362948717067)
              ·
                refine ⟨36129768326666044423075601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24086512217777362948717067 36129768326666044423075601)
                ·
                  refine ⟨27097326244999533317306701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36129768326666044423075601 27097326244999533317306701)
                  ·
                    refine ⟨10161497341874824993990013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27097326244999533317306701 10161497341874824993990013)
                    ·
                      refine ⟨3810561503203059372746255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10161497341874824993990013 3810561503203059372746255)
                      ·
                        rfl

theorem cell23_7421042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_7421042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421042 prefixEnd_7421042 := by exact prefixLift 7421042
  have htrace : WordTrace (prefixWord ++ tailWord_7421042) baseStart_7421042 baseEnd_7421042 := by
    simpa [prefixWord, tailWord_7421042, baseEnd_7421042] using wordTrace_append hprefix tailTrace_7421042
  have hstable : (prefixWord ++ tailWord_7421042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421042).length < 2 ^ (prefixWord ++ tailWord_7421042).sum := by decide
  have hdescent : baseEnd_7421042 < baseStart_7421042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421052 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_7421052 : Nat := 118140960795 + 7421052 * 2 ^ 59
def prefixEnd_7421052 : Nat := 4983230072969 + 3 ^ 40 * 7421052 * 2
def baseEnd_7421052 : Nat := 3810566638009604333621209

theorem tailTrace_7421052 : CollatzResearch.WordTrace tailWord_7421052 prefixEnd_7421052 3810566638009604333621209 := by
  unfold tailWord_7421052
  simp only [CollatzResearch.WordTrace]
  refine ⟨135334001355401746811332705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180445335140535662415110273 135334001355401746811332705)
  ·
    refine ⟨101500501016551310108499529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135334001355401746811332705 101500501016551310108499529)
    ·
      refine ⟨76125375762413482581374647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101500501016551310108499529 76125375762413482581374647)
      ·
        refine ⟨114188063643620223872061971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76125375762413482581374647 114188063643620223872061971)
        ·
          refine ⟨171282095465430335808092957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114188063643620223872061971 171282095465430335808092957)
          ·
            refine ⟨64230785799536375928034859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171282095465430335808092957 64230785799536375928034859)
            ·
              refine ⟨96346178699304563892052289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64230785799536375928034859 96346178699304563892052289)
              ·
                refine ⟨72259634024478422919039217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96346178699304563892052289 72259634024478422919039217)
                ·
                  refine ⟨54194725518358817189279413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72259634024478422919039217 54194725518358817189279413)
                  ·
                    refine ⟨5080755517346139111494945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54194725518358817189279413 5080755517346139111494945)
                    ·
                      refine ⟨3810566638009604333621209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080755517346139111494945 3810566638009604333621209)
                      ·
                        rfl

theorem cell23_7421052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_7421052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421052 prefixEnd_7421052 := by exact prefixLift 7421052
  have htrace : WordTrace (prefixWord ++ tailWord_7421052) baseStart_7421052 baseEnd_7421052 := by
    simpa [prefixWord, tailWord_7421052, baseEnd_7421052] using wordTrace_append hprefix tailTrace_7421052
  have hstable : (prefixWord ++ tailWord_7421052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421052).length < 2 ^ (prefixWord ++ tailWord_7421052).sum := by decide
  have hdescent : baseEnd_7421052 < baseStart_7421052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421133 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7421133 : Nat := 118140960795 + 7421133 * 2 ^ 59
def prefixEnd_7421133 : Nat := 4983230072969 + 3 ^ 40 * 7421133 * 2
def baseEnd_7421133 : Nat := 3810608229942618516708337

theorem tailTrace_7421133 : CollatzResearch.WordTrace tailWord_7421133 prefixEnd_7421133 3810608229942618516708337 := by
  unfold tailWord_7421133
  simp only [CollatzResearch.WordTrace]
  refine ⟨270670957023510044456364053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180447304682340029637576035 270670957023510044456364053)
  ·
    refine ⟨12687701110477033333892065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270670957023510044456364053 12687701110477033333892065)
    ·
      refine ⟨9515775832857775000419049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12687701110477033333892065 9515775832857775000419049)
      ·
        refine ⟨7136831874643331250314287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9515775832857775000419049 7136831874643331250314287)
        ·
          refine ⟨10705247811964996875471431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136831874643331250314287 10705247811964996875471431)
          ·
            refine ⟨16057871717947495313207147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10705247811964996875471431 16057871717947495313207147)
            ·
              refine ⟨24086807576921242969810721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16057871717947495313207147 24086807576921242969810721)
              ·
                refine ⟨18065105682690932227358041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24086807576921242969810721 18065105682690932227358041)
                ·
                  refine ⟨13548829262018199170518531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18065105682690932227358041 13548829262018199170518531)
                  ·
                    refine ⟨20323243893027298755777797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13548829262018199170518531 20323243893027298755777797)
                    ·
                      refine ⟨3810608229942618516708337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20323243893027298755777797 3810608229942618516708337)
                      ·
                        rfl

theorem cell23_7421133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7421133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421133 prefixEnd_7421133 := by exact prefixLift 7421133
  have htrace : WordTrace (prefixWord ++ tailWord_7421133) baseStart_7421133 baseEnd_7421133 := by
    simpa [prefixWord, tailWord_7421133, baseEnd_7421133] using wordTrace_append hprefix tailTrace_7421133
  have hstable : (prefixWord ++ tailWord_7421133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421133).length < 2 ^ (prefixWord ++ tailWord_7421133).sum := by decide
  have hdescent : baseEnd_7421133 < baseStart_7421133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421145 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7421145 : Nat := 118140960795 + 7421145 * 2 ^ 59
def prefixEnd_7421145 : Nat := 4983230072969 + 3 ^ 40 * 7421145 * 2
def baseEnd_7421145 : Nat := 3810614391710472469758281

theorem tailTrace_7421145 : CollatzResearch.WordTrace tailWord_7421145 prefixEnd_7421145 3810614391710472469758281 := by
  unfold tailWord_7421145
  simp only [CollatzResearch.WordTrace]
  refine ⟨270671394699466570505800889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180447596466311047003867259 270671394699466570505800889)
  ·
    refine ⟨203003546024599927879350667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270671394699466570505800889 203003546024599927879350667)
    ·
      refine ⟨304505319036899891819026001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203003546024599927879350667 304505319036899891819026001)
      ·
        refine ⟨228378989277674918864269501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304505319036899891819026001 228378989277674918864269501)
        ·
          refine ⟨85642120979128094574101063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228378989277674918864269501 85642120979128094574101063)
          ·
            refine ⟨128463181468692141861151595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85642120979128094574101063 128463181468692141861151595)
            ·
              refine ⟨192694772203038212791727393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128463181468692141861151595 192694772203038212791727393)
              ·
                refine ⟨144521079152278659593795545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192694772203038212791727393 144521079152278659593795545)
                ·
                  refine ⟨108390809364208994695346659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144521079152278659593795545 108390809364208994695346659)
                  ·
                    refine ⟨162586214046313492043019989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108390809364208994695346659 162586214046313492043019989)
                    ·
                      refine ⟨3810614391710472469758281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162586214046313492043019989 3810614391710472469758281)
                      ·
                        rfl

theorem cell23_7421145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7421145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421145 prefixEnd_7421145 := by exact prefixLift 7421145
  have htrace : WordTrace (prefixWord ++ tailWord_7421145) baseStart_7421145 baseEnd_7421145 := by
    simpa [prefixWord, tailWord_7421145, baseEnd_7421145] using wordTrace_append hprefix tailTrace_7421145
  have hstable : (prefixWord ++ tailWord_7421145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421145).length < 2 ^ (prefixWord ++ tailWord_7421145).sum := by decide
  have hdescent : baseEnd_7421145 < baseStart_7421145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421195 : List Nat := [1, 1, 1, 1, 5, 14]
def baseStart_7421195 : Nat := 118140960795 + 7421195 * 2 ^ 59
def prefixEnd_7421195 : Nat := 4983230072969 + 3 ^ 40 * 7421195 * 2
def baseEnd_7421195 : Nat := 15681646361083116354457

theorem tailTrace_7421195 : CollatzResearch.WordTrace tailWord_7421195 prefixEnd_7421195 15681646361083116354457 := by
  unfold tailWord_7421195
  simp only [CollatzResearch.WordTrace]
  refine ⟨270673218349285429045121039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180448812232856952696747359 270673218349285429045121039)
  ·
    refine ⟨406009827523928143567681559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270673218349285429045121039 406009827523928143567681559)
    ·
      refine ⟨609014741285892215351522339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406009827523928143567681559 609014741285892215351522339)
      ·
        refine ⟨913522111928838323027283509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609014741285892215351522339 913522111928838323027283509)
        ·
          refine ⟨85642697993328592783807829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 913522111928838323027283509 85642697993328592783807829)
          ·
            refine ⟨15681646361083116354457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 85642697993328592783807829 15681646361083116354457)
            ·
              rfl

theorem cell23_7421195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 14].length) (baseStart_7421195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421195 prefixEnd_7421195 := by exact prefixLift 7421195
  have htrace : WordTrace (prefixWord ++ tailWord_7421195) baseStart_7421195 baseEnd_7421195 := by
    simpa [prefixWord, tailWord_7421195, baseEnd_7421195] using wordTrace_append hprefix tailTrace_7421195
  have hstable : (prefixWord ++ tailWord_7421195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421195).length < 2 ^ (prefixWord ++ tailWord_7421195).sum := by decide
  have hdescent : baseEnd_7421195 < baseStart_7421195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421212 : List Nat := [2, 2, 3, 1, 1, 1, 5, 8]
def baseStart_7421212 : Nat := 118140960795 + 7421212 * 2 ^ 59
def prefixEnd_7421212 : Nat := 4983230072969 + 3 ^ 40 * 7421212 * 2
def baseEnd_7421212 : Nat := 141135140552382359541499

theorem tailTrace_7421212 : CollatzResearch.WordTrace tailWord_7421212 prefixEnd_7421212 141135140552382359541499 := by
  unfold tailWord_7421212
  simp only [CollatzResearch.WordTrace]
  refine ⟨135336919195111920474244945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180449225593482560632326593 135336919195111920474244945)
  ·
    refine ⟨101502689396333940355683709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135336919195111920474244945 101502689396333940355683709)
    ·
      refine ⟨38063508523625227633381391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101502689396333940355683709 38063508523625227633381391)
      ·
        refine ⟨57095262785437841450072087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38063508523625227633381391 57095262785437841450072087)
        ·
          refine ⟨85642894178156762175108131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57095262785437841450072087 85642894178156762175108131)
          ·
            refine ⟨128464341267235143262662197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85642894178156762175108131 128464341267235143262662197)
            ·
              refine ⟨12043531993803294680874581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128464341267235143262662197 12043531993803294680874581)
              ·
                refine ⟨141135140552382359541499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12043531993803294680874581 141135140552382359541499)
                ·
                  rfl

theorem cell23_7421212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 8].length) (baseStart_7421212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421212 prefixEnd_7421212 := by exact prefixLift 7421212
  have htrace : WordTrace (prefixWord ++ tailWord_7421212) baseStart_7421212 baseEnd_7421212 := by
    simpa [prefixWord, tailWord_7421212, baseEnd_7421212] using wordTrace_append hprefix tailTrace_7421212
  have hstable : (prefixWord ++ tailWord_7421212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421212).length < 2 ^ (prefixWord ++ tailWord_7421212).sum := by decide
  have hdescent : baseEnd_7421212 < baseStart_7421212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421219 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 4]
def baseStart_7421219 : Nat := 118140960795 + 7421219 * 2 ^ 59
def prefixEnd_7421219 : Nat := 4983230072969 + 3 ^ 40 * 7421219 * 2
def baseEnd_7421219 : Nat := 3810652389278905180232941

theorem tailTrace_7421219 : CollatzResearch.WordTrace tailWord_7421219 prefixEnd_7421219 3810652389278905180232941 := by
  unfold tailWord_7421219
  simp only [CollatzResearch.WordTrace]
  refine ⟨270674093701198481143994711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180449395800798987429329807 270674093701198481143994711)
  ·
    refine ⟨406011140551797721715992067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270674093701198481143994711 406011140551797721715992067)
    ·
      refine ⟨609016710827696582573988101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406011140551797721715992067 609016710827696582573988101)
      ·
        refine ⟨114190633280193109232622769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 609016710827696582573988101 114190633280193109232622769)
        ·
          refine ⟨85642974960144831924467077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114190633280193109232622769 85642974960144831924467077)
          ·
            refine ⟨16058057805027155985837577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85642974960144831924467077 16058057805027155985837577)
            ·
              refine ⟨12043543353770366989378183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16058057805027155985837577 12043543353770366989378183)
              ·
                refine ⟨18065315030655550484067275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12043543353770366989378183 18065315030655550484067275)
                ·
                  refine ⟨27097972545983325726100913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18065315030655550484067275 27097972545983325726100913)
                  ·
                    refine ⟨20323479409487494294575685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27097972545983325726100913 20323479409487494294575685)
                    ·
                      refine ⟨3810652389278905180232941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20323479409487494294575685 3810652389278905180232941)
                      ·
                        rfl

theorem cell23_7421219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_7421219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421219 prefixEnd_7421219 := by exact prefixLift 7421219
  have htrace : WordTrace (prefixWord ++ tailWord_7421219) baseStart_7421219 baseEnd_7421219 := by
    simpa [prefixWord, tailWord_7421219, baseEnd_7421219] using wordTrace_append hprefix tailTrace_7421219
  have hstable : (prefixWord ++ tailWord_7421219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421219).length < 2 ^ (prefixWord ++ tailWord_7421219).sum := by decide
  have hdescent : baseEnd_7421219 < baseStart_7421219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421226 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7421226 : Nat := 118140960795 + 7421226 * 2 ^ 59
def prefixEnd_7421226 : Nat := 4983230072969 + 3 ^ 40 * 7421226 * 2
def baseEnd_7421226 : Nat := 3810655983643486652845409

theorem tailTrace_7421226 : CollatzResearch.WordTrace tailWord_7421226 prefixEnd_7421226 3810655983643486652845409 := by
  unfold tailWord_7421226
  simp only [CollatzResearch.WordTrace]
  refine ⟨67668587253043280334874883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180449566008115414226333021 67668587253043280334874883)
  ·
    refine ⟨101502880879564920502312325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67668587253043280334874883 101502880879564920502312325)
    ·
      refine ⟨19031790164918422594183561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101502880879564920502312325 19031790164918422594183561)
      ·
        refine ⟨14273842623688816945637671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19031790164918422594183561 14273842623688816945637671)
        ·
          refine ⟨21410763935533225418456507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14273842623688816945637671 21410763935533225418456507)
          ·
            refine ⟨32116145903299838127684761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21410763935533225418456507 32116145903299838127684761)
            ·
              refine ⟨24087109427474878595763571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32116145903299838127684761 24087109427474878595763571)
              ·
                refine ⟨36130664141212317893645357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24087109427474878595763571 36130664141212317893645357)
                ·
                  refine ⟨13548999052954619210117009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36130664141212317893645357 13548999052954619210117009)
                  ·
                    refine ⟨10161749289715964407587757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13548999052954619210117009 10161749289715964407587757)
                    ·
                      refine ⟨3810655983643486652845409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10161749289715964407587757 3810655983643486652845409)
                      ·
                        rfl

theorem cell23_7421226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7421226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421226 prefixEnd_7421226 := by exact prefixLift 7421226
  have htrace : WordTrace (prefixWord ++ tailWord_7421226) baseStart_7421226 baseEnd_7421226 := by
    simpa [prefixWord, tailWord_7421226, baseEnd_7421226] using wordTrace_append hprefix tailTrace_7421226
  have hstable : (prefixWord ++ tailWord_7421226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421226).length < 2 ^ (prefixWord ++ tailWord_7421226).sum := by decide
  have hdescent : baseEnd_7421226 < baseStart_7421226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421270 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7421270 : Nat := 118140960795 + 7421270 * 2 ^ 59
def prefixEnd_7421270 : Nat := 4983230072969 + 3 ^ 40 * 7421270 * 2
def baseEnd_7421270 : Nat := 3810678576792284480695207

theorem tailTrace_7421270 : CollatzResearch.WordTrace tailWord_7421270 prefixEnd_7421270 3810678576792284480695207 := by
  unfold tailWord_7421270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917247114000857303381329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180450635882675811236067509 16917247114000857303381329)
  ·
    refine ⟨12687935335500642977535997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16917247114000857303381329 12687935335500642977535997)
    ·
      refine ⟨4757975750812741116575999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12687935335500642977535997 4757975750812741116575999)
      ·
        refine ⟨7136963626219111674863999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757975750812741116575999 7136963626219111674863999)
        ·
          refine ⟨10705445439328667512295999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136963626219111674863999 10705445439328667512295999)
          ·
            refine ⟨16058168158993001268443999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10705445439328667512295999 16058168158993001268443999)
            ·
              refine ⟨24087252238489501902665999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16058168158993001268443999 24087252238489501902665999)
              ·
                refine ⟨36130878357734252853998999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24087252238489501902665999 36130878357734252853998999)
                ·
                  refine ⟨54196317536601379280998499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36130878357734252853998999 54196317536601379280998499)
                  ·
                    refine ⟨81294476304902068921497749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54196317536601379280998499 81294476304902068921497749)
                    ·
                      refine ⟨3810678576792284480695207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81294476304902068921497749 3810678576792284480695207)
                      ·
                        rfl

theorem cell23_7421270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7421270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421270 prefixEnd_7421270 := by exact prefixLift 7421270
  have htrace : WordTrace (prefixWord ++ tailWord_7421270) baseStart_7421270 baseEnd_7421270 := by
    simpa [prefixWord, tailWord_7421270, baseEnd_7421270] using wordTrace_append hprefix tailTrace_7421270
  have hstable : (prefixWord ++ tailWord_7421270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421270).length < 2 ^ (prefixWord ++ tailWord_7421270).sum := by decide
  have hdescent : baseEnd_7421270 < baseStart_7421270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421272 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_7421272 : Nat := 118140960795 + 7421272 * 2 ^ 59
def prefixEnd_7421272 : Nat := 4983230072969 + 3 ^ 40 * 7421272 * 2
def baseEnd_7421272 : Nat := 1270226534584531157623399

theorem tailTrace_7421272 : CollatzResearch.WordTrace tailWord_7421272 prefixEnd_7421272 1270226534584531157623399 := by
  unfold tailWord_7421272
  simp only [CollatzResearch.WordTrace]
  refine ⟨135338013385003235597837035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180450684513337647463782713 135338013385003235597837035)
  ·
    refine ⟨203007020077504853396755553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135338013385003235597837035 203007020077504853396755553)
    ·
      refine ⟨152255265058128640047566665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203007020077504853396755553 152255265058128640047566665)
      ·
        refine ⟨114191448793596480035674999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152255265058128640047566665 114191448793596480035674999)
        ·
          refine ⟨171287173190394720053512499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114191448793596480035674999 171287173190394720053512499)
          ·
            refine ⟨256930759785592080080268749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171287173190394720053512499 256930759785592080080268749)
            ·
              refine ⟨96349034919597030030100781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256930759785592080080268749 96349034919597030030100781)
              ·
                refine ⟨36130888094848886261287793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96349034919597030030100781 36130888094848886261287793)
                ·
                  refine ⟨27098166071136664695965845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36130888094848886261287793 27098166071136664695965845)
                  ·
                    refine ⟨1270226534584531157623399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27098166071136664695965845 1270226534584531157623399)
                    ·
                      rfl

theorem cell23_7421272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_7421272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421272 prefixEnd_7421272 := by exact prefixLift 7421272
  have htrace : WordTrace (prefixWord ++ tailWord_7421272) baseStart_7421272 baseEnd_7421272 := by
    simpa [prefixWord, tailWord_7421272, baseEnd_7421272] using wordTrace_append hprefix tailTrace_7421272
  have hstable : (prefixWord ++ tailWord_7421272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421272).length < 2 ^ (prefixWord ++ tailWord_7421272).sum := by decide
  have hdescent : baseEnd_7421272 < baseStart_7421272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421277 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7421277 : Nat := 118140960795 + 7421277 * 2 ^ 59
def prefixEnd_7421277 : Nat := 4983230072969 + 3 ^ 40 * 7421277 * 2
def baseEnd_7421277 : Nat := 3810682171156865953307675

theorem tailTrace_7421277 : CollatzResearch.WordTrace tailWord_7421277 prefixEnd_7421277 3810682171156865953307675 := by
  unfold tailWord_7421277
  simp only [CollatzResearch.WordTrace]
  refine ⟨270676209134988357049606085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180450806089992238033070723 270676209134988357049606085)
  ·
    refine ⟨50751789212810316946801141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270676209134988357049606085 50751789212810316946801141)
    ·
      refine ⟨4757980238700967213762607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50751789212810316946801141 4757980238700967213762607)
      ·
        refine ⟨7136970358051450820643911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757980238700967213762607 7136970358051450820643911)
        ·
          refine ⟨10705455537077176230965867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136970358051450820643911 10705455537077176230965867)
          ·
            refine ⟨16058183305615764346448801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10705455537077176230965867 16058183305615764346448801)
            ·
              refine ⟨12043637479211823259836601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16058183305615764346448801 12043637479211823259836601)
              ·
                refine ⟨9032728109408867444877451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12043637479211823259836601 9032728109408867444877451)
                ·
                  refine ⟨13549092164113301167316177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032728109408867444877451 13549092164113301167316177)
                  ·
                    refine ⟨10161819123084975875487133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13549092164113301167316177 10161819123084975875487133)
                    ·
                      refine ⟨3810682171156865953307675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10161819123084975875487133 3810682171156865953307675)
                      ·
                        rfl

theorem cell23_7421277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7421277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421277 prefixEnd_7421277 := by exact prefixLift 7421277
  have htrace : WordTrace (prefixWord ++ tailWord_7421277) baseStart_7421277 baseEnd_7421277 := by
    simpa [prefixWord, tailWord_7421277, baseEnd_7421277] using wordTrace_append hprefix tailTrace_7421277
  have hstable : (prefixWord ++ tailWord_7421277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421277).length < 2 ^ (prefixWord ++ tailWord_7421277).sum := by decide
  have hdescent : baseEnd_7421277 < baseStart_7421277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421283 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 1, 3, 2]
def baseStart_7421283 : Nat := 118140960795 + 7421283 * 2 ^ 59
def prefixEnd_7421283 : Nat := 4983230072969 + 3 ^ 40 * 7421283 * 2
def baseEnd_7421283 : Nat := 3810685252040792929832647

theorem tailTrace_7421283 : CollatzResearch.WordTrace tailWord_7421283 prefixEnd_7421283 3810685252040792929832647 := by
  unfold tailWord_7421283
  simp only [CollatzResearch.WordTrace]
  refine ⟨270676427972966620074324503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180450951981977746716216335 270676427972966620074324503)
  ·
    refine ⟨406014641959449930111486755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270676427972966620074324503 406014641959449930111486755)
    ·
      refine ⟨609021962939174895167230133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406014641959449930111486755 609021962939174895167230133)
      ·
        refine ⟨57095809025547646421927825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 609021962939174895167230133 57095809025547646421927825)
        ·
          refine ⟨42821856769160734816445869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57095809025547646421927825 42821856769160734816445869)
          ·
            refine ⟨16058196288435275556167201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42821856769160734816445869 16058196288435275556167201)
            ·
              refine ⟨12043647216326456667125401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16058196288435275556167201 12043647216326456667125401)
              ·
                refine ⟨9032735412244842500344051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12043647216326456667125401 9032735412244842500344051)
                ·
                  refine ⟨13549103118367263750516077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032735412244842500344051 13549103118367263750516077)
                  ·
                    refine ⟨5080913669387723906443529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13549103118367263750516077 5080913669387723906443529)
                    ·
                      refine ⟨3810685252040792929832647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080913669387723906443529 3810685252040792929832647)
                      ·
                        rfl

theorem cell23_7421283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_7421283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421283 prefixEnd_7421283 := by exact prefixLift 7421283
  have htrace : WordTrace (prefixWord ++ tailWord_7421283) baseStart_7421283 baseEnd_7421283 := by
    simpa [prefixWord, tailWord_7421283, baseEnd_7421283] using wordTrace_append hprefix tailTrace_7421283
  have hstable : (prefixWord ++ tailWord_7421283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421283).length < 2 ^ (prefixWord ++ tailWord_7421283).sum := by decide
  have hdescent : baseEnd_7421283 < baseStart_7421283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421296 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 6, 2, 2]
def baseStart_7421296 : Nat := 118140960795 + 7421296 * 2 ^ 59
def prefixEnd_7421296 : Nat := 4983230072969 + 3 ^ 40 * 7421296 * 2
def baseEnd_7421296 : Nat := 3810691927289301378970087

theorem tailTrace_7421296 : CollatzResearch.WordTrace tailWord_7421296 prefixEnd_7421296 3810691927289301378970087 := by
  unfold tailWord_7421296
  simp only [CollatzResearch.WordTrace]
  refine ⟨135338451060959761647273871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180451268081279682196365161 135338451060959761647273871)
  ·
    refine ⟨203007676591439642470910807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135338451060959761647273871 203007676591439642470910807)
    ·
      refine ⟨304511514887159463706366211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203007676591439642470910807 304511514887159463706366211)
      ·
        refine ⟨456767272330739195559549317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304511514887159463706366211 456767272330739195559549317)
        ·
          refine ⟨85643863562013599167415497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456767272330739195559549317 85643863562013599167415497)
          ·
            refine ⟨64232897671510199375561623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85643863562013599167415497 64232897671510199375561623)
            ·
              refine ⟨96349346507265299063342435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64232897671510199375561623 96349346507265299063342435)
              ·
                refine ⟨144524019760897948595013653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96349346507265299063342435 144524019760897948595013653)
                ·
                  refine ⟨6774563426292091340391265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144524019760897948595013653 6774563426292091340391265)
                  ·
                    refine ⟨5080922569719068505293449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6774563426292091340391265 5080922569719068505293449)
                    ·
                      refine ⟨3810691927289301378970087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080922569719068505293449 3810691927289301378970087)
                      ·
                        rfl

theorem cell23_7421296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 2, 2].length) (baseStart_7421296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421296 prefixEnd_7421296 := by exact prefixLift 7421296
  have htrace : WordTrace (prefixWord ++ tailWord_7421296) baseStart_7421296 baseEnd_7421296 := by
    simpa [prefixWord, tailWord_7421296, baseEnd_7421296] using wordTrace_append hprefix tailTrace_7421296
  have hstable : (prefixWord ++ tailWord_7421296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421296).length < 2 ^ (prefixWord ++ tailWord_7421296).sum := by decide
  have hdescent : baseEnd_7421296 < baseStart_7421296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421319 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 7]
def baseStart_7421319 : Nat := 118140960795 + 7421319 * 2 ^ 59
def prefixEnd_7421319 : Nat := 4983230072969 + 3 ^ 40 * 7421319 * 2
def baseEnd_7421319 : Nat := 423411526371594976553609

theorem tailTrace_7421319 : CollatzResearch.WordTrace tailWord_7421319 prefixEnd_7421319 423411526371594976553609 := by
  unfold tailWord_7421319
  simp only [CollatzResearch.WordTrace]
  refine ⟨270677741000836198222635011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180451827333890798815090007 270677741000836198222635011)
  ·
    refine ⟨406016611501254297333952517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270677741000836198222635011 406016611501254297333952517)
    ·
      refine ⟨76128114656485180750116097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406016611501254297333952517 76128114656485180750116097)
      ·
        refine ⟨57096085992363885562587073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76128114656485180750116097 57096085992363885562587073)
        ·
          refine ⟨42822064494272914171940305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57096085992363885562587073 42822064494272914171940305)
          ·
            refine ⟨32116548370704685628955229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42822064494272914171940305 32116548370704685628955229)
            ·
              refine ⟨12043705639014257110858211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32116548370704685628955229 12043705639014257110858211)
              ·
                refine ⟨18065558458521385666287317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12043705639014257110858211 18065558458521385666287317)
                ·
                  refine ⟨423411526371594976553609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18065558458521385666287317 423411526371594976553609)
                  ·
                    rfl

theorem cell23_7421319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 7].length) (baseStart_7421319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421319 prefixEnd_7421319 := by exact prefixLift 7421319
  have htrace : WordTrace (prefixWord ++ tailWord_7421319) baseStart_7421319 baseEnd_7421319 := by
    simpa [prefixWord, tailWord_7421319, baseEnd_7421319] using wordTrace_append hprefix tailTrace_7421319
  have hstable : (prefixWord ++ tailWord_7421319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421319).length < 2 ^ (prefixWord ++ tailWord_7421319).sum := by decide
  have hdescent : baseEnd_7421319 < baseStart_7421319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421339 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 7, 2]
def baseStart_7421339 : Nat := 118140960795 + 7421339 * 2 ^ 59
def prefixEnd_7421339 : Nat := 4983230072969 + 3 ^ 40 * 7421339 * 2
def baseEnd_7421339 : Nat := 3810714006957444710732389

theorem tailTrace_7421339 : CollatzResearch.WordTrace tailWord_7421339 prefixEnd_7421339 3810714006957444710732389 := by
  unfold tailWord_7421339
  simp only [CollatzResearch.WordTrace]
  refine ⟨270678470460763741638363071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180452313640509161092242047 270678470460763741638363071)
  ·
    refine ⟨406017705691145612457544607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270678470460763741638363071 406017705691145612457544607)
    ·
      refine ⟨609026558536718418686316911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406017705691145612457544607 609026558536718418686316911)
      ·
        refine ⟨913539837805077628029475367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609026558536718418686316911 913539837805077628029475367)
        ·
          refine ⟨1370309756707616442044213051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913539837805077628029475367 1370309756707616442044213051)
          ·
            refine ⟨2055464635061424663066319577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370309756707616442044213051 2055464635061424663066319577)
            ·
              refine ⟨1541598476296068497299739683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055464635061424663066319577 1541598476296068497299739683)
              ·
                refine ⟨2312397714444102745949609525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541598476296068497299739683 2312397714444102745949609525)
                ·
                  refine ⟨216787285729134632432775893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2312397714444102745949609525 216787285729134632432775893)
                  ·
                    refine ⟨5080952009276592947643185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216787285729134632432775893 5080952009276592947643185)
                    ·
                      refine ⟨3810714006957444710732389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080952009276592947643185 3810714006957444710732389)
                      ·
                        rfl

theorem cell23_7421339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7, 2].length) (baseStart_7421339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421339 prefixEnd_7421339 := by exact prefixLift 7421339
  have htrace : WordTrace (prefixWord ++ tailWord_7421339) baseStart_7421339 baseEnd_7421339 := by
    simpa [prefixWord, tailWord_7421339, baseEnd_7421339] using wordTrace_append hprefix tailTrace_7421339
  have hstable : (prefixWord ++ tailWord_7421339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421339).length < 2 ^ (prefixWord ++ tailWord_7421339).sum := by decide
  have hdescent : baseEnd_7421339 < baseStart_7421339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421386 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_7421386 : Nat := 118140960795 + 7421386 * 2 ^ 59
def prefixEnd_7421386 : Nat := 4983230072969 + 3 ^ 40 * 7421386 * 2
def baseEnd_7421386 : Nat := 3810738140548206026844673

theorem tailTrace_7421386 : CollatzResearch.WordTrace tailWord_7421386 prefixEnd_7421386 3810738140548206026844673 := by
  unfold tailWord_7421386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67670046172898367166331003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180453456461062312443549341 67670046172898367166331003)
  ·
    refine ⟨101505069259347550749496505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67670046172898367166331003 101505069259347550749496505)
    ·
      refine ⟨76128801944510663062122379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101505069259347550749496505 76128801944510663062122379)
      ·
        refine ⟨114193202916765994593183569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76128801944510663062122379 114193202916765994593183569)
        ·
          refine ⟨85644902187574495944887677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114193202916765994593183569 85644902187574495944887677)
          ·
            refine ⟨32116838320340435979332879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85644902187574495944887677 32116838320340435979332879)
            ·
              refine ⟨48175257480510653968999319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32116838320340435979332879 48175257480510653968999319)
              ·
                refine ⟨72262886220765980953498979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48175257480510653968999319 72262886220765980953498979)
                ·
                  refine ⟨108394329331148971430248469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72262886220765980953498979 108394329331148971430248469)
                  ·
                    refine ⟨5080984187397608035792897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108394329331148971430248469 5080984187397608035792897)
                    ·
                      refine ⟨3810738140548206026844673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5080984187397608035792897 3810738140548206026844673)
                      ·
                        rfl

theorem cell23_7421386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_7421386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421386 prefixEnd_7421386 := by exact prefixLift 7421386
  have htrace : WordTrace (prefixWord ++ tailWord_7421386) baseStart_7421386 baseEnd_7421386 := by
    simpa [prefixWord, tailWord_7421386, baseEnd_7421386] using wordTrace_append hprefix tailTrace_7421386
  have hstable : (prefixWord ++ tailWord_7421386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421386).length < 2 ^ (prefixWord ++ tailWord_7421386).sum := by decide
  have hdescent : baseEnd_7421386 < baseStart_7421386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421426 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_7421426 : Nat := 118140960795 + 7421426 * 2 ^ 59
def prefixEnd_7421426 : Nat := 4983230072969 + 3 ^ 40 * 7421426 * 2
def baseEnd_7421426 : Nat := 423417631086042874482721

theorem tailTrace_7421426 : CollatzResearch.WordTrace tailWord_7421426 prefixEnd_7421426 423417631086042874482721 := by
  unfold tailWord_7421426
  simp only [CollatzResearch.WordTrace]
  refine ⟨67670410902862138874195033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180454429074299036997853421 67670410902862138874195033)
  ·
    refine ⟨50752808177146604155646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67670410902862138874195033 50752808177146604155646275)
    ·
      refine ⟨76129212265719906233469413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50752808177146604155646275 76129212265719906233469413)
      ·
        refine ⟨14274227299822482418775515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76129212265719906233469413 14274227299822482418775515)
        ·
          refine ⟨21411340949733723628163273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14274227299822482418775515 21411340949733723628163273)
          ·
            refine ⟨16058505712300292721122455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21411340949733723628163273 16058505712300292721122455)
            ·
              refine ⟨24087758568450439081683683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16058505712300292721122455 24087758568450439081683683)
              ·
                refine ⟨36131637852675658622525525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24087758568450439081683683 36131637852675658622525525)
                ·
                  refine ⟨423417631086042874482721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36131637852675658622525525 423417631086042874482721)
                  ·
                    rfl

theorem cell23_7421426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_7421426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421426 prefixEnd_7421426 := by exact prefixLift 7421426
  have htrace : WordTrace (prefixWord ++ tailWord_7421426) baseStart_7421426 baseEnd_7421426 := by
    simpa [prefixWord, tailWord_7421426, baseEnd_7421426] using wordTrace_append hprefix tailTrace_7421426
  have hstable : (prefixWord ++ tailWord_7421426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421426).length < 2 ^ (prefixWord ++ tailWord_7421426).sum := by decide
  have hdescent : baseEnd_7421426 < baseStart_7421426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421430 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_7421430 : Nat := 118140960795 + 7421430 * 2 ^ 59
def prefixEnd_7421430 : Nat := 4983230072969 + 3 ^ 40 * 7421430 * 2
def baseEnd_7421430 : Nat := 1270253577899001284898157

theorem tailTrace_7421430 : CollatzResearch.WordTrace tailWord_7421430 prefixEnd_7421430 1270253577899001284898157 := by
  unfold tailWord_7421430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917611843964629011245359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180454526335622709453283829 16917611843964629011245359)
  ·
    refine ⟨25376417765946943516868039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16917611843964629011245359 25376417765946943516868039)
    ·
      refine ⟨38064626648920415275302059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25376417765946943516868039 38064626648920415275302059)
      ·
        refine ⟨57096939973380622912953089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38064626648920415275302059 57096939973380622912953089)
        ·
          refine ⟨42822704980035467184714817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57096939973380622912953089 42822704980035467184714817)
          ·
            refine ⟨32117028735026600388536113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42822704980035467184714817 32117028735026600388536113)
            ·
              refine ⟨24087771551269950291402085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32117028735026600388536113 24087771551269950291402085)
              ·
                refine ⟨4516457165863115679637891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24087771551269950291402085 4516457165863115679637891)
                ·
                  refine ⟨6774685748794673519456837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516457165863115679637891 6774685748794673519456837)
                  ·
                    refine ⟨1270253577899001284898157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774685748794673519456837 1270253577899001284898157)
                    ·
                      rfl

theorem cell23_7421430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_7421430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421430 prefixEnd_7421430 := by exact prefixLift 7421430
  have htrace : WordTrace (prefixWord ++ tailWord_7421430) baseStart_7421430 baseEnd_7421430 := by
    simpa [prefixWord, tailWord_7421430, baseEnd_7421430] using wordTrace_append hprefix tailTrace_7421430
  have hstable : (prefixWord ++ tailWord_7421430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421430).length < 2 ^ (prefixWord ++ tailWord_7421430).sum := by decide
  have hdescent : baseEnd_7421430 < baseStart_7421430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421439 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 3, 5]
def baseStart_7421439 : Nat := 118140960795 + 7421439 * 2 ^ 59
def prefixEnd_7421439 : Nat := 4983230072969 + 3 ^ 40 * 7421439 * 2
def baseEnd_7421439 : Nat := 1270255118340964773160643

theorem tailTrace_7421439 : CollatzResearch.WordTrace tailWord_7421439 prefixEnd_7421439 1270255118340964773160643 := by
  unfold tailWord_7421439
  simp only [CollatzResearch.WordTrace]
  refine ⟨270682117760401458717003371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180454745173600972478002247 270682117760401458717003371)
  ·
    refine ⟨406023176640602188075505057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270682117760401458717003371 406023176640602188075505057)
    ·
      refine ⟨304517382480451641056628793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406023176640602188075505057 304517382480451641056628793)
      ·
        refine ⟨228388036860338730792471595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304517382480451641056628793 228388036860338730792471595)
        ·
          refine ⟨342582055290508096188707393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228388036860338730792471595 342582055290508096188707393)
          ·
            refine ⟨256936541467881072141530545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342582055290508096188707393 256936541467881072141530545)
            ·
              refine ⟨192702406100910804106147909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256936541467881072141530545 192702406100910804106147909)
              ·
                refine ⟨36131701143920775769902733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192702406100910804106147909 36131701143920775769902733)
                ·
                  refine ⟨13549387928970290913713525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36131701143920775769902733 13549387928970290913713525)
                  ·
                    refine ⟨1270255118340964773160643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13549387928970290913713525 1270255118340964773160643)
                    ·
                      rfl

theorem cell23_7421439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_7421439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421439 prefixEnd_7421439 := by exact prefixLift 7421439
  have htrace : WordTrace (prefixWord ++ tailWord_7421439) baseStart_7421439 baseEnd_7421439 := by
    simpa [prefixWord, tailWord_7421439, baseEnd_7421439] using wordTrace_append hprefix tailTrace_7421439
  have hstable : (prefixWord ++ tailWord_7421439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421439).length < 2 ^ (prefixWord ++ tailWord_7421439).sum := by decide
  have hdescent : baseEnd_7421439 < baseStart_7421439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421496 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_7421496 : Nat := 118140960795 + 7421496 * 2 ^ 59
def prefixEnd_7421496 : Nat := 4983230072969 + 3 ^ 40 * 7421496 * 2
def baseEnd_7421496 : Nat := 3810794623420200596469167

theorem tailTrace_7421496 : CollatzResearch.WordTrace tailWord_7421496 prefixEnd_7421496 3810794623420200596469167 := by
  unfold tailWord_7421496
  simp only [CollatzResearch.WordTrace]
  refine ⟨135342098360597478725914171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180456131147463304967885561 135342098360597478725914171)
  ·
    refine ⟨203013147540896218088871257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135342098360597478725914171 203013147540896218088871257)
    ·
      refine ⟨152259860655672163566653443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203013147540896218088871257 152259860655672163566653443)
      ·
        refine ⟨228389790983508245349980165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152259860655672163566653443 228389790983508245349980165)
        ·
          refine ⟨42823085809407796003121281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228389790983508245349980165 42823085809407796003121281)
          ·
            refine ⟨32117314357055847002340961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42823085809407796003121281 32117314357055847002340961)
            ·
              refine ⟨24087985767791885251755721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32117314357055847002340961 24087985767791885251755721)
              ·
                refine ⟨18065989325843913938816791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24087985767791885251755721 18065989325843913938816791)
                ·
                  refine ⟨27098983988765870908225187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18065989325843913938816791 27098983988765870908225187)
                  ·
                    refine ⟨40648475983148806362337781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27098983988765870908225187 40648475983148806362337781)
                    ·
                      refine ⟨3810794623420200596469167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40648475983148806362337781 3810794623420200596469167)
                      ·
                        rfl

theorem cell23_7421496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_7421496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421496 prefixEnd_7421496 := by exact prefixLift 7421496
  have htrace : WordTrace (prefixWord ++ tailWord_7421496) baseStart_7421496 baseEnd_7421496 := by
    simpa [prefixWord, tailWord_7421496, baseEnd_7421496] using wordTrace_append hprefix tailTrace_7421496
  have hstable : (prefixWord ++ tailWord_7421496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421496).length < 2 ^ (prefixWord ++ tailWord_7421496).sum := by decide
  have hdescent : baseEnd_7421496 < baseStart_7421496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421503 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 2, 4]
def baseStart_7421503 : Nat := 118140960795 + 7421503 * 2 ^ 59
def prefixEnd_7421503 : Nat := 4983230072969 + 3 ^ 40 * 7421503 * 2
def baseEnd_7421503 : Nat := 1270266072594927356360545

theorem tailTrace_7421503 : CollatzResearch.WordTrace tailWord_7421503 prefixEnd_7421503 1270266072594927356360545 := by
  unfold tailWord_7421503
  simp only [CollatzResearch.WordTrace]
  refine ⟨270684452032169597647333163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180456301354779731764888775 270684452032169597647333163)
  ·
    refine ⟨406026678048254396470999745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270684452032169597647333163 406026678048254396470999745)
    ·
      refine ⟨304520008536190797353249809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406026678048254396470999745 304520008536190797353249809)
      ·
        refine ⟨228390006402143098014937357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304520008536190797353249809 228390006402143098014937357)
        ·
          refine ⟨85646252400803661755601509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228390006402143098014937357 85646252400803661755601509)
          ·
            refine ⟨16058672325150686579175283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85646252400803661755601509 16058672325150686579175283)
            ·
              refine ⟨24088008487726029868762925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16058672325150686579175283 24088008487726029868762925)
              ·
                refine ⟨9033003182897261200786097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24088008487726029868762925 9033003182897261200786097)
                ·
                  refine ⟨6774752387172945900589573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033003182897261200786097 6774752387172945900589573)
                  ·
                    refine ⟨1270266072594927356360545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774752387172945900589573 1270266072594927356360545)
                    ·
                      rfl

theorem cell23_7421503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_7421503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421503 prefixEnd_7421503 := by exact prefixLift 7421503
  have htrace : WordTrace (prefixWord ++ tailWord_7421503) baseStart_7421503 baseEnd_7421503 := by
    simpa [prefixWord, tailWord_7421503, baseEnd_7421503] using wordTrace_append hprefix tailTrace_7421503
  have hstable : (prefixWord ++ tailWord_7421503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421503).length < 2 ^ (prefixWord ++ tailWord_7421503).sum := by decide
  have hdescent : baseEnd_7421503 < baseStart_7421503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421529 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_7421529 : Nat := 118140960795 + 7421529 * 2 ^ 59
def prefixEnd_7421529 : Nat := 4983230072969 + 3 ^ 40 * 7421529 * 2
def baseEnd_7421529 : Nat := 1270270522760599655785505

theorem tailTrace_7421529 : CollatzResearch.WordTrace tailWord_7421529 prefixEnd_7421529 1270270522760599655785505 := by
  unfold tailWord_7421529
  simp only [CollatzResearch.WordTrace]
  refine ⟨270685400330075404087779641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180456933553383602725186427 270685400330075404087779641)
  ·
    refine ⟨203014050247556553065834731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270685400330075404087779641 203014050247556553065834731)
    ·
      refine ⟨304521075371334829598752097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203014050247556553065834731 304521075371334829598752097)
      ·
        refine ⟨228390806528501122199064073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304521075371334829598752097 228390806528501122199064073)
        ·
          refine ⟨171293104896375841649298055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228390806528501122199064073 171293104896375841649298055)
          ·
            refine ⟨256939657344563762473947083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171293104896375841649298055 256939657344563762473947083)
            ·
              refine ⟨385409486016845643710920625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256939657344563762473947083 385409486016845643710920625)
              ·
                refine ⟨289057114512634232783190469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385409486016845643710920625 289057114512634232783190469)
                ·
                  refine ⟨54198208971118918646848213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289057114512634232783190469 54198208971118918646848213)
                  ·
                    refine ⟨1270270522760599655785505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54198208971118918646848213 1270270522760599655785505)
                    ·
                      rfl

theorem cell23_7421529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_7421529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421529 prefixEnd_7421529 := by exact prefixLift 7421529
  have htrace : WordTrace (prefixWord ++ tailWord_7421529) baseStart_7421529 baseEnd_7421529 := by
    simpa [prefixWord, tailWord_7421529, baseEnd_7421529] using wordTrace_append hprefix tailTrace_7421529
  have hstable : (prefixWord ++ tailWord_7421529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421529).length < 2 ^ (prefixWord ++ tailWord_7421529).sum := by decide
  have hdescent : baseEnd_7421529 < baseStart_7421529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421533 : List Nat := [1, 4, 4, 2, 1, 11]
def baseStart_7421533 : Nat := 118140960795 + 7421533 * 2 ^ 59
def prefixEnd_7421533 : Nat := 4983230072969 + 3 ^ 40 * 7421533 * 2
def baseEnd_7421533 : Nat := 15682360585203361941179

theorem tailTrace_7421533 : CollatzResearch.WordTrace tailWord_7421533 prefixEnd_7421533 15682360585203361941179 := by
  unfold tailWord_7421533
  simp only [CollatzResearch.WordTrace]
  refine ⟨270685546222060912770925253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180457030814707275180616835 270685546222060912770925253)
  ·
    refine ⟨50753539916636421144548485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270685546222060912770925253 50753539916636421144548485)
    ·
      refine ⟨9516288734369328964602841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50753539916636421144548485 9516288734369328964602841)
      ·
        refine ⟨7137216550776996723452131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9516288734369328964602841 7137216550776996723452131)
        ·
          refine ⟨10705824826165495085178197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137216550776996723452131 10705824826165495085178197)
          ·
            refine ⟨15682360585203361941179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10705824826165495085178197 15682360585203361941179)
            ·
              rfl

theorem cell23_7421533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 11].length) (baseStart_7421533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421533 prefixEnd_7421533 := by exact prefixLift 7421533
  have htrace : WordTrace (prefixWord ++ tailWord_7421533) baseStart_7421533 baseEnd_7421533 := by
    simpa [prefixWord, tailWord_7421533, baseEnd_7421533] using wordTrace_append hprefix tailTrace_7421533
  have hstable : (prefixWord ++ tailWord_7421533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421533).length < 2 ^ (prefixWord ++ tailWord_7421533).sum := by decide
  have hdescent : baseEnd_7421533 < baseStart_7421533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421543 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_7421543 : Nat := 118140960795 + 7421543 * 2 ^ 59
def prefixEnd_7421543 : Nat := 4983230072969 + 3 ^ 40 * 7421543 * 2
def baseEnd_7421543 : Nat := 3810818757010961912581451

theorem tailTrace_7421543 : CollatzResearch.WordTrace tailWord_7421543 prefixEnd_7421543 3810818757010961912581451 := by
  unfold tailWord_7421543
  simp only [CollatzResearch.WordTrace]
  refine ⟨270685910952024684478789283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180457273968016456319192855 270685910952024684478789283)
  ·
    refine ⟨406028866428037026718183925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270685910952024684478789283 406028866428037026718183925)
    ·
      refine ⟨38065206227628471254829743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406028866428037026718183925 38065206227628471254829743)
      ·
        refine ⟨57097809341442706882244615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38065206227628471254829743 57097809341442706882244615)
        ·
          refine ⟨85646714012164060323366923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57097809341442706882244615 85646714012164060323366923)
          ·
            refine ⟨128470071018246090485050385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85646714012164060323366923 128470071018246090485050385)
            ·
              refine ⟨96352553263684567863787789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128470071018246090485050385 96352553263684567863787789)
              ·
                refine ⟨36132207473881712948920421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96352553263684567863787789 36132207473881712948920421)
                ·
                  refine ⟨6774788901352821177922579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36132207473881712948920421 6774788901352821177922579)
                  ·
                    refine ⟨10162183352029231766883869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6774788901352821177922579 10162183352029231766883869)
                    ·
                      refine ⟨3810818757010961912581451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10162183352029231766883869 3810818757010961912581451)
                      ·
                        rfl

theorem cell23_7421543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_7421543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421543 prefixEnd_7421543 := by exact prefixLift 7421543
  have htrace : WordTrace (prefixWord ++ tailWord_7421543) baseStart_7421543 baseEnd_7421543 := by
    simpa [prefixWord, tailWord_7421543, baseEnd_7421543] using wordTrace_append hprefix tailTrace_7421543
  have hstable : (prefixWord ++ tailWord_7421543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421543).length < 2 ^ (prefixWord ++ tailWord_7421543).sum := by decide
  have hdescent : baseEnd_7421543 < baseStart_7421543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421544 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7421544 : Nat := 118140960795 + 7421544 * 2 ^ 59
def prefixEnd_7421544 : Nat := 4983230072969 + 3 ^ 40 * 7421544 * 2
def baseEnd_7421544 : Nat := 3810819270491616408668947

theorem tailTrace_7421544 : CollatzResearch.WordTrace tailWord_7421544 prefixEnd_7421544 3810819270491616408668947 := by
  unfold tailWord_7421544
  simp only [CollatzResearch.WordTrace]
  refine ⟨135342973712510530824787843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180457298283347374433050457 135342973712510530824787843)
  ·
    refine ⟨203014460568765796237181765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135342973712510530824787843 203014460568765796237181765)
    ·
      refine ⟨38065211356643586794471581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203014460568765796237181765 38065211356643586794471581)
      ·
        refine ⟨14274454258741345047926843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38065211356643586794471581 14274454258741345047926843)
        ·
          refine ⟨21411681388112017571890265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14274454258741345047926843 21411681388112017571890265)
          ·
            refine ⟨16058761041084013178917699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21411681388112017571890265 16058761041084013178917699)
            ·
              refine ⟨24088141561626019768376549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16058761041084013178917699 24088141561626019768376549)
              ·
                refine ⟨4516526542804878706570603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24088141561626019768376549 4516526542804878706570603)
                ·
                  refine ⟨6774789814207318059855905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516526542804878706570603 6774789814207318059855905)
                  ·
                    refine ⟨5081092360655488544891929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6774789814207318059855905 5081092360655488544891929)
                    ·
                      refine ⟨3810819270491616408668947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081092360655488544891929 3810819270491616408668947)
                      ·
                        rfl

theorem cell23_7421544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7421544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421544 prefixEnd_7421544 := by exact prefixLift 7421544
  have htrace : WordTrace (prefixWord ++ tailWord_7421544) baseStart_7421544 baseEnd_7421544 := by
    simpa [prefixWord, tailWord_7421544, baseEnd_7421544] using wordTrace_append hprefix tailTrace_7421544
  have hstable : (prefixWord ++ tailWord_7421544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421544).length < 2 ^ (prefixWord ++ tailWord_7421544).sum := by decide
  have hdescent : baseEnd_7421544 < baseStart_7421544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421546 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_7421546 : Nat := 118140960795 + 7421546 * 2 ^ 59
def prefixEnd_7421546 : Nat := 4983230072969 + 3 ^ 40 * 7421546 * 2
def baseEnd_7421546 : Nat := 1270273432484308466947979

theorem tailTrace_7421546 : CollatzResearch.WordTrace tailWord_7421546 prefixEnd_7421546 1270273432484308466947979 := by
  unfold tailWord_7421546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67671505092753453997787123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180457346914009210660765661 67671505092753453997787123)
  ·
    refine ⟨101507257639130180996680685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67671505092753453997787123 101507257639130180996680685)
    ·
      refine ⟨38065221614673817873755257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101507257639130180996680685 38065221614673817873755257)
      ·
        refine ⟨28548916211005363405316443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38065221614673817873755257 28548916211005363405316443)
        ·
          refine ⟨42823374316508045107974665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28548916211005363405316443 42823374316508045107974665)
          ·
            refine ⟨32117530737381033830980999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42823374316508045107974665 32117530737381033830980999)
            ·
              refine ⟨48176296106071550746471499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32117530737381033830980999 48176296106071550746471499)
              ·
                refine ⟨72264444159107326119707249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48176296106071550746471499 72264444159107326119707249)
                ·
                  refine ⟨54198333119330494589780437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72264444159107326119707249 54198333119330494589780437)
                  ·
                    refine ⟨1270273432484308466947979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54198333119330494589780437 1270273432484308466947979)
                    ·
                      rfl

theorem cell23_7421546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_7421546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421546 prefixEnd_7421546 := by exact prefixLift 7421546
  have htrace : WordTrace (prefixWord ++ tailWord_7421546) baseStart_7421546 baseEnd_7421546 := by
    simpa [prefixWord, tailWord_7421546, baseEnd_7421546] using wordTrace_append hprefix tailTrace_7421546
  have hstable : (prefixWord ++ tailWord_7421546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421546).length < 2 ^ (prefixWord ++ tailWord_7421546).sum := by decide
  have hdescent : baseEnd_7421546 < baseStart_7421546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421550 : List Nat := [4, 1, 2, 2, 4, 1, 1, 8]
def baseStart_7421550 : Nat := 118140960795 + 7421550 * 2 ^ 59
def prefixEnd_7421550 : Nat := 4983230072969 + 3 ^ 40 * 7421550 * 2
def baseEnd_7421550 : Nat := 141141568569464569821997

theorem tailTrace_7421550 : CollatzResearch.WordTrace tailWord_7421550 prefixEnd_7421550 141141568569464569821997 := by
  unfold tailWord_7421550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33835770782874915584286763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180457444175332883116196069 33835770782874915584286763)
  ·
    refine ⟨50753656174312373376430145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33835770782874915584286763 50753656174312373376430145)
    ·
      refine ⟨38065242130734280032322609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50753656174312373376430145 38065242130734280032322609)
      ·
        refine ⟨28548931598050710024241957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38065242130734280032322609 28548931598050710024241957)
        ·
          refine ⟨5352924674634508129545367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28548931598050710024241957 5352924674634508129545367)
          ·
            refine ⟨8029387011951762194318051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352924674634508129545367 8029387011951762194318051)
            ·
              refine ⟨12044080517927643291477077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029387011951762194318051 12044080517927643291477077)
              ·
                refine ⟨141141568569464569821997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12044080517927643291477077 141141568569464569821997)
                ·
                  rfl

theorem cell23_7421550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_7421550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421550 prefixEnd_7421550 := by exact prefixLift 7421550
  have htrace : WordTrace (prefixWord ++ tailWord_7421550) baseStart_7421550 baseEnd_7421550 := by
    simpa [prefixWord, tailWord_7421550, baseEnd_7421550] using wordTrace_append hprefix tailTrace_7421550
  have hstable : (prefixWord ++ tailWord_7421550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421550).length < 2 ^ (prefixWord ++ tailWord_7421550).sum := by decide
  have hdescent : baseEnd_7421550 < baseStart_7421550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421613 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7421613 : Nat := 118140960795 + 7421613 * 2 ^ 59
def prefixEnd_7421613 : Nat := 4983230072969 + 3 ^ 40 * 7421613 * 2
def baseEnd_7421613 : Nat := 3810854700656776638706129

theorem tailTrace_7421613 : CollatzResearch.WordTrace tailWord_7421613 prefixEnd_7421613 3810854700656776638706129 := by
  unfold tailWord_7421613
  simp only [CollatzResearch.WordTrace]
  refine ⟨270688464061771086433837493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180458976041180724289224995 270688464061771086433837493)
  ·
    refine ⟨25377043505791039353172265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270688464061771086433837493 25377043505791039353172265)
    ·
      refine ⟨19032782629343279514879199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25377043505791039353172265 19032782629343279514879199)
      ·
        refine ⟨28549173944014919272318799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19032782629343279514879199 28549173944014919272318799)
        ·
          refine ⟨42823760916022378908478199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28549173944014919272318799 42823760916022378908478199)
          ·
            refine ⟨64235641374033568362717299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42823760916022378908478199 64235641374033568362717299)
            ·
              refine ⟨96353462061050352544075949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64235641374033568362717299 96353462061050352544075949)
              ·
                refine ⟨36132548272893882204028481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96353462061050352544075949 36132548272893882204028481)
                ·
                  refine ⟨27099411204670411653021361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36132548272893882204028481 27099411204670411653021361)
                  ·
                    refine ⟨20324558403502808739766021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27099411204670411653021361 20324558403502808739766021)
                    ·
                      refine ⟨3810854700656776638706129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20324558403502808739766021 3810854700656776638706129)
                      ·
                        rfl

theorem cell23_7421613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7421613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421613 prefixEnd_7421613 := by exact prefixLift 7421613
  have htrace : WordTrace (prefixWord ++ tailWord_7421613) baseStart_7421613 baseEnd_7421613 := by
    simpa [prefixWord, tailWord_7421613, baseEnd_7421613] using wordTrace_append hprefix tailTrace_7421613
  have hstable : (prefixWord ++ tailWord_7421613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421613).length < 2 ^ (prefixWord ++ tailWord_7421613).sum := by decide
  have hdescent : baseEnd_7421613 < baseStart_7421613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421673 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 6, 2]
def baseStart_7421673 : Nat := 118140960795 + 7421673 * 2 ^ 59
def prefixEnd_7421673 : Nat := 4983230072969 + 3 ^ 40 * 7421673 * 2
def baseEnd_7421673 : Nat := 3810885509496046403955853

theorem tailTrace_7421673 : CollatzResearch.WordTrace tailWord_7421673 prefixEnd_7421673 3810885509496046403955853 := by
  unfold tailWord_7421673
  simp only [CollatzResearch.WordTrace]
  refine ⟨270690652441553716681021673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180460434961035811120681115 270690652441553716681021673)
  ·
    refine ⟨203017989331165287510766255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270690652441553716681021673 203017989331165287510766255)
    ·
      refine ⟨304526983996747931266149383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203017989331165287510766255 304526983996747931266149383)
      ·
        refine ⟨456790475995121896899224075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304526983996747931266149383 456790475995121896899224075)
        ·
          refine ⟨685185713992682845348836113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456790475995121896899224075 685185713992682845348836113)
          ·
            refine ⟨513889285494512134011627085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685185713992682845348836113 513889285494512134011627085)
            ·
              refine ⟨192708482060442050254360157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513889285494512134011627085 192708482060442050254360157)
              ·
                refine ⟨72265680772665768845385059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192708482060442050254360157 72265680772665768845385059)
                ·
                  refine ⟨108398521158998653268077589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72265680772665768845385059 108398521158998653268077589)
                  ·
                    refine ⟨5081180679328061871941137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108398521158998653268077589 5081180679328061871941137)
                    ·
                      refine ⟨3810885509496046403955853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081180679328061871941137 3810885509496046403955853)
                      ·
                        rfl

theorem cell23_7421673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 6, 2].length) (baseStart_7421673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421673 prefixEnd_7421673 := by exact prefixLift 7421673
  have htrace : WordTrace (prefixWord ++ tailWord_7421673) baseStart_7421673 baseEnd_7421673 := by
    simpa [prefixWord, tailWord_7421673, baseEnd_7421673] using wordTrace_append hprefix tailTrace_7421673
  have hstable : (prefixWord ++ tailWord_7421673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421673).length < 2 ^ (prefixWord ++ tailWord_7421673).sum := by decide
  have hdescent : baseEnd_7421673 < baseStart_7421673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421683 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 3, 4]
def baseStart_7421683 : Nat := 118140960795 + 7421683 * 2 ^ 59
def prefixEnd_7421683 : Nat := 4983230072969 + 3 ^ 40 * 7421683 * 2
def baseEnd_7421683 : Nat := 1270296881434197121610269

theorem tailTrace_7421683 : CollatzResearch.WordTrace tailWord_7421683 prefixEnd_7421683 1270296881434197121610269 := by
  unfold tailWord_7421683
  simp only [CollatzResearch.WordTrace]
  refine ⟨270691017171517488388885703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180460678114344992259257135 270691017171517488388885703)
  ·
    refine ⟨406036525757276232583328555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270691017171517488388885703 406036525757276232583328555)
    ·
      refine ⟨609054788635914348874992833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406036525757276232583328555 609054788635914348874992833)
      ·
        refine ⟨456791091476935761656244625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609054788635914348874992833 456791091476935761656244625)
        ·
          refine ⟨342593318607701821242183469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456791091476935761656244625 342593318607701821242183469)
          ·
            refine ⟨128472494477888182965818801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342593318607701821242183469 128472494477888182965818801)
            ·
              refine ⟨96354370858416137224364101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128472494477888182965818801 96354370858416137224364101)
              ·
                refine ⟨18066444535953025729568269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96354370858416137224364101 18066444535953025729568269)
                ·
                  refine ⟨6774916700982384648588101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18066444535953025729568269 6774916700982384648588101)
                  ·
                    refine ⟨1270296881434197121610269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774916700982384648588101 1270296881434197121610269)
                    ·
                      rfl

theorem cell23_7421683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 4].length) (baseStart_7421683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421683 prefixEnd_7421683 := by exact prefixLift 7421683
  have htrace : WordTrace (prefixWord ++ tailWord_7421683) baseStart_7421683 baseEnd_7421683 := by
    simpa [prefixWord, tailWord_7421683, baseEnd_7421683] using wordTrace_append hprefix tailTrace_7421683
  have hstable : (prefixWord ++ tailWord_7421683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421683).length < 2 ^ (prefixWord ++ tailWord_7421683).sum := by decide
  have hdescent : baseEnd_7421683 < baseStart_7421683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421702 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7421702 : Nat := 118140960795 + 7421702 * 2 ^ 59
def prefixEnd_7421702 : Nat := 4983230072969 + 3 ^ 40 * 7421702 * 2
def baseEnd_7421702 : Nat := 3810900400435026790493221

theorem tailTrace_7421702 : CollatzResearch.WordTrace tailWord_7421702 prefixEnd_7421702 3810900400435026790493221 := by
  unfold tailWord_7421702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8459115942451520457307105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180461140105632436422551573 8459115942451520457307105)
  ·
    refine ⟨6344336956838640342980329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8459115942451520457307105 6344336956838640342980329)
    ·
      refine ⟨4758252717628980257235247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6344336956838640342980329 4758252717628980257235247)
      ·
        refine ⟨7137379076443470385852871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758252717628980257235247 7137379076443470385852871)
        ·
          refine ⟨10706068614665205578779307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137379076443470385852871 10706068614665205578779307)
          ·
            refine ⟨16059102921997808368168961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10706068614665205578779307 16059102921997808368168961)
            ·
              refine ⟨12044327191498356276126721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16059102921997808368168961 12044327191498356276126721)
              ·
                refine ⟨9033245393623767207095041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12044327191498356276126721 9033245393623767207095041)
                ·
                  refine ⟨6774934045217825405321281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033245393623767207095041 6774934045217825405321281)
                  ·
                    refine ⟨5081200533913369053990961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6774934045217825405321281 5081200533913369053990961)
                    ·
                      refine ⟨3810900400435026790493221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081200533913369053990961 3810900400435026790493221)
                      ·
                        rfl

theorem cell23_7421702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7421702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421702 prefixEnd_7421702 := by exact prefixLift 7421702
  have htrace : WordTrace (prefixWord ++ tailWord_7421702) baseStart_7421702 baseEnd_7421702 := by
    simpa [prefixWord, tailWord_7421702, baseEnd_7421702] using wordTrace_append hprefix tailTrace_7421702
  have hstable : (prefixWord ++ tailWord_7421702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421702).length < 2 ^ (prefixWord ++ tailWord_7421702).sum := by decide
  have hdescent : baseEnd_7421702 < baseStart_7421702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421710 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7421710 : Nat := 118140960795 + 7421710 * 2 ^ 59
def prefixEnd_7421710 : Nat := 4983230072969 + 3 ^ 40 * 7421710 * 2
def baseEnd_7421710 : Nat := 3810904508280262759193183

theorem tailTrace_7421710 : CollatzResearch.WordTrace tailWord_7421710 prefixEnd_7421710 3810904508280262759193183 := by
  unfold tailWord_7421710
  simp only [CollatzResearch.WordTrace]
  refine ⟨33836500242802459000014823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180461334628279781333412389 33836500242802459000014823)
  ·
    refine ⟨50754750364203688500022235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33836500242802459000014823 50754750364203688500022235)
    ·
      refine ⟨76132125546305532750033353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50754750364203688500022235 76132125546305532750033353)
      ·
        refine ⟨57099094159729149562525015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76132125546305532750033353 57099094159729149562525015)
        ·
          refine ⟨85648641239593724343787523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57099094159729149562525015 85648641239593724343787523)
          ·
            refine ⟨128472961859390586515681285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85648641239593724343787523 128472961859390586515681285)
            ·
              refine ⟨24088680348635734971690241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128472961859390586515681285 24088680348635734971690241)
              ·
                refine ⟨18066510261476801228767681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24088680348635734971690241 18066510261476801228767681)
                ·
                  refine ⟨13549882696107600921575761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18066510261476801228767681 13549882696107600921575761)
                  ·
                    refine ⟨10162412022080700691181821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13549882696107600921575761 10162412022080700691181821)
                    ·
                      refine ⟨3810904508280262759193183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10162412022080700691181821 3810904508280262759193183)
                      ·
                        rfl

theorem cell23_7421710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7421710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421710 prefixEnd_7421710 := by exact prefixLift 7421710
  have htrace : WordTrace (prefixWord ++ tailWord_7421710) baseStart_7421710 baseEnd_7421710 := by
    simpa [prefixWord, tailWord_7421710, baseEnd_7421710] using wordTrace_append hprefix tailTrace_7421710
  have hstable : (prefixWord ++ tailWord_7421710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421710).length < 2 ^ (prefixWord ++ tailWord_7421710).sum := by decide
  have hdescent : baseEnd_7421710 < baseStart_7421710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421717 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_7421717 : Nat := 118140960795 + 7421717 * 2 ^ 59
def prefixEnd_7421717 : Nat := 4983230072969 + 3 ^ 40 * 7421717 * 2
def baseEnd_7421717 : Nat := 1270302700881614743935217

theorem tailTrace_7421717 : CollatzResearch.WordTrace tailWord_7421717 prefixEnd_7421717 1270302700881614743935217 := by
  unfold tailWord_7421717
  simp only [CollatzResearch.WordTrace]
  refine ⟨270692257253394312195623405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180461504835596208130415603 270692257253394312195623405)
  ·
    refine ⟨101509596470022867073358777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270692257253394312195623405 101509596470022867073358777)
    ·
      refine ⟨76132197352517150305019083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101509596470022867073358777 76132197352517150305019083)
      ·
        refine ⟨114198296028775725457528625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76132197352517150305019083 114198296028775725457528625)
        ·
          refine ⟨85648722021581794093146469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114198296028775725457528625 85648722021581794093146469)
          ·
            refine ⟨16059135379046586392464963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85648722021581794093146469 16059135379046586392464963)
            ·
              refine ⟨24088703068569879588697445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16059135379046586392464963 24088703068569879588697445)
              ·
                refine ⟨4516631825356852422880771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24088703068569879588697445 4516631825356852422880771)
                ·
                  refine ⟨6774947738035278634321157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516631825356852422880771 6774947738035278634321157)
                  ·
                    refine ⟨1270302700881614743935217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6774947738035278634321157 1270302700881614743935217)
                    ·
                      rfl

theorem cell23_7421717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_7421717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421717 prefixEnd_7421717 := by exact prefixLift 7421717
  have htrace : WordTrace (prefixWord ++ tailWord_7421717) baseStart_7421717 baseEnd_7421717 := by
    simpa [prefixWord, tailWord_7421717, baseEnd_7421717] using wordTrace_append hprefix tailTrace_7421717
  have hstable : (prefixWord ++ tailWord_7421717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421717).length < 2 ^ (prefixWord ++ tailWord_7421717).sum := by decide
  have hdescent : baseEnd_7421717 < baseStart_7421717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421740 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_7421740 : Nat := 118140960795 + 7421740 * 2 ^ 59
def prefixEnd_7421740 : Nat := 4983230072969 + 3 ^ 40 * 7421740 * 2
def baseEnd_7421740 : Nat := 3810919912699897641818045

theorem tailTrace_7421740 : CollatzResearch.WordTrace tailWord_7421740 prefixEnd_7421740 3810919912699897641818045 := by
  unfold tailWord_7421740
  simp only [CollatzResearch.WordTrace]
  refine ⟨135346548066155493561855337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180462064088207324749140449 135346548066155493561855337)
  ·
    refine ⟨101509911049616620171391503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135346548066155493561855337 101509911049616620171391503)
    ·
      refine ⟨152264866574424930257087255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101509911049616620171391503 152264866574424930257087255)
      ·
        refine ⟨228397299861637395385630883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152264866574424930257087255 228397299861637395385630883)
        ·
          refine ⟨342595949792456093078446325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228397299861637395385630883 342595949792456093078446325)
          ·
            refine ⟨32118370293042758726104343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342595949792456093078446325 32118370293042758726104343)
            ·
              refine ⟨48177555439564138089156515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32118370293042758726104343 48177555439564138089156515)
              ·
                refine ⟨72266333159346207133734773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48177555439564138089156515 72266333159346207133734773)
                ·
                  refine ⟨6774968733688706918787635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72266333159346207133734773 6774968733688706918787635)
                  ·
                    refine ⟨10162453100533060378181453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6774968733688706918787635 10162453100533060378181453)
                    ·
                      refine ⟨3810919912699897641818045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10162453100533060378181453 3810919912699897641818045)
                      ·
                        rfl

theorem cell23_7421740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_7421740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421740 prefixEnd_7421740 := by exact prefixLift 7421740
  have htrace : WordTrace (prefixWord ++ tailWord_7421740) baseStart_7421740 baseEnd_7421740 := by
    simpa [prefixWord, tailWord_7421740, baseEnd_7421740] using wordTrace_append hprefix tailTrace_7421740
  have hstable : (prefixWord ++ tailWord_7421740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421740).length < 2 ^ (prefixWord ++ tailWord_7421740).sum := by decide
  have hdescent : baseEnd_7421740 < baseStart_7421740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421793 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_7421793 : Nat := 118140960795 + 7421793 * 2 ^ 59
def prefixEnd_7421793 : Nat := 4983230072969 + 3 ^ 40 * 7421793 * 2
def baseEnd_7421793 : Nat := 3810947127174585934455301

theorem tailTrace_7421793 : CollatzResearch.WordTrace tailWord_7421793 prefixEnd_7421793 3810947127174585934455301 := by
  unfold tailWord_7421793
  simp only [CollatzResearch.WordTrace]
  refine ⟨270695029201118977175390033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180463352800745984783593355 270695029201118977175390033)
  ·
    refine ⟨203021271900839232881542525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270695029201118977175390033 203021271900839232881542525)
    ·
      refine ⟨76132976962814712330578447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203021271900839232881542525 76132976962814712330578447)
      ·
        refine ⟨114199465444222068495867671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76132976962814712330578447 114199465444222068495867671)
        ·
          refine ⟨171299198166333102743801507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114199465444222068495867671 171299198166333102743801507)
          ·
            refine ⟨256948797249499654115702261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171299198166333102743801507 256948797249499654115702261)
            ·
              refine ⟨24088949742140592573347087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256948797249499654115702261 24088949742140592573347087)
              ·
                refine ⟨36133424613210888860020631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24088949742140592573347087 36133424613210888860020631)
                ·
                  refine ⟨54200136919816333290030947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36133424613210888860020631 54200136919816333290030947)
                  ·
                    refine ⟨81300205379724499935046421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54200136919816333290030947 81300205379724499935046421)
                    ·
                      refine ⟨3810947127174585934455301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81300205379724499935046421 3810947127174585934455301)
                      ·
                        rfl

theorem cell23_7421793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_7421793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421793 prefixEnd_7421793 := by exact prefixLift 7421793
  have htrace : WordTrace (prefixWord ++ tailWord_7421793) baseStart_7421793 baseEnd_7421793 := by
    simpa [prefixWord, tailWord_7421793, baseEnd_7421793] using wordTrace_append hprefix tailTrace_7421793
  have hstable : (prefixWord ++ tailWord_7421793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421793).length < 2 ^ (prefixWord ++ tailWord_7421793).sum := by decide
  have hdescent : baseEnd_7421793 < baseStart_7421793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421831 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_7421831 : Nat := 118140960795 + 7421831 * 2 ^ 59
def prefixEnd_7421831 : Nat := 4983230072969 + 3 ^ 40 * 7421831 * 2
def baseEnd_7421831 : Nat := 3810966639439456785780127

theorem tailTrace_7421831 : CollatzResearch.WordTrace tailWord_7421831 prefixEnd_7421831 3810966639439456785780127 := by
  unfold tailWord_7421831
  simp only [CollatzResearch.WordTrace]
  refine ⟨270696415174981309665273347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180464276783320873110182231 270696415174981309665273347)
  ·
    refine ⟨406044622762471964497910021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270696415174981309665273347 406044622762471964497910021)
    ·
      refine ⟨76133366767963493343358129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406044622762471964497910021 76133366767963493343358129)
      ·
        refine ⟨57100025075972620007518597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76133366767963493343358129 57100025075972620007518597)
        ·
          refine ⟨10706254701744866251409737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57100025075972620007518597 10706254701744866251409737)
          ·
            refine ⟨8029691026308649688557303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10706254701744866251409737 8029691026308649688557303)
            ·
              refine ⟨12044536539462974532835955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029691026308649688557303 12044536539462974532835955)
              ·
                refine ⟨18066804809194461799253933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12044536539462974532835955 18066804809194461799253933)
                ·
                  refine ⟨6775051803447923174720225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18066804809194461799253933 6775051803447923174720225)
                  ·
                    refine ⟨5081288852585942381040169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6775051803447923174720225 5081288852585942381040169)
                    ·
                      refine ⟨3810966639439456785780127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081288852585942381040169 3810966639439456785780127)
                      ·
                        rfl

theorem cell23_7421831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_7421831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421831 prefixEnd_7421831 := by exact prefixLift 7421831
  have htrace : WordTrace (prefixWord ++ tailWord_7421831) baseStart_7421831 baseEnd_7421831 := by
    simpa [prefixWord, tailWord_7421831, baseEnd_7421831] using wordTrace_append hprefix tailTrace_7421831
  have hstable : (prefixWord ++ tailWord_7421831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421831).length < 2 ^ (prefixWord ++ tailWord_7421831).sum := by decide
  have hdescent : baseEnd_7421831 < baseStart_7421831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421833 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_7421833 : Nat := 118140960795 + 7421833 * 2 ^ 59
def prefixEnd_7421833 : Nat := 4983230072969 + 3 ^ 40 * 7421833 * 2
def baseEnd_7421833 : Nat := 1270322555466921925985039

theorem tailTrace_7421833 : CollatzResearch.WordTrace tailWord_7421833 prefixEnd_7421833 1270322555466921925985039 := by
  unfold tailWord_7421833
  simp only [CollatzResearch.WordTrace]
  refine ⟨270696488120974064006846153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180464325413982709337897435 270696488120974064006846153)
  ·
    refine ⟨203022366090730548005134615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270696488120974064006846153 203022366090730548005134615)
    ·
      refine ⟨304533549136095822007701923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203022366090730548005134615 304533549136095822007701923)
      ·
        refine ⟨456800323704143733011552885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304533549136095822007701923 456800323704143733011552885)
        ·
          refine ⟨42825030347263474969833083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 456800323704143733011552885 42825030347263474969833083)
          ·
            refine ⟨64237545520895212454749625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42825030347263474969833083 64237545520895212454749625)
            ·
              refine ⟨48178159140671409341062219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64237545520895212454749625 48178159140671409341062219)
              ·
                refine ⟨72267238711007114011593329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48178159140671409341062219 72267238711007114011593329)
                ·
                  refine ⟨54200429033255335508694997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72267238711007114011593329 54200429033255335508694997)
                  ·
                    refine ⟨1270322555466921925985039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54200429033255335508694997 1270322555466921925985039)
                    ·
                      rfl

theorem cell23_7421833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_7421833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421833 prefixEnd_7421833 := by exact prefixLift 7421833
  have htrace : WordTrace (prefixWord ++ tailWord_7421833) baseStart_7421833 baseEnd_7421833 := by
    simpa [prefixWord, tailWord_7421833, baseEnd_7421833] using wordTrace_append hprefix tailTrace_7421833
  have hstable : (prefixWord ++ tailWord_7421833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421833).length < 2 ^ (prefixWord ++ tailWord_7421833).sum := by decide
  have hdescent : baseEnd_7421833 < baseStart_7421833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421900 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7421900 : Nat := 118140960795 + 7421900 * 2 ^ 59
def prefixEnd_7421900 : Nat := 4983230072969 + 3 ^ 40 * 7421900 * 2
def baseEnd_7421900 : Nat := 3811002069604617015817309

theorem tailTrace_7421900 : CollatzResearch.WordTrace tailWord_7421900 prefixEnd_7421900 3811002069604617015817309 := by
  unfold tailWord_7421900
  simp only [CollatzResearch.WordTrace]
  refine ⟨135349465905865667224767577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180465954541154222966356769 135349465905865667224767577)
  ·
    refine ⟨101512099429399250418575683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135349465905865667224767577 101512099429399250418575683)
    ·
      refine ⟨152268149144098875627863525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101512099429399250418575683 152268149144098875627863525)
      ·
        refine ⟨28550277964518539180224411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152268149144098875627863525 28550277964518539180224411)
        ·
          refine ⟨42825416946777808770336617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28550277964518539180224411 42825416946777808770336617)
          ·
            refine ⟨32119062710083356577752463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42825416946777808770336617 32119062710083356577752463)
            ·
              refine ⟨48178594065125034866628695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32119062710083356577752463 48178594065125034866628695)
              ·
                refine ⟨72267891097687552299943043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48178594065125034866628695 72267891097687552299943043)
                ·
                  refine ⟨108401836646531328449914565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72267891097687552299943043 108401836646531328449914565)
                  ·
                    refine ⟨20325344371224624084358981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108401836646531328449914565 20325344371224624084358981)
                    ·
                      refine ⟨3811002069604617015817309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20325344371224624084358981 3811002069604617015817309)
                      ·
                        rfl

theorem cell23_7421900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7421900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421900 prefixEnd_7421900 := by exact prefixLift 7421900
  have htrace : WordTrace (prefixWord ++ tailWord_7421900) baseStart_7421900 baseEnd_7421900 := by
    simpa [prefixWord, tailWord_7421900, baseEnd_7421900] using wordTrace_append hprefix tailTrace_7421900
  have hstable : (prefixWord ++ tailWord_7421900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421900).length < 2 ^ (prefixWord ++ tailWord_7421900).sum := by decide
  have hdescent : baseEnd_7421900 < baseStart_7421900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421904 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 2, 2, 2]
def baseStart_7421904 : Nat := 118140960795 + 7421904 * 2 ^ 59
def prefixEnd_7421904 : Nat := 4983230072969 + 3 ^ 40 * 7421904 * 2
def baseEnd_7421904 : Nat := 3811004123527235000167291

theorem tailTrace_7421904 : CollatzResearch.WordTrace tailWord_7421904 prefixEnd_7421904 3811004123527235000167291 := by
  unfold tailWord_7421904
  simp only [CollatzResearch.WordTrace]
  refine ⟨135349538851858421566340383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180466051802477895421787177 135349538851858421566340383)
  ·
    refine ⟨203024308277787632349510575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135349538851858421566340383 203024308277787632349510575)
    ·
      refine ⟨304536462416681448524265863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203024308277787632349510575 304536462416681448524265863)
      ·
        refine ⟨456804693625022172786398795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304536462416681448524265863 456804693625022172786398795)
        ·
          refine ⟨685207040437533259179598193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456804693625022172786398795 685207040437533259179598193)
          ·
            refine ⟨513905280328149944384698645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685207040437533259179598193 513905280328149944384698645)
            ·
              refine ⟨24089310015382028643032749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 513905280328149944384698645 24089310015382028643032749)
              ·
                refine ⟨9033491255768260741137281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24089310015382028643032749 9033491255768260741137281)
                ·
                  refine ⟨6775118441826195555852961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033491255768260741137281 6775118441826195555852961)
                  ·
                    refine ⟨5081338831369646666889721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6775118441826195555852961 5081338831369646666889721)
                    ·
                      refine ⟨3811004123527235000167291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081338831369646666889721 3811004123527235000167291)
                      ·
                        rfl

theorem cell23_7421904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 2, 2].length) (baseStart_7421904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421904 prefixEnd_7421904 := by exact prefixLift 7421904
  have htrace : WordTrace (prefixWord ++ tailWord_7421904) baseStart_7421904 baseEnd_7421904 := by
    simpa [prefixWord, tailWord_7421904, baseEnd_7421904] using wordTrace_append hprefix tailTrace_7421904
  have hstable : (prefixWord ++ tailWord_7421904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421904).length < 2 ^ (prefixWord ++ tailWord_7421904).sum := by decide
  have hdescent : baseEnd_7421904 < baseStart_7421904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7421960 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_7421960 : Nat := 118140960795 + 7421960 * 2 ^ 59
def prefixEnd_7421960 : Nat := 4983230072969 + 3 ^ 40 * 7421960 * 2
def baseEnd_7421960 : Nat := 3811032878443886781067033

theorem tailTrace_7421960 : CollatzResearch.WordTrace tailWord_7421960 prefixEnd_7421960 3811032878443886781067033 := by
  unfold tailWord_7421960
  simp only [CollatzResearch.WordTrace]
  refine ⟨135350560095756982348359667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180467413461009309797812889 135350560095756982348359667)
  ·
    refine ⟨203025840143635473522539501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135350560095756982348359667 203025840143635473522539501)
    ·
      refine ⟨76134690053863302570952313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203025840143635473522539501 76134690053863302570952313)
      ·
        refine ⟨57101017540397476928214235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76134690053863302570952313 57101017540397476928214235)
        ·
          refine ⟨85651526310596215392321353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57101017540397476928214235 85651526310596215392321353)
          ·
            refine ⟨64238644732947161544241015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85651526310596215392321353 64238644732947161544241015)
            ·
              refine ⟨96357967099420742316361523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64238644732947161544241015 96357967099420742316361523)
              ·
                refine ⟨144536950649131113474542285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96357967099420742316361523 144536950649131113474542285)
                ·
                  refine ⟨54201356493424167552953357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144536950649131113474542285 54201356493424167552953357)
                  ·
                    refine ⟨20325508685034062832357509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54201356493424167552953357 20325508685034062832357509)
                    ·
                      refine ⟨3811032878443886781067033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20325508685034062832357509 3811032878443886781067033)
                      ·
                        rfl

theorem cell23_7421960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_7421960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421960 prefixEnd_7421960 := by exact prefixLift 7421960
  have htrace : WordTrace (prefixWord ++ tailWord_7421960) baseStart_7421960 baseEnd_7421960 := by
    simpa [prefixWord, tailWord_7421960, baseEnd_7421960] using wordTrace_append hprefix tailTrace_7421960
  have hstable : (prefixWord ++ tailWord_7421960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421960).length < 2 ^ (prefixWord ++ tailWord_7421960).sum := by decide
  have hdescent : baseEnd_7421960 < baseStart_7421960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
